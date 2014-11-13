#include "llvm/CodeGen/Passes.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/CodeGen/LiveInterval.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include "LiveOutSets.h"
#include <set>
#include <unordered_map>
#include <iostream>
#include <list>

using namespace llvm;

#define DEBUG_TYPE "regalloc"

namespace llvm{
  FunctionPass* createGCRegisterAllocator();
}

static RegisterRegAlloc gcRegAlloc("gc", "graph coloring register allocator",
    createGCRegisterAllocator);

namespace {
  class Graph {
    private:
      std::unordered_map<unsigned, std::set<unsigned>> AdjList;
      std::unordered_map<unsigned, unsigned> Degree;
      std::unordered_map<unsigned, unsigned> Color;
      std::set<std::pair<unsigned, unsigned>> AdjSet;
      std::set<unsigned> Nodes;

    public:
      Graph() {};

      void addSet(unsigned u, unsigned v) {
        AdjSet.insert(std::make_pair(u, v));
      }

      bool isAdjSet(unsigned u, unsigned v) {
        return (AdjSet.find(std::make_pair(u, v)) != AdjSet.end()
            || AdjSet.find(std::make_pair(v, u)) != AdjSet.end());
      }

      void addEdge(unsigned u , unsigned v) {
        AdjList[u].insert(v);
        Degree[u] += 1;
        Nodes.insert(u);
      }

      std::set<unsigned>& getNodes() {
        return Nodes;
      };

      unsigned getDegree(unsigned reg) {
        return Degree[reg];
      }

      std::set<unsigned> getAdj(unsigned u) {
        return AdjList[u];
      }

      void setDegree(unsigned reg, unsigned degree) {
        Degree[reg] = degree;
      }

      void setColor(unsigned reg, unsigned color) {
        Color[reg] = color;
      }

      unsigned getColor(unsigned reg) {
        if (Color.find(reg) != Color.end())
          return Color[reg];
        else return reg;
      }

      bool hasEdge(unsigned u, unsigned v) {
        return (AdjList[u].find(v) != AdjList[u].end()
            || AdjList[v].find(u) != AdjList[v].end());
      }
  };

  class RAGraphColoring : public MachineFunctionPass {
    // context
    private:
      MachineFunction *MF;            //check
      const TargetRegisterInfo *TRI;  //check
      const TargetMachine *TM;        //check
      const TargetInstrInfo *TII;     //check
      MachineRegisterInfo *MRI;       //check
      VirtRegMap *VRM;                //check
      RegisterClassInfo RegClassInfo; //check
      LiveIntervals *LIS;
      SlotIndexes* SI;

      std::set<unsigned> UsedPhys, VirtRegs;

      std::unordered_map<unsigned, std::set<MachineInstr*>> MoveList;
      std::set<MachineInstr*> WorklistMoves, ActiveMoves, CoalescedMoves, 
        ConstrainedMoves;

      std::unordered_map<unsigned, unsigned> Alias;

      std::unordered_map<unsigned, int> StackSlot;

      unsigned spills, removedMoves;

      std::list<unsigned> Stack;

      Graph* InterGraph;

      std::set<unsigned> SpillWorklist, FreezeWorklist, SimplifyWorklist,
        CoalescedNodes, ColoredNodes, SpilledNodes;

    public:
      RAGraphColoring();

      /// Return the pass name.
      const char* getPassName() const override {
        return "Graph Coloring Register Allocator";
      }

      /// RAGraphColoring analysis usage.
      void getAnalysisUsage(AnalysisUsage &AU) const override;

      /// Perform register allocation.
      bool runOnMachineFunction(MachineFunction &mf) override;

      static char ID;

    private:
      void init(MachineFunction &MF);
      void buildInterferenceGraph();
      void getAllRegs();
      void getSuccessor(MachineBasicBlock&, std::set<MachineBasicBlock*>&,
          std::set<unsigned>&, std::set<unsigned>&, bool&);
      void getUsesDefs(MachineInstr&, std::set<unsigned>&, std::set<unsigned>&);
      bool isMoveInstr(MachineInstr&);
      void makeWorklist();
      void addEdge(unsigned, unsigned);
      std::set<uint16_t> getPhysRegs(unsigned);
      void releaseMemory();
      std::set<MachineInstr*> nodeMoves(unsigned);
      std::set<unsigned> adjacent(unsigned);
      std::string getRegClassName(unsigned);
      unsigned getSpillWorklistNode();
      void enableMoves(std::set<unsigned>&);
      void addWorklist(unsigned);
      void getMoveReg(MachineInstr*, unsigned&, unsigned&);
      unsigned getAlias(unsigned);
      bool moveRelated(unsigned);
      void decrementDegree(unsigned);
      void combine(unsigned, unsigned);
      bool OK(unsigned, unsigned);
      bool conservative(std::set<unsigned>&);
      void freezeMoves(unsigned);
      void simplify();
      void coalesce();
      void freeze();
      void selectSpill();
      void assignColors();
      int getStackSpaceFor(unsigned);
      void rewriteProgram();
  };

  char RAGraphColoring::ID = 0;

}

RAGraphColoring::RAGraphColoring(): MachineFunctionPass(ID) {
  initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
  initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
  initializeRegisterCoalescerPass(*PassRegistry::getPassRegistry());
  initializeMachineSchedulerPass(*PassRegistry::getPassRegistry());
  initializeLiveStacksPass(*PassRegistry::getPassRegistry());
  initializeMachineDominatorTreePass(*PassRegistry::getPassRegistry());
  initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
  initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
}

void RAGraphColoring::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  AU.addRequired<AliasAnalysis>();
  AU.addPreserved<AliasAnalysis>();
  AU.addRequired<LiveIntervals>();
  AU.addPreserved<LiveIntervals>();
  AU.addPreserved<SlotIndexes>();
  AU.addRequired<SlotIndexes>();
  AU.addRequired<LiveStacks>();
  AU.addPreserved<LiveStacks>();
  AU.addRequired<MachineBlockFrequencyInfo>();
  AU.addPreserved<MachineBlockFrequencyInfo>();
  AU.addRequiredID(MachineDominatorsID);
  AU.addPreservedID(MachineDominatorsID);
  AU.addRequired<MachineLoopInfo>();
  AU.addPreserved<MachineLoopInfo>();
  AU.addRequired<VirtRegMap>();
  AU.addPreserved<VirtRegMap>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

void RAGraphColoring::init(MachineFunction &MF) {
  this->MF  = &MF;
  this->MRI = &this->MF->getRegInfo();
  this->TM  = &this->MF->getTarget();
  this->TII = this->TM->getInstrInfo();
  this->TRI = this->TM->getRegisterInfo();
  this->VRM = &getAnalysis<VirtRegMap>();
  this->SI  = &getAnalysis<SlotIndexes>();
  this->LIS = &getAnalysis<LiveIntervals>();
  MRI->freezeReservedRegs(VRM->getMachineFunction());
  RegClassInfo.runOnMachineFunction(VRM->getMachineFunction());
}

void RAGraphColoring::getAllRegs() {
  for (MachineBasicBlock& MBB: *MF) {
    for (MachineInstr& Instr: MBB) {
      std::set<unsigned> uses, defs;
      getUsesDefs(Instr, uses, defs);
      for (unsigned reg: uses) {
        if (TRI->isVirtualRegister(reg))
          VirtRegs.insert(reg);
        else UsedPhys.insert(reg);
      }
      for (unsigned reg: defs) {
        if (TRI->isVirtualRegister(reg))
          VirtRegs.insert(reg);
        else UsedPhys.insert(reg);
      }
    }
  }
}

void RAGraphColoring::getUsesDefs(MachineInstr& Instr, std::set<unsigned>& uses,
    std::set<unsigned>& defs) {
  for (unsigned i = 0; i < Instr.getNumOperands(); i++) {
    MachineOperand& oper = Instr.getOperand(i);
    if (oper.isReg() && oper.getReg() != 0) {
      unsigned Reg = oper.getReg();
      if (oper.isUse()) uses.insert(Reg);
      else if (oper.isDef()) defs.insert(Reg);
    } 
  }
  //implicit use of registers
  if (Instr.getDesc().getImplicitUses())
    for (const uint16_t *regs = Instr.getDesc().getImplicitUses(); 
        *regs; regs++) {
      uses.insert(*regs);
    }
  //implicit def of registers
  if (Instr.getDesc().getImplicitDefs())
    for (const uint16_t *regs = Instr.getDesc().getImplicitDefs(); 
        *regs; regs++) {
      defs.insert(*regs);
    }
}

bool RAGraphColoring::isMoveInstr(MachineInstr& Instr) {
  return Instr.isCopyLike();
}

void RAGraphColoring::releaseMemory() {
  UsedPhys.clear();
  VirtRegs.clear();
  SpillWorklist.clear();
  FreezeWorklist.clear();
  SimplifyWorklist.clear();
  MoveList.clear();
  WorklistMoves.clear();
  CoalescedMoves.clear();
  ActiveMoves.clear();
  ConstrainedMoves.clear();
  Stack.clear();
  CoalescedNodes.clear();
  ColoredNodes.clear();
  SpilledNodes.clear();
  Alias.clear();
  StackSlot.clear();
}

std::set<unsigned> RAGraphColoring::adjacent(unsigned n) {
  std::set<unsigned> temp, adj, adjNodes;
  std::set_union(Stack.begin(), Stack.end(),
      CoalescedNodes.begin(), CoalescedNodes.end(),
      std::inserter(temp, temp.begin()));
  adjNodes = InterGraph->getAdj(n);
  std::set_difference(adjNodes.begin(), adjNodes.end(),
      temp.begin(), temp.end(),
      std::inserter(adj, adj.begin()));
  return adj;
}

void RAGraphColoring::addEdge(unsigned u, unsigned v) {
  if (u != v && !InterGraph->isAdjSet(u, v)) {
    InterGraph->addSet(u, v);
    InterGraph->addSet(v, u);
    if (UsedPhys.find(u) == UsedPhys.end())
      InterGraph->addEdge(u, v);
    if (UsedPhys.find(v) == UsedPhys.end())
      InterGraph->addEdge(v, u);
  }
}

void RAGraphColoring::buildInterferenceGraph() {
  InterGraph = new Graph();

  LiveOutSets* los = new LiveOutSets(*MF);

  for (MachineBasicBlock& MBB: *MF) {
    std::set<unsigned> live(los->getAliveOutSet(&MBB));
    for (MachineBasicBlock::reverse_instr_iterator instrIt = MBB.instr_rbegin();
        instrIt != MBB.instr_rend(); instrIt++) {
      MachineInstr& Instr = *instrIt;
      std::set<unsigned> uses, defs, temp;
      getUsesDefs(Instr, uses, defs);
      if (isMoveInstr(Instr)) {
        bool insertMove = false;
        if (TRI->isVirtualRegister(*uses.begin()) 
            && TRI->isPhysicalRegister(*defs.begin())) {
          std::set<uint16_t> regs = getPhysRegs(*uses.begin());
          if (regs.find(*defs.begin()) != regs.end())
            insertMove = true;
        }
        if (insertMove) {
          live.erase(*uses.begin());

          std::set<unsigned> UsesDefs;
          std::set_union(uses.begin(), uses.end(),
              defs.begin(), defs.end(),
              std::inserter(UsesDefs, UsesDefs.begin()));
          for (unsigned n: UsesDefs) {
            MoveList[n].insert(&Instr);
          }
          WorklistMoves.insert(&Instr);
        }
      }
      std::copy(defs.begin(), defs.end(),
          std::inserter(live, live.begin()));
      for (unsigned d: defs) {
        for (unsigned l: live){
          addEdge(l, d);
        }
      }
      temp.clear();
      std::set_difference(live.begin(), live.end(),
          defs.begin(), defs.end(),
          std::inserter(temp, temp.begin()));
      live.clear();
      std::set_union(temp.begin(), temp.end(),
          uses.begin(), uses.end(),
          std::inserter(live, live.begin()));
    }
  }
}

std::set<uint16_t> RAGraphColoring::getPhysRegs(unsigned VirtReg) {
  ArrayRef<uint16_t> regs = RegClassInfo.getOrder(MRI->getRegClass(VirtReg));
  std::set<uint16_t> AvailablePhys;
  for (size_t i = 0; i < regs.size(); i++)
    AvailablePhys.insert(regs[i]);
  return AvailablePhys;
}

void RAGraphColoring::makeWorklist() {
  for (unsigned VirtReg: VirtRegs) {
    unsigned K = getPhysRegs(VirtReg).size();
    if (InterGraph->getDegree(VirtReg) >= K)
      SpillWorklist.insert(VirtReg);
    else if (moveRelated(VirtReg))
      FreezeWorklist.insert(VirtReg);
    else
      SimplifyWorklist.insert(VirtReg);
  }
}

std::set<MachineInstr*> RAGraphColoring::nodeMoves(unsigned node) {
  std::set<MachineInstr*> temp;
  std::set_union(WorklistMoves.begin(), WorklistMoves.end(),
      ActiveMoves.begin(), ActiveMoves.end(),
      std::inserter(temp, temp.begin()));
  std::set<MachineInstr*> tempUnion;
  std::set_intersection(MoveList[node].begin(), MoveList[node].end(),
      temp.begin(), temp.end(),
      std::inserter(tempUnion, tempUnion.begin()));
  return tempUnion;
}

bool RAGraphColoring::moveRelated(unsigned node) {
  return !nodeMoves(node).empty();
}

void RAGraphColoring::enableMoves(std::set<unsigned>& nodes) {
  for (unsigned n: nodes) {
    for (MachineInstr* m: nodeMoves(n)) {
      if (ActiveMoves.find(m) != ActiveMoves.end()) {
        ActiveMoves.erase(m);
        WorklistMoves.insert(m);
      }
    }
  }
}

void RAGraphColoring::decrementDegree(unsigned node) {
  if (UsedPhys.find(node) != UsedPhys.end()) return;
  unsigned d = InterGraph->getDegree(node);
  InterGraph->setDegree(node, d - 1);
  assert(TRI->isVirtualRegister(node) && "not virtual!");
  unsigned K = getPhysRegs(node).size();
  if (d == K) {
    std::set<unsigned> temp = adjacent(node);
    temp.insert(node);
    enableMoves(temp);
    SpillWorklist.erase(node);
    if (moveRelated(node))
      FreezeWorklist.insert(node);
    else
      SimplifyWorklist.insert(node);
  }
}

void RAGraphColoring::simplify() {
  unsigned n = *SimplifyWorklist.begin();
  SimplifyWorklist.erase(n);
  Stack.push_back(n);
  for (unsigned m: adjacent(n)) {
    decrementDegree(m);
  }
}

unsigned RAGraphColoring::getAlias(unsigned n) {
  if (CoalescedNodes.find(n) != CoalescedNodes.end())
    return getAlias(Alias[n]);
  else return n;
}

void RAGraphColoring::getMoveReg(MachineInstr* Instr, unsigned& x, 
    unsigned& y) {
  std::vector<unsigned> regs;
  for (auto& val: MoveList) {
    if (val.second.find(Instr) != val.second.end())
      regs.push_back(val.first);
  }
  assert(regs.size() == 2 && "More than two registers on a move!");
  x = regs[0];
  y = regs[1];
}

void RAGraphColoring::addWorklist(unsigned u) {
  if (UsedPhys.find(u) == UsedPhys.end()) {
    unsigned K = getPhysRegs(u).size();
    if (!moveRelated(u) && InterGraph->getDegree(u) < K) {
      FreezeWorklist.erase(u);
      SimplifyWorklist.insert(u);
    }
  }
}

bool RAGraphColoring::OK(unsigned t, unsigned r) {
  if (UsedPhys.find(t) != UsedPhys.end()) return true;
  assert(TRI->isVirtualRegister(t) && "not virtual!");
  unsigned K = getPhysRegs(t).size();
  if (InterGraph->getDegree(t) < K) return true;
  if (InterGraph->isAdjSet(t, r)) return true;
  return false;
}

std::string RAGraphColoring::getRegClassName(unsigned n) {
  if (UsedPhys.find(n) != UsedPhys.end()) {
    for (unsigned i = 0; i < TRI->getNumRegClasses(); i++) {
      if (TRI->getRegClass(i)->contains(n))
        return std::string(TRI->getRegClass(i)->getName());
    }
  }
  return std::string(MRI->getRegClass(n)->getName());
}

bool RAGraphColoring::conservative(std::set<unsigned>& nodes) {
  std::unordered_map<std::string, std::pair<unsigned, unsigned>> RegClass;
  for (unsigned n: nodes) {
    if (TRI->isVirtualRegister(n)) {
      unsigned K = getPhysRegs(n).size();
      if (InterGraph->getDegree(n) >= K) {
        RegClass[getRegClassName(n)].first = K;
        RegClass[getRegClassName(n)].second++;
      }
    }
    else RegClass[getRegClassName(n)].second++;
  }
  for (auto& reg: RegClass) {
    if (reg.second.second >= reg.second.first){
      return false;
    }
  }
  return true;
}

void RAGraphColoring::combine(unsigned u, unsigned v) {
  if (FreezeWorklist.find(v) != FreezeWorklist.end()) {
    FreezeWorklist.erase(v);
  }
  else
    SpillWorklist.erase(v);
  CoalescedNodes.insert(v);
  Alias[v] = u;
  for (unsigned t: adjacent(v)) {
    addEdge(t, u);
    decrementDegree(t);
  }
  if (FreezeWorklist.find(u) != FreezeWorklist.end()) {
    assert(TRI->isVirtualRegister(u) && "not virtual!");
    unsigned K = getPhysRegs(u).size();
    if (InterGraph->getDegree(u) >= K) {
      FreezeWorklist.erase(u);
      SpillWorklist.insert(u);
    }
  }
}

void RAGraphColoring::coalesce() {
  MachineInstr* m = *WorklistMoves.begin();
  unsigned x, y;
  getMoveReg(m, x, y);
  x = getAlias(x);
  y = getAlias(y);
  std::pair<unsigned, unsigned> pair;
  if (UsedPhys.find(y) != UsedPhys.end())
    pair = std::make_pair(y, x);
  else
    pair = std::make_pair(x, y);
  WorklistMoves.erase(m);
  if (pair.first == pair.second) {
    CoalescedMoves.insert(m);
    addWorklist(pair.first);
    return;
  } 
  else if (UsedPhys.find(pair.second) != UsedPhys.end()
      || InterGraph->isAdjSet(pair.first, pair.second)) {
    ConstrainedMoves.insert(m);
    addWorklist(pair.first);
    addWorklist(pair.second);
    return;
  }
  bool isConservative = false, allOK = false;
  if (UsedPhys.find(pair.first) != UsedPhys.end()) {
    allOK = true;
    for (unsigned t: adjacent(pair.second)) {
      if (!OK(t, pair.first)) {
        allOK = false;
        break;
      }
    }
  }
  else {
    std::set<unsigned> nodes, adjU, adjV;
    adjU = adjacent(pair.first);
    adjV = adjacent(pair.second);
    std::set_union(adjU.begin(), adjU.end(),
        adjV.begin(), adjV.end(),
        std::inserter(nodes, nodes.begin()));
    isConservative = conservative(nodes);
  }
  if (allOK || isConservative) {
    CoalescedMoves.insert(m);
    combine(pair.first, pair.second);
    addWorklist(pair.first);
  }
  else {
    ActiveMoves.insert(m);
  }
}

void RAGraphColoring::freezeMoves(unsigned u) {
  for (MachineInstr* m: nodeMoves(u)) {
    unsigned x, y, v;
    getMoveReg(m, x, y);
    if (getAlias(y) == getAlias(u))
      v = getAlias(x);
    else
      v = getAlias(y);
    ActiveMoves.erase(m);
    if (nodeMoves(v).empty() && TRI->isVirtualRegister(v)) {
      unsigned K = getPhysRegs(v).size();
      if (InterGraph->getDegree(v) < K) {
        FreezeWorklist.erase(v);
        SimplifyWorklist.insert(v);
      }
    }
  }
}

void RAGraphColoring::freeze() {
  unsigned u = *FreezeWorklist.begin();
  FreezeWorklist.erase(u);
  SimplifyWorklist.insert(u);
  freezeMoves(u);
}

unsigned RAGraphColoring::getSpillWorklistNode() {
  unsigned bestNode = 0, minWeight = std::numeric_limits<unsigned>::max();
  for (unsigned m: SpillWorklist) {
    unsigned degree = InterGraph->getDegree(m);
    if (degree < minWeight) {
      bestNode  = m;
      minWeight = degree;
    }
  }
  return bestNode;
}

void RAGraphColoring::selectSpill() {
  unsigned m = getSpillWorklistNode();
  SpillWorklist.erase(m);
  SimplifyWorklist.insert(m);
  freezeMoves(m);
}

void RAGraphColoring::assignColors() {
  for (unsigned n: CoalescedNodes) {
    unsigned color = InterGraph->getColor(getAlias(n));
    InterGraph->setColor(n, color);
  }
  while (!Stack.empty()) {
    unsigned n = Stack.back();
    Stack.pop_back();
    std::set<uint16_t> okColors = getPhysRegs(n);
    for (unsigned w: InterGraph->getAdj(n)) {
      std::set<unsigned> temp;
      
      std::set_union(ColoredNodes.begin(), ColoredNodes.end(),
          UsedPhys.begin(), UsedPhys.end(),
          std::inserter(temp, temp.begin()));
      
      if (temp.find(getAlias(w)) != temp.end()) {
        unsigned colorNode = InterGraph->getColor(getAlias(w));
        std::set<unsigned> subSuperRegs;
        for (MCSubRegIterator I(colorNode, TRI); I.isValid(); ++I)
          subSuperRegs.insert(*I);
        for (MCSuperRegIterator I(colorNode, TRI); I.isValid(); ++I)
          subSuperRegs.insert(*I);
        subSuperRegs.insert(colorNode);
        for (unsigned reg: subSuperRegs) {
          if (okColors.find(reg) != okColors.end()) {
            okColors.erase(reg);
            break;
          }
        }
      }
    }
    if (okColors.empty()) {
      SpilledNodes.insert(n);
    }
    else {
      ColoredNodes.insert(n);
      unsigned c = *okColors.begin();
      InterGraph->setColor(n, c);
    }
  }
}

int RAGraphColoring::getStackSpaceFor(unsigned VirtReg) {
  if (StackSlot.find(VirtReg) != StackSlot.end())
    return StackSlot[VirtReg];
  const TargetRegisterClass *RC = MRI->getRegClass(VirtReg);
  StackSlot[VirtReg] = MF->getFrameInfo()->CreateSpillStackObject(RC->getSize(),
      RC->getAlignment());
  return StackSlot[VirtReg];
}

void RAGraphColoring::rewriteProgram() {
  for (MachineBasicBlock& MBB: *MF) {
    for (MachineBasicBlock::iterator MI = MBB.begin(); MI != MBB.end(); MI++) {
      for (unsigned i = 0; i < MI->getNumOperands(); i++) {
        MachineOperand& oper = MI->getOperand(i);
        if (oper.isReg() 
            && SpilledNodes.find(oper.getReg()) != SpilledNodes.end()) {
          unsigned Reg = oper.getReg();
          int FrameIdx = getStackSpaceFor(Reg);
          const TargetRegisterClass *RC = MRI->getRegClass(Reg);
          unsigned NewReg = MRI->createVirtualRegister(RC);
          if (oper.isUse()) {
            TII->loadRegFromStackSlot(MBB, MI, NewReg, FrameIdx, RC, TRI);
          }
          else if (oper.isDef()) {
            TII->storeRegToStackSlot(MBB, next(MI), NewReg, oper.isKill(), FrameIdx, RC, TRI);
          }
          SI->repairIndexesInRange(&MBB, MBB.begin(), MBB.end());
          oper.setReg(NewReg);
        }
      }
    }
  }
}

bool RAGraphColoring::runOnMachineFunction(MachineFunction &mf) {
  DEBUG(dbgs() << "********** GRAPH COLORING REGISTER ALLOCATION **********\n"
      << "********** Function: "  << mf.getName() << '\n');

  std::cout << std::string(mf.getName()) << ":\n";

  init(mf);

  bool finished = false;

  while (!finished) {
    getAllRegs();

    buildInterferenceGraph();

    makeWorklist();

    while (!SimplifyWorklist.empty() || !WorklistMoves.empty()
        || !FreezeWorklist.empty() || !SpillWorklist.empty()) {
      if (!SimplifyWorklist.empty()) simplify();
      else if (!WorklistMoves.empty()) coalesce();
      else if (!FreezeWorklist.empty()) freeze();
      else if (!SpillWorklist.empty()) selectSpill();
    }

    assignColors();

    finished = true;
    if (!SpilledNodes.empty()) {
      finished = false;
      spills += SpilledNodes.size();
      rewriteProgram();
      releaseMemory();
    }
  }

  std::cout << "\tVirtual registers: " << VirtRegs.size() << "\n";
  std::cout << "\tRemoved moves: " << CoalescedNodes.size() << "\n";
  std::cout << "\tSpills: " << spills << "\n";

  VRM->clearAllVirt();
  for (unsigned n: VirtRegs) {
    VRM->assignVirt2Phys(n, InterGraph->getColor(n));
  }

  releaseMemory();

  spills = 0;

  return true;
}

FunctionPass* llvm::createGCRegisterAllocator() {
  return new RAGraphColoring();
}
