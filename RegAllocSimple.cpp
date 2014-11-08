#include "../../CodeGen/AllocationOrder.h"
#include "../../CodeGen/LiveDebugVariables.h"
#include "../../CodeGen/Spiller.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/CodeGen/LiveInterval.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include <set>
#include <unordered_map>
#include <iostream>
#include <list>

using namespace llvm;

#define DEBUG_TYPE "regalloc"

namespace llvm{
  FunctionPass* createSimpleRegisterAllocator();
};

static RegisterRegAlloc simpleRegAlloc("simple", "simple register allocator",
    createSimpleRegisterAllocator);

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
        if ((AdjSet.find(std::make_pair(u, v)) != AdjSet.end())
            || (AdjSet.find(std::make_pair(v, u)) != AdjSet.end()))
          return true;
        return false;
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
  };

  class RASimple : public MachineFunctionPass {
    // context
    private:
      MachineFunction *MF;            //check
      const TargetRegisterInfo *TRI;  //check
      const TargetMachine *TM;        //check
      const TargetInstrInfo *TII;     //check
      MachineRegisterInfo *MRI;       //check
      VirtRegMap *VRM;                //check
      LiveIntervals *LIS;
      LiveRegMatrix *Matrix;
      RegisterClassInfo RegClassInfo; //check


      //1st set is Uses regs; 2nd is Defs regs
      typedef std::pair<std::set<unsigned>, std::set<unsigned>> RegsMap;
      typedef std::unordered_map<MachineBasicBlock*, RegsMap>  BBRegsMap;
      BBRegsMap BBRegs;


      std::set<unsigned> UsedPhys, VirtRegs;

      std::unordered_map<MachineBasicBlock*, std::set<unsigned>> LiveOutRegs;
      std::unordered_map<MachineBasicBlock*, std::set<unsigned>> LiveInRegs;

      std::unordered_map<unsigned, std::set<MachineInstr*>> MoveList;
      std::set<MachineInstr*> WorklistMoves, ActiveMoves, CoalescedMoves, 
        ConstrainedMoves;

      std::unordered_map<unsigned, unsigned> Alias;

      std::list<unsigned> Stack;

      Graph* InterGraph;

      std::set<unsigned> SpillWorklist, FreezeWorklist, SimplifyWorklist,
        CoalescedNodes, ColoredNodes, SpilledNodes;

    public:
      RASimple();

      /// Return the pass name.
      const char* getPassName() const override {
        return "Simple Register Allocator";
      }

      /// RASimple analysis usage.
      void getAnalysisUsage(AnalysisUsage &AU) const override;

      /// Perform register allocation.
      bool runOnMachineFunction(MachineFunction &mf) override;

      static char ID;

    private:
      void init(MachineFunction &MF);
      void livenessAnalysis();
      void buildInterferenceGraph();
      void getAllRegs();
      void getLiveness();
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
  };

  char RASimple::ID = 0;

}

RASimple::RASimple(): MachineFunctionPass(ID) {
  initializeLiveDebugVariablesPass(*PassRegistry::getPassRegistry());
  initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
  initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
  initializeRegisterCoalescerPass(*PassRegistry::getPassRegistry());
  initializeMachineSchedulerPass(*PassRegistry::getPassRegistry());
  initializeLiveStacksPass(*PassRegistry::getPassRegistry());
  initializeMachineDominatorTreePass(*PassRegistry::getPassRegistry());
  initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
  initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
  initializeLiveRegMatrixPass(*PassRegistry::getPassRegistry());

}

void RASimple::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  AU.addRequired<AliasAnalysis>();
  AU.addPreserved<AliasAnalysis>();
  AU.addRequired<LiveIntervals>();
  AU.addPreserved<LiveIntervals>();
  AU.addPreserved<SlotIndexes>();
  AU.addRequired<LiveDebugVariables>();
  AU.addPreserved<LiveDebugVariables>();
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
  AU.addRequired<LiveRegMatrix>();
  AU.addPreserved<LiveRegMatrix>();
  MachineFunctionPass::getAnalysisUsage(AU);

}
void RASimple::init(MachineFunction &MF) {
  this->MF  = &MF;
  this->MRI = &this->MF->getRegInfo();
  this->TM  = &this->MF->getTarget();
  this->TII = this->TM->getInstrInfo();
  this->TRI = this->TM->getRegisterInfo();
  this->VRM = &getAnalysis<VirtRegMap>();
  this->LIS = &getAnalysis<LiveIntervals>();
  this->Matrix = &getAnalysis<LiveRegMatrix>();
  RegClassInfo.runOnMachineFunction(VRM->getMachineFunction());
}

void RASimple::getAllRegs() {
  for (MachineBasicBlock& MBB: *MF) {
    for (MachineInstr& Instr: MBB) {
      std::set<unsigned> uses, defs;
      getUsesDefs(Instr, uses, defs);
      for (unsigned reg: uses) {
        BBRegs[&MBB].first.insert(reg);
        if (TRI->isVirtualRegister(reg))
          VirtRegs.insert(reg);
        else UsedPhys.insert(reg);
      }
      for (unsigned reg: defs) {
        BBRegs[&MBB].second.insert(reg);
        if (TRI->isVirtualRegister(reg))
          VirtRegs.insert(reg);
        else UsedPhys.insert(reg);
      }
    }
  }
}

void RASimple::getLiveness() {
  std::set<unsigned> oldIn, oldOut;

  bool finished = false;
  while (!finished) {
    finished = true;
    for (MachineBasicBlock& mbb: *MF) {
      oldIn  = LiveInRegs[&mbb];
      oldOut = LiveOutRegs[&mbb];

      std::set<unsigned> temp;

      LiveInRegs[&mbb].clear();

      std::set_difference(LiveOutRegs[&mbb].begin(), LiveOutRegs[&mbb].end(),
          BBRegs[&mbb].second.begin(), BBRegs[&mbb].second.end(),
          std::inserter(temp, temp.begin()));

      std::set_union(BBRegs[&mbb].first.begin(), BBRegs[&mbb].first.end(),
          temp.begin(), temp.end(),
          std::inserter(LiveInRegs[&mbb], LiveInRegs[&mbb].begin()));

      LiveOutRegs[&mbb].clear();
      if (!mbb.succ_empty()) {
        for (MachineBasicBlock::succ_iterator succIt = mbb.succ_begin(); 
            succIt != mbb.succ_end(); succIt++) {
          MachineBasicBlock *mbbSucc = *succIt;
          std::copy(LiveInRegs[mbbSucc].begin(), LiveInRegs[mbbSucc].end(),
              std::inserter(LiveOutRegs[&mbb], LiveOutRegs[&mbb].begin()));
        }
      }

      if ((LiveInRegs[&mbb] != oldIn) || (LiveOutRegs[&mbb] != oldOut))
        finished = false;
    }
  }
}

void RASimple::livenessAnalysis() {
  getAllRegs();
  getLiveness();
}


void RASimple::getUsesDefs(MachineInstr& Instr, std::set<unsigned>& uses,
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

bool RASimple::isMoveInstr(MachineInstr& Instr) {
  return Instr.isCopyLike();
}

void RASimple::releaseMemory() {
  BBRegs.clear();
  UsedPhys.clear();
  VirtRegs.clear();
  LiveOutRegs.clear();
  LiveInRegs.clear();
  SpillWorklist.clear();
  FreezeWorklist.clear();
  SimplifyWorklist.clear();
  MoveList.clear();
  WorklistMoves.clear();
  CoalescedMoves.clear();
  ConstrainedMoves.clear();
  Stack.clear();
  CoalescedNodes.clear();
  ColoredNodes.clear();
  SpilledNodes.clear();
  Alias.clear();
}

std::set<unsigned> RASimple::adjacent(unsigned n) {
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

void RASimple::addEdge(unsigned u, unsigned v) {
  if (u != v && !InterGraph->isAdjSet(u, v)) {
    InterGraph->addSet(u, v);
    InterGraph->addSet(v, u);
    if (UsedPhys.find(u) == UsedPhys.end())
      InterGraph->addEdge(u, v);
    if (UsedPhys.find(v) == UsedPhys.end())
      InterGraph->addEdge(v, u);
  }
}

void RASimple::buildInterferenceGraph() {
  if (InterGraph != nullptr) delete InterGraph;

  InterGraph = new Graph();

  for (MachineBasicBlock& MBB: *MF) {
    std::set<unsigned> live = LiveOutRegs[&MBB];
    for (MachineBasicBlock::reverse_instr_iterator instrIt = MBB.instr_rbegin();
        instrIt != MBB.instr_rend(); instrIt++) {
      MachineInstr& Instr = *instrIt;
      std::set<unsigned> uses, defs, temp;
      getUsesDefs(Instr, uses, defs);
      if (isMoveInstr(Instr)) {
        temp.clear();
        std::set_difference(live.begin(), live.end(),
            uses.begin(), uses.end(),
            std::inserter(temp, temp.begin()));

        live = temp;

        std::set<unsigned> UsesDefs;
        std::set_union(uses.begin(), uses.end(),
            defs.begin(), defs.end(),
            std::inserter(UsesDefs, UsesDefs.begin()));
        for (unsigned n: UsesDefs) {
          MoveList[n].insert(&Instr);
        }
        WorklistMoves.insert(&Instr);
      }
      temp.clear();
      std::set_union(live.begin(), live.end(),
          defs.begin(), defs.end(),
          std::inserter(temp, temp.begin()));
      live = temp;
      for (unsigned d: defs) {
        for (unsigned l: live)
          addEdge(l, d);
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

std::set<uint16_t> RASimple::getPhysRegs(unsigned VirtReg) {
  ArrayRef<uint16_t> regs = RegClassInfo.getOrder(MRI->getRegClass(VirtReg));
  std::set<uint16_t> AvailablePhys;
  for (size_t i = 0; i < regs.size(); i++)
    AvailablePhys.insert(regs[i]);
  return AvailablePhys;
}

void RASimple::makeWorklist() {
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

std::set<MachineInstr*> RASimple::nodeMoves(unsigned node) {
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

bool RASimple::moveRelated(unsigned node) {
  return !nodeMoves(node).empty();
}

void RASimple::enableMoves(std::set<unsigned>& nodes) {
  for (unsigned n: nodes) {
    for (MachineInstr* m: nodeMoves(n)) {
      if (ActiveMoves.find(m) != ActiveMoves.end()) {
        ActiveMoves.erase(m);
        WorklistMoves.insert(m);
      }
    }
  }
}

void RASimple::decrementDegree(unsigned node) {
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

void RASimple::simplify() {
  unsigned n = *SimplifyWorklist.begin();
  SimplifyWorklist.erase(n);
  Stack.push_back(n);
  for (unsigned m: adjacent(n)) {
    decrementDegree(m);
  }
}

unsigned RASimple::getAlias(unsigned n) {
  if (CoalescedNodes.find(n) != CoalescedNodes.end())
    return getAlias(Alias[n]);
  else return n;
}

void RASimple::getMoveReg(MachineInstr* Instr, unsigned& x, unsigned& y) {
  std::vector<unsigned> regs;
  for (auto& val: MoveList) {
    if (val.second.find(Instr) != val.second.end())
      regs.push_back(val.first);
  }
  assert(regs.size() == 2 && "More than two registers on a move!");
  x = regs[0];
  y = regs[1];
}

void RASimple::addWorklist(unsigned u) {
  if (UsedPhys.find(u) == UsedPhys.end()) {
    unsigned K = getPhysRegs(u).size();
    if (!moveRelated(u) && InterGraph->getDegree(u) < K) {
      FreezeWorklist.erase(u);
      SimplifyWorklist.insert(u);
    }
  }
}

bool RASimple::OK(unsigned t, unsigned r) {
  if (UsedPhys.find(t) != UsedPhys.end()) return true;
  assert(TRI->isVirtualRegister(t) && "not virtual!");
  unsigned K = getPhysRegs(t).size();
  if (InterGraph->getDegree(t) < K) return true;
  if (InterGraph->isAdjSet(t, r)) return true;
  return false;
}

std::string RASimple::getRegClassName(unsigned n) {
  if (UsedPhys.find(n) != UsedPhys.end()) {
    for (unsigned i = 0; i < TRI->getNumRegClasses(); i++) {
      if (TRI->getRegClass(i)->contains(n))
        return std::string(TRI->getRegClass(i)->getName());
    }
  }
  return std::string(MRI->getRegClass(n)->getName());
}

bool RASimple::conservative(std::set<unsigned>& nodes) {
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

void RASimple::combine(unsigned u, unsigned v) {
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

void RASimple::coalesce() {
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

void RASimple::freezeMoves(unsigned u) {
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

void RASimple::freeze() {
  unsigned u = *FreezeWorklist.begin();
  FreezeWorklist.erase(u);
  SimplifyWorklist.insert(u);
  freezeMoves(u);
}

void RASimple::selectSpill() {
  //TODO -> implement heuristic to get a node.
  unsigned m = *SpillWorklist.begin();
  SpillWorklist.erase(m);
  SimplifyWorklist.insert(m);
  freezeMoves(m);
}

void RASimple::assignColors() {
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
        okColors.erase(InterGraph->getColor(getAlias(w)));
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
  for (unsigned n: CoalescedNodes) {
    InterGraph->setColor(n, InterGraph->getColor(getAlias(n)));
  }
}

bool RASimple::runOnMachineFunction(MachineFunction &mf) {
  DEBUG(dbgs() << "********** SIMPLE REGISTER ALLOCATION **********\n"
      << "********** Function: "  << mf.getName() << '\n');

  init(mf);

  livenessAnalysis();

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

  for (unsigned n: VirtRegs) {
    if (InterGraph->getColor(n) != 0) {
      std::cout << n << ": " << InterGraph->getColor(n) << std::endl;
      VRM->assignVirt2Phys(n, InterGraph->getColor(n));
    }
    else if (SpilledNodes.find(n) == SpilledNodes.end()) {
      std::cout << n << ": " << getAlias(n) << std::endl;
      VRM->assignVirt2Phys(n, getAlias(n));
      for (MachineInstr* instr: MoveList[n]) {
        instr->eraseFromParent();
      }
    }
  }
  while (!SpilledNodes.empty()) {
    unsigned n = *SpilledNodes.begin();
    VRM->assignVirt2StackSlot(n);
  }

  std::cout << "\n";

  releaseMemory();

  return true;
}

FunctionPass* llvm::createSimpleRegisterAllocator() {
  return new RASimple();
}
