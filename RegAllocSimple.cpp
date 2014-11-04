#include "../../CodeGen/AllocationOrder.h"
#include "../../CodeGen/Spiller.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include <set>
#include <unordered_map>
#include <iostream>

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
      std::set<unsigned> Nodes;
    
      bool isAdjSet(unsigned u, unsigned v) {
        if (AdjList.find(u) != AdjList.end()) {
          if (AdjList[u].find(v) != AdjList[u].end())
            return true;
        }
        return false;
      };

      void makeAdjSet(unsigned u, unsigned v) {
        AdjList[u].insert(v);
        AdjList[v].insert(u);
        Nodes.insert(u);
        Nodes.insert(v);
      };

    public:
      Graph() {};
      void addEdge(unsigned u , unsigned v) {
        if ((u != v) && !isAdjSet(u, v)) {
          makeAdjSet(u, v);
          Degree[u] += 1;
          Degree[v] += 1;
        }
      };

      std::set<unsigned>& getNodes() {
        return Nodes;
      };

      unsigned getDegree(unsigned reg) {
        return Degree[reg];
      }
  };

  class RASimple : public MachineFunctionPass {
    // context
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

    std::set<unsigned> UsedPhys;

    std::unordered_map<MachineBasicBlock*, std::set<unsigned>> LiveOutRegs;
    std::unordered_map<MachineBasicBlock*, std::set<unsigned>> LiveInRegs;

    std::unordered_map<unsigned, std::set<MachineInstr*>> MoveList;
    std::set<MachineInstr*> WorklistMoves;

    Graph* InterGraph;

    std::set<unsigned> spillWorklist, freezeWorklist, simplifyWorklist;

    // state
    Spiller *SpillerInstance;

    public:
    RASimple();

    /// Return the pass name.
    const char* getPassName() const override {
      return "Simple Register Allocator";
    }

    // A RegAlloc pass should call this before allocatePhysRegs.
    void init(MachineFunction &MF);

    // The top-level driver. The output is a VirtRegMap that us updated with
    // physical register assignments.
    void allocatePhysRegs();

    /// RASimple analysis usage.
    void getAnalysisUsage(AnalysisUsage &AU) const override;

    unsigned selectOrSpill(LiveInterval &VirtReg);

    /// Perform register allocation.
    bool runOnMachineFunction(MachineFunction &mf) override;

    static char ID;

    private:
      void livenessAnalysis();
      void buildInterferenceGraph();
      void getAllRegs();
      void getLiveness();
      void DFS(MachineBasicBlock&, std::vector<MachineBasicBlock*>&, std::set<MachineBasicBlock*>&);
      void getSuccessor(MachineBasicBlock&, std::set<MachineBasicBlock*>&,
                        std::set<unsigned>&, std::set<unsigned>&, bool&);
      void getUsesDefs(MachineInstr&, std::set<unsigned>&, std::set<unsigned>&);
      bool isMoveInstr(MachineInstr&);
      void makeWorklist();
      std::set<uint16_t> getPhysRegs(unsigned);
      void releaseMemory();
  };

  char RASimple::ID = 0;

}

RASimple::RASimple(): MachineFunctionPass(ID) {
  initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
  initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
  initializeLiveRegMatrixPass(*PassRegistry::getPassRegistry());
  initializeLiveStacksPass(*PassRegistry::getPassRegistry());
  initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
  initializeMachineBlockFrequencyInfoPass(*PassRegistry::getPassRegistry());
}

void RASimple::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<AliasAnalysis>();
  AU.addPreserved<AliasAnalysis>();
  AU.addRequired<LiveIntervals>();
  AU.addPreserved<LiveIntervals>();
  AU.addRequired<VirtRegMap>();
  AU.addPreserved<VirtRegMap>();
  AU.addRequired<LiveRegMatrix>();
  AU.addPreserved<LiveRegMatrix>();
  AU.addRequired<LiveStacks>();
  AU.addPreserved<LiveStacks>();  
  AU.addRequired<MachineLoopInfo>();
  AU.addPreserved<MachineLoopInfo>();
  AU.addRequired<MachineBlockFrequencyInfo>();
  AU.addPreserved<MachineBlockFrequencyInfo>();
  AU.addRequiredID(MachineDominatorsID);
  AU.addPreservedID(MachineDominatorsID);
  MachineFunctionPass::getAnalysisUsage(AU);
}
void RASimple::init(MachineFunction &MF) {
  this->MF  = &MF;
  this->MRI = &this->MF->getRegInfo();
  this->TM  = &this->MF->getTarget();
  this->TII = this->TM->getInstrInfo();
  this->TRI = this->TM->getRegisterInfo();
  this->VRM = &getAnalysis<VirtRegMap>();


  RegClassInfo.runOnMachineFunction(VRM->getMachineFunction());
}

void RASimple::allocatePhysRegs() {
  DEBUG(dbgs() << "********** LIVE REGISTERS **********\n" <<
      "Num Virt Regs: " << MRI->getNumVirtRegs() << "\n");

  // Continue assigning vregs one at a time to available physical registers.
  for (unsigned i = 0; i < MRI->getNumVirtRegs(); i++){
    unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
    if (!MRI->reg_nodbg_empty(Reg)){
      LiveInterval *VirtReg = &LIS->getInterval(Reg);

      assert(!VRM->hasPhys(VirtReg->reg) && "Register already assigned");

      DEBUG(dbgs() << "\nselectOrSpill "
          << MRI->getRegClass(VirtReg->reg)->getName()
          << ':' << *VirtReg << '\n');

      unsigned AvailablePhysReg = selectOrSpill(*VirtReg);

      if (AvailablePhysReg)
        Matrix->assign(*VirtReg, AvailablePhysReg);
    }
  }
}

unsigned RASimple::selectOrSpill(LiveInterval &VirtReg) {
  // Check for an available register in this class.
  AllocationOrder Order(VirtReg.reg, *VRM, RegClassInfo);
  while (unsigned PhysReg = Order.next()) {
    // Check for interference in PhysReg
    switch (Matrix->checkInterference(VirtReg, PhysReg)) {
      case LiveRegMatrix::IK_Free:
        // PhysReg is available, allocate it.
        return PhysReg;

      default:
        // Virt Reg, RegMask or RegUnit interference.
        continue;
    }
  }
  // No other spill candidates were found, so spill the current VirtReg.
  DEBUG(dbgs() << "spilling: " << VirtReg << '\n');
  SmallVector<unsigned, 1> VirtVet;
  LiveRangeEdit LRE(&VirtReg, VirtVet, *MF, *LIS, VRM);
  SpillerInstance->spill(LRE);

  return 0;
}

void RASimple::getAllRegs() {
  for (MachineBasicBlock& MBB: *MF) {
    for (MachineInstr& Instr: MBB) {
      std::set<unsigned> uses, defs;
      getUsesDefs(Instr, uses, defs);
      for (unsigned reg: uses)
        BBRegs[&MBB].first.insert(reg);
      for (unsigned reg: defs)
        BBRegs[&MBB].second.insert(reg);
    }
  }
}

void RASimple::DFS(MachineBasicBlock& MBB, 
                   std::vector<MachineBasicBlock*>& mbbOrder,
                   std::set<MachineBasicBlock*>& visited) {
  if (visited.find(&MBB) == visited.end()){
    visited.insert(&MBB);
    mbbOrder.push_back(&MBB);
    if (!MBB.succ_empty()){
      for (MachineBasicBlock::succ_iterator succIt = MBB.succ_begin();
              succIt != MBB.succ_end(); succIt++) {
        MachineBasicBlock* succ = *succIt;
        DFS(*succ, mbbOrder, visited);
      }
    } 
  }
}

void RASimple::getLiveness() {
  //std::vector<MachineBasicBlock*> mbbOrder;
  //std::set<MachineBasicBlock*> visited;
 
  //for (MachineBasicBlock& MBB: *MF) {
  //  DFS(MBB, mbbOrder, visited);
  //}

  std::set<unsigned> oldIn, oldOut;
  
  bool finished = false;
  while (!finished) {
    finished = true;
    for (MachineBasicBlock& mbb: *MF) {
    //for (std::vector<MachineBasicBlock*>::reverse_iterator 
    //          mbbIt = mbbOrder.rbegin(); mbbIt != mbbOrder.rend(); mbbIt++) {

      //MachineBasicBlock *mbb = *mbbIt;

      oldIn  = LiveInRegs[&mbb];
      oldOut = LiveOutRegs[&mbb];
    
      std::set<unsigned> temp;

      //LiveInRegs[&mbb].clear();

      std::set_difference(LiveOutRegs[&mbb].begin(), LiveOutRegs[&mbb].end(),
                          BBRegs[&mbb].second.begin(), BBRegs[&mbb].second.end(),
                          std::inserter(temp, temp.begin()));

      std::set_union(BBRegs[&mbb].first.begin(), BBRegs[&mbb].first.end(),
                     temp.begin(), temp.end(),
                     std::inserter(LiveInRegs[&mbb], LiveInRegs[&mbb].begin()));

      //LiveOutRegs[&mbb].clear();
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
  //for (auto& t: LiveOutRegs){
  //  std::cout << t.first << ": ";
  //  for (auto& a: t.second){
  //    std::cout << a << " ";
  //  }
  //  std::cout << "\n\n";
  //}
}

void RASimple::livenessAnalysis() {
  this->LIS = &getAnalysis<LiveIntervals>();
  this->Matrix = &getAnalysis<LiveRegMatrix>();
  getAllRegs();
  getLiveness();
}


void RASimple::getUsesDefs(MachineInstr& Instr, std::set<unsigned>& uses,
                            std::set<unsigned>& defs) {
  for (unsigned i = 0; i < Instr.getNumOperands(); i++) {
    MachineOperand& oper = Instr.getOperand(i);
    if (oper.isReg() && TRI->isVirtualRegister(oper.getReg())) {
      unsigned Reg = oper.getReg();
      if (oper.isUse()) uses.insert(Reg);
      else if (oper.isDef()) defs.insert(Reg);
    } 
    else if (oper.isReg())
      UsedPhys.insert(oper.getReg());
  }
  //implicit use of registers
  if (Instr.getDesc().getImplicitUses())
    for (const uint16_t *regs = Instr.getDesc().getImplicitUses(); 
                                        *regs; regs++) {
      if (TRI->isVirtualRegister(*regs))
        uses.insert(*regs);
      else UsedPhys.insert(*regs);
    }
  //implicit def of registers
  if (Instr.getDesc().getImplicitDefs())
    for (const uint16_t *regs = Instr.getDesc().getImplicitDefs(); 
                                        *regs; regs++) {
      if (TRI->isVirtualRegister(*regs))
        defs.insert(*regs);
      else UsedPhys.insert(*regs);
    }
}

bool RASimple::isMoveInstr(MachineInstr& Instr) {
  if (Instr.isCopyLike()) return true;
  return false;
}

void RASimple::releaseMemory() {
  BBRegs.clear();
  UsedPhys.clear();
  LiveOutRegs.clear();
  LiveInRegs.clear();
  spillWorklist.clear();
  freezeWorklist.clear();
  simplifyWorklist.clear();
  MoveList.clear();
  WorklistMoves.clear();
}

void RASimple::buildInterferenceGraph() {
  if (InterGraph != nullptr) delete InterGraph;
  
  InterGraph = new Graph();

  for (MachineBasicBlock& MBB: *MF) {
    std::set<unsigned> live = LiveOutRegs[&MBB];
    for (MachineBasicBlock::reverse_instr_iterator instrIt = MBB.instr_rbegin();
              instrIt != MBB.instr_rend(); instrIt++) {
      MachineInstr& Instr = *instrIt;
      std::set<unsigned> uses, defs;
      getUsesDefs(Instr, uses, defs);
      if (isMoveInstr(Instr)) {
        std::set_difference(live.begin(), live.end(),
                            uses.begin(), uses.end(),
                            std::inserter(live, live.begin()));
        
        std::set<unsigned> UsesDefs;
        std::set_union(uses.begin(), uses.end(),
                        defs.begin(), defs.end(),
                        std::inserter(UsesDefs, UsesDefs.begin()));
        for (unsigned n: UsesDefs)
          MoveList[n].insert(&Instr);
        WorklistMoves.insert(&Instr);
      }
      std::set_union(live.begin(), live.end(),
                      defs.begin(), defs.end(),
                      std::inserter(live, live.begin()));
      for (unsigned d: defs) {
        for (unsigned l: live)
          InterGraph->addEdge(l, d);
      }
      std::set<unsigned> temp;
      std::set_difference(live.begin(), live.end(),
                          defs.begin(), defs.end(),
                          std::inserter(temp, temp.begin()));
      std::set_union(temp.begin(), temp.end(),
                      uses.begin(), uses.end(),
                      std::inserter(live, live.begin()));
    }
  }
}

std::set<uint16_t> RASimple::getPhysRegs(unsigned VirtReg) {
  AllocationOrder Order(VirtReg, *VRM, RegClassInfo);
  std::set<uint16_t> AvailablePhys;
  while (uint16_t reg = Order.next()) {
    if (UsedPhys.find(reg) == UsedPhys.end())
      AvailablePhys.insert(reg);
  }
  return AvailablePhys;
}

void RASimple::makeWorklist() {
  for (unsigned VirtReg: InterGraph->getNodes()) {
    unsigned K = getPhysRegs(VirtReg).size();
    if (InterGraph->getDegree(VirtReg) >= K)
      spillWorklist.insert(VirtReg);
    else if (MoveList.find(VirtReg) != MoveList.end())
      freezeWorklist.insert(VirtReg);
    else
      simplifyWorklist.insert(VirtReg);
  }
  //std::cout << spillWorklist.size() << std::endl;
  //std::cout << freezeWorklist.size() << std::endl;
  //std::cout << simplifyWorklist.size() << "\n\n";
}

bool RASimple::runOnMachineFunction(MachineFunction &mf) {
  DEBUG(dbgs() << "********** SIMPLE REGISTER ALLOCATION **********\n"
      << "********** Function: "  << mf.getName() << '\n');
  
  init(mf);

  livenessAnalysis();

  buildInterferenceGraph();

  makeWorklist();

  SpillerInstance = createInlineSpiller(*this, *this->MF, *this->VRM);

  allocatePhysRegs();

  delete SpillerInstance;

  releaseMemory();

  return true;
}

FunctionPass* llvm::createSimpleRegisterAllocator()
{
  return new RASimple();
}
