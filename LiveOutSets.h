// LiveOutSets.h - Pass for obtaining live out sets for basic blocks
// Author: Lang Hames, 08/02/2007

#ifndef LLVM_CODEGEN_LIVEOUTSETS_H
#define LLVM_CODEGEN_LIVEOUTSETS_H

#include <set>
#include <map>

#include "llvm/CodeGen/MachineBasicBlock.h"

namespace llvm
{
  
  /**
   * \brief Computes the sets of variables live out of each basic block in the
   * given MachineFunction.
   */
  
  class LiveOutSets
  {
  public:
    LiveOutSets(MachineFunction&);
    
    virtual void releaseMemory()
    {
      aliveOutSets.clear();
    }
    
    const std::set<unsigned>& getAliveOutSet(const MachineBasicBlock *mbb) const
    {
      std::map<const MachineBasicBlock*, std::set<unsigned> >::const_iterator
        blockLiveOutSetItr = aliveOutSets.find(mbb);

      if (blockLiveOutSetItr != aliveOutSets.end())
        return blockLiveOutSetItr->second;

      return theEmptySet;
    }
    
  private:
    
    void reverseDFS(const MachineBasicBlock *mbb,
                    std::vector<const MachineBasicBlock*> &mbbOrdering,
                    std::set<const MachineBasicBlock*> &visited,
                    std::set<const MachineBasicBlock*> &exitBlocks);
  
    void getReverseDFSBlocks(const MachineFunction *mf,
                             std::vector<const MachineBasicBlock*> &mbbOrdering,
                             std::set<const MachineBasicBlock*> &exitBlocks);

    void getMBBUseDefs(const MachineFunction *mf,
                       std::map<const MachineBasicBlock*, std::set<unsigned> > &mbbUses,
                       std::map<const MachineBasicBlock*, std::set<unsigned> > &mbbDefs);
  
    std::map<const MachineBasicBlock*, std::set<unsigned> > aliveOutSets;
    std::set<unsigned> theEmptySet;
  };
  
}


#endif /* LLVM_CODEGEN_LIVEOUTSETS_H */
