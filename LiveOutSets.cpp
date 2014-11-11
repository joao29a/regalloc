// LiveOutSets.cpp - Pass for obtaining live out sets for basic blocks
// Author: Lang Hames, 08/02/2007

#include "LiveOutSets.h"

#include "llvm/CodeGen/Passes.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <iostream>
#include <algorithm>
#include <iterator>


using namespace llvm;

LiveOutSets::LiveOutSets(MachineFunction &mf)
{
  std::vector<const MachineBasicBlock*> mbbOrdering;
  std::map<const MachineBasicBlock*, std::set<unsigned> > mbbIn, mbbUses, mbbDefs;
  std::map<const MachineBasicBlock*, std::set<unsigned> > &mbbOut = aliveOutSets;
  std::set<const MachineBasicBlock*> exitBlocks;
  
  getReverseDFSBlocks(&mf, mbbOrdering, exitBlocks);
  
  getMBBUseDefs(&mf, mbbUses, mbbDefs);
  
  bool converged = false;
  std::set<unsigned> oldIn, oldOut, temp;
  
  while (!converged)
  {
    //DEBUG(std::cerr << "LiveOutSets - Round " << round++ << "\n");
    
    converged = true; // assume we're going to converge
    
    for (std::vector<const MachineBasicBlock*>::const_reverse_iterator
         mbbItr = mbbOrdering.rbegin(), mbbEnd = mbbOrdering.rend();
         mbbItr != mbbEnd; ++mbbItr)
    {
      const MachineBasicBlock *mbb = *mbbItr;

      oldIn = mbbIn[mbb];
      oldOut = mbbOut[mbb];
      
      temp.clear();
      mbbIn[mbb].clear();
      
      std::set_difference(mbbOut[mbb].begin(), mbbOut[mbb].end(),
                          mbbDefs[mbb].begin(), mbbDefs[mbb].end(),
                          std::inserter(temp, temp.begin()));
      
      std::set_union(mbbUses[mbb].begin(), mbbUses[mbb].end(), 
                     temp.begin(), temp.end(),
                     std::inserter(mbbIn[mbb], mbbIn[mbb].begin()));
      
      mbbOut[mbb].clear();
      if (exitBlocks.find(mbb) == exitBlocks.end())
      {
        for (MachineBasicBlock::const_succ_iterator
             succItr = mbb->succ_begin(), succEnd = mbb->succ_end();
             succItr != succEnd; ++succItr)
        {
          const MachineBasicBlock *mbbSucc = *succItr;
        
          std::copy(mbbIn[mbbSucc].begin(), mbbIn[mbbSucc].end(),
                    std::inserter(mbbOut[mbb], mbbOut[mbb].begin()));
        }
      }
      //else
      //{
      //  std::copy(mf.liveout_begin(), mf.liveout_end(),
      //            std::inserter(mbbOut[mbb], mbbOut[mbb].begin()));
      //}  

      //DEBUG(
      //        std::cerr << "uses[" << mbb->getNumber() << "]: ";
      //        std::copy(mbbUses[mbb].begin(), mbbUses[mbb].end(),
      //  		      std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\ndefs[" << mbb->getNumber() << "]: ";
      //        std::copy(mbbDefs[mbb].begin(), mbbDefs[mbb].end(),
      //  		      std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\noldIn[" << mbb->getNumber() << "]: ";
      //        std::copy(oldIn.begin(), oldIn.end(), std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\noldOut[" << mbb->getNumber() << "]: ";
      //        std::copy(oldOut.begin(), oldOut.end(), std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\n";
      //        
      //        std::cerr << "newIn[" << mbb->getNumber() << "]: ";
      //        std::copy(mbbIn[mbb].begin(), mbbIn[mbb].end(), std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\nnewOut[" << mbb->getNumber() << "]: ";
      //        std::copy(mbbOut[mbb].begin(), mbbOut[mbb].end(), std::ostream_iterator<unsigned>(std::cerr, " "));
      //        std::cerr << "\n------------------------------------------------------------------------------------------\n";
      //);

      if ((mbbIn[mbb] != oldIn) || (mbbOut[mbb] != oldOut))
        converged = false; // we failed to converge
    }
    
  } 
}

void LiveOutSets::reverseDFS(const MachineBasicBlock *mbb,
                             std::vector<const MachineBasicBlock*> &mbbOrdering,
                             std::set<const MachineBasicBlock*> &visited,
                             std::set<const MachineBasicBlock*> &exitBlocks)
{
  
  if (visited.find(mbb) != visited.end())
    return;
  
  mbbOrdering.push_back(mbb);
  visited.insert(mbb);
  
  if (mbb->succ_empty())
  {
    exitBlocks.insert(mbb);
  }
  else
  { 
    for (MachineBasicBlock::const_succ_iterator
         succItr = mbb->succ_begin(), succEnd = mbb->succ_end();
         succItr != succEnd; ++succItr)
    {
      reverseDFS(*succItr, mbbOrdering, visited, exitBlocks);
    }
  }
}

void LiveOutSets::getReverseDFSBlocks(const MachineFunction *mf,
                                      std::vector<const MachineBasicBlock*> &mbbOrdering,
                                      std::set<const MachineBasicBlock*> &exitBlocks)
{
  std::set<const MachineBasicBlock*> visited;
  
  for (MachineFunction::const_iterator
       mbbItr = mf->begin(), mbbEnd = mf->end();
       mbbItr != mbbEnd; ++mbbItr)
  {
    reverseDFS(mbbItr, mbbOrdering, visited, exitBlocks);
  }
}

void LiveOutSets::getMBBUseDefs(const MachineFunction *mf,
                                std::map<const MachineBasicBlock*, std::set<unsigned> > &mbbUses,
                                std::map<const MachineBasicBlock*, std::set<unsigned> > &mbbDefs)
{
  for (MachineFunction::const_iterator
       mbbItr = mf->begin(), mbbEnd = mf->end();
       mbbItr != mbbEnd; ++mbbItr)
  {
    const MachineBasicBlock *mbb = mbbItr;
    
    for (MachineBasicBlock::const_reverse_iterator
         miItr = mbb->rbegin(), miEnd = mbb->rend();
         miItr != miEnd; ++miItr)
    {
      const MachineInstr *mi = &*miItr;
      std::vector<unsigned> uses, defs;
      
      for (int i = 0, e = mi->getNumOperands(); i < e; ++i)
      {
        const MachineOperand &mo = mi->getOperand(i);
        
        if (!mo.isReg())
          continue;
        
        unsigned moReg = mo.getReg();
        
        if (moReg == 0)
          continue;
        
        if (mo.isUse())
          uses.push_back(moReg);
        else
          defs.push_back(moReg);
      }
     
      const MCInstrDesc *tid = &mi->getDesc();

      if (tid->getImplicitUses() != 0)
      {
        for (const uint16_t *implicitUse = tid->getImplicitUses();
             *implicitUse != 0; ++implicitUse)
        {
          uses.push_back(*implicitUse);
        }
      }

      if (tid->getImplicitDefs() != 0)
      {
        for (const uint16_t *implicitDef = tid->getImplicitDefs();
             *implicitDef != 0; ++implicitDef)
        {  
          defs.push_back(*implicitDef);
        }
      }

      for (std::vector<unsigned>::const_iterator
           defsItr = defs.begin(), defsEnd = defs.end();
           defsItr != defsEnd; ++defsItr)
      {
        mbbUses[mbb].erase(*defsItr);
        mbbDefs[mbb].insert(*defsItr);
      }

      for (std::vector<unsigned>::const_iterator
           usesItr = uses.begin(), usesEnd = uses.end();
           usesItr != usesEnd; ++usesItr)
      {
        mbbUses[mbb].insert(*usesItr);
      }
         
    }
    
  }

}
