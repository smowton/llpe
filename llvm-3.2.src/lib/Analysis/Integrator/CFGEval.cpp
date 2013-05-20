
#define DEBUG_TYPE "hypotheticalconstantfolder"

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h" // For isIdentifiedObject
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
// For elaboration of Calculate et al in Dominators.h:
#include "llvm/Analysis/DominatorInternals.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Assembly/Writer.h"

#include "PostDoms.h"

using namespace llvm;

// Implement instruction/block analysis concerning control flow, i.e. determining a block's
// status and relatedly analysing terminator instructions.

void IntegrationAttempt::setBlockStatus(ShadowBBInvar* BBI, ShadowBBStatus s) {

  ShadowBB* BB = getOrCreateBB(BBI);
  BB->status = s;
    
}

// specialise WriteAsOperand to allow printing of our special DomTree's BBWrapper nodes:
namespace llvm {

  void WriteAsOperand(raw_ostream& os, const BBWrapper* BBW, bool ign) {

    if(BBW->BB) {
      WriteAsOperand(os, BBW->BB->BB, ign);
    }
    else {
      os << "<<next iteration>>";
    }

  }

}

DomTreeNodeBase<BBWrapper>* IntegrationHeuristicsPass::getPostDomTreeNode(const Loop* L, ShadowBBInvar* BB, ShadowFunctionInvar& invarInfo) {

  std::pair<LoopWrapper*, DominatorTreeBase<BBWrapper>*> P;

  const Loop* Key = L;
  if(!Key) {

    // Hack: for root contexts use the ShadowFI pointer as a key. This should be fine as those
    // are never deallocated and so can never clash with loop pointers.
    Key = (const Loop*)(&invarInfo);

  }

  DenseMap<const Loop*, std::pair<LoopWrapper*, DominatorTreeBase<BBWrapper>*> >::iterator it = 
    LoopPDTs.find(Key);

  if(it != LoopPDTs.end()) {

    P = it->second;

  }
  else {
    
    LoopWrapper* LW = new LoopWrapper(L, invarInfo);
    DominatorTreeBase <BBWrapper>* LPDT = new DominatorTreeBase<BBWrapper>(true);
    LPDT->recalculate(*LW);

    /*
    DEBUG(dbgs() << "Calculated postdom tree for loop " << (L->getHeader()->getName()) << ":\n");
    DEBUG(LPDT->print(dbgs()));
    */

    LoopPDTs[Key] = P = std::make_pair(LW, LPDT);

  }

  BBWrapper* BBW = P.first->get(BB);
  if(!BBW)
    return 0;
  else
    return P.second->getNode(BBW);

}

bool InlineAttempt::entryBlockIsCertain() {

  if(!parent)
    return true;
  return blockCertainlyExecutes(CI->parent);

}

bool PeelIteration::entryBlockIsCertain() {

  if(iterationCount == 0)
    return blockCertainlyExecutes(parent->getBB(parentPA->invarInfo->preheaderIdx));

  // Otherwise it's certain if we're certain to iterate and at least the previous header was certain.
  PeelIteration* prevIter = parentPA->Iterations[iterationCount - 1];
  return blockCertainlyExecutes(prevIter->getBB(parentPA->invarInfo->latchIdx)) && prevIter->allExitEdgesDead();

}

bool InlineAttempt::entryBlockAssumed() {

  if(!parent)
    return true;
  if(blockAssumedToExecute(CI->parent))
    return true;
  if(pass->shouldAlwaysExplore(&F))
    return true;

  return false;

}

bool PeelIteration::entryBlockAssumed() {

  // Having been entered at all currently signifies at least the assumption that we will run.
  return true;

}

bool IntegrationAttempt::createEntryBlock() {

  if(BBs[0])
    return false;

  ShadowBBStatus newStatus = BBSTATUS_UNKNOWN;

  if(entryBlockIsCertain())
    newStatus = BBSTATUS_CERTAIN;
  else if(entryBlockAssumed())
    newStatus = BBSTATUS_ASSUMED;

  createBBAndPostDoms(BBsOffset, newStatus);

  return true;

}

// Return true on change.
bool IntegrationAttempt::tryEvaluateTerminatorInst(ShadowInstruction* SI) {

  if (!(inst_is<BranchInst>(SI) || inst_is<SwitchInst>(SI))) {
    
    return false;

  }

  if(BranchInst* BI = dyn_cast_inst<BranchInst>(SI)) {
    if(BI->isUnconditional()) {
      bool changed = !SI->parent->succsAlive[0];
      SI->parent->succsAlive[0] = true;
      return changed;
    }
  }

  // Both switches and conditional branches use operand 0 for the condition.
  ShadowValue Condition = SI->getOperand(0);
      
  bool changed = false;
  
  ConstantInt* ConstCondition = dyn_cast_or_null<ConstantInt>(getConstReplacement(Condition));

  if(ConstCondition) {

    BasicBlock* takenTarget = 0;

    if(BranchInst* BI = dyn_cast_inst<BranchInst>(SI)) {
      // This ought to be a boolean.
      if(ConstCondition->isZero())
	takenTarget = BI->getSuccessor(1);
      else
	takenTarget = BI->getSuccessor(0);
    }
    else {
      SwitchInst* SwI = cast_inst<SwitchInst>(SI);
      SwitchInst::CaseIt targetidx = SwI->findCaseValue(ConstCondition);
      takenTarget = targetidx.getCaseSuccessor();
    }
    if(takenTarget) {
      // We know where the instruction is going -- remove this block as a predecessor for its other targets.
      LPDEBUG("Branch or switch instruction given known target: " << takenTarget->getName() << "\n");

      TerminatorInst* TI = cast_inst<TerminatorInst>(SI);

      const unsigned NumSucc = TI->getNumSuccessors();

      for (unsigned I = 0; I != NumSucc; ++I) {

	BasicBlock* thisTarget = TI->getSuccessor(I);

	if(thisTarget == takenTarget) {

	  // Mark this edge alive
	  if(!SI->parent->succsAlive[I])
	    changed = true;
	  SI->parent->succsAlive[I] = true;

	}

      }

      return changed;

    }
    
    // Else fall through to set all alive.

  }

  // Condition unknown -- set all successors alive.
  TerminatorInst* TI = cast_inst<TerminatorInst>(SI);
  const unsigned NumSucc = TI->getNumSuccessors();
  for (unsigned I = 0; I != NumSucc; ++I) {
    
    // Mark outgoing edge alive
    if(!SI->parent->succsAlive[I])
      changed = true;
    SI->parent->succsAlive[I] = true;
    
  }

  return changed;

}

IntegrationAttempt* IntegrationAttempt::getIAForScope(const Loop* Scope) {

  if((!L) || L->contains(Scope))
    return this;

  return getIAForScopeFalling(Scope);

}

IntegrationAttempt* IntegrationAttempt::getIAForScopeFalling(const Loop* Scope) {

  if(L == Scope)
    return this;
  release_assert(parent && "Out of scope getIAForScopeFalling");
  return parent->getIAForScopeFalling(Scope);

}

void IntegrationAttempt::createBBAndPostDoms(uint32_t idx, ShadowBBStatus newStatus) {

  ShadowBBInvar* SBB = getBBInvar(idx);
  setBlockStatus(SBB, newStatus);
  
  if(newStatus != BBSTATUS_UNKNOWN) {

    for(DomTreeNodeBase<BBWrapper>* DTN = pass->getPostDomTreeNode(L, SBB, *invarInfo); DTN && DTN->getBlock(); DTN = DTN->getIDom()) {
	
      const BBWrapper* BW = DTN->getBlock();
      if(BW->BB) {
	  
	if((!BW->BB->naturalScope) || BW->BB->naturalScope->contains(L)) {
	  IntegrationAttempt* BlockIA = getIAForScope(BW->BB->naturalScope);
	  BlockIA->setBlockStatus(const_cast<ShadowBBInvar*>(BW->BB), newStatus);
	}

      }

    }

  }

}

// Return true if the result changes:
bool IntegrationAttempt::tryEvaluateTerminator(ShadowInstruction* SI, bool thisBlockLoadedVararg) {

  // Clarify branch target if possible:
  bool anyChange = tryEvaluateTerminatorInst(SI);

  // Return instruction breaks early to avoid the refcount juggling below:
  // a live return always has one successor, the call-merge.
  if(inst_is<ReturnInst>(SI)) {
    // Drop local allocas from the store:
    InlineAttempt* thisIA = getFunctionRoot();
    for(SmallVector<ShadowInstruction*, 4>::iterator it = thisIA->localAllocas.begin(),
	  it2 = thisIA->localAllocas.end(); it != it2; ++it) {
      //errs() << "Drop val " << itcache(*it) << " from local map\n";
      SI->parent->localStore->store.erase(ShadowValue(*it));
    }
    return false;
  }

  ShadowBB* BB = SI->parent;
  ShadowBBInvar* BBI = BB->invar;
  
  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

    if(!BB->succsAlive[i])
      continue;

    // Create a store reference for each live successor
    ++SI->parent->localStore->refCount;

  }

  // This block relinquishes its reference. Might free the store in e.g. an unreachable block.
  SI->parent->localStore->dropReference();

  uint32_t uniqueSucc = 0xffffffff;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {
    
    if(uniqueSucc == BBI->succIdxs[i] || uniqueSucc == 0xffffffff)
      uniqueSucc = BBI->succIdxs[i];
    else {
      uniqueSucc = 0xffffffff;
      break;
    }

  }

  if(!anyChange)
    return false;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

    if(!BB->succsAlive[i])
      continue;

    ShadowBBInvar* SBBI = getBBInvar(BB->invar->succIdxs[i]);

    IntegrationAttempt* IA = getIAForScope(SBBI->naturalScope);

    if(!IA->getBB(BB->invar->succIdxs[i])) {

      // Can grant the new block some status if either (a) I have status and this is my only live successor,
      // or (b) this edge should be assumed.

      ShadowBBStatus newStatus = BBSTATUS_UNKNOWN;
      
      if(BB->status != BBSTATUS_UNKNOWN && uniqueSucc != 0xffffffff)
	newStatus = BB->status;
      else if(shouldAssumeEdge(BBI->BB, SBBI->BB))
	newStatus = BBSTATUS_ASSUMED;

      IA->createBBAndPostDoms(BB->invar->succIdxs[i], newStatus);

    }
    
    IA->getBB(BB->invar->succIdxs[i])->useSpecialVarargMerge = thisBlockLoadedVararg;

  }

  return true;

}
