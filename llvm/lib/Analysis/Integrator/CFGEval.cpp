
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

#include "PostDoms.h"

using namespace llvm;

// Implement instruction/block analysis concerning control flow, i.e. determining a block's
// status and relatedly analysing terminator instructions.

void IntegrationAttempt::markBlockCertain(ShadowBBInvar* BB) {

  LPDEBUG("Block " << BB->getName() << " is certain to execute\n");
  if(!BBs[BB->idx])
    createBB(BB->idx);
  BB->status = BBSTATUS_CERTAIN;
    
}

void IntegrationAttempt::markBlockAssumed(ShadowBBInvar* BB) {

  if(!BBs[BB->idx])
    createBB(BB->idx);
  BB->status = BBSTATUS_ASSUMED;

}

PostDominatorTree* IntegrationHeuristicsPass::getPostDomTree(Function* F) {

  DenseMap<Function*, PostDominatorTree*>::iterator it = PDTs.find(F);
  if(it != PDTs.end())
    return it->second;
  else {

    PostDominatorTree* PDT = new PostDominatorTree();
    PDT->runOnFunction(*F);
    PDTs[F] = PDT;
    return PDT;

  }

}

PostDominatorTree* IntegrationAttempt::getPostDomTree() {

  return pass->getPostDomTree(&F);

}

// specialise WriteAsOperand to allow printing of our special DomTree's BBWrapper nodes:
namespace llvm {

  void WriteAsOperand(raw_ostream& os, const BBWrapper* BBW, bool ign) {

    if(BBW->BB) {
      WriteAsOperand(os, BBW->BB, ign);
    }
    else {
      os << "<<next iteration>>";
    }

  }

}

DomTreeNodeBase<const BBWrapper>* IntegrationHeuristicsPass::getPostDomTreeNode(const Loop* L, BasicBlock* BB) {

  std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> P;

  DenseMap<const Loop*, std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> >::iterator it = LoopPDTs.find(L);
  if(it != LoopPDTs.end()) {

    P = it->second;

  }
  else {
    
    const LoopWrapper* LW = new LoopWrapper(L);
    DominatorTreeBase <const BBWrapper>* LPDT = new DominatorTreeBase<const BBWrapper>(true);
    LPDT->recalculate(*LW);

    /*
    DEBUG(dbgs() << "Calculated postdom tree for loop " << (L->getHeader()->getName()) << ":\n");
    DEBUG(LPDT->print(dbgs()));
    */

    LoopPDTs[L] = P = std::make_pair(LW, LPDT);

  }

  DenseMap<const BasicBlock*, BBWrapper>::const_iterator it2 = P.first->Map.find(BB);
  if(it2 == P.first->Map.end())
    return 0;
  else  
    return P.second->getNode(&it2->second);

}

bool InlineAttempt::entryBlockIsCertain() {

  if(!parent)
    return true;
  return blockCertainlyExecutes(CI->parent);

}

bool PeelIteration::entryBlockIsCertain() {

  if(iterationCount == 0)
    return blockCertainlyExecutes(parent->getBB(parentPA->preheaderIdx));

  // Otherwise it's certain if we're certain to iterate and at least the previous header was certain.
  PeelIteration* prevIter = parentPA->Iterations[iterationCount - 1];
  return blockCertainlyExecutes(prevIter->getBB(parentPA->latchIdx)) && prevIter->allExitEdgesDead();

}

bool InlineAttempt::entryBlockAssumed() {

  if(!parent)
    return true;
  return parent->blockAssumed(CI->getParent());

}

bool PeelIteration::entryBlockAssumed() {

  // Having been entered at all currently signifies at least the assumption that we will run.
  return true;

}


void IntegrationAttempt::checkBlock(uint32_t blockIdx) {

  const ShadowBBInvar& SBBI = invarInfo->BBs[blockIdx];
  BasicBlock* BB = SBBI.BB;

  LPDEBUG("Checking status of block " << BB->getName() << "\n");

  release_assert((!getBB(blockIdx)) && "Block already created?");

  // Check whether this block has become dead or certain
  
  bool isDead = true;
  bool isCertain = true;
  bool isAssumed = true;

  if(BB == getEntryBlock()) {

    isCertain = entryBlockIsCertain();
    isAssumed = isCertain || entryBlockAssumed();
    isDead = false;

  }
  else {

    for(unsigned i = 0, ilim = SBBI.predIdxs.size(); i < ilim; ++i) {

      ShadowBBInvar* PSBBI = &(invarInfo->BBs[SBBI.predIdxs[i]]);

      if(!edgeIsDead(PSBBI, SBBI)) {

	isDead = false;

	// We know the BB exists somewhere because edgeIsDead returned false,
	// so a failure here means the predecessor is not unique.
	ShadowBB* PredBB = getUniqueBBRising(PSBBI);

	if(PredBB) {

	  bool PICertain = PredBB->status == BBSTATUS_CERTAIN;
	  if(!PICertain)
	    isCertain = false;

	  bool PIAssumed = PICertain || PredBB->status == BBSTATUS_ASSUMED;

	  if(PIAssumed) {

	    bool onlySuccessor = true;

	    for(uint32_t j = 0, jlim = PSBBI.succIdxs.size(); j != jlim; ++j) {

	      ShadowBBInvar* SSBBI = getBBInvar(PSBBI.succIdxs[j]);

	      if(SBBI.BB != SSBBI.BB && !edgeIsDead(PredBB, SSBBI)) {
		onlySuccessor = false;
		break;
	      }

	    }

	    if(!onlySuccessor) {
	      isCertain = false;
	      if(!shouldAssumeEdge(PSBBI.BB, SBBI.BB))
		isAssumed = false;
	    }
	    
	  }
	  else {

	    isAssumed = false;

	  }

	}
	else {
	  
	  // Else there's more than once successor possible, i.e. more than one exiting loop iteration.

	  isCertain = false;
	  isAssumed = false;

	}

      }

    }

  }

  if(isDead && (isCertain || isAssumed)) {
    isCertain = false;
    isAssumed = false;
  }

  if(isDead) {

    // Block is implied dead as we do not create a BB structure for it at this point.
    return;

  }
  else if(isCertain || isAssumed) {

    const Loop* MyL = L;

    for(DomTreeNodeBase<const BBWrapper>* DTN = pass->getPostDomTreeNode(MyL, BB); DTN && DTN->getBlock(); DTN = DTN->getIDom()) {
	
      const BBWrapper* BW = DTN->getBlock();
      if(BW->BB) {
	  
	const Loop* BBL = const_cast<ShadowBBInvar*>(BW->BB)->scope;
	if(BBL == MyL) {

	  if(isCertain)
	    markBlockCertain(const_cast<ShadowBBInvar*>(BW->BB));
	  else
	    markBlockAssumed(const_cast<ShadowBBInvar*>(BW->BB));

	}

      }

    }

  }
  else {

    createBB(SBBI.idx);

  }

}


void IntegrationAttempt::tryEvaluateTerminator(ShadowInstruction* SI) {

  if (!(isa<BranchInst>(I) || isa<SwitchInst>(I)))
    return;

  // Unconditional branches are already eliminated.

  // Easiest case: copy edge liveness from our parent.
  if(tryCopyDeadEdges(parent->getBB(SI->parent->invar), SI->parent))
    return ShadowValue();

  // Both switches and conditional branches use operand 0 for the condition.
  ShadowValue Condition = SI->getOperand(0);
      
  ConstantInt* ConstCondition = dyn_cast_or_null<ConstantInt>(getConstReplacement(Condition));

  if(ConstCondition) {

    BasicBlock* takenTarget = 0;

    if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
      // This ought to be a boolean.
      if(ConstCondition->isZero())
	takenTarget = BI->getSuccessor(1);
      else
	takenTarget = BI->getSuccessor(0);
    }
    else {
      SwitchInst* SI = cast<SwitchInst>(I);
      unsigned targetidx = SI->findCaseValue(ConstCondition);
      takenTarget = SI->getSuccessor(targetidx);
    }
    if(takenTarget) {
      // We know where the instruction is going -- remove this block as a predecessor for its other targets.
      LPDEBUG("Branch or switch instruction given known target: " << takenTarget->getName() << "\n");

      TerminatorInst* TI = cast<TerminatorInst>(I);

      const unsigned NumSucc = TI->getNumSuccessors();

      for (unsigned I = 0; I != NumSucc; ++I) {

	BasicBlock* thisTarget = TI->getSuccessor(I);

	if(thisTarget != takenTarget) {

	  // Mark outgoing edge dead.
	  SI->parent->succsAlive[I] = false;

	}

      }

    }

  }

  return ShadowValue();

}
