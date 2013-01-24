
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

BIC::BIC(Instruction* I, IntegrationAttempt* _ctx) : it(BasicBlock::iterator(I)), BB(I->getParent()), ctx(_ctx) { }

//// Implement the backward walker:

BackwardIAWalker::BackwardIAWalker(Instruction* I, IntegrationAttempt* Ctx, bool skipFirst, void* initialCtx) : IAWalker(initialCtx) {

  PList = &Worklist1;
  CList = &Worklist2;
  BasicBlock::iterator startit(I);
  if(!skipFirst)
    --startit;
  PList->push_back(std::make_pair(BIC(startit, I->getParent(), Ctx), initialCtx));
  Visited.insert(BIC(startit, I->getParent(), Ctx));

}

void IntegrationAttempt::queueLoopExitingBlocksBW(BasicBlock* ExitedBB, BasicBlock* ExitingBB, const Loop* ExitingBBL, BackwardIAWalker* Walker, void* Ctx, bool& firstPred) {

  const Loop* MyL = getLoopContext();
  if(MyL == ExitingBBL) {

    if(!edgeIsDead(ExitingBB, ExitedBB)) {
      Walker->queueWalkFrom(BIC(ExitingBB->end(), ExitingBB, this), Ctx, !firstPred);
      firstPred = false;
    }

  }
  else {

    const Loop* ChildL = immediateChildLoop(MyL, ExitingBBL);
    if(PeelAttempt* LPA = getPeelAttempt(ChildL)) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i)
	LPA->Iterations[i]->queueLoopExitingBlocksBW(ExitedBB, ExitingBB, ExitingBBL, Walker, Ctx, firstPred);

    }
    else {

      Walker->queueWalkFrom(BIC(ExitingBB->end(), ExitingBB, this), Ctx, !firstPred);
      firstPred = false;

    }

  }

}

bool InlineAttempt::queuePredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB == &(F.getEntryBlock())) {

    if(!parent)
      return Walker->reachedTop();
    if(!Walker->mayAscendFromContext(this))
      return false;

    Walker->queueWalkFrom(BIC(BasicBlock::iterator(CI), CI->getParent(), parent), Ctx, false);
    return true;

  }
  else {

    queueNormalPredecessorsBW(FromBB, Walker, Ctx);
    return true;

  }

}

bool PeelIteration::queuePredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB == L->getHeader()) {

    if(!Walker->mayAscendFromContext(this))
      return false;

    if(iterationCount == 0) {

      Walker->queueWalkFrom(BIC(L->getLoopPreheader()->end(), L->getLoopPreheader(), parent), Ctx, false);

    }
    else {

      Walker->queueWalkFrom(BIC(L->getLoopLatch()->end(), L->getLoopLatch(), parentPA->Iterations[iterationCount - 1]), Ctx, false);

    }

  }
  else {

    queueNormalPredecessorsBW(FromBB, Walker, Ctx);

  }

  return true;

}

void IntegrationAttempt::queueNormalPredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  // This isn't the function entry block and isn't our loop header. Queue all predecessors.

  bool firstPred = true;

  const Loop* CtxLoop = getLoopContext();
  const Loop* FromBBLoop = getBlockScopeVariant(FromBB);

  for(pred_iterator PI = pred_begin(FromBB), PE = pred_end(FromBB); PI != PE; ++PI) {

    bool queueHere = false;

    BasicBlock* BB = *PI;
    // CtxLoop != FromBBLoop indicates we're looking at loop blocks in an invariant context,
    // which in turn implies there's no point trying to climb into FromBBLoop or any of its
    // children.
    if(CtxLoop != FromBBLoop) {

      queueHere = true;
    
    }
    else {

      const Loop* BBLoop = getBlockScopeVariant(BB);
      if(BBLoop == CtxLoop) {

	queueHere = true;

      }
      else {

	// Must be a child loop; could be several loops deep however.
	queueLoopExitingBlocksBW(FromBB, BB, BBLoop, Walker, Ctx, firstPred);
	      
      }

    }

    if(queueHere) {

      // Edges are never marked dead as a pseudo-invariant... yet.
      if(CtxLoop == FromBBLoop && edgeIsDead(BB, FromBB))
	continue;
      Walker->queueWalkFrom(BIC(BB->end(), BB, this), Ctx, !firstPred);
      firstPred = false;

    }

  }

}

void IAWalker::queueWalkFrom(BIC bic, void* Ctx, bool shouldCopyContext) {

  if(Visited.insert(bic)) {
    if(shouldCopyContext) {
      Ctx = copyContext(Ctx);
      Contexts.push_back(Ctx);
    }
    PList->push_back(std::make_pair(bic, Ctx));
  }

}

void BackwardIAWalker::walkInternal() {

  while(PList->size() || CList->size()) {

    for(unsigned i = 0; i < CList->size(); ++i) {

      BIC ThisStart = (*CList)[i].first;
      void* Ctx = (*CList)[i].second;
      CallInst* StoppedCI = 0;
      WalkInstructionResult thisBlockResult = walkFromInst(ThisStart, Ctx, StoppedCI);

      if(thisBlockResult == WIRStopThisPath)
	continue;
      else if(thisBlockResult == WIRStopWholeWalk) {
	return;
      }

      // Else we walked up to either a call instruction or the top of the block
      // and should consider the predecessors.

      if(StoppedCI) {

	// Enter this call instruction from its return blocks:
	InlineAttempt* IA = ThisStart.ctx->getInlineAttempt(StoppedCI);

	bool firstPred = true;

	for(Function::iterator FI = IA->F.begin(), FE = IA->F.end(); FI != FE; ++FI) {
	  
	  BasicBlock* BB = FI;
	  if(isa<ReturnInst>(BB->getTerminator()) && !IA->blockIsDead(BB)) {
	    
	    queueWalkFrom(BIC(BB->end(), BB, IA), Ctx, !firstPred);
	    firstPred = false;
	    
	  }
	  
	}

      }
      else {

	// Else we've hit the top of a block. Figure out what to do with each predecessor:
	if(!ThisStart.ctx->queuePredecessorsBW(ThisStart.BB, this, Ctx))
	  return;

      }

    }

    CList->clear();
    std::swap(PList, CList);

  }

}

void IAWalker::walk() {

  walkInternal();
  for(SmallVector<void*, 4>::iterator it = Contexts.begin(), it2 = Contexts.end(); it != it2; ++it) {
    freeContext(*it);
  }

}

WalkInstructionResult BackwardIAWalker::walkFromInst(BIC bic, void* Ctx, CallInst*& StoppedCI) {

  for(BasicBlock::iterator it = bic.it, itend = bic.BB->begin(); it != itend;) {

    --it;
    Instruction* I = it;

    WalkInstructionResult WIR = walkInstruction(I, bic.ctx, Ctx);
    if(WIR != WIRContinue) {
      return WIR;
    }

    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      if(!shouldEnterCall(CI, bic.ctx))
	continue;

      if(!bic.ctx->getInlineAttempt(CI)) {

	// Return value = should we abort?
	if(blockedByUnexpandedCall(CI, bic.ctx)) {
	  return WIRStopWholeWalk;
	}
	else {
	  continue;
	}

      }
      else {

	StoppedCI = CI;
	break;

      }

    }

  }

  return WIRContinue;

}

//// End backward walker.

//// Implement the forward walker:

ForwardIAWalker::ForwardIAWalker(Instruction* I, IntegrationAttempt* IA, bool skipFirst, void* initialCtx) : IAWalker(initialCtx) {

  BasicBlock::iterator it(I);
  if(skipFirst)
    ++it;

  BIC bic(it, I->getParent(), IA);
  Visited.insert(bic);
  PList->push_back(std::make_pair(bic, initialCtx));
  
}

void ForwardIAWalker::walkInternal() {

  while(PList->size() || CList->size()) {

    for(unsigned i = 0; i < CList->size(); ++i) {

      BIC ThisStart = ((*CList)[i]).first;
      void* Ctx = ((*CList)[i]).second;
      CallInst* StoppedCI = 0;

      WalkInstructionResult thisBlockResult = walkFromInst(ThisStart, Ctx, StoppedCI);

      if(thisBlockResult == WIRStopThisPath)
	continue;
      else if(thisBlockResult == WIRStopWholeWalk)
	return;

      // Else we walked to either a call instruction or the bottom of the block
      // and should consider the successors.

      if(StoppedCI) {

	// Enter this call instruction from its entry block:
	if(InlineAttempt* IA = ThisStart.ctx->getInlineAttempt(StoppedCI)) {

	  BasicBlock* BB = &(IA->F.getEntryBlock());
	  queueWalkFrom(BIC(BB->begin(), BB, IA), Ctx, false);

	}
	else {

	  // Return value = should we abort?
	  if(blockedByUnexpandedCall(StoppedCI, ThisStart.ctx))
	    return;

	}

      }
      else {

	// Else we've hit the bottom of a block. Figure out what to do with each successor:
	ThisStart.ctx->queueSuccessorsFW(ThisStart.BB, this, Ctx);

      }

    }

    CList->clear();
    std::swap(PList, CList);

  }

}

WalkInstructionResult ForwardIAWalker::walkFromInst(BIC bic, void* Ctx, CallInst*& StoppedCI) {

  for(BasicBlock::iterator it = bic.it, itend = bic.BB->end(); it != itend; ++it) {
    
    Instruction* I = it;
    WalkInstructionResult WIR = walkInstruction(I, bic.ctx, Ctx);
    if(WIR != WIRContinue)
      return WIR;

    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      if(!shouldEnterCall(CI, bic.ctx))
	continue;

      StoppedCI = CI;
      break;

    }

  }

  return WIRContinue;

}

void IntegrationAttempt::queueSuccessorsFWFalling(BasicBlock* BB, const Loop* SuccLoop, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  if(SuccLoop == getLoopContext()) {

    Walker->queueWalkFrom(BIC(BB->begin(), BB, this), Ctx, !firstSucc);
    firstSucc = false;

  }
  else {

    parent->queueSuccessorsFWFalling(BB, SuccLoop, Walker, Ctx, firstSucc);

  }

}

void InlineAttempt::queueSuccessorsFW(BasicBlock* BB, ForwardIAWalker* Walker, void* Ctx) {

  if(isa<ReturnInst>(BB->getTerminator())) {

    if(parent) {

      BasicBlock::iterator CallIt(CI);
      ++CallIt;
      Walker->queueWalkFrom(BIC(CallIt, CI->getParent(), parent), Ctx, false);

    }

    return;

  }

  IntegrationAttempt::queueSuccessorsFW(BB, Walker, Ctx);

}

// Note here that the forward IA walker, when confronted with an unterminated loop, will first walk
// through all iterations which have been analysed seperately, then if we run off the end, through the
// loop in parent context, representing the general case.
// This gives maximum precision: if we analysed the first 3 iterations and we can show some property
// along all live paths without reaching the 4th, we can use that knowledge. Only if we find a live
// edge leading into the 4th do we consider it and all future iterations.
bool PeelIteration::queueNextLoopIterationFW(BasicBlock* PresentBlock, BasicBlock* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  if(PresentBlock == L->getLoopLatch() && NextBlock == L->getHeader()) {

    PeelIteration* nextIter = getNextIteration();
    if(!nextIter) {

      LPDEBUG("FIAW: Analysing loop in parent context because loop " << L->getHeader()->getName() << " does not yet have iteration " << iterationCount+1 << "\n");
      Walker->queueWalkFrom(BIC(NextBlock->begin(), NextBlock, parent), Ctx, !firstSucc);

    }
    else {

      Walker->queueWalkFrom(BIC(NextBlock->begin(), NextBlock, nextIter), Ctx, !firstSucc);

    }

    firstSucc = false;
    return true;

  }

  return false;

}

bool InlineAttempt::queueNextLoopIterationFW(BasicBlock* PresentBlock, BasicBlock* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  return false;
  
}

void IntegrationAttempt::queueSuccessorsFW(BasicBlock* BB, ForwardIAWalker* Walker, void* Ctx) {

  bool firstSucc = true;

  const Loop* MyLoop = getLoopContext();
  const Loop* BBLoop = getBlockScopeVariant(BB);

  for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {

    BasicBlock* SB = *SI;

    if(edgeIsDead(BB, SB))
      continue;

    if(queueNextLoopIterationFW(BB, SB, Walker, Ctx, firstSucc))
      continue;

    bool queueHere = false;

    if(MyLoop != BBLoop) {

      // Already running in "wrong" context, don't rise.
      queueHere = true;

    }
    else {

      const Loop* SuccLoop = getBlockScopeVariant(SB);
      if(SuccLoop != MyLoop) {

	if((!MyLoop) || MyLoop->contains(SuccLoop)) {

	  if(PeelAttempt* LPA = getPeelAttempt(SuccLoop)) {

	    assert(SuccLoop->getHeader() == SB);
	    Walker->queueWalkFrom(BIC(SB->begin(), SB, LPA->Iterations[0]), Ctx, !firstSucc);
	    firstSucc = false;

	  }
	  else {

	    // Otherwise we're entering an unexpanded loop, just walk it here.
	    queueHere = true;

	  }

	}
	else {

	  // Loop exit edge. Find the context for the outside block:
	  queueSuccessorsFWFalling(SB, SuccLoop, Walker, Ctx, firstSucc);

	}

      }
      else {

	queueHere = true;

      }

    }

    if(queueHere) {
      Walker->queueWalkFrom(BIC(SB->begin(), SB, this), Ctx, !firstSucc);
      firstSucc = false;
    }

  }

}

