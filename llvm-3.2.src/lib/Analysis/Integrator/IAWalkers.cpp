
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

//// Implement the backward walker:

BackwardIAWalker::BackwardIAWalker(uint32_t instIdx, ShadowBB* BB, bool skipFirst, void* initialCtx, DenseSet<WLItem>* AlreadyVisited, bool doIgnoreEdges) : IAWalker(initialCtx, doIgnoreEdges) {

  PList = &Worklist1;
  CList = &Worklist2;
  if(!skipFirst)
    --instIdx;
  
  WLItem firstItem = makeWL(instIdx, BB);

  if(AlreadyVisited)
    Visited = *AlreadyVisited;

  PList->push_back(std::make_pair(firstItem, initialCtx));
  Visited.insert(firstItem);

}

struct QueueWalkVisitor : public ShadowBBVisitor {

  BackwardIAWalker* W;
  QueueWalkVisitor(BackwardIAWalker* _W, bool ign) : ShadowBBVisitor(ign), W(_W) { }

  void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) {

    W->queueWalkFrom(BB->invar->insts.size(), BB, Ctx, mustCopyCtx);

  }

};

void IntegrationAttempt::visitLoopExitingBlocksBW(ShadowBBInvar* ExitedBB, ShadowBBInvar* ExitingBB, ShadowBBVisitor* Visitor, void* Ctx, bool& firstPred) {

  if(edgeIsDead(ExitingBB, ExitedBB))
    return;

  const Loop* MyL = L;
  const Loop* ExitingBBL = ExitingBB->outerScope;
  if(MyL == ExitingBBL) {

    Visitor->visit(getBB(*ExitingBB), Ctx, !firstPred);
    firstPred = false;

  }
  else {

    const Loop* ChildL = immediateChildLoop(MyL, ExitingBBL);
    PeelAttempt* LPA = getPeelAttempt(ChildL);
    if(LPA && LPA->Iterations.back()->iterStatus == IterationStatusFinal) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i)
	LPA->Iterations[i]->visitLoopExitingBlocksBW(ExitedBB, ExitingBB, Visitor, Ctx, firstPred);

    }
    else {

      Visitor->visit(getBB(*ExitingBB), Ctx, !firstPred);
      firstPred = false;

    }

  }

}

WalkInstructionResult InlineAttempt::queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB->invar->BB == &(F.getEntryBlock())) {

    if(Callers.empty())
      return Walker->reachedTop();
    WalkInstructionResult WIR = Walker->mayAscendFromContext(this, Ctx);
    if(WIR != WIRContinue)
      return WIR;

    bool firstQueue = true;
    
    for(SmallVector<ShadowInstruction*, 1>::iterator it = Callers.begin(), 
	  itend = Callers.end(); it != itend; ++it) {
 
      Walker->queueWalkFrom((*it)->invar->idx, (*it)->parent, Ctx, !firstQueue);
      firstQueue = false;

    }

  }
  else {
    
    QueueWalkVisitor V(Walker, Walker->doIgnoreEdges);
    visitNormalPredecessorsBW(FromBB, &V, Ctx);

  }

  return WIRContinue;

}

WalkInstructionResult PeelIteration::queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB->invar->BB == L->getHeader()) {

    WalkInstructionResult WIR = Walker->mayAscendFromContext(this, Ctx);
    if(WIR != WIRContinue)
      return WIR;

    if(iterationCount == 0) {

      ShadowBB* BB = parent->getBB(parentPA->invarInfo->preheaderIdx);
      Walker->queueWalkFrom(BB->insts.size(), BB, Ctx, false);

    }
    else {

      ShadowBB* BB = parentPA->Iterations[iterationCount - 1]->getBB(parentPA->invarInfo->latchIdx);
      Walker->queueWalkFrom(BB->insts.size(), BB, Ctx, false);

    }

  }
  else {

    QueueWalkVisitor V(Walker, Walker->doIgnoreEdges);    
    visitNormalPredecessorsBW(FromBB, &V, Ctx);

  }

  return WIRContinue;

}

void IntegrationAttempt::visitNormalPredecessorsBW(ShadowBB* FromBB, ShadowBBVisitor* Visitor, void* Ctx) {

  // This isn't the function entry block and isn't our loop header. Queue all predecessors.

  bool firstPred = true;

  const Loop* CtxLoop = L;
  const Loop* FromBBLoop = FromBB->invar->outerScope;

  ShadowBBInvar* FromBBI = FromBB->invar;

  for(uint32_t i = 0, ilim = FromBBI->predIdxs.size(); i != ilim; ++i) {

    bool queueHere = false;

    ShadowBBInvar* BBI = getBBInvar(FromBBI->predIdxs[i]);

    if(edgeIsDead(BBI, FromBBI))
      continue;

    if(shouldIgnoreEdge(BBI, FromBB->invar)) {
      if(!Visitor->doIgnoreEdges)
	Visitor->hitIgnoredEdge();
      continue;
    }
      
    // CtxLoop != FromBBLoop indicates we're looking at loop blocks in an invariant context,
    // which in turn implies there's no point trying to climb into FromBBLoop or any of its
    // children.
    if(CtxLoop != FromBBLoop) {

      queueHere = true;
    
    }
    else {

      const Loop* BBLoop = BBI->outerScope;
      if(BBLoop == CtxLoop) {

	queueHere = true;

      }
      else {

	// Must be a child loop; could be several loops deep however.
	visitLoopExitingBlocksBW(FromBBI, BBI, Visitor, Ctx, firstPred);
	      
      }

    }

    if(queueHere) {

      ShadowBB* BB = getBB(*BBI);
      Visitor->visit(BB, Ctx, !firstPred);
      firstPred = false;

    }

  }

}

void IAWalker::queueWalkFrom(uint32_t idx, ShadowBB* BB, void* Ctx, bool shouldCopyContext) {

  release_assert(BB && "Queue walk from null BB");

  WLItem wl = makeWL(idx, BB);

  if(Visited.insert(wl).second) {
    if(shouldCopyContext) {
      Ctx = copyContext(Ctx);
      Contexts.push_back(Ctx);
    }
    PList->push_back(std::make_pair(wl, Ctx));
  }

}

void IntegrationAttempt::queueReturnBlocks(BackwardIAWalker* Walker, void* Ctx) {

  bool firstPred = true;
	
  for(uint32_t j = 0, jlim = nBBs; j != jlim; ++j) {

    ShadowBB* BB = BBs[j];
    if(BB && inst_is<ReturnInst>(&(BB->insts.back()))) {
	    
      Walker->queueWalkFrom(BB->insts.size(), BB, Ctx, !firstPred);
      firstPred = false;
	    
    }
	  
  }

}

void BackwardIAWalker::walkInternal() {

  while(PList->size() || CList->size()) {

    for(unsigned i = 0; i < CList->size(); ++i) {

      WLItem ThisStart = (*CList)[i].first;
      void* Ctx = (*CList)[i].second;
      ShadowInstruction* StoppedCI = 0;
      ShadowBB* BB = ThisStart.second;

      WalkInstructionResult thisBlockResult = walkFromInst(ThisStart.first, BB, Ctx, StoppedCI);

      if(thisBlockResult == WIRStopThisPath)
	continue;
      else if(thisBlockResult == WIRStopWholeWalk) {
	return;
      }

      // Else we walked up to either a call instruction or the top of the block
      // and should consider the predecessors.

      if(StoppedCI) {

	// Enter this call instruction from its return blocks:
	InlineAttempt* IA = BB->IA->getInlineAttempt(StoppedCI);
	IA->queueReturnBlocks(this, Ctx);

      }
      else {

	// Else we've hit the top of a block:
	WalkInstructionResult leaveBlockResult = walkFromBlock(BB, Ctx);
	if(leaveBlockResult == WIRStopThisPath)
	  continue;
	else if(leaveBlockResult == WIRStopWholeWalk)
	  return;

	// OK, queue predecessors.
	if(BB->IA->queuePredecessorsBW(BB, this, Ctx) == WIRStopWholeWalk)
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

WalkInstructionResult BackwardIAWalker::walkFromInst(uint32_t startidx, ShadowBB* BB, void* Ctx, ShadowInstruction*& StoppedCI) {

  for(uint32_t i = startidx; i != 0;) {

    --i;
    ShadowInstruction* SI = &(BB->insts[i]);

    WalkInstructionResult WIR = walkInstruction(SI, Ctx);
    if(WIR != WIRContinue) {
      return WIR;
    }

    if(inst_is<CallInst>(SI)) {

      if(!shouldEnterCall(SI, Ctx))
	continue;

      if(!BB->IA->getInlineAttempt(SI)) {

	// Return value = should we abort?
	if(blockedByUnexpandedCall(SI, Ctx)) {
	  return WIRStopWholeWalk;
	}
	else {
	  continue;
	}

      }
      else {

	StoppedCI = SI;
	break;

      }

    }

  }

  return WIRContinue;

}

//// End backward walker.

//// Implement the forward walker:

ForwardIAWalker::ForwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* initialCtx, bool doIgnoreEdges) : IAWalker(initialCtx, doIgnoreEdges) {

  if(skipFirst)
    ++idx;

  WLItem firstWL = makeWL(idx, BB);

  Visited.insert(firstWL);
  PList->push_back(std::make_pair(firstWL, initialCtx));
  
}

void ForwardIAWalker::walkInternal() {

  while(PList->size() || CList->size()) {

    for(unsigned i = 0; i < CList->size(); ++i) {
      
      WLItem ThisStart = ((*CList)[i]).first;
      ShadowBB* BB = ThisStart.second;
      void* Ctx = ((*CList)[i]).second;
      ShadowInstruction* StoppedCI = 0;

      WalkInstructionResult thisBlockResult = walkFromInst(ThisStart.first, BB, Ctx, StoppedCI);

      if(thisBlockResult == WIRStopThisPath)
	continue;
      else if(thisBlockResult == WIRStopWholeWalk)
	return;

      // Else we walked to either a call instruction or the bottom of the block
      // and should consider the successors.

      if(StoppedCI) {

	// Enter this call instruction from its entry block:
	if(InlineAttempt* IA = BB->IA->getInlineAttempt(StoppedCI)) {

	  // Get entry block:
	  ShadowBB* BB = IA->getBB(0);
	  enterCall(IA, Ctx);
	  queueWalkFrom(0, BB, Ctx, false);

	}
	else {

	  // Return value = should we abort?
	  if(blockedByUnexpandedCall(StoppedCI, Ctx))
	    return;

	}

      }
      else {

	// Else we've hit the bottom of a block. Figure out what to do with each successor:
	BB->IA->queueSuccessorsFW(BB, this, Ctx);
	if(!shouldContinue())
	  return;

      }

    }

    CList->clear();
    std::swap(PList, CList);

  }

}

WalkInstructionResult ForwardIAWalker::walkFromInst(uint32_t startidx, ShadowBB* BB, void* Ctx, ShadowInstruction*& StoppedCI) {

  for(uint32_t idx = startidx, idxlim = BB->insts.size(); idx != idxlim; ++idx) {
    
    ShadowInstruction* I = &(BB->insts[idx]);
    WalkInstructionResult WIR = walkInstruction(I, Ctx);
    if(WIR != WIRContinue)
      return WIR;

    if(inst_is<CallInst>(I)) {

      if(!shouldEnterCall(I, Ctx))
	continue;

      StoppedCI = I;
      break;

    }

  }

  return WIRContinue;

}

void InlineAttempt::queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  release_assert((!BB->outerScope) && "Dropped out of scope in queueSuccessorsFWFalling");
  Walker->queueWalkFrom(0, getBB(*BB), Ctx, !firstSucc);
  firstSucc = false;

}

void PeelIteration::queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {
  
  if(BB->outerScope == L) {

    Walker->queueWalkFrom(0, getBB(*BB), Ctx, !firstSucc);
    firstSucc = false;

  }
  else {

    Walker->leaveLoop(parentPA, Ctx);
    parent->queueSuccessorsFWFalling(BB, Walker, Ctx, firstSucc);

  }

}

void InlineAttempt::queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* Ctx) {

  if(isa<ReturnInst>(BB->invar->BB->getTerminator())) {

    if(!Callers.empty()) {

      // CallInst isn't a terminatorinst so can't be end of block.
      
      bool firstQueue = true;
      for(SmallVector<ShadowInstruction*, 1>::iterator it = Callers.begin(),
	    itend = Callers.end(); it != itend; ++it) {

	Walker->leaveCall(this, Ctx);
	Walker->queueWalkFrom((*it)->invar->idx + 1, (*it)->parent, Ctx, !firstQueue);
	firstQueue = false;

      }

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
bool PeelIteration::queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  if(PresentBlock->invar->BB == L->getLoopLatch() && NextBlock->BB == L->getHeader()) {

    PeelIteration* nextIter = getNextIteration();
    if(!nextIter) {

      LPDEBUG("FIAW: Analysing loop in parent context because loop " << L->getHeader()->getName() << " does not yet have iteration " << iterationCount+1 << "\n");
      Walker->queueWalkFrom(0, parent->getBB(*NextBlock), Ctx, !firstSucc);

    }
    else {

      Walker->queueWalkFrom(0, nextIter->getBB(*NextBlock), Ctx, !firstSucc);

    }

    firstSucc = false;
    return true;

  }

  return false;

}

bool InlineAttempt::queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  return false;
  
}

void IntegrationAttempt::queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* Ctx) {

  bool firstSucc = true;

  const Loop* MyLoop = L;
  const Loop* BBLoop = BB->invar->outerScope;

  for(uint32_t i = 0, ilim = BB->invar->succIdxs.size(); i != ilim; ++i) { 

    ShadowBBInvar* SB = getBBInvar(BB->invar->succIdxs[i]);

    if(edgeIsDead(BB->invar, SB))
      continue;

    if(shouldIgnoreEdge(BB->invar, SB)) {
      if(!Walker->doIgnoreEdges)
	Walker->hitIgnoredEdge();
      continue;
    }

    if(queueNextLoopIterationFW(BB, SB, Walker, Ctx, firstSucc))
      continue;

    bool queueHere = false;

    const Loop* SuccLoop = SB->outerScope;
    if(SuccLoop != MyLoop) {

      if((!MyLoop) || MyLoop->contains(SuccLoop)) {

	if(MyLoop != BBLoop) {

	  // We're emitting a residual loop, don't rise into it.
	  queueHere = true;
	  
	}
	else if(PeelAttempt* LPA = getPeelAttempt(SuccLoop)) {
	  
	  assert(SuccLoop->getHeader() == SB->BB);
	  Walker->enterLoop(LPA, Ctx);
	  Walker->queueWalkFrom(0, LPA->Iterations[0]->getBB(*SB), Ctx, !firstSucc);
	  firstSucc = false;
	  
	}
	else {

	  // Otherwise we're entering an unexpanded loop, just walk it here.
	  queueHere = true;

	}

      }
      else {

	// Loop exit edge. Find the context for the outside block:
	queueSuccessorsFWFalling(SB, Walker, Ctx, firstSucc);

      }

    }
    else {

      queueHere = true;

    }

    if(queueHere) {
      Walker->queueWalkFrom(0, getBB(*SB), Ctx, !firstSucc);
      firstSucc = false;
    }

  }

}

