//===-- IAWalkers.cpp -----------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "IAWalkers"

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Support/Debug.h"

using namespace llvm;

// IAWalkers are forwards and backwards generic walkers over function and basic block instances, taking into account
// block and edge liveness. They are typically used to discover "all-paths" properties concerning a particular instruction,
// such as for example "is this allocation null-checked on all paths?"
// Their use is discouraged because they try to step into functions and loop instances, which may have been committed
// and their analysis results discarded; in this case we have to be conservative about the function's side-effects.
// Preferably any use of an IAWalker should be merged into the main analysis pass (so e.g. the is-null-checked flag could
// be maintained along with the symbolic store), but some uses have not yet been converted this way because the desired property
// is usually or always context-local, so there was little to gain from making the improvement.

// Throughout this file, all the firstPred / shouldCopyContext logic is intended to allow a walker implementation to track some
// context as we walk and perhaps have that context copied when control flow diverges and merged when it converges.

// The backward walker is currently unused. The forward and backward walkers are also somewhat diverged in feature terms
// due to the particular needs of previous subclasses.

// Make a backward walker starting from BB / instIdx. initialCtx is an arbitrary context object passed to the visit function;
// AlreadyVisited may mark some paths already done, and doIgnoreEdges dictates whether the visitor cares about edges
// leading to unspecialised code.
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

  void leaveLoop(PeelAttempt* LPA, void* Ctx) {
    W->leaveLoop(LPA, Ctx);
  }

};

// Walk from ExitedBB, outside some number of nested loops, back to ExitingBB which is inside them. Set firstPred to false after visiting
// any block instance this way.
void IntegrationAttempt::visitLoopExitingBlocksBW(ShadowBBInvar* ExitedBB, ShadowBBInvar* ExitingBB, ShadowBBVisitor* Visitor, void* Ctx, bool& firstPred) {

  if(edgeIsDead(ExitingBB, ExitedBB))
    return;

  const ShadowLoopInvar* MyL = L;
  const ShadowLoopInvar* ExitingBBL = ExitingBB->outerScope;
  if(MyL == ExitingBBL) {

    Visitor->visit(getBB(*ExitingBB), Ctx, !firstPred);
    firstPred = false;

  }
  else {

    const ShadowLoopInvar* ChildL = immediateChildLoop(MyL, ExitingBBL);
    PeelAttempt* LPA = getPeelAttempt(ChildL);
    if(LPA && LPA->isTerminated()) {

      Visitor->enterLoop(LPA, Ctx);

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i)
	LPA->Iterations[i]->visitLoopExitingBlocksBW(ExitedBB, ExitingBB, Visitor, Ctx, firstPred);

    }
    else {

      Visitor->visit(getBB(*ExitingBB), Ctx, !firstPred);
      firstPred = false;

    }

  }

}

// Walk backwards from FromBB: if it's the entry block of this context, walk out to our parent context.
WalkInstructionResult InlineAttempt::queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB->invar->BB == &(F.getEntryBlock())) {

    Walker->leaveCall(this, Ctx);

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

// Walk backwards from FromBB, into a previous loop iteration or out into our parent context if appropriate.
WalkInstructionResult PeelIteration::queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) {

  if(FromBB->invar->idx == L->headerIdx) {

    WalkInstructionResult WIR = Walker->mayAscendFromContext(this, Ctx);
    if(WIR != WIRContinue)
      return WIR;

    if(iterationCount == 0) {

      Walker->leaveLoop(parentPA, Ctx);
      ShadowBB* BB = parent->getBB(parentPA->L->preheaderIdx);
      Walker->queueWalkFrom(BB->insts.size(), BB, Ctx, false);

    }
    else {

      ShadowBB* BB = parentPA->Iterations[iterationCount - 1]->getBB(parentPA->L->latchIdx);
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

  const ShadowLoopInvar* CtxLoop = L;
  const ShadowLoopInvar* FromBBLoop = FromBB->invar->outerScope;

  ShadowBBInvar* FromBBI = FromBB->invar;

  for(uint32_t i = 0, ilim = FromBBI->predIdxs.size(); i != ilim; ++i) {

    bool queueHere = false;

    ShadowBBInvar* BBI = getBBInvar(FromBBI->predIdxs[i]);

    if(edgeIsDead(BBI, FromBBI))
      continue;

    if(edgeBranchesToUnspecialisedCode(BBI, FromBB->invar)) {
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

      const ShadowLoopInvar* BBLoop = BBI->outerScope;
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

// Add block BB, instruction idx to the queue of blocks to explore from.
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

// We're walking backwards into this context; queue any block with a return instruction.
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

// Backwards walker main loop. The particular walker implementation should be given the chance
// to visit each block in turn and perhaps terminate the walk because some conclusion has been drawn.
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
	enterCall(IA, Ctx);
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

    if(inst_is<CallInst>(SI) || inst_is<InvokeInst>(SI)) {

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

// Start walking from block BB / instruction idx; doIgnoreEdges dictates whether we care about branches to unspecialised code.
ForwardIAWalker::ForwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* initialCtx, bool doIgnoreEdges) : IAWalker(initialCtx, doIgnoreEdges) {

  if(skipFirst)
    ++idx;

  WLItem firstWL = makeWL(idx, BB);

  Visited.insert(firstWL);
  PList->push_back(std::make_pair(firstWL, initialCtx));
  
}

// Forward walker main loop; see comments for BackwardIAWalker... only, y'know, forwards.
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
	InlineAttempt* IA;
	if((IA = BB->IA->getInlineAttempt(StoppedCI)) && !IA->isCommitted()) {

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

    if(inst_is<CallInst>(I) || inst_is<InvokeInst>(I)) {

      if(!shouldEnterCall(I, Ctx))
	continue;

      StoppedCI = I;
      break;

    }

  }

  return WIRContinue;

}

// Recursive functions to descend the context tree when walking out of a loop.
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

// Walk out of this call if appropriate.
void InlineAttempt::queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* Ctx) {

  if(isa<ReturnInst>(BB->invar->BB->getTerminator())) {

    if(!Callers.empty()) {

      bool firstQueue = true;
      for(SmallVector<ShadowInstruction*, 1>::iterator it = Callers.begin(),
	    itend = Callers.end(); it != itend; ++it) {

	Walker->leaveCall(this, Ctx);
	if(inst_is<CallInst>(*it))
	  Walker->queueWalkFrom((*it)->invar->idx + 1, (*it)->parent, Ctx, !firstQueue);
	else
	  (*it)->parent->IA->queueSuccessorsFW((*it)->parent, Walker, Ctx);
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

// Note in this sort of case the specialised iterations will not actually get emitted, but the analysis results
// still hold.
bool PeelIteration::queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) {

  if(PresentBlock->invar->idx == L->latchIdx && NextBlock->idx == L->headerIdx) {

    PeelIteration* nextIter = getNextIteration();
    if(!nextIter) {

      LPDEBUG("FIAW: Analysing loop in parent context because loop " << getBBInvar(L->headerIdx)->BB->getName() << " does not yet have iteration " << iterationCount+1 << "\n");
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

// Walk forwards, definitely not out of a return block, but possibly into a loop.
void IntegrationAttempt::queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* Ctx) {

  bool firstSucc = true;

  const ShadowLoopInvar* MyLoop = L;
  const ShadowLoopInvar* BBLoop = BB->invar->outerScope;

  for(uint32_t i = 0, ilim = BB->invar->succIdxs.size(); i != ilim; ++i) { 

    ShadowBBInvar* SB = getBBInvar(BB->invar->succIdxs[i]);

    if(edgeIsDead(BB->invar, SB))
      continue;

    if(edgeBranchesToUnspecialisedCode(BB->invar, SB)) {
      if(!Walker->doIgnoreEdges)
	Walker->hitIgnoredEdge();
      continue;
    }

    if(queueNextLoopIterationFW(BB, SB, Walker, Ctx, firstSucc))
      continue;

    bool queueHere = false;

    const ShadowLoopInvar* SuccLoop = SB->outerScope;
    if(SuccLoop != MyLoop) {

      if((!MyLoop) || MyLoop->contains(SuccLoop)) {

	if(MyLoop != BBLoop) {

	  // We're emitting a residual loop, don't rise into it.
	  queueHere = true;
	  
	}
	else if(PeelAttempt* LPA = getPeelAttempt(SuccLoop)) {
	  
	  assert(SuccLoop->headerIdx == SB->idx);
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

