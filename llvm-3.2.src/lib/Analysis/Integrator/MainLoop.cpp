// Implement the main loop for exploring and specialising a program.
// Algorithm:
// For each BB in a topologically ordered walk of the CFG:
// Check scope (see if we need to enter a loop, ignore because out of scope, etc)
// checkBlock it. If it hasn't been created then it has no live predecessors; skip.
// If it's the top of a loop:
//   Open up the loop, investigate within the loop according to the same rules.
//   If we didn't establish that it terminates analyse for invariants (in parent scope).
// Otherwise, for each instruction:
//   If it's a store, memcpy, memset or other memory-writing instruction (including read from file), modify the local store.
//   Elif it's a load instruction, try to read from the block-local store
//   Elif it's a VFS call, try to forward it.
//   Elif it's an expandable call (and e.g. certainty / recursion doesn't forbid it), expand it and recurse.
//   Else, (or if it's a load not yet resolved), try to constant fold it.
//
// For the topo walk, use reverse postorder DFS, where loop headers are entered in the ordering
// implying that we should at that point enter the loop rather than listing all blocks in some order.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

int debugDOT = 0;

bool InlineAttempt::analyseWithArgs(ShadowInstruction* SI, bool inLoopAnalyser, bool inAnyLoop, uint32_t parent_stack_depth) {

  bool anyChange = false;

  for(unsigned i = 0, ilim = SI->getNumArgOperands(); i != ilim; ++i) {

    ShadowArg* SArg = &(argShadows[i]);
    ShadowValue Op = SI->getCallArgOperand(i);
    
    if(SArg->i.PB) {

      if(IVMatchesVal(Op, SArg->i.PB))
	continue;

      releaseIndirectUse(ShadowValue(SArg), SArg->i.PB);
      deleteIV(SArg->i.PB);

    }

    anyChange = true;
    copyImprovedVal(Op, SArg->i.PB);
    noteIndirectUse(ShadowValue(SArg), SArg->i.PB);

  }

  anyChange |= analyseNoArgs(inLoopAnalyser, inAnyLoop, parent_stack_depth);

  return anyChange;

}

bool InlineAttempt::analyseNoArgs(bool inLoopAnalyser, bool inAnyLoop, uint32_t parent_stack_depth) {

  uint32_t new_stack_depth = (invarInfo->frameSize == -1) ? parent_stack_depth : parent_stack_depth + 1;
  return analyse(inLoopAnalyser, inAnyLoop, new_stack_depth);

}

void InlineAttempt::getInitialStore() {

  // Take our caller's store; they will make a new one
  // upon return.

  if(Callers.size())
    BBs[0]->u.localStore = activeCaller->parent->u.localStore;
  else
    BBs[0]->u.localStore = new OrdinaryLocalStore(0);

  if(invarInfo->frameSize != -1)
    BBs[0]->pushStackFrame(this);

}

void PeelIteration::getInitialStore() {
  
  if(iterationCount == 0) {

    BBs[0]->u.localStore = parent->getBB(parentPA->invarInfo->preheaderIdx)->u.localStore;

  }
  else {

    // Take the previous latch's store
    BBs[0]->u.localStore = parentPA->Iterations[iterationCount-1]->getBB(parentPA->invarInfo->latchIdx)->u.localStore;

  } 

}

bool IntegrationAttempt::analyse(bool inLoopAnalyser, bool inAnyLoop, uint32_t new_stack_depth) {

  stack_depth = new_stack_depth;

  bool anyChange = false;

  anyChange |= createEntryBlock();

  getInitialStore();

  sharingInit();

  for(uint32_t i = BBsOffset; i < (BBsOffset + nBBs); ++i) {

    // analyseBlock can increment i past loops
    anyChange |= analyseBlock(i, inLoopAnalyser, inAnyLoop, i == BBsOffset, L);

  }

  sharingCleanup();

  return anyChange;

}

void IntegrationAttempt::analyse() {

  analyse(false, false, 0);

}

bool PeelAttempt::analyse(uint32_t parent_stack_depth) {
  
  bool anyChange = false;
  stack_depth = parent_stack_depth;

  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    anyChange |= PI->analyse(false, true, parent_stack_depth);

  }

  Iterations.back()->checkFinalIteration();
  if(!isTerminated())
    dropNonterminatedStoreRefs();
 
  return anyChange;

}

bool IntegrationAttempt::analyseBlock(uint32_t& blockIdx, bool inLoopAnalyser, bool inAnyLoop, bool skipStoreMerge, const Loop* MyL) {

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return false;

  bool anyChange = false;

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoop
  ShadowBBInvar* BBI = BB->invar;
  const Loop* BBL = BBI->naturalScope;

  if(BBL != MyL) {

    BB->inAnyLoop = true;
    inAnyLoop = true;

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // Now explore the loop, if possible.
    // At the moment can't ever happen inside the loop analyser.
    PeelAttempt* LPA = 0;
    if(!inLoopAnalyser) {
      if((LPA = getOrCreatePeelAttempt(BBL))) {

	// Give the preheader an extra reference in case we need that store
	// to calculate a general version of the loop body if it doesn't terminate.
	getBB(LPA->invarInfo->preheaderIdx)->u.localStore->refCount++;
	LPA->analyse(stack_depth);

      }
    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || !LPA->isTerminated()) {

      anyChange |= analyseLoop(BBL, inLoopAnalyser);

    }
    else {

      // The loop preheader's local store was copied by the loop analysis assuming we'd
      // need it to analyse the loop body, but we've found the loop terminates; drop the extra ref.
      ShadowLoopInvar* LInfo = invarInfo->LInfo[BBL];
      getBB(LInfo->preheaderIdx)->u.localStore->dropReference();

      // Copy edges found always dead to local scope, to accelerate edgeIsDead queries without
      // checking every iteration every time.
      copyLoopExitingDeadEdges(LPA);

      // Take account of the number of live edges leaving the last iteration
      // when deciding which blocks are certain:
      // The -1 accounts for the header's incoming edge.
      pendingEdges += (LPA->Iterations.back()->pendingEdges - 1);
      LPA->Iterations.back()->pendingEdges = 0;

    }

    // Advance the main loop past this loop. Loop blocks are always contiguous in the topo ordering.
    while(blockIdx < invarInfo->BBs.size() && BBL->contains(getBBInvar(blockIdx)->naturalScope))
      ++blockIdx;
    --blockIdx;
      
    return anyChange;

  }

  BB->inAnyLoop = inAnyLoop;
   
  if(!skipStoreMerge) {

    // Loop headers and entry blocks are given their stores in other ways
    // If doBlockStoreMerge returned false this block isn't currently reachable.
    // See comments in that function for reasons why that can happen.
    if(!doBlockStoreMerge(BB))
      return false;

    // Check if the block becomes a certainty (only applicable when not in a loop!)
    checkBlockStatus(BB, inLoopAnalyser);

  }

  // As-expected checks may also be noted duirng analyseBlockInstructions:
  // they are cleared each time around because the flag might not make sense anymore if the instruction's
  // operands have degraded to the point that the instruction will no longer be resolved.

  applyMemoryPathConditions(BB);
  clearAsExpectedChecks(BB);
  noteAsExpectedChecks(BB);

  LFV3(errs() << nestingIndent() << "Start block " << BB->invar->BB->getName() << " store " << BB->u.localStore << " refcount " << BB->u.localStore->refCount << "\n");

  // Else we should just analyse this block here.
  anyChange |= analyseBlockInstructions(BB, 
					/* skip successor creation = */ false, 
					inLoopAnalyser, inAnyLoop);

  LFV3(errs() << nestingIndent() << "End block " << BB->invar->BB->getName() << " store " << BB->u.localStore << " refcount " << BB->u.localStore->refCount << "\n");

  return anyChange;

}

// Returns true if there was any change
bool IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool skipTerminatorEval, bool inLoopAnalyser, bool inAnyLoop) {

  bool anyChange = false;
  bool loadedVarargsHere = false;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &(BB->insts[i]);
    ShadowInstructionInvar* SII = SI->invar;
    Instruction* I = SII->I;

    if(inst_is<TerminatorInst>(SI)) {
      if(skipTerminatorEval)
	return anyChange;
      // Call tryEvalTerminator regardless of scope.
      anyChange |= tryEvaluateTerminator(SI, loadedVarargsHere);
      continue;
    }

    switch(I->getOpcode()) {

    case Instruction::Alloca:
      executeAllocaInst(SI);
      continue;
    case Instruction::Store:
      executeStoreInst(SI);
      continue;
    case Instruction::Call: 
      {
	
	// Certain intrinsics manifest as calls but fold like ordinary instructions.
	if(Function* F = cast_inst<CallInst>(SI)->getCalledFunction()) {
	  if(canConstantFoldCallTo(F))
	    break;
	}

	if(tryPromoteOpenCall(SI))
	  continue;
	if(tryResolveVFSCall(SI))
	  continue;
      
	bool changed;
	if(analyseExpandableCall(SI, changed, inLoopAnalyser, inAnyLoop)) {
	  
	  anyChange |= changed;
	  if(!SI->parent->u.localStore) {

	    // Call must have ended in unreachable.
	    // Don't bother analysing the rest of this path.
	    return anyChange;

	  }

	}
	else {

	  // For special calls like malloc this might define a return value.
	  executeUnexpandedCall(SI);
	  continue;

	}

      }

      // Fall through to try to get the call's return value

    }

    anyChange |= tryEvaluate(ShadowValue(SI), inLoopAnalyser, loadedVarargsHere);

  }

  return anyChange;

}

void InlineAttempt::releaseCallLatchStores() {

  releaseLatchStores(0);

}

void IntegrationAttempt::releaseLatchStores(const Loop* L) {

  // Release loops belonging to sub-calls and loops:

  ShadowLoopInvar* LInfo;
  uint32_t startBlock;
  if(L) {
    LInfo = invarInfo->LInfo[L];
    startBlock = LInfo->headerIdx;
  }
  else {
    LInfo = 0;
    startBlock = 0;
  }

  for(uint32_t i = startBlock; i < (BBsOffset + nBBs); ++i) {

    if(L && !L->contains(getBBInvar(i)->naturalScope))
      break;

    ShadowBB* BB = getBB(i);
    if(!BB)
      continue;

    ShadowBBInvar* BBI = BB->invar;
    const Loop* BBL = BBI->naturalScope;
   
    if(BBL != L) {

      releaseLatchStores(BBL);

      // Skip past the loop:
      while(i < (BBsOffset + nBBs) && BBL->contains(getBBInvar(i)->naturalScope))
	++i;
      --i;
      
    }
    else {

      // Look for calls with subloops:
      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &(BB->insts[j]);

	if(inst_is<CallInst>(SI)) {

	  if(InlineAttempt* IA = getInlineAttempt(SI))
	    IA->releaseCallLatchStores();

	}

      }

    }

  }
   
  // Release here:

  if(LInfo) {
    // Release the latch store that the header will not use again:
    if(pass->latchStoresRetained.erase(std::make_pair(this, L))) {
      ShadowBB* LBB = getBB(LInfo->latchIdx);
      release_assert("Releasing store from dead latch?");
      LBB->u.localStore->dropReference();
    }
  }

}

// nestedLoop indicates we're being analysed in the context of a loop further out,
// either in our call or a parent call.
bool IntegrationAttempt::analyseLoop(const Loop* L, bool nestedLoop) {

  ShadowLoopInvar* LInfo = invarInfo->LInfo[L];
  bool anyChange = true;
  bool firstIter = true;
  bool everChanged = false;
  uint64_t iters = 0;

  ShadowBB* PHBB = getBB(LInfo->preheaderIdx);
  ShadowBB* HBB = getBB(LInfo->headerIdx);
  ShadowBB* LBB = getBB(LInfo->latchIdx);

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at entry: " << PHBB->u.localStore->refCount << "\n");

  // Stop iterating if we show that the latch edge died!
  while(anyChange && (firstIter || !edgeIsDead(getBBInvar(LInfo->latchIdx), HBB->invar))) {
    
    ++iters;

    // Give the preheader store an extra reference to ensure it is never modified.
    // This ref corresponds to ph retaining its reference (h has already been given one by ph's successor code).
    PHBB->u.localStore->refCount++;

    {

      if(!firstIter) {

	// Drop store references at exit edges: we're going around again.
	for(std::vector<std::pair<uint32_t, uint32_t> >::iterator it = LInfo->exitEdges.begin(),
	      itend = LInfo->exitEdges.end(); it != itend; ++it) {

	  ShadowBB* BB = getBB(it->first);

	  if(BB && !edgeIsDead(BB->invar, getBBInvar(it->second))) {

	    LFV3(errs() << "Drop exit edge " << BB->invar->BB->getName() << " -> " << getBBInvar(it->second)->BB->getName() << " with store " << BB->u.localStore << "\n");
	    BB->u.localStore->dropReference();

	    // Drop a pendingEdges count at the same time, for the same reason:
	    release_assert(pendingEdges && "Reducing pending edges below zero");
	    --pendingEdges;

	  }

	}

      }

      if(pass->latchStoresRetained.count(std::make_pair(this, L))) {
	release_assert(LBB && "Latch store retained but latch block dead?");
	// We've analysed this loop before -- we must be under analysis as a nested loop.
	// If our latch edge lives we should use its store ref, which was saved last time around.
	firstIter = false;
      }

      OrdinaryMerger V(false);

      if(!firstIter) {

	// Merge the latch store with the preheader store:
	release_assert(LBB && "Iterating on a loop with a dead latch block?");
	V.visit(LBB, 0, false);
	V.visit(PHBB, 0, false);

      }
      else {

	// Give the header block the store from the preheader
	V.visit(PHBB, 0, false);

      }

      V.doMerge();
      HBB->u.localStore = V.newMap;

    }

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after old exit elim: " << PHBB->u.localStore->refCount << "\n");

    anyChange = false;

    for(uint32_t i = LInfo->headerIdx; i < (BBsOffset + nBBs); ++i) {

      if(!L->contains(getBBInvar(i)->naturalScope))
	break;

      if(i == LInfo->headerIdx) {

	release_assert(pendingEdges && "Decrementing pendingEdges below zero");
	// Drop the preheader->header or latch->header edge.
	--pendingEdges;

      }

      anyChange |= analyseBlock(i, true, true, i == LInfo->headerIdx, L);

    }

    if(!LBB)
      LBB = getBB(LInfo->latchIdx);

    everChanged |= anyChange;

    firstIter = false;

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after block analysis: " << PHBB->u.localStore->refCount << "\n");

  }

  if(edgeIsDead(getBBInvar(LInfo->latchIdx), HBB->invar))
    release_assert(iters == 1 && "Loop analysis found the latch dead but not first time around?");

  // Release the preheader store that was held for merging in each iteration:
  PHBB->u.localStore->dropReference();

  // If this is a nested loop, hang onto the reference given from latch to header
  // for use in the next iteration of analysing this loop.
  bool thisLatchAlive = LBB && !edgeIsDead(LBB->invar, HBB->invar);
  if(!nestedLoop) {
    
    releaseLatchStores(L);
    if(thisLatchAlive)
      LBB->u.localStore->dropReference();

  }
  else {

    if(thisLatchAlive)
      pass->latchStoresRetained.insert(std::make_pair(this, L));

  }

  // Similarly the latch block will have given the header a reference towards determining successor block certainty. Drop it.
  if(thisLatchAlive)
    --pendingEdges;

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at exit: " << PHBB->u.localStore->refCount << "\n");
  
  return everChanged;

}

void InlineAttempt::executeCall(uint32_t parent_stack_depth) {

  uint32_t new_stack_depth = (invarInfo->frameSize == -1) ? parent_stack_depth : parent_stack_depth + 1;
  execute(new_stack_depth);

}

void IntegrationAttempt::executeLoop(const Loop* ThisL) {

  ShadowLoopInvar* LInfo = invarInfo->LInfo[ThisL];

  ShadowBB* PHBB = getBB(LInfo->preheaderIdx);
  ShadowBB* HBB = getBB(LInfo->headerIdx); 

  // If this context had a retained latch store from previous instances
  // we don't need it anymore, drop now.
  if(pass->latchStoresRetained.erase(std::make_pair(this, ThisL))) {

    ShadowBB* LBB = getBB(LInfo->latchIdx);
    release_assert(LBB && "Executed loop with retained latch, but not available?");
    LBB->u.localStore->dropReference();

  }

  // No need for extra references: we simply execute the residual loop once
  // as fixpoints have already been established about what is stored.
  // We only need special treatment to prevent header blocks from trying to
  // consume a store from their latch blocks.
  HBB->u.localStore = PHBB->u.localStore;

  for(uint32_t i = LInfo->headerIdx; i < (BBsOffset + nBBs); ++i) {

    ShadowBB* BB = getBB(i);
    if(!BB)
      continue;

    ShadowBBInvar* BBI = BB->invar;

    if(!ThisL->contains(BBI->naturalScope))
      break;
    else if(BBI->naturalScope != ThisL) {

      // Subloop requires the same special store treatment as this loop.
      executeLoop(BBI->naturalScope);
      while(i < (BBsOffset + nBBs) && BBI->naturalScope->contains(getBBInvar(i)->naturalScope))
	++i;
      --i;
      
    }
    else {

      if(i != LInfo->headerIdx) {
	if(!doBlockStoreMerge(BB))
	  return;
      }
      
      executeBlock(BB);

    }

  }

  // Drop extra ref given to the header block if one was granted.
  ShadowBB* LBB = getBB(LInfo->latchIdx);
  if(LBB && !edgeIsDead(LBB->invar, HBB->invar))
    LBB->u.localStore->dropReference();

}

// Like analyse(), but used from sharing pathways when we're sure none of the functions need re-evaluating.
// We really only want to recreate its effects on the store.
void IntegrationAttempt::execute(uint32_t new_stack_depth) {

  stack_depth = new_stack_depth;

  getInitialStore();
  for(uint32_t i = 0; i < nBBs; ++i) {

    if(!BBs[i])
      continue;

    ShadowBB* BB = BBs[i];
    ShadowBBInvar* BBI = BB->invar;
    
    if(BBI->naturalScope != L) {

      PeelAttempt* LPA = getPeelAttempt(BBI->naturalScope);
      if(LPA && LPA->isTerminated()) {

	// Run each individual iteration

	for(std::vector<PeelIteration*>::iterator it = LPA->Iterations.begin(), 
	      itend = LPA->Iterations.end(); it != itend; ++it) {

	  (*it)->execute(stack_depth);

	}

      }
      else {

	executeLoop(BBI->naturalScope);

      }

      // Skip blocks in this scope

      while(i < nBBs && BBI->naturalScope->contains(getBBInvar(i + BBsOffset)->naturalScope))
	++i;
      --i;

    }
    else {

      if(i != 0) {
	if(!doBlockStoreMerge(BB))
	  return;
      }

      executeBlock(BB);

    }

  }

}

// Part of executing known-not-changed contexts.
// Just execute potentially side-effecting instructions.
void IntegrationAttempt::executeBlock(ShadowBB* BB) {

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &BB->insts[i];
    Instruction* I = SI->invar->I;
    switch(I->getOpcode()) {

    case Instruction::Alloca:
      executeAllocaInst(SI);
      break;

    case Instruction::Store:
      executeStoreInst(SI);
      break;

    case Instruction::Call:
      {

	if(Function* F = cast_inst<CallInst>(SI)->getCalledFunction()) {
	  if(canConstantFoldCallTo(F))
	    break;
	}

	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  IA->activeCaller = SI;
	  IA->executeCall(stack_depth);
	  doCallStoreMerge(SI);
	  if(!SI->parent->u.localStore)
	    return;

	}
	else {
	  
	  executeUnexpandedCall(SI);

	}

      }
      break;

    default:
      break;

    }

  }

  // Frame push happens in getInitialStore; pop would usually happen in terminator evaluation.
  if(inst_is<ReturnInst>(&BB->insts[BB->insts.size() - 1])) {
    if(invarInfo->frameSize != -1)
      BB->popStackFrame();
    return;
  }

  for(uint32_t i = 0; i < BB->invar->succIdxs.size(); ++i) {
	
    if(!BB->succsAlive[i])
      continue;

    // Create a store reference for each live successor
    ++BB->u.localStore->refCount;
	
  }

  // Drop ref belonging to this block.
  BB->u.localStore->dropReference();

}
