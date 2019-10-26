//===- MainLoop.cpp -------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

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

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

int nLoopsWritten = 0;

// Analyse this function call instance. SI is the call instruction; inLoopAnalyser indicates that we're investigating the general
// case of a loop body or mutually recursive function; inAnyLoop indicates we're within a loop at some level of the call graph
// even if we're investigating a specific loop iteration; parent_stack_depth is the stack frame depth used by the parent call.
bool InlineAttempt::analyseWithArgs(ShadowInstruction* SI, bool inLoopAnalyser, bool inAnyLoop, uint32_t parent_stack_depth) {

  bool anyChange = false;

  for(unsigned i = 0, ilim = SI->getNumArgOperands(); i != ilim; ++i) {

    ShadowArg* SArg = &(argShadows[i]);
    ShadowValue Op = SI->getCallArgOperand(i);
    
    if(SArg->i.PB) {

      if(IVMatchesVal(Op, SArg->i.PB))
	continue;
      deleteIV(SArg->i.PB);

    }

    anyChange = true;
    copyImprovedVal(Op, SArg->i.PB);

  }

  anyChange |= analyseNoArgs(inLoopAnalyser, inAnyLoop, parent_stack_depth);

  return anyChange;

}

// As above, but exclude trying to pull argument values from our parent. Called directly for the entry
// point of the specialisation root, since its arguments are given by user directives, not its caller.
bool InlineAttempt::analyseNoArgs(bool inLoopAnalyser, bool inAnyLoop, uint32_t parent_stack_depth) {

  uint32_t new_stack_depth = (invarInfo->frameSize == -1) ? parent_stack_depth : parent_stack_depth + 1;
  bool ret = analyse(inLoopAnalyser, inAnyLoop, new_stack_depth);

  returnValue = 0;

  if(!F.getFunctionType()->getReturnType()->isVoidTy()) {
    SmallVector<ShadowValue, 4> Vals;
    getLiveReturnVals(Vals);
    getMergeValue(Vals, returnValue);
  }

  return ret;

}

// Set up the block-local store at the start of specialisation.
// Essentially this just imports globals if possible and notes that things that predate
// specialisation have a special "old" aliasing class compared to some objects allocated during
// specialisation.
static void initialiseStore(ShadowBB* BB) {

  for(uint32_t i = 0, ilim = GlobalIHP->heap.size(); i != ilim; ++i) {

    AllocData& AD = GlobalIHP->heap[i];
    ImprovedValSetSingle* Init = new ImprovedValSetSingle();

    if(AD.allocValue.isGV()) {

      GlobalVariable* G = AD.allocValue.getGV()->G;

      if(GlobalIHP->useGlobalInitialisers && G->hasDefinitiveInitializer()) {

	Constant* I = G->getInitializer();
	if(isa<ConstantAggregateZero>(I)) {

	  Init->SetType = ValSetTypeScalarSplat;
	  Type* I8 = Type::getInt8Ty(BB->invar->BB->getContext());
	  Constant* I8Z = Constant::getNullValue(I8);
	  Init->insert(ImprovedVal(I8Z));

	}
	else {

	  std::pair<ValSetType, ImprovedVal> InitIV = getValPB(I);
	  (*Init) = ImprovedValSetSingle(InitIV.second, InitIV.first);

	}

      }
      else {

	// Start off overdef, and known-older-than-specialisation.
	Init->SetType = ValSetTypeOldOverdef;

      }

    }
    else {

      // All non-GVs initialise to an old value.
      Init->SetType = ValSetTypeOldOverdef;

    }

    LocStore* LS = BB->getWritableStoreFor(AD.allocValue, 0, AD.storeSize, true);
    release_assert(LS && "Non-writable location in initialiseStore?");
    LS->store->dropReference();
    LS->store = Init;

  }

}

// Set up the entry block store by pulling from all call instructions that
// target this function instance. There can only be more than one if function
// sharing is enabled.
void InlineAttempt::getInitialStore(bool inLoopAnalyser) {

  // Take our caller's store; they will make a new one
  // upon return.

  if(Callers.size())
    BBs[0]->takeStoresFrom(activeCaller->parent, inLoopAnalyser);
  else {
    BBs[0]->localStore = new OrdinaryLocalStore(0);
    initialiseStore(BBs[0]);
    BBs[0]->fdStore = new FDStore();
    initialiseFDStore(BBs[0]->fdStore);
    BBs[0]->tlStore = new TLLocalStore(0);
    BBs[0]->dseStore = new DSELocalStore(0);
    BBs[0]->tlStore->allOthersClobbered = false;
    BBs[0]->dseStore->allOthersClobbered = false;
  }

  if(BBs[0]->tlStore) {
    // Store a copy of the TL store for use if the context is disabled.
    backupTlStore = BBs[0]->tlStore;
    ++backupTlStore->refCount;
  }
  if(BBs[0]->dseStore) {
    backupDSEStore = BBs[0]->dseStore;
    ++backupDSEStore->refCount;
  }
  
  if(invarInfo->frameSize != -1 || !Callers.size()) {
   
    BBs[0]->pushStackFrame(this);
    if(BBs[0]->tlStore) {

      BBs[0]->tlStore = BBs[0]->tlStore->getWritableFrameList();
      BBs[0]->tlStore->pushStackFrame(this);

    }
    if(BBs[0]->dseStore) {

      BBs[0]->dseStore = BBs[0]->dseStore->getWritableFrameList();
      BBs[0]->dseStore->pushStackFrame(this);

    }

  }

}

// Get the initial store for this loop iteration, either from the preheader or the latch block.
void PeelIteration::getInitialStore(bool inLoopAnalyser) {
  
  if(iterationCount == 0) {

    BBs[0]->takeStoresFrom(parent->getBB(parentPA->L->preheaderIdx), inLoopAnalyser);

  }
  else {

    // Take the previous latch's store
    BBs[0]->takeStoresFrom(parentPA->Iterations[iterationCount-1]->getBB(parentPA->L->latchIdx), inLoopAnalyser);

  } 

}

// Root analysis function for this context. Analyse each basic block in top-sorted order; recurse
// into any child contexts as they are encountered. Parameter meanings are as for InlineAttempt::analyseWithArgs.
bool IntegrationAttempt::analyse(bool inLoopAnalyser, bool inAnyLoop, uint32_t new_stack_depth) {

  stack_depth = new_stack_depth;

  bool anyChange = false;
  
  // Mark entry block certain or assumed-reached if appropriate
  anyChange |= createEntryBlock();

  getInitialStore(inLoopAnalyser);

  sharingInit();

  for(uint32_t i = BBsOffset; i < (BBsOffset + nBBs); ++i) {

    // analyseBlock can increment i past loops
    anyChange |= analyseBlock(i, inLoopAnalyser, inAnyLoop, i == BBsOffset, L);

  }

  sharingCleanup();

  return anyChange;

}

// Root analysis entry point, called after parsing user directives such as assertions
// about initial state when entering analysis.
void IntegrationAttempt::analyse() {

  analyse(false, false, 0);

}

// Analyse a loop in the particular case where we consider each iteration individually.
// parent_stack_depth is the parent function's stack frame index; readsTentativeData gets set if the loop
// ever makes a read that needs checking for correctness (e.g. to guard against concurrent alteration by
// another thread); containsCheckedReads gets set if any file-reading operations require a runtime check.
bool PeelAttempt::analyse(uint32_t parent_stack_depth, bool& readsTentativeData, bool& containsCheckedReads) {
  
  bool anyChange = false;
  stack_depth = parent_stack_depth;

  readsTentativeData = false;

  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    anyChange |= PI->analyse(false, true, parent_stack_depth);
    parent->inheritDiagnosticsFrom(PI);
    readsTentativeData |= PI->readsTentativeData;
    containsCheckedReads |= PI->containsCheckedReads;

  }

  Iterations.back()->checkFinalIteration();
  if(!isTerminated())
    dropNonterminatedStoreRefs();
 
  return anyChange;

}

// Set the block-local store for BBI to S. 'kind' is used to implement half-assed polymorphism, since TLLocalStore
// and DSELocalStore don't have a common base class at the moment.
void PeelIteration::setExitingStore(void* S, ShadowBBInvar* BBI, const ShadowLoopInvar* exitLoop, StoreKind kind) {

  PeelAttempt* LPA;

  // Defer to child loop iterations?

  if(BBI->naturalScope != L && 
     (LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) && 
     LPA->isTerminated()) {

    // This gets called for every iteration since a non-final iteration may exit
    // in the presence of user options allowing loop exploration to continue regardless.
    for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
      LPA->Iterations[i]->setExitingStore(S, BBI, exitLoop, kind);

    return;

  }

  // For each live edge leaving the loop, replace the exiting block's store with S.
  ShadowBB* ExitingBB = getBB(*BBI);
  if(!ExitingBB)
    return;

  uint32_t exitingEdges = 0;

  for(uint32_t i = 0, ilim = BBI->succIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* ExitedBBI = getBBInvar(BBI->succIdxs[i]);
    if(ExitingBB->succsAlive[i] && 
       ((!ExitedBBI->naturalScope) || !exitLoop->contains(ExitedBBI->naturalScope))) {

      ++exitingEdges;

    }

  }

  if(kind == StoreKindTL) {

    for(uint32_t i = 0; i != exitingEdges; ++i) {
      
      SAFE_DROP_REF(ExitingBB->tlStore);
      ((TLLocalStore*)S)->refCount++;
    }
    
    ExitingBB->tlStore = (TLLocalStore*)S;

  }
  else if(kind == StoreKindDSE) {

    for(uint32_t i = 0; i != exitingEdges; ++i) {
      
      SAFE_DROP_REF(ExitingBB->dseStore);
      ((DSELocalStore*)S)->refCount++;
    }
    
    ExitingBB->dseStore = (DSELocalStore*)S;

  }

}

// Push store references out from this loop iteration.
void PeelIteration::setExitingStores(void* S, StoreKind SK) {

  for(std::vector<uint32_t>::const_iterator it = parentPA->L->exitingBlocks.begin(),
	itend = parentPA->L->exitingBlocks.end(); it != itend; ++it) {

    ShadowBBInvar* ExitingBBI = getBBInvar(*it);
    setExitingStore(S, ExitingBBI, L, SK);

  }
  
}

// Our parent want to take NewCBs, NewFCBs and NewFs from us. These are parentless basic blocks, failed-path basic blocks and functions
// generated by this context and its children.
void PeelIteration::inheritCommitBlocksAndFunctions(std::vector<BasicBlock*>& NewCBs, std::vector<BasicBlock*>& NewFCBs, std::vector<Function*>& NewFs) {

  parentPA->CommitBlocks.insert(parentPA->CommitBlocks.end(), NewCBs.begin(), NewCBs.end());
  parentPA->CommitFailedBlocks.insert(parentPA->CommitFailedBlocks.end(), NewFCBs.begin(), NewFCBs.end());
  parentPA->CommitFunctions.insert(parentPA->CommitFunctions.end(), NewFs.begin(), NewFs.end());

  NewCBs.clear();
  NewFCBs.clear();
  NewFs.clear();

}

// As above.
void InlineAttempt::inheritCommitBlocksAndFunctions(std::vector<BasicBlock*>& NewCBs, std::vector<BasicBlock*>& NewFCBs, std::vector<Function*>& NewFs) {

  CommitBlocks.insert(CommitBlocks.end(), NewCBs.begin(), NewCBs.end());
  CommitFailedBlocks.insert(CommitFailedBlocks.end(), NewFCBs.begin(), NewFCBs.end());
  CommitFunctions.insert(CommitFunctions.end(), NewFs.begin(), NewFs.end());

  NewCBs.clear();
  NewFCBs.clear();
  NewFs.clear();

}

// Analyse / interpret each instruction in block BBs[blockIdx]. inLoopAnalyser and inAnyLoop have the same meanings as for
// InlineAttempt::analyseWithArgs above. skipStoreMerge means we shouldn't try to pull and merge
// block-local stores from our predecessor blocks, usually because there is a special case here
// like a function entry block that doesn't have local predecessors.
bool IntegrationAttempt::analyseBlock(uint32_t& blockIdx, bool inLoopAnalyser, bool inAnyLoop, bool skipStoreMerge, const ShadowLoopInvar* MyL) {

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return false;

  bool anyChange = false;

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoop
  ShadowBBInvar* BBI = BB->invar;
  const ShadowLoopInvar* BBL = BBI->naturalScope;

  if(BBL != MyL) {

    BB->inAnyLoop = true;
    inAnyLoop = true;

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // Now explore the loop, if possible.
    // At the moment can't ever happen inside the loop analyser.
    PeelAttempt* LPA = 0;
    if((!inLoopAnalyser) && (LPA = getOrCreatePeelAttempt(BBL))) {

      // Give the preheader an extra reference in case we need that store
      // to calculate a general version of the loop body if it doesn't terminate.
      ShadowBB* PHBB = getBB(LPA->L->preheaderIdx);
      PHBB->refStores();

      bool loopReadsTentativeData, loopContainsCheckedReads;
      LPA->analyse(stack_depth, loopReadsTentativeData, loopContainsCheckedReads);
      readsTentativeData |= loopReadsTentativeData;
      containsCheckedReads |= loopContainsCheckedReads;  

      // We're certainly not in the loop analyser, so pick whether to keep a terminated
      // version of the loop now.

      if(LPA->isTerminated()) {

	LPA->findProfitableIntegration();
	if(!LPA->isEnabled()) {

	  // The preheader already has a copy of the TL and DSE stores
	  // in case the loop didn't terminate -- give it to each exiting block.

	  TLLocalStore* backupTlStore;
	  bool dropTlRef;
	  if(readsTentativeData) {
	    backupTlStore = new TLLocalStore(stack_depth);
	    backupTlStore->allOthersClobbered = true;
	    dropTlRef = true;
	  }
	  else {
	    backupTlStore = PHBB->tlStore;
	    dropTlRef = false;
	  }

	  LPA->Iterations.back()->setExitingStores(backupTlStore, StoreKindTL);
	  
	  if(dropTlRef)
	    backupTlStore->dropReference();

	  DSELocalStore* backupDSEStore = PHBB->dseStore;

	  setAllNeededTop(backupDSEStore);
	  DSELocalStore* emptyStore = new DSELocalStore(stack_depth);
	  emptyStore->allOthersClobbered = true;
	  LPA->Iterations.back()->setExitingStores(emptyStore, StoreKindDSE);
	  emptyStore->dropReference();

	}

      }

      if(LPA->isTerminated() && LPA->isEnabled()) {

	// Committed blocks in the iterations will be used;
	// next parent inherits them.
	inheritCommitBlocksAndFunctions(LPA->CommitBlocks, LPA->CommitFailedBlocks, LPA->CommitFunctions);

      }
      else {

	LPA->releaseCommittedChildren();

      }

    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || !LPA->isTerminated()) {

      anyChange |= analyseLoop(BBL, inLoopAnalyser);

      if(!inLoopAnalyser) {

	// Run other passes over the whole loop
	gatherIndirectUsersInLoop(BBL);
	
	findTentativeLoadsInUnboundedLoop(BBL, /* commit disabled here = */ false, /* second pass = */ false);
	tryKillStoresInUnboundedLoop(BBL, /* commit disabled here = */ false, /* disable writes = */ false);

      }
	
    }
    else {

      // The loop preheader's local store was copied by the loop analysis assuming we'd
      // need it to analyse the loop body, but we've found the loop terminates; drop the extra ref.

      // For the common case where the loop has a single known exit point, perform store simplifications.
      // These apply because the store was forked anticipating failure to establish an iteration count.

      ShadowBB* ExitingBlock = LPA->Iterations.back()->getUniqueExitingBlock();

      std::vector<ShadowValue> simplifyStores;
      getBB(BBL->preheaderIdx)->derefStores(ExitingBlock ? &simplifyStores : 0);

      for(std::vector<ShadowValue>::iterator it = simplifyStores.begin(),
	    itend = simplifyStores.end(); it != itend; ++it) {
	  
	if(LocStore* LS = ExitingBlock->getReadableStoreFor(*it))
	  LocStore::simplifyStore(LS);

      }

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

    // Check if the block becomes a certainty (only applicable when not in a loop!)
    checkBlockStatus(BB, inLoopAnalyser);

    // Loop headers and entry blocks are given their stores in other ways
    // If doBlockStoreMerge returned false this block isn't currently reachable.
    // See comments in that function for reasons why that can happen.
    if(!doBlockStoreMerge(BB))
      return false;

    if(!inLoopAnalyser) {

      doTLStoreMerge(BB);
      doDSEStoreMerge(BB);

    }

  }

  // As-expected checks may also be noted duirng analyseBlockInstructions:
  // they are cleared each time around because the flag might not make sense anymore if the instruction's
  // operands have degraded to the point that the instruction will no longer be resolved.
  // The noteAsExpected function here only tags those which are mentioned in path conditions.

  applyMemoryPathConditions(BB, inLoopAnalyser, inAnyLoop);
  clearAsExpectedChecks(BB);
  noteAsExpectedChecks(BB);

  if(!inLoopAnalyser) {

    //TLWalkPathConditions(BB, true, false);
    if(pass->countPathConditionsAtBlockStart(BB->invar, BB->IA)) {
      setAllNeededTop(BB->dseStore);
      BB->dseStore = BB->dseStore->getEmptyMap();
    }
     
  }

  LFV3(errs() << nestingIndent() << "Start block " << BB->invar->BB->getName() << " store " << BB->localStore << " refcount " << BB->localStore->refCount << "\n");

  // Else we should just analyse this block here.
  anyChange |= analyseBlockInstructions(BB, inLoopAnalyser, inAnyLoop);

  LFV3(errs() << nestingIndent() << "End block " << BB->invar->BB->getName() << " store " << BB->localStore << " refcount " << BB->localStore->refCount << "\n");

  return anyChange;

}

// Try to analyse a call/invoke instruction SI by creating or reusing a specialisation context
// representing the call. Set 'changed' if anything about the analysis changed (e.g. arguments
// or instructions had different values to any previous analysis). inLoopAnalyser, inAnyLoop
// have the same meanings as for InlineAttempt::analyseWithArgs.
// Return true if we ended up with an InlineAttempt available for this call.
bool IntegrationAttempt::analyseExpandableCall(ShadowInstruction* SI, bool& changed, bool inLoopAnalyser, bool inAnyLoop) {

  changed = false;

  bool created, needsAnalyse;
  InlineAttempt* IA = getOrCreateInlineAttempt(SI, created, needsAnalyse);

  if(IA) {

    IA->activeCaller = SI;

    if(needsAnalyse) {

      changed |= created;
      
      // Setting active = true prevents incomplete dependency information from being used
      // to justify sharing the function node.
      IA->active = true;

      changed |= IA->analyseWithArgs(SI, inLoopAnalyser, inAnyLoop, stack_depth);
      readsTentativeData |= IA->readsTentativeData;
      containsCheckedReads |= IA->containsCheckedReads;
      
      inheritDiagnosticsFrom(IA);
      mergeChildDependencies(IA);

      if(created && !IA->isUnsharable())
	pass->addSharableFunction(IA);
      else if(IA->registeredSharable && IA->isUnsharable())
	pass->removeSharableFunction(IA);
     
      IA->active = false;

      if(changed && IA->hasFailedReturnPath()) {

	// Must create a copy of this block for failure paths, starting at the call successor.
	// Invoke instructions fail directly to their non-exception successors;
	// call instructions introduce a break in their basic block.
	if(inst_is<CallInst>(SI))
	  getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(SI->parent->invar->idx, SI->invar->idx + 1);
	else
	  getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(SI->parent->invar->succIdxs[0], 0);

      }

      doCallStoreMerge(SI);

      if(!inLoopAnalyser) {
	    
	doTLCallMerge(SI->parent, IA);
	doDSECallMerge(SI->parent, IA);

	IA->finaliseAndCommit(inLoopAnalyser);

      }
      
    }
    else {

      IA->executeCall(stack_depth);

    }

  }

  return !!IA;

}

// Analyse instruction SI in this context. inLoopAnalyser and anyLoop have the same meanings as in InlineAttempt::analyseWithArgs above.
// loadedVarargsHere indicates this instruction read a vararg. bail indicates that this path ended in an unreachable instruction.
bool IntegrationAttempt::analyseInstruction(ShadowInstruction* SI, bool inLoopAnalyser, bool inAnyLoop, bool& loadedVarargsHere, bool& bail) {

  ShadowInstructionInvar* SII = SI->invar;
  Instruction* I = SII->I;

  if(SI->isTerminator() && !inst_is<InvokeInst>(SI)) {
    // Call tryEvalTerminator regardless of scope.
    return tryEvaluateTerminator(SI, loadedVarargsHere);
  }

  bool changed = false;

  switch(I->getOpcode()) {

  // All fence logic is implemented in the tentative loads passlet; nothing to do here.
  case Instruction::Fence:
    return false;
  case Instruction::Alloca:
    executeAllocaInst(SI);
    return false;
  case Instruction::Store:
    executeStoreInst(SI);
    return false;
  case Instruction::Call: 
  case Instruction::Invoke:
    {
	
      // Certain intrinsics manifest as calls but fold like ordinary instructions.
      if(Function* F = getCalledFunction(SI)) {
	if(canConstantFoldCallTo(cast<CallInst>(I), F))
	  break;
      }

      if(tryPromoteOpenCall(SI))
	return false;
      if(tryResolveVFSCall(SI))
	return false;
      
      bool isExpanded = analyseExpandableCall(SI, changed, inLoopAnalyser, inAnyLoop);
      if(isExpanded) {
	  
	if(!SI->parent->localStore) {

	  // Call must have ended in unreachable.
	  // Don't bother analysing the rest of this path.
	  bail = true;

	}

      }
      else {

	// For special calls like malloc this might define a return value;
	// for others it is responsible for placing an Overdef return.
	executeUnexpandedCall(SI);

      }

      // Invoke instructions are also block terminators.
      if(inst_is<InvokeInst>(SI))
	changed |= tryEvaluateTerminator(SI, loadedVarargsHere);

      if(!isExpanded)
	return changed;

    }

    // Fall through to try to get the call's return value

  }

  if(!bail)
    changed |= tryEvaluate(ShadowValue(SI), inLoopAnalyser, loadedVarargsHere);
  return changed;

}

// Analyse all instructions in block BB. Returns true if there was any change.
bool IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool inLoopAnalyser, bool inAnyLoop) {

  bool anyChange = false;
  bool loadedVarargsHere = false;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &(BB->insts[i]);
    bool bail = false;
    anyChange |= analyseInstruction(SI, inLoopAnalyser, inAnyLoop, loadedVarargsHere, bail);
    if(bail)
      return anyChange;

    if(!inLoopAnalyser) {

      // In the loop analysis case we reach a fixed point before running other passes.

      // Check if this uses an FD or allocation:
      noteIndirectUse(ShadowValue(SI), SI->i.PB);
      
      // Check if this load or memcpy should be checked at runtime:
      TLAnalyseInstruction(*SI, /* commit disabled = */ false, /* second pass = */ false, /* in loop analyser = */ false);

      // Update the DSE store:
      DSEAnalyseInstruction(SI, /* commit disabled = */false, 
			    /*disable writes=*/false, 
			    /*enter calls =*/false, bail);

    }

  }

  return anyChange;

}

// Loop latch edges retain a reference on their block-local stores used when finding fixed-point solutions
// concerning general cases of loop bodies, recursive functions and their children. This releases those
// references when we get back to top level.
void InlineAttempt::releaseCallLatchStores() {

  releaseLatchStores(0);

}

// As above.
void IntegrationAttempt::releaseLatchStores(const ShadowLoopInvar* L) {

  // Release loops belonging to sub-calls and loops:

  uint32_t startBlock = 0;
  if(L)
    startBlock = L->headerIdx;

  for(uint32_t i = startBlock; i < (BBsOffset + nBBs); ++i) {

    if(L && !L->contains(getBBInvar(i)->naturalScope))
      break;

    ShadowBB* BB = getBB(i);
    if(!BB)
      continue;

    ShadowBBInvar* BBI = BB->invar;
    const ShadowLoopInvar* BBL = BBI->naturalScope;
   
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

	if(InlineAttempt* IA = getInlineAttempt(SI))
	  IA->releaseCallLatchStores();

      }

    }

  }
   
  // Release here:

  if(L) {
    // Release the latch store that the header will not use again:
    if(pass->latchStoresRetained.erase(std::make_pair(this, L))) {
      ShadowBB* LBB = getBB(L->latchIdx);
      release_assert("Releasing store from dead latch?");
      LBB->derefStores();
    }
  }

}

// Analyse a loop's general case (i.e. trying to find a fixed-point solution regarding
// the body, rather than analysing each individual iteration; for that see PeelAttempt::analyse)
// nestedLoop indicates we're being analysed in the context of a loop further out,
// either in our call or a parent call.
bool IntegrationAttempt::analyseLoop(const ShadowLoopInvar* L, bool nestedLoop) {

  bool anyChange = true;
  bool firstIter = true;
  bool everChanged = false;
  uint64_t iters = 0;

  ShadowBB* PHBB = getBB(L->preheaderIdx);
  ShadowBB* HBB = getBB(L->headerIdx);
  ShadowBB* LBB = getBB(L->latchIdx);

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at entry: " << PHBB->localStore->refCount << "\n");

  // Stop iterating if we show that the latch edge died!
  while(anyChange && (firstIter || !edgeIsDead(getBBInvar(L->latchIdx), HBB->invar))) {
    
    ++iters;

    // Give the preheader store an extra reference to ensure it is never modified.
    // This ref corresponds to ph retaining its reference (h has already been given one by ph's successor code).
    PHBB->refStores();

    {

      if(!firstIter) {

	// Drop store references at exit edges: we're going around again.
	for(std::vector<std::pair<uint32_t, uint32_t> >::const_iterator it = L->exitEdges.begin(),
	      itend = L->exitEdges.end(); it != itend; ++it) {

	  ShadowBB* BB = getBB(it->first);

	  if(BB 
	     && (!edgeIsDead(BB->invar, getBBInvar(it->second)))
	     && (!edgeBranchesToUnspecialisedCode(BB->invar, getBBInvar(it->second)))) {

	    LFV3(errs() << "Drop exit edge " << BB->invar->BB->getName() << " -> " << getBBInvar(it->second)->BB->getName() << " with store " << BB->localStore << "\n");
	    BB->derefStores();

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

      OrdinaryMerger V(this, false);
      FDStoreMerger V2;

      if(!firstIter) {

	// Merge the latch store with the preheader store:
	release_assert(LBB && "Iterating on a loop with a dead latch block?");
	V.visit(LBB, 0, false);
	V2.visit(LBB, 0, false);
	V.visit(PHBB, 0, false);
	V2.visit(PHBB, 0, false);

      }
      else {

	// Give the header block the store from the preheader
	V.visit(PHBB, 0, false);
	V2.visit(PHBB, 0, false);

      }

      V.doMerge();
      HBB->localStore = V.newMap;
      V2.doMerge();
      HBB->fdStore = V2.newStore;

    }

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after old exit elim: " << PHBB->localStore->refCount << "\n");

    anyChange = false;

    for(uint32_t i = L->headerIdx; i < (BBsOffset + nBBs); ++i) {

      if(!L->contains(getBBInvar(i)->naturalScope))
	break;

      if(i == L->headerIdx) {

	release_assert(pendingEdges && "Decrementing pendingEdges below zero");
	// Drop the preheader->header or latch->header edge.
	--pendingEdges;

      }

      anyChange |= analyseBlock(i, true, true, i == L->headerIdx, L);

    }

    if(!LBB)
      LBB = getBB(L->latchIdx);

    everChanged |= anyChange;

    firstIter = false;

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after block analysis: " << PHBB->localStore->refCount << "\n");

  }

  if(edgeIsDead(getBBInvar(L->latchIdx), HBB->invar))
    release_assert(iters == 1 && "Loop analysis found the latch dead but not first time around?");

  // Release the preheader store that was held for merging in each iteration:
  PHBB->derefStores();

  // If this is a nested loop, hang onto the reference given from latch to header
  // for use in the next iteration of analysing this loop.
  bool thisLatchAlive = LBB && !edgeIsDead(LBB->invar, HBB->invar);
  if(!nestedLoop) {
    
    releaseLatchStores(L);
    if(thisLatchAlive)
      LBB->derefStores();

  }
  else {

    if(thisLatchAlive)
      pass->latchStoresRetained.insert(std::make_pair(this, L));

  }

  // Similarly the latch block will have given the header a reference towards determining successor block certainty. Drop it.
  if(thisLatchAlive)
    --pendingEdges;

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at exit: " << PHBB->localStore->refCount << "\n");
  
  return everChanged;

}

// Run this function instance through the 'interpreter' without changing findings about any of the instructions etc.
// Used when a function instance is being shared as we have detected that all relevant state matches a previously-
// analysed version.
void InlineAttempt::executeCall(uint32_t parent_stack_depth) {

  uint32_t new_stack_depth = (invarInfo->frameSize == -1) ? parent_stack_depth : parent_stack_depth + 1;
  execute(new_stack_depth);

}

// Similarly, execute but do not re-analyse a loop.
void IntegrationAttempt::executeLoop(const ShadowLoopInvar* ThisL) {

  ShadowBB* PHBB = getBB(ThisL->preheaderIdx);
  ShadowBB* HBB = getBB(ThisL->headerIdx); 

  // If this context had a retained latch store from previous instances
  // we don't need it anymore, drop now.
  if(pass->latchStoresRetained.erase(std::make_pair(this, ThisL))) {

    ShadowBB* LBB = getBB(ThisL->latchIdx);
    release_assert(LBB && "Executed loop with retained latch, but not available?");
    LBB->derefStores();

  }

  // No need for extra references: we simply execute the residual loop once
  // as fixpoints have already been established about what is stored.
  // We only need special treatment to prevent header blocks from trying to
  // consume a store from their latch blocks.
  HBB->localStore = PHBB->localStore;

  for(uint32_t i = ThisL->headerIdx; i < (BBsOffset + nBBs); ++i) {

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

      if(i != ThisL->headerIdx) {
	if(!doBlockStoreMerge(BB))
	  return;
      }
      
      executeBlock(BB);

    }

  }

  // Drop extra ref given to the header block if one was granted.
  ShadowBB* LBB = getBB(ThisL->latchIdx);
  if(LBB && !edgeIsDead(LBB->invar, HBB->invar))
    LBB->derefStores();

}

// Similar to above.
// Like analyse(), but used from sharing pathways when we're sure none of the functions need re-evaluating.
// We really only want to recreate its effects on the store.
void IntegrationAttempt::execute(uint32_t new_stack_depth) {

  stack_depth = new_stack_depth;

  getInitialStore(false);
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

    // All fence logic is implemented in the tentative loads passlet; nothing to do here.
    case Instruction::Fence:
      break;

    case Instruction::Call:
      {

	if(Function* F = getCalledFunction(SI)) {
	  if(canConstantFoldCallTo(cast_inst<CallInst>(SI), F))
	    break;
	}

	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  IA->activeCaller = SI;
	  IA->executeCall(stack_depth);
	  doCallStoreMerge(SI);
	  if(!SI->parent->localStore)
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
    BB->refStores();
	
  }

  // Drop ref belonging to this block.
  BB->derefStores();

}
