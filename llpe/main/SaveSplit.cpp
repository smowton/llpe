//===- SaveSplit.cpp ------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/InstructionSimplify.h"

using namespace llvm;

// Code in this file determines how to split committed code into residual functions. We don't want to just
// inline everything everywhere, since this makes a huge function that chokes the LLVM optimisation/analysis
// passes, nor do we want to simply emit a residual function per specialised context since this leaves
// a lot of call overhead and chokes the standard inliner.

// Replace the instruction-operands listed in Refs with V. This is used when a source argument wasn't
// available during a context's commit phase, so either an argument was left 'undef' (e.g. a phi node operand)
// or a 'select' instruction was created as a temporary and one of its arguments queued for patching.
// SimplifyInstruction is used to resolve cases where the target instruction is no longer necessary
// once its argument is known.
void llvm::patchReferences(std::vector<std::pair<WeakVH, uint32_t> >& Refs, Value* V) {

  for(std::vector<std::pair<WeakVH, uint32_t> >::iterator it = Refs.begin(),
	itend = Refs.end(); it != itend; ++it) {

    // Value must have gone away due to e.g. discarding a previously committed function.
    if(!it->first)
      continue;

    release_assert(isa<SelectInst>(it->first));

    Instruction* I = cast<Instruction>(it->first);

    I->setOperand(it->second, V);
    // Note this would be unsafe if any of the patch recipients were listed more than
    // once in patch lists.
    if(Value* V = SimplifyInstruction(I, *GlobalTD)) {
      I->replaceAllUsesWith(V);
      I->eraseFromParent();
    }

  }

  Refs.clear();

}

// If we want to introduce an instruction right after V becomes defined, return the Instruction
// we should insert before.
static Instruction* getInsertLocation(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {

    BasicBlock::iterator BI(I);
    ++BI;
    release_assert(BI != I->getParent()->end());
    return &*BI;

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {
    
    release_assert(A->getParent() && A->getParent()->getEntryBlock().size());
    return &*(A->getParent()->getEntryBlock().begin());

  }
  else {

    release_assert(0 && "Bad value type in getInsertLocation");
    llvm_unreachable("Bad value type in getInsertLocation");

  }

}

static Function* getFunctionFor(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {

    return I->getParent()->getParent();

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {
    
    return A->getParent();

  }
  else {

    release_assert(0 && "Bad value type in getFunctionFor");
    llvm_unreachable("Bad value type in getInsertLocation");

  }

}

// Value Fwd might have users that aren't function-local. This happens because
// e.g. a malloc instruction ended up committed in a different function than residual
// users that refer to that allocation.
// With some cunning trickery we could get the value forwarded by function return values
// and arguments; here we use the simpler solution of storing Fwd to a global as it is created and then
// loading it at each non-local user.
// The disadvantage is this might confuse downstream alias analysis a little.
void llvm::forwardReferences(Value* Fwd, Module* M) {

  GlobalVariable* NewGV = 0;

  SmallVector<std::pair<Use*, Instruction*>, 4> replaceUses;

  for(Instruction::user_iterator UI = Fwd->user_begin(),
	UE = Fwd->user_end(); UI != UE; ++UI) {

    Use* U = &UI.getUse();
    Value* V = *UI;

    if(Instruction* UserI = dyn_cast<Instruction>(V)) {

      if(UserI->getParent()->getParent() != getFunctionFor(Fwd)) {

	// This user is non-local: replace it. Use aux list because Use::set invalidates a user_iterator.

	if(!NewGV) {

	  // Create a global and a store at the definition site.
	  NewGV = new GlobalVariable(*M, Fwd->getType(), false, GlobalVariable::InternalLinkage, 
				     UndefValue::get(Fwd->getType()), "specglobalfwd");
	  Instruction* InsertLoc = getInsertLocation(Fwd);
	  new StoreInst(Fwd, NewGV, InsertLoc);

	}

	Instruction* InsertBefore;
	if(PHINode* PN = dyn_cast<PHINode>(UserI)) {

	  // The load needs to go at the end of the predecessor block, since it can't go right before a phi.
	  // Find the particular predecessor corresponding to this use:
	  int32_t phiOpIdx = -1;
	  
	  for(uint32_t i = 0, ilim = PN->getNumIncomingValues(); i != ilim && phiOpIdx == -1; ++i)
	    if((&PN->getOperandUse(PN->getOperandNumForIncomingValue(i))) == U)
	      phiOpIdx = i;

	  release_assert(phiOpIdx != -1 && "No PHI corresponding Use?");
	  InsertBefore = PN->getIncomingBlock(phiOpIdx)->getTerminator();

	}
	else {

	  // The load goes right before the user instruction.
	  InsertBefore = UserI;

	}

	Instruction* Fwd = new LoadInst(NewGV, "", InsertBefore);
	replaceUses.push_back(std::make_pair(U, Fwd));

      }

    }

  }

  // Do the actual replacements now we don't need the user_iterator.
  for(SmallVector<std::pair<Use*, Instruction*>, 4>::iterator it = replaceUses.begin(),
	itend = replaceUses.end(); it != itend; ++it) {

    it->first->set(it->second);

  }

}

void InlineAttempt::fixNonLocalStackUses() {

  // This context has been committed: patch any instruction that is "owed" a pointer
  // to a stack allocation, and if any user is in a different function insert a forwarding
  // global variable. This is valid even if neither of us has been given a target functionm
  // yet, as we will inevitably end up colocated.

  for(std::vector<AllocData>::iterator it = localAllocas.begin(),
	itend = localAllocas.end(); it != itend; ++it) {

    // Replace any placeholder select instructions so that def->use relationships are all present.
    patchReferences(it->PatchRefs, it->committedVal);
    // Forward nonlocal def->use edges via a global variable.
    forwardReferences(it->committedVal, F.getParent());

  }

}

void LLPEAnalysisPass::fixNonLocalUses() {

  // Similar to the above, but also take care of FDs which are always global.

  for(std::vector<AllocData>::iterator it = heap.begin(),
	itend = heap.end(); it != itend; ++it) {

    if(!it->allocValue.isInst())
      continue;

    if(!it->committedVal) {

      errs() << "Warning: heap allocation " << it->allocIdx << " not committed\n";
      continue;

    }

    patchReferences(it->PatchRefs, it->committedVal);
    forwardReferences(it->committedVal, getGlobalModule());

  }

  for(std::vector<FDGlobalState>::iterator it = fds.begin(),
	itend = fds.end(); it != itend; ++it) {

    if(!it->CommittedVal) {

      if(it->SI)
	errs() << "Warning: some FD not committed\n";

      continue;

    }

    patchReferences(it->PatchRefs, it->CommittedVal);
    forwardReferences(it->CommittedVal, getGlobalModule());

  }
  
}

// Set all child functions to use the same commit function as this context.
void IntegrationAttempt::inheritCommitFunction() {

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
        itend = peelChildren.end(); it != itend; ++it) {

    if((!it->second->isEnabled()) || !it->second->isTerminated())
      continue;

    for(std::vector<PeelIteration*>::iterator iterit = it->second->Iterations.begin(),
	  iteritend = it->second->Iterations.end(); iterit != iteritend; ++iterit)
      (*iterit)->inheritCommitFunction();
    
  }

  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->inheritCommitFunctionCall(false);

  }

}

// Set all child functions to use the same commit function as this context. onlyAdd is always false at the moment.
void InlineAttempt::inheritCommitFunctionCall(bool onlyAdd) {

  // In this case our commit function is already set in stone.
  if(isCommitted())
    return;

  if(!onlyAdd) {
    
    if(CommitF)
      return;
    CommitF = uniqueParent->getFunctionRoot()->CommitF;

  }

  inheritCommitFunction();

}

// Try to split a specialised program up into chunks of around 10,000 instructions.
// That's large enough that the inliner won't be appetised to reverse our work, and also will hopefully
// not hinder optimisation too much.

// Return a rough estimate of the number of residual instructions that will result from this context
// and its children. Notionally this could split the residual code other than at source program
// function boundaries, hence the name, but in practice at present splits always align with source program
// functions, for which see InlineAttempt::findSaveSplits.
uint64_t IntegrationAttempt::findSaveSplits() {

  // Already committed here -- we already know the actual number of residual instructions.
  // This may have been set to 1 if this context is to be the root of a residual function, so
  // only one call instruction will materialise from our parent's point of view.
  if(isCommitted())
    return residualInstructionsHere;
  
  residualInstructionsHere = 0;

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {
    
    ShadowBBInvar* BBI = getBBInvar(i);
    if(BBI->naturalScope != L && ((!L) || L->contains(BBI->naturalScope))) {

      // Skip over this child loop if it will be peeled in the committed program;
      // in this case we will gather its stats below.
      
      DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator findit = 
	peelChildren.find(immediateChildLoop(L, BBI->naturalScope));

      if(findit != peelChildren.end() && findit->second->isTerminated() && findit->second->isEnabled()) {

	while(i != ilim && getBBInvar(i)->naturalScope && getBBInvar(i)->naturalScope->contains(BBI->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }

    // Count likely residual instructions from each block. Note this is a rough
    // estimate as unspecialised code will not be included.
    
    ShadowBB* BB = getBB(*BBI);
    if(!BB)
      continue;

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      if(!willBeReplacedWithConstantOrDeleted(ShadowValue(&BB->insts[j])))
	++residualInstructionsHere;

    }
    
  }

  // Count residual instructions belonging to our child contexts.

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if((!it->second->isEnabled()) || !it->second->isTerminated())
      continue;

    for(std::vector<PeelIteration*>::iterator iterit = it->second->Iterations.begin(),
	  iteritend = it->second->Iterations.end(); iterit != iteritend; ++iterit)
      residualInstructionsHere += (*iterit)->findSaveSplits();

  }

  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    residualInstructionsHere += it->second->findSaveSplits();

  }

  return residualInstructionsHere;

}

// Queue PatchI's operand PatchOp to be written with the committed version of Needed when it is
// eventually synthesised.
void IntegrationAttempt::addPatchRequest(ShadowValue Needed, Instruction* PatchI, uint32_t PatchOp) {

  std::pair<WeakVH, uint32_t> PRQ(WeakVH(PatchI), PatchOp);

  switch(Needed.t) {

    // Forwarding a root-function argument, which can be considered a globally-unique object.
  case SHADOWVAL_ARG: {
    release_assert(Needed.u.A->IA->isRootMainCall());
    ArgStore& AS = GlobalIHP->argStores[Needed.u.A->invar->A->getArgNo()];
    AS.PatchRefs.push_back(PRQ);
    break;
  }

    // Forwarding an allocation that occurs during specialisation e.g. an alloca or malloc.
  case SHADOWVAL_PTRIDX: {
    AllocData& AD = *getAllocData(Needed);
    AD.PatchRefs.push_back(PRQ);
    release_assert(!AD.committedVal);
    break;
  }

    // Forwarding a file descriptor allocated during specialisation.
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64: {
    FDGlobalState& FDS = pass->fds[Needed.getFd()];
    FDS.PatchRefs.push_back(PRQ);
    break;
  }

  default:

    release_assert(0 && "Bad type for patch request");

  }

}

// Create a fresh residual function to contain residual blocks from this context and any child contexts
// that haven't already been assigned a commit function.
void InlineAttempt::splitCommitHere() {

  // Since we're committing out-of-line, we will only add a single instruction to our parent's residual function.
  residualInstructionsHere = 1;
  
  std::string Name;
  {
    raw_string_ostream RSO(Name);
    RSO << getCommittedBlockPrefix() << "clone";
  }

  // Create an empty function; inherit attributes etc from the source program function.
  GlobalValue::LinkageTypes LT;
  if(isRootMainCall())
    LT = F.getLinkage();
  else
    LT = GlobalValue::InternalLinkage;
  
  CommitF = cloneEmptyFunction(&F, LT, Name, hasFailedReturnPath() && !isRootMainCall());
  firstFailedBlock = CommitF->end();

  Function::BasicBlockListType& BBL = CommitF->getBasicBlockList();

  // Add any already-committed blocks to the new function.
  for(std::vector<BasicBlock*>::iterator it = CommitBlocks.begin(), 
	itend = CommitBlocks.end(); it != itend; ++it) {

    BBL.push_back(*it);

  }

  for(std::vector<BasicBlock*>::iterator it = CommitFailedBlocks.begin(),
	itend = CommitFailedBlocks.end(); it != itend; ++it) {

    BBL.push_back(*it);

    if(it == CommitFailedBlocks.begin())
      firstFailedBlock = Function::iterator(BBL.back());

  }

  CommitBlocks.clear();
  CommitFailedBlocks.clear();
  CommitFunctions.push_back(CommitF);

  residualInstructionsHere = 1;

  // Assign any children that haven't committed yet
  // to target the new residual function too.
  inheritCommitFunction();

}

#define SPLIT_THRESHOLD 50000

// Similarly to IntegrationAttempt::findSaveSplits above, return the number of instructions this context
// and its children will emit in our parent's commit function. If that number would be excessive,
// split this context and its children off into a new commit function and note that we now only
// show up as a single call instruction to our parent.
uint64_t InlineAttempt::findSaveSplits() {
  
  if(isCommitted())
    return residualInstructionsHere;
  
  uint64_t residuals;

  if(mustCommitOutOfLine() || (residuals = IntegrationAttempt::findSaveSplits()) > SPLIT_THRESHOLD) {
    splitCommitHere();
    return 1;
  }
  else {
    // Will inherit CommitF from parent (in next phase).
    return residuals;
  }
    
}
