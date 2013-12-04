
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Function.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/InstructionSimplify.h"

using namespace llvm;

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
    if(Value* V = SimplifyInstruction(I)) {
      I->replaceAllUsesWith(V);
      I->eraseFromParent();
    }

  }

  Refs.clear();

}

static Instruction* getInsertLocation(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {

    BasicBlock::iterator BI(I);
    ++BI;
    release_assert(BI != I->getParent()->end());
    return BI;

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {
    
    release_assert(A->getParent() && A->getParent()->getEntryBlock().size());
    return A->getParent()->getEntryBlock().begin();

  }
  else {

    release_assert(0 && "Bad value type in getInsertLocation");
    llvm_unreachable();

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
    llvm_unreachable();

  }

}

void llvm::forwardReferences(Value* Fwd, Module* M) {

  GlobalVariable* NewGV = 0;

  SmallVector<std::pair<Use*, Instruction*>, 4> replaceUses;

  for(Instruction::use_iterator UI = Fwd->use_begin(),
	UE = Fwd->use_end(); UI != UE; ++UI) {

    Use* U = &UI.getUse();
    Value* V = *UI;

    if(Instruction* UserI = dyn_cast<Instruction>(V)) {

      if(UserI->getParent()->getParent() != getFunctionFor(Fwd)) {

	// This user is non-local: replace it. Use aux list because Use::set invalidates a use_iterator.

	if(!NewGV) {

	  // Create a global and a store at the definition site.
	  NewGV = new GlobalVariable(*M, Fwd->getType(), false, GlobalVariable::InternalLinkage, 
				     UndefValue::get(Fwd->getType()), "specglobalfwd");
	  Instruction* InsertLoc = getInsertLocation(Fwd);
	  new StoreInst(Fwd, NewGV, InsertLoc);

	}

	// Create a load before the user. TODO: fix this for phis.
	Instruction* Fwd = new LoadInst(NewGV, "", UserI);
	replaceUses.push_back(std::make_pair(U, Fwd));

      }

    }

  }

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
    
    patchReferences(it->PatchRefs, it->committedVal);
    forwardReferences(it->committedVal, F.getParent());

  }

}

void IntegrationHeuristicsPass::fixNonLocalUses() {

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

void IntegrationAttempt::inheritCommitFunction() {

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
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

void InlineAttempt::inheritCommitFunctionCall(bool onlyAdd) {

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

uint64_t IntegrationAttempt::findSaveSplits() {

  if(isCommitted())
    return residualInstructionsHere;
  
  residualInstructionsHere = 0;

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {
    
    ShadowBBInvar* BBI = getBBInvar(i);
    if(BBI->naturalScope != L && ((!L) || L->contains(BBI->naturalScope))) {

      DenseMap<const Loop*, PeelAttempt*>::iterator findit = 
	peelChildren.find(immediateChildLoop(L, BBI->naturalScope));

      if(findit != peelChildren.end() && findit->second->isTerminated() && findit->second->isEnabled()) {

	while(i != ilim && getBBInvar(i)->naturalScope && getBBInvar(i)->naturalScope->contains(BBI->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }

    ShadowBB* BB = getBB(*BBI);
    if(!BB)
      continue;

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      if(!willBeReplacedWithConstantOrDeleted(ShadowValue(&BB->insts[j])))
	++residualInstructionsHere;

    }
    
  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
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

void IntegrationAttempt::addPatchRequest(ShadowValue Needed, Instruction* PatchI, uint32_t PatchOp) {

  std::pair<WeakVH, uint32_t> PRQ(WeakVH(PatchI), PatchOp);

  switch(Needed.t) {

  case SHADOWVAL_ARG: {
    release_assert(Needed.u.A->IA->isRootMainCall());
    ArgStore& AS = GlobalIHP->argStores[Needed.u.A->invar->A->getArgNo()];
    AS.PatchRefs.push_back(PRQ);
    break;
  }

  case SHADOWVAL_PTRIDX: {
    AllocData& AD = *getAllocData(Needed);
    AD.PatchRefs.push_back(PRQ);
    release_assert(!AD.committedVal);
    break;
  }

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

void InlineAttempt::splitCommitHere() {

  residualInstructionsHere = 1;
  
  std::string Name;
  {
    raw_string_ostream RSO(Name);
    RSO << getCommittedBlockPrefix() << "clone";
  }

  GlobalValue::LinkageTypes LT;
  if(isRootMainCall())
    LT = F.getLinkage();
  else
    LT = GlobalValue::InternalLinkage;
  
  CommitF = cloneEmptyFunction(&F, LT, Name, hasFailedReturnPath() && !isRootMainCall());

  Function::BasicBlockListType& BBL = CommitF->getBasicBlockList();
  
  for(std::vector<BasicBlock*>::iterator it = CommitBlocks.begin(), 
	itend = CommitBlocks.end(); it != itend; ++it) {

    BBL.push_back(*it);

  }

  CommitBlocks.clear();
  CommitFunctions.push_back(CommitF);

  residualInstructionsHere = 1;

  inheritCommitFunction();

}

#define SPLIT_THRESHOLD 50000

uint64_t InlineAttempt::findSaveSplits() {

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
