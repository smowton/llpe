
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Function.h"
#include "llvm/Analysis/LoopInfo.h"

using namespace llvm;

// Where a pointer is used in a context that will be committed to a different function,
// create a global that will store the pointer.

void IntegrationAttempt::findNonLocalPointers() {

  PointerType* VoidPtr = cast<PointerType>(Type::getInt8PtrTy(F.getContext()));
  PointerType* Int32 = cast<PointerType>(Type::getInt32Ty(F.getContext()));
  
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

      ShadowInstruction& SI = BB->insts[j];
      if(SI.dieStatus != INSTSTATUS_ALIVE)
	continue;

      ShadowValue Base;
      ImprovedValSetSingle* IVS;
      if(getBaseObject(ShadowValue(&SI), Base)) {

	if(Base.isInst() && Base.objectAvailable() && Base.u.I->parent->IA->getFunctionRoot()->CommitF != getFunctionRoot()->CommitF) {

	  // Base has a nonlocal user.
	  if(!pass->globalisedAllocations.count(Base.u.I)) {

	    GlobalVariable* NewGV = new GlobalVariable(*(F.getParent()), VoidPtr, false, GlobalValue::InternalLinkage, UndefValue::get(VoidPtr), "specglobalptr");
	    pass->globalisedAllocations[Base.u.I] = NewGV;
	    errs() << "Global created for " << itcache(Base) << " because of user " << itcache(ShadowValue(&SI)) << "\n";

	  }

	}
	else if(Base.isArg() && pass->RootIA->CommitF != getFunctionRoot()->CommitF) {

	  if(!pass->argStores[Base.u.A->invar->A->getArgNo()].fwdGV) {

	    GlobalVariable* NewGV = new GlobalVariable(*(F.getParent()), VoidPtr, false, GlobalValue::InternalLinkage, UndefValue::get(VoidPtr), "specglobalptr");
	    pass->argStores[Base.u.A->invar->A->getArgNo()].fwdGV = NewGV;

	  }

	}

      }
      else if((IVS = dyn_cast_or_null<ImprovedValSetSingle>(SI.i.PB)) && 
	      IVS->SetType == ValSetTypeFD &&
	      IVS->Values.size() == 1) {

	ShadowInstruction* FDI = IVS->Values[0].V.u.I;

	if(FDI->parent->IA->getFunctionRoot()->CommitF != getFunctionRoot()->CommitF) {

	  if(!pass->globalisedFDs.count(FDI)) {

	    GlobalVariable* NewGV = new GlobalVariable(*(F.getParent()), Int32, false, GlobalVariable::InternalLinkage, UndefValue::get(Int32), "specglobalfd");
	    pass->globalisedFDs[FDI] = NewGV;
	    
	  }

	}

      }

    }
    
  }
  
  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if((!it->second->isEnabled()) || !it->second->isTerminated())
      continue;
    
    for(std::vector<PeelIteration*>::iterator iterit = it->second->Iterations.begin(),
	  iteritend = it->second->Iterations.end(); iterit != iteritend; ++iterit)
      (*iterit)->findNonLocalPointers();
    
  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->findNonLocalPointers();

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

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->inheritCommitFunction();

  }

}

void InlineAttempt::inheritCommitFunction() {

  if(!CommitF)
    CommitF = Callers[0]->parent->IA->getFunctionRoot()->CommitF;
  IntegrationAttempt::inheritCommitFunction();

}

// Try to split a specialised program up into chunks of around 10,000 instructions.
// That's large enough that the inliner won't be appetised to reverse our work, and also will hopefully
// not hinder optimisation too much.

uint64_t IntegrationAttempt::findSaveSplits() {

  uint64_t residualInstructionsHere = 0;

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

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    residualInstructionsHere += it->second->findSaveSplits();

  }

  return residualInstructionsHere;

}

void InlineAttempt::splitCommitHere() {

  // Only split shared functions once.
  if(CommitF)
    return;
  
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
  
}

#define SPLIT_THRESHOLD 50000

uint64_t InlineAttempt::findSaveSplits() {

  uint64_t residuals = IntegrationAttempt::findSaveSplits();

  if(mustCommitOutOfLine() || residuals > SPLIT_THRESHOLD) {
    splitCommitHere();
    return 1;
  }
  else {
    // Will inherit CommitF from parent (in next phase).
    return residuals;
  }
    
}

void IntegrationHeuristicsPass::saveSplitPhase() {

  RootIA->findSaveSplits();
  RootIA->inheritCommitFunction();
  RootIA->findNonLocalPointers();
  
}
