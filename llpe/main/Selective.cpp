//===- Selective.cpp ------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// Functions which enable / disable inlining or peeling of particular sub-elements of the program
// and which queue reconsideration of parts whose results will have changed.

#include "llvm/Analysis/LLPE.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

void InlineAttempt::resetDeadArgsAndInstructions() {

  for(uint32_t i = 0; i < F.arg_size(); ++i)
    argShadows[i].dieStatus = INSTSTATUS_ALIVE;

  resetDeadInstructions();

}

void IntegrationAttempt::resetDeadInstructions() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);
      I->dieStatus = INSTSTATUS_ALIVE;

    }

  }

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {

    it->second->resetDeadArgsAndInstructions();

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i) {

      it->second->Iterations[i]->resetDeadInstructions();

    }

  }

}

void LLPEAnalysisPass::runDSEAndDIE() {

  errs() << "Killing memory instructions";
  RootIA->tryKillStores(false, false);

  DEBUG(dbgs() << "Finding dead VFS operations\n");
  RootIA->tryKillAllVFSOps();

  DEBUG(dbgs() << "Finding remaining dead instructions\n");
  
  errs() << "\nKilling other instructions";
  
  RootIA->runDIE();
  
  errs() << "\n";

}

void LLPEAnalysisPass::rerunDSEAndDIE() {

  if(mustRecomputeDIE) {
    RootIA->resetDeadArgsAndInstructions();
    runDSEAndDIE();
    mustRecomputeDIE = false;
  }

}

bool InlineAttempt::isEnabled() {

  if(!Callers.size())
    return true;
  else if(isPathCondition)
    return false;
  else
    return isShared() || enabled;

}

bool PeelIteration::isEnabled() {

  return true;

}

bool PeelAttempt::isEnabled() {

  return enabled;

}

void InlineAttempt::setEnabled(bool en, bool skipStats) {

  if(!Callers.size())
    return;

  if(isShared())
    return;

  if(isPathCondition)
    return;

  if(enabled != en)
    pass->mustRecomputeDIE = true;    

  enabled = en;

  if(!skipStats)
    pass->getRoot()->collectStats();

}

void PeelIteration::setEnabled(bool en, bool skipStats) {

  assert(0 && "Can't individually disable iterations yet");

}

void PeelAttempt::setEnabled(bool en, bool skipStats) {

  if(en != enabled)
    pass->mustRecomputeDIE = true;

  enabled = en;

}

bool InlineAttempt::commitsOutOfLine() {

  if(isRootMainCall())
    return true;

  for(SmallVector<ShadowInstruction*, 1>::iterator it = Callers.begin(),
	itend = Callers.end(); it != itend; ++it) {

    // If this function has null CommitF and a parent has one, this implies
    // that this context was committed before our parent acquired its commit function,
    // and since we hadn't claimed one of our own we inherited it implicitly.

    if(CommitF && (*it)->parent->IA->getFunctionRoot()->CommitF != CommitF)
      return true;

  }

  return false;

}

bool PeelIteration::commitsOutOfLine() {

  return false;

}

// Return true if this function will be committed as a residual function
// rather than being inlined everywhere as usual.
bool InlineAttempt::mustCommitOutOfLine() {

  if(isRootMainCall())
    return true;

  if(F.isVarArg())
    return true;

  if(isShared())
    return true;

  if(pass->splitFunctions.count(&F))
    return true;
  
  if(hasFailedReturnPath()) {

    for(uint32_t i = 0, ilim = Callers.size(); i != ilim; ++i) {
      
      if(inst_is<InvokeInst>(Callers[i]))
	return true;
	
    }

  }

  return false;

}

bool PeelIteration::mustCommitOutOfLine() {

  return false;

}

bool IntegrationAttempt::allAncestorsEnabled() {

  // Not enabled?
  if(!isEnabled())
    return false;
  
  // Not getting inlined/unrolled at all?
  // Note on use of getUniqueParent: this function is only used to determine whether a user can refer
  // to a heap object allocated in a given context. Contexts from which allocations may escape are
  // unsharable, so if getUniqueParent fails that means we're a shared function, the allocation does
  // not escape from this context, and therefore the user context is equal to or a child of this one.
  // Thus it's safe to return true in this case: either we're both committed and the use is ok,
  // or we're both not committed and it doesn't make any difference.

  IntegrationAttempt* parent = getUniqueParent();

  if(parent && !parent->allAncestorsEnabled())
    return false;

  return true;

}
