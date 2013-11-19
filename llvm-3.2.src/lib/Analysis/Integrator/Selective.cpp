// Functions which enable / disable inlining or peeling of particular sub-elements of the program
// and which queue reconsideration of parts whose results will have changed.

#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Instructions.h"

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

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->resetDeadArgsAndInstructions();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i) {

      it->second->Iterations[i]->resetDeadInstructions();

    }

  }

}

void IntegrationHeuristicsPass::rerunDSEAndDIE() {

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

    if((*it)->parent->IA->getFunctionRoot()->CommitF != CommitF)
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

  return isRootMainCall() || F.isVarArg() || isShared();

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
