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
    argShadows[i].i.dieStatus = INSTSTATUS_ALIVE;

  resetDeadInstructions();

}

void IntegrationAttempt::resetDeadInstructions() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);
      I->i.dieStatus = INSTSTATUS_ALIVE;

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

void IntegrationAttempt::enableInline(CallInst* CI) {

  pass->mustRecomputeDIE = true;
  ignoreIAs.erase(CI);

}

void IntegrationAttempt::disableInline(CallInst* CI) {

  pass->mustRecomputeDIE = true;
  ignoreIAs.insert(CI);

}

void IntegrationAttempt::enablePeel(const Loop* L) {

  pass->mustRecomputeDIE = true;
  ignorePAs.erase(L);

}

void IntegrationAttempt::disablePeel(const Loop* L) {

  pass->mustRecomputeDIE = true;
  ignorePAs.insert(L);

}

bool IntegrationAttempt::loopIsEnabled(const Loop* L) {

  return !ignorePAs.count(L);

}

bool IntegrationAttempt::inlineIsEnabled(CallInst* CI) {

  return !ignoreIAs.count(CI);

}

bool InlineAttempt::isEnabled() {

  if(!Callers.size())
    return true;
  else if(isPathCondition)
    return false;
  else
    return isShared() || getUniqueParent()->inlineIsEnabled(cast<CallInst>(Callers[0]->invar->I));

}

bool PeelIteration::isEnabled() {

  return parentPA->isEnabled();

}

bool PeelAttempt::isEnabled() {

  return parent->loopIsEnabled(L);

}

void InlineAttempt::setEnabled(bool en) {

  if(!Callers.size())
    return;

  if(isShared())
    return;

  if(isPathCondition)
    return;

  IntegrationAttempt* Parent = Callers[0]->parent->IA;

  if(en)
    Parent->enableInline(cast<CallInst>(Callers[0]->invar->I));
  else
    Parent->disableInline(cast<CallInst>(Callers[0]->invar->I));

  pass->getRoot()->collectStats();

}

void PeelIteration::setEnabled(bool en) {

  assert(0 && "Can't individually disable iterations yet");

}

void PeelAttempt::setEnabled(bool en) {

  if(en)
    parent->enablePeel(L);
  else
    parent->disablePeel(L);

}

// Return true if this function will be committed as a residual function
// rather than being inlined everywhere as usual.
bool InlineAttempt::commitsOutOfLine() {

  return isRootMainCall() || F.isVarArg() || isShared();

}

bool PeelIteration::commitsOutOfLine() {

  return false;

}

bool IntegrationAttempt::unsharedContextAvailable() {

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

  if(parent && !parent->unsharedContextAvailable())
    return false;

  return true;

}

// OtherIA must be a child without an intervening out-of-line commit point
bool IntegrationAttempt::allocasAvailableFrom(IntegrationAttempt* OtherIA) {

  while(OtherIA && OtherIA != this) {

    if(!OtherIA->isEnabled())
      return false;
    if(OtherIA->commitsOutOfLine())
      return false;
    OtherIA = OtherIA->getUniqueParent();

  }

  return !!OtherIA;

}

// Return true if an object allocated here will be accessible from OtherIA.
// This context may or may not be shared, but due to the definition of isUnsharable,
// if it is then the allocation does not escape this context and we must be equal to
// or a parent of OtherIA.
bool IntegrationAttempt::heapObjectsAvailableFrom(IntegrationAttempt* OtherIA) {

  if(!unsharedContextAvailable())
    return false;

  // Walk down to the nearest function boundary. Note that if OtherIA is shared, directly or otherwise,
  // we don't care which version we're talking about because allocations cannot cross shared
  // function boundaries. If they become able to do so then we need a context-sensitive test here.

  IntegrationAttempt* AvailCtx1 = this;
  while(AvailCtx1 && !AvailCtx1->commitsOutOfLine())
    AvailCtx1 = AvailCtx1->getUniqueParent();

  IntegrationAttempt* AvailCtx2 = OtherIA;
  while(AvailCtx2 && !AvailCtx2->commitsOutOfLine())
    AvailCtx2 = AvailCtx2->getUniqueParent();

  // If we hit different barriers we'll end up integrated into different functions.
  if(AvailCtx1 != AvailCtx2)
    return false;

  return true;

}

