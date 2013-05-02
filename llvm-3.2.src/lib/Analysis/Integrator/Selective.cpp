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

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

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

  if(!parent)
    return true;
  else
    return parent->inlineIsEnabled(cast<CallInst>(CI->invar->I));

}

bool PeelIteration::isEnabled() {

  return parentPA->isEnabled();

}

bool PeelAttempt::isEnabled() {

  return parent->loopIsEnabled(L);

}

void InlineAttempt::setEnabled(bool en) {

  if(!parent)
    return;

  if(en)
    parent->enableInline(cast<CallInst>(CI->invar->I));
  else
    parent->disableInline(cast<CallInst>(CI->invar->I));

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

bool IntegrationAttempt::isVararg() {

  return (!L) && F.isVarArg();

}

bool IntegrationAttempt::isAvailable() {

  // Not enabled?
  if(!isEnabled())
    return false;

  // Not getting inlined/unrolled at all?
  if(parent && !parent->isAvailable())
    return false;

  return true;

}

bool IntegrationAttempt::isAvailableFromCtx(IntegrationAttempt* OtherIA) {

  if(!isAvailable())
    return false;

  // Values not directly available due to intervening varargs?
  // Walk ourselves and the other down til we hit a varargs barrier.
  IntegrationAttempt* AvailCtx1 = this;
  while(AvailCtx1 && !AvailCtx1->isVararg())
    AvailCtx1 = AvailCtx1->parent;

  IntegrationAttempt* AvailCtx2 = OtherIA;
  while(AvailCtx2 && !AvailCtx2->isVararg())
    AvailCtx2 = AvailCtx2->parent;

  // If we hit different barriers we'll end up integrated into different functions.
  if(AvailCtx1 != AvailCtx2)
    return false;

  return true;

}

