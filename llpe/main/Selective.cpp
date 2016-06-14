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

// Will this specialsiation context be committed (return true), or just used to inform others (false)?
bool InlineAttempt::isEnabled() {

  if(!Callers.size()) // Root function: always committed.
    return true;
  else if(isPathCondition) // Path condition functions are symbolic and don't result in runtime code.
    return false;
  else
    return isShared() || enabled;

}

// Loop iterations are always committed if their parent loop is.
bool PeelIteration::isEnabled() {

  return true;

}

bool PeelAttempt::isEnabled() {

  return enabled;

}

// Try to set enabled (will-commit) status to 'en'.
void InlineAttempt::setEnabled(bool en, bool skipStats) {

  // Root function can't be disabled.
  if(!Callers.size())
    return;

  // Shared functions can't currently be disabled.
  if(isShared())
    return;

  // Path conditions are never committed anyhow
  if(isPathCondition)
    return;

  enabled = en;

  if(!skipStats)
    pass->getRoot()->collectStats();

}

void PeelIteration::setEnabled(bool en, bool skipStats) {

  assert(0 && "Can't individually disable iterations yet");

}

void PeelAttempt::setEnabled(bool en, bool skipStats) {

  enabled = en;

}

// Will this specialisation context be committed in a different residual function
// to its parent?
bool InlineAttempt::commitsOutOfLine() {

  // In this case we don't have a parent at all.
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

// Loop iterations currently always commit in the same function as their immediate parent.
bool PeelIteration::commitsOutOfLine() {

  return false;

}

// Return true if this function must be committed as a residual function
// rather than being inlined everywhere as usual.
// Note it might also commit out-of-line to keep committed function sizes amenable to conventional optimisation
// even though it could potentially commit inline-- SaveSplit.cpp takes care of this decision.
bool InlineAttempt::mustCommitOutOfLine() {

  // Root function naturally needs its own residual function.
  if(isRootMainCall())
    return true;

  // Vararg functions: we currently don't rewrite vararg intrinsics, and the Dragonegg vararg handling
  // directly exposes the implementation which we can't alter, so we must make sure the va_list exists for real.
  if(F.isVarArg())
    return true;

  // Shared functions need to be out-of-line so we can have multiple callers.
  // Note this functionality is probably rotted.
  if(isShared())
    return true;

  // Has the user manually nominated this as a split-point?
  if(pass->splitFunctions.count(&F))
    return true;

  // Unsure why this is required. Perhaps the needed logic
  // to add the bailed-to-unspecialised-code-during-execution flag
  // and then add a test post-invoke is missing right now?
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
