//===-- FunctionSharing.cpp -----------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseMap.h"

// The function sharing code should permit identical invocations of a particular function to share analysis results.
// However the feature hasn't been tested in some time and is almost certainly bitrotted.

// In theory this should establish reasons why a function shouldn't be shared (e.g. arguments, important memory locations
// differ, or memory allocations or file descriptors escape, leading to inappropriate conflation of distinct
// objects), and if all checks pass, share both the analysis and the specialised emitted code.

using namespace llvm;

// The external dependencies are the memory locations, FDs etc that indirectly flow information into
// this function.
void InlineAttempt::clearExternalDependencies() {

  for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = sharing->externalDependencies.begin(), 
	it2 = sharing->externalDependencies.end(); it != it2; ++it) {

    it->second->dropReference();
    
  }
   
  sharing->externalDependencies.clear();

}

void IntegrationAttempt::sharingInit() { }

// Record a copy of the symbolic store as we entered, for use comparing against a future state
// to determine whether this function instance can be re-used.
void InlineAttempt::sharingInit() {

  if(pass->enableSharing) {

    if(!sharing)
      sharing = new SharingState();

    sharing->storeAtEntry = BBs[0]->localStore;
    sharing->storeAtEntry->refCount++;

    clearExternalDependencies();

  }
  else {

    sharing = 0;

  }

}

// Print our dependencies for debugging purposes.
void InlineAttempt::dumpSharingState() {

  errs() << F.getName() << " / " << SeqNumber << ":";

  if(isUnsharable()) {
    errs() << " UNSHARABLE\n";
  }
  else {

    errs() << "\n";

    for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = sharing->externalDependencies.begin(),
	  itend = sharing->externalDependencies.end(); it != itend; ++it) {

      errs() << itcache(it->first) << ": ";
      it->second->print(errs(), true);
      errs() << "\n";

    }

  }

  errs() << "=== end " << F.getName() << " / " << SeqNumber << " ===\n\n";

}

void IntegrationAttempt::sharingCleanup() { }

// Called after the main analysis loop exits this function.
void InlineAttempt::sharingCleanup() {

  if(!pass->enableSharing)
    return;

  if(sharing->storeAtEntry)
    sharing->storeAtEntry->dropReference();

  SmallVector<ShadowInstruction*, 4> toRemove;

  // Eliminate escaping mallocs that are known to be freed, both as dependencies and escapes.
  // This tries to permit a function to be re-used by showing its effects are not externally
  // observable.
  // The real work has happened during the main analysis loop, where free(...) and similar
  // functions overwrite the local store with a special Deallocated value, which merges only
  // with other Deallocated values; it then suffices to check all the return blocks carry that flag.
  for(SmallPtrSet<ShadowInstruction*, 4>::iterator it = sharing->escapingMallocs.begin(),
	itend = sharing->escapingMallocs.end(); it != itend; ++it) {

    ShadowInstruction* Alloc = *it;
    bool mayEscape = false;

    for(uint32_t i = 0; i < nBBs && !mayEscape; ++i) {

      if(!BBs[i])
	continue;

      ShadowBB* BB = BBs[i];

      if(!isa<ReturnInst>(BB->invar->BB->getTerminator()))
	continue;

      ShadowValue AllocSV(Alloc);
      LocStore* thisStore = BB->getReadableStoreFor(AllocSV);
      
      // Not allocated on this path?
      if(!thisStore)
	continue;

      // Freed on this path?
      if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(thisStore->store)) {

	if(IVS->SetType == ValSetTypeDeallocated)
	  continue;

      }

      mayEscape = true;

    }

    if(!mayEscape)
      toRemove.push_back(Alloc);

  }

  for(SmallVector<ShadowInstruction*, 4>::iterator it = toRemove.begin(),
	itend = toRemove.end(); it != itend; ++it) {

    if(pass->verboseSharing) {
      
      errs() << "Eliminate dependency on freed heap location " << itcache(*it) << "\n";

    }

    sharing->escapingMallocs.erase(*it);
    DenseMap<ShadowValue, ImprovedValSet*>::iterator findit = sharing->externalDependencies.find(ShadowValue(*it));
    if(findit != sharing->externalDependencies.end()) {
      findit->second->dropReference();
      sharing->externalDependencies.erase(findit);
    }

  }

  if(pass->verboseSharing)
    dumpSharingState();

}

void IntegrationAttempt::noteVFSOp() {

  if(!pass->enableSharing)
    return;

  InlineAttempt* Root = getFunctionRoot();
  Root->hasVFSOps = true;

}

// This function depends on V, where V is a memory object.
void IntegrationAttempt::noteDependency(ShadowValue V) {

  if(!pass->enableSharing)
    return;
  
  InlineAttempt* Root = getFunctionRoot();

  // Don't register dependency on local stack objects.
  int32_t frameNo = V.getFrameNo();
  if(Root->invarInfo->frameSize != -1 && frameNo == Root->stack_depth)
    return;

  // Don't depend on constants
  if(ShadowGV* GV = V.getGV()) {

    if(GV->G->isConstant())
      return;

  }

  std::pair<DenseMap<ShadowValue, ImprovedValSet*>::iterator, bool> it = Root->sharing->externalDependencies.insert(std::make_pair(V, (ImprovedValSet*)0));

  // Already registered?
  if(!it.second)
    return;

  // When sharing is enabled the base store is only used for initialisers. Therefore
  // this must be the most up-to-date value at function entry.

  LocStore* saveStore = Root->sharing->storeAtEntry->getReadableStoreFor(V);
  if(!saveStore)
    return;

  it.first->second = saveStore->store->getReadableCopy();

}

// Record an allocation which, for the time being, is assumed to escape. sharingCleanup may then
// determine that in fact it is always freed.
void IntegrationAttempt::noteMalloc(ShadowInstruction* SI) {

  if(!pass->enableSharing)
    return;

  InlineAttempt* Root = getFunctionRoot();
  
  Root->sharing->escapingMallocs.insert(SI);

}

// This context calls some function; ChildIA is a completed analysis of that function.
// Inherit its external dependencies and escaping allocations.
void IntegrationAttempt::mergeChildDependencies(InlineAttempt* ChildIA) {

  if(!pass->enableSharing)
    return;

  if(ChildIA->hasVFSOps)
    noteVFSOp();

  for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = ChildIA->sharing->externalDependencies.begin(),
	it2 = ChildIA->sharing->externalDependencies.end(); it != it2; ++it) {

    // Note this might record a different dependency to our child if this function or a sibling
    // has altered a relevant location since we entered this function.
    noteDependency(it->first);
      
  }
    
  for(SmallPtrSet<ShadowInstruction*, 4>::iterator it = ChildIA->sharing->escapingMallocs.begin(),
	itend = ChildIA->sharing->escapingMallocs.end(); it != itend; ++it) {
    
    noteMalloc(*it);

  }

}


// Check incoming arguments and memory locations last seen for this IA match those at callsite SI.
bool InlineAttempt::matchesCallerEnvironment(ShadowInstruction* SI) {

  if(!pass->enableSharing)
    return false;

  // Differing vararg counts?
  if(SI->getNumArgOperands() != argShadows.size())
    return false;

  // Check all arguments match.
  for(uint32_t i = 0, ilim = argShadows.size(); i != ilim; ++i) {

    // Can use shallow equality for arguments

    ShadowValue Operand = SI->getCallArgOperand(i);
    if(!IVMatchesVal(Operand, argShadows[i].i.PB))
      return false;
    
  }

  // Check all memory locations upon which we depend match the values at the proposed callsite.
  // TODO: consider using deep equality test here if we find too many false negatives due to 
  // e.g. identical structures being produced by different means leading to different representations.

  for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = sharing->externalDependencies.begin(),
	itend = sharing->externalDependencies.end(); it != itend; ++it) {

    // Note that if function sharing is enabled the base store is only used to represent initialisers
    // in order to facilitate creating a copy of the store at function entry.
    LocStore* callsiteStore = SI->parent->getReadableStoreFor(it->first);
    if(!callsiteStore)
      return false;

    if(!IVsEqualShallow(callsiteStore->store, it->second))
      return false;

  }

  return true;

}

// This function is permissible for sharing!
void LLPEAnalysisPass::addSharableFunction(InlineAttempt* IA) {
  
  if(!enableSharing)
    return;

  IAsByFunction[&IA->F].push_back(IA);
  IA->registeredSharable = true;

}

void LLPEAnalysisPass::removeSharableFunction(InlineAttempt* IA) {

  if(!enableSharing)
    return;

  std::vector<InlineAttempt*>& IAs = IAsByFunction[&IA->F];
  std::vector<InlineAttempt*>::iterator findit = std::find(IAs.begin(), IAs.end(), IA);
  release_assert(findit != IAs.end() && "Function unshared twice?");
  IAs.erase(findit);
  IA->registeredSharable = false;

}

// Before trying to analyse the call at SI, see if we can find an existing analysis
// that sufficiently resembles the current circumstances to re-use.
InlineAttempt* LLPEAnalysisPass::findIAMatching(ShadowInstruction* SI) {

  if(!enableSharing)
    return 0;
  
  Function* FCalled = getCalledFunction(SI);

  DenseMap<Function*, std::vector<InlineAttempt*> >::iterator findit = IAsByFunction.find(FCalled);
  if(findit == IAsByFunction.end())
    return 0;

  std::vector<InlineAttempt*>& candidates = findit->second;
  for(std::vector<InlineAttempt*>::iterator it = candidates.begin(), 
	itend = candidates.end(); it != itend; ++it) {

    // Skip functions that are currently on the stack, as their dependency information is incomplete.
    if((*it)->active)
      continue;

    if((*it)->matchesCallerEnvironment(SI)) {
      (*it)->Callers.push_back(SI);
      (*it)->uniqueParent = 0;
      return *it;
    }

  }

  return 0;

}

// CoW break this IA, but with the proviso that we're about to run analyseWithArgs() against it,
// so we can leave work undone if that will reconstruct it anyway. This happens when a call was shared,
// but it has become clear that actually the circumstances at two of its callsites differ. This happens
// when iteratively analysing an unbounded loop, for example, and at the first pass a call is approved
// to re-use an existing analysis, but at a subsequent pass it becomes clear the analysis can't actually
// be shared.

// This is currently maximally lazy: it makes a blank IA.
InlineAttempt* InlineAttempt::getWritableCopyFrom(ShadowInstruction* SI) {

  release_assert(pass->enableSharing && "getWritableCopyFrom without sharing enabled?");

  InlineAttempt* Copy = new InlineAttempt(pass, F, SI, nesting_depth);

  SmallVector<ShadowInstruction*, 1>:: iterator findit = std::find(Callers.begin(), Callers.end(), SI);
  release_assert(findit != Callers.end() && "CoW break IA with bad caller?");
  Callers.erase(findit);
  
  return Copy;

}
