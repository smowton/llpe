

#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Function.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;

void InlineAttempt::clearExternalDependencies() {

  for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = externalDependencies.begin(), 
	it2 = externalDependencies.end(); it != it2; ++it) {

    it->second->dropReference();
    
  }
   
  externalDependencies.clear();

}

void IntegrationAttempt::sharingInit() { }

void InlineAttempt::sharingInit() {

  if(pass->enableSharing && !unsharable) {

    storeAtEntry = BBs[0]->localStore;
    storeAtEntry->refCount++;

    clearExternalDependencies();

  }
  else {
    storeAtEntry = 0;
  }

}

void InlineAttempt::dumpSharingState() {

  errs() << F.getName() << " / " << SeqNumber << ":";

  if(unsharable) {
    errs() << " UNSHARABLE\n";
  }
  else {

    errs() << "\n";

    for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = externalDependencies.begin(),
	  itend = externalDependencies.end(); it != itend; ++it) {

      errs() << itcache(it->first) << ": ";
      it->second->print(errs(), true);
      errs() << "\n";

    }

  }

  errs() << "=== end " << F.getName() << " / " << SeqNumber << " ===\n\n";

}

void IntegrationAttempt::sharingCleanup() { }

void InlineAttempt::sharingCleanup() {

  if(storeAtEntry)
    storeAtEntry->dropReference();

  if(pass->verboseSharing)
    dumpSharingState();

}

void IntegrationAttempt::markUnsharable() {

  if(!pass->enableSharing)
    return;

  InlineAttempt* Root = getFunctionRoot();
  if(!Root->storeAtEntry)
    return;

  Root->unsharable = true;
  Root->clearExternalDependencies();
  Root->storeAtEntry->dropReference();
  Root->storeAtEntry = 0;

}

// This function depends on V, where V is a memory object.
// 
void IntegrationAttempt::noteDependency(ShadowValue V) {

  if(!pass->enableSharing)
    return;
  
  InlineAttempt* Root = getFunctionRoot();

  if(Root->unsharable)
    return;
 
  // Don't register dependency on local stack objects.
  int32_t frameNo = V.getFrameNo();
  if(Root->invarInfo->frameSize != -1 && frameNo == Root->stack_depth)
    return;

  // Don't depend on constants
  if(ShadowGV* GV = V.getGV()) {

    if(GV->G->isConstant())
      return;

  }

  std::pair<DenseMap<ShadowValue, ImprovedValSet*>::iterator, bool> it = Root->externalDependencies.insert(std::make_pair<ShadowValue, ImprovedValSet*>(V, 0));

  // Already registered?
  if(!it.second)
    return;

  // When sharing is enabled the base store is only used for initialisers. Therefore
  // this must be the most up-to-date value at function entry.

  LocStore* saveStore = Root->storeAtEntry->getReadableStoreFor(V);
  if(!saveStore)
    saveStore = &(V.getBaseStore());

  it.first->second = saveStore->store->getReadableCopy();

}

void IntegrationAttempt::mergeChildDependencies(InlineAttempt* ChildIA) {

  if(!pass->enableSharing)
    return;

  if(ChildIA->unsharable)
    markUnsharable();
  else {

    for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = ChildIA->externalDependencies.begin(),
	  it2 = ChildIA->externalDependencies.end(); it != it2; ++it) {

      // Note this might record a different dependency to our child if this function or a sibling
      // has altered a relevant location since we entered this function.
      noteDependency(it->first);
      
    }

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

  for(DenseMap<ShadowValue, ImprovedValSet*>::iterator it = externalDependencies.begin(),
	itend = externalDependencies.end(); it != itend; ++it) {

    // Note that if function sharing is enabled the base store is only used to represent initialisers
    // in order to facilitate creating a copy of the store at function entry.
    LocStore* callsiteStore = SI->parent->getReadableStoreFor(it->first);
    if(!callsiteStore)
      callsiteStore = &(it->first.getBaseStore());

    if(!IVsEqualShallow(callsiteStore->store, it->second))
      return false;

  }

  return true;

}


void IntegrationHeuristicsPass::addSharableFunction(InlineAttempt* IA) {
  
  if(!enableSharing)
    return;

  IAsByFunction[&IA->F].push_back(IA);

}

void IntegrationHeuristicsPass::removeSharableFunction(InlineAttempt* IA) {

  if(!enableSharing)
    return;

  std::vector<InlineAttempt*>& IAs = IAsByFunction[&IA->F];
  std::vector<InlineAttempt*>::iterator findit = std::find(IAs.begin(), IAs.end(), IA);
  release_assert(findit != IAs.end() && "Function unshared twice?");
  IAs.erase(findit);

}

InlineAttempt* IntegrationHeuristicsPass::findIAMatching(ShadowInstruction* SI) {

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
      return *it;
    }

  }

  return 0;

}

// CoW break this IA, but with the proviso that we're about to run analyseWithArgs() against it,
// so we can leave work undone if that will reconstruct it anyway.

// This is currently maximally lazy: it makes a blank IA.
InlineAttempt* InlineAttempt::getWritableCopyFrom(ShadowInstruction* SI) {

  release_assert(pass->enableSharing && "getWritableCopyFrom without sharing enabled?");

  InlineAttempt* Copy = new InlineAttempt(pass, F, LI, SI, nesting_depth);

  SmallVector<ShadowInstruction*, 1>:: iterator findit = std::find(Callers.begin(), Callers.end(), SI);
  release_assert(findit != Callers.end() && "CoW break IA with bad caller?");
  Callers.erase(findit);
  
  return Copy;

}
