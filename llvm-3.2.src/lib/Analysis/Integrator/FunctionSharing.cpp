

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
