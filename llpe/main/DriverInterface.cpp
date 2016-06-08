//===-- DriverInterface.cpp ----------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// This file implements functions that interface with the GUI pass.

#include "llvm/Analysis/LLPE.h"

#define DEBUG_TYPE "llpe-misc"

using namespace llvm;

// Helpers for the driver pass to check whether it's appropriate to show a disable-this-context checkbox:

bool InlineAttempt::canDisable() {
  return Callers.size() == 1;
}

bool PeelIteration::canDisable() {
  return false;
}

// Implement data export functions, for the GUI to get a description of the context tree:

bool IntegrationAttempt::hasChildren() {

  return (child_calls_begin(this) != child_calls_end(this)) || peelChildren.size();

}

bool PeelAttempt::hasChildren() {
  
  return Iterations.size() != 0;

}

void InlineAttempt::addExtraTagsFrom(PathConditions& PC, IntegratorTag* myTag) {

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(),
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx == UINT_MAX || it->stackIdx == targetCallInfo->targetStackDepth) {

      // May happen if the user has specified a limit on how many IAs
      // should be explored.
      if(!it->IA)
	continue;

      IntegratorTag* newTag = it->IA->createTag(myTag);
      myTag->children.push_back(newTag);

    }

  }  

}

void IntegrationAttempt::addExtraTags(IntegratorTag* myTag) { }
void InlineAttempt::addExtraTags(IntegratorTag* myTag) {

  if(targetCallInfo)
    addExtraTagsFrom(pass->pathConditions, myTag);
  if(invarInfo->pathConditions)
    addExtraTagsFrom(*invarInfo->pathConditions, myTag);

}

static uint32_t getTagBlockIdx(const IntegratorTag* t, IntegrationAttempt* Ctx) {

  if(t->type == IntegratorTypeIA)
    return (uint32_t)((InlineAttempt*)t->ptr)->SeqNumber;
  else
    return (uint32_t)((PeelAttempt*)t->ptr)->Iterations[0]->SeqNumber;

}

struct tagComp {

  IntegrationAttempt* FromCtx;

  bool operator()(const IntegratorTag* t1, const IntegratorTag* t2) {
    
    return getTagBlockIdx(t1, FromCtx) < getTagBlockIdx(t2, FromCtx);
    
  }

  tagComp(IntegrationAttempt* C) : FromCtx(C) {}

};

IntegratorTag* IntegrationAttempt::createTag(IntegratorTag* parent) {

  IntegratorTag* myTag = pass->newTag();
  myTag->ptr = (void*)this;
  myTag->type = IntegratorTypeIA;
  myTag->parent = parent;
  
  for(IAIterator it = child_calls_begin(this),
	it2 = child_calls_end(this); it != it2; ++it) {
    
    IntegratorTag* inlineTag = it->second->createTag(myTag);
    myTag->children.push_back(inlineTag);

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	it2 = peelChildren.end(); it != it2; ++it) {

    IntegratorTag* peelTag = it->second->createTag(myTag);
    myTag->children.push_back(peelTag);

  }

  addExtraTags(myTag);

  tagComp C(this);
  std::sort(myTag->children.begin(), myTag->children.end(), C);

  return myTag;

}

IntegratorTag* PeelAttempt::createTag(IntegratorTag* parent) {

  IntegratorTag* myTag = pass->newTag();
  myTag->ptr = (void*)this;
  myTag->type = IntegratorTypePA;
  myTag->parent = parent;
  
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), 
	it2 = Iterations.end(); it != it2; ++it) {

    IntegratorTag* iterTag = (*it)->createTag(myTag);
    myTag->children.push_back(iterTag);

  }

  return myTag;

}

IntegratorTag* llvm::searchFunctions(IntegratorTag* thisTag, std::string& search, IntegratorTag*& startAt) {

  if(startAt == thisTag) {
    
    startAt = 0;

  }
  else if(!startAt) {
    
    if(thisTag->type == IntegratorTypeIA) {

      IntegrationAttempt* IA = (IntegrationAttempt*)thisTag->ptr;

      if(IA->getShortHeader().find(search) != std::string::npos) {
      
	return thisTag;

      }

    }

  }

  for(std::vector<IntegratorTag*>::iterator it = thisTag->children.begin(), 
	itend = thisTag->children.end(); it != itend; ++it) {

    if(IntegratorTag* SubRes = searchFunctions(*it, search, startAt))
      return SubRes;

  }

  return 0;

}

