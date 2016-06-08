//===-- CreateSpecialisationContext.cpp -----------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"

#define DEBUG_TYPE "llpe-misc"

using namespace llvm;

// List of functions that should never be expanded, even if bitcode implementations
// appear to be available. Most are syscalls or thin wrappers around syscalls,
// but some are allocators or synchronisation functions which we handle specially.

static const char* blacklistedFnNames[] = {
  
   "malloc" ,  "free" ,
   "realloc" ,  "ioctl" ,
   "gettimeofday" ,  "clock_gettime" ,
   "time" ,
   "open" ,  "read" ,
   "llseek" ,  "lseek" ,
   "lseek64" ,  "close" ,
   "write" , 
   "__libc_fcntl" ,
   "posix_fadvise" ,
   "stat" ,
   "isatty" ,
   "__libc_sigaction" ,
   "socket" ,  "bind" ,
   "listen" ,  "setsockopt" ,
   "_exit" ,  "__libc_accept" ,
   "poll" ,  "shutdown" ,
   "mkdir" ,
   "__libc_nanosleep" ,
   "rename" ,
   "setgid" ,
   "setuid" ,
   "__fcntl_nocancel" ,
   "closedir" ,
   "opendir" ,
   "getsockname" ,
   "__libc_recvfrom" ,
   "__libc_sendto" ,
   "mmap" ,
   "munmap" ,
   "mremap" ,
   "clock_getres" ,
   "fstat" ,
   "getegid" ,
   "geteuid" ,
   "getgid" ,
   "getrlimit" ,
   "getuid" ,
   "rmdir" ,
   "sigprocmask" ,
   "unlink" ,
   "__getdents64" ,
   "brk" ,
   "getpid" ,
   "kill" ,
   "uname",
   "__pthread_mutex_init",
   "__pthread_mutex_lock",
   "__pthread_mutex_trylock",
   "__pthread_mutex_unlock",
   "pthread_setcanceltype",
   "pthread_setcancelstate",
   "writev",
   "epoll_create",
   "dup2",
   "access"
   
};

// Make a table of Function pointers that shouldn't be explored.

void LLPEAnalysisPass::initBlacklistedFunctions(Module& M) {

  uint32_t nfns = sizeof(blacklistedFnNames) / sizeof(blacklistedFnNames[0]);

  for(uint32_t i = 0; i != nfns; ++i) {

    if(Function* F = M.getFunction(blacklistedFnNames[i]))
      blacklistedFunctions.insert(F);

  }
   
}

// Are we within any call to FCalled?

bool PeelIteration::stackIncludesCallTo(Function* FCalled) {

  return parent->stackIncludesCallTo(FCalled);

}

bool InlineAttempt::stackIncludesCallTo(Function* FCalled) {

  if((&F) == FCalled)
    return true;
  else if(Callers.empty())
    return false;
  
  IntegrationAttempt* Parent = getUniqueParent();
  release_assert(Parent && "Call to stackIncludesCallTo whilst shared?");
  
  return Parent->stackIncludesCallTo(FCalled);

}

// Should we create a new specialisation context for SI's call to FCalled?
// We always do if this path is a certain consequence of our specialisation assumptions
// or the user explicitly directs us to; we never do if this would be a (transitive) recurison
// on a path that only may be reached due to the possibility of infinite regress.

bool IntegrationAttempt::shouldInlineFunction(ShadowInstruction* SI, Function* FCalled) {

  if(SI->parent->status & (BBSTATUS_CERTAIN | BBSTATUS_ASSUMED))
    return true;

  if(pass->shouldAlwaysInline(FCalled))
    return true;

  // Inline if this wouldn't be a recursive call.
  if(!stackIncludesCallTo(FCalled))
    return true;
  
  return false;

}

// Check all the possible reasons why call instruction SI shouldn't make a specialisation context.

bool IntegrationAttempt::callCanExpand(ShadowInstruction* SI, InlineAttempt*& Result) {

  if(InlineAttempt* IA = getInlineAttempt(SI)) {
    Result = IA;
    return true;
  }

  Result = 0;
  
  if(pass->maxContexts != 0 && pass->IAs.size() > pass->maxContexts)
    return false;

  Function* FCalled = getCalledFunction(SI);
  if(!FCalled) {
    LPDEBUG("Ignored " << itcache(SI) << " because it's an uncertain indirect call\n");
    return false;
  }

  if(FCalled->isDeclaration()) {
    LPDEBUG("Ignored " << itcache(SI) << " because we don't know the function body\n");
    return false;
  }

  if(!shouldInlineFunction(SI, FCalled)) {
    LPDEBUG("Ignored " << itcache(SI) << " because it shouldn't be inlined (not on certain path, and would cause recursion)\n");
    return false;
  }

  if(pass->yieldFunctions.count(FCalled))
    return false;

  if(pass->specialLocations.count(FCalled))
    return false;
  
  if(SpecialFunctionMap.count(FCalled))
    return false;

  if(functionIsBlacklisted(FCalled)) {
    LPDEBUG("Ignored " << itcache(SI) << " because it is a special function we are not allowed to inline\n");
    return false;
  }

  return true;

}

// These are used to provide a crude progress bar.

static uint32_t mainPhaseProgressN = 0;
const uint32_t mainPhaseProgressLimit = 1000;

static void mainPhaseProgress() {

  mainPhaseProgressN++;
  if(mainPhaseProgressN == mainPhaseProgressLimit) {

    errs() << ".";
    mainPhaseProgressN = 0;

  }

}

// Get an existing specialisation context representing the call made by SI, or try to create one.
// 'created' is set if the context is new; 'needsAnalyse' is set to false if we have reused
// a context that already existed and had the same preconditions as this call-site (only possible when function sharing is on)

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(ShadowInstruction* SI, bool& created, bool& needsAnalyse) {

  created = false;
  
  InlineAttempt* Result;
  if(!callCanExpand(SI, Result))
    return 0;

  needsAnalyse = false;
  
  // Found existing call. Already completely up to date?
  if(Result && Result->matchesCallerEnvironment(SI)) {
    if(pass->verboseSharing)
      errs() << "KEEP: " << itcache(SI) << " #" << Result->SeqNumber << "\n";
    return Result;
  }
  
  // Result needs to be re-analysed or doesn't exist at all.
  // Try to find an existing IA we can simply use as-is.
  if(InlineAttempt* Share = pass->findIAMatching(SI)) {
    if(Result) {
      if(pass->verboseSharing)
	errs() << "DROP: " << itcache(SI) << " #" << Result->SeqNumber << "\n";
      Result->dropReferenceFrom(SI);
    }
    if(pass->verboseSharing)
      errs() << "SHARE: " << itcache(SI) << " #" << Share->SeqNumber << " (refs: " << Share->Callers.size() << ")\n";
    SI->typeSpecificData = Share;
    return Share;
  }

  needsAnalyse = true;

  // CoW break existing IA if necessary and analyse it.
  if(Result) {
    if(!Result->isShared())
      return Result;
    else {
      InlineAttempt* Unshared = Result->getWritableCopyFrom(SI);
      if(pass->verboseSharing)
	errs() << "BREAK: " << itcache(SI) << " #" << Result->SeqNumber << " -> #" << Unshared->SeqNumber << "\n";
      SI->typeSpecificData = Unshared;
      created = true;
      return Unshared;
    }
  }

  // Finally create a brand new IA if we must.

  mainPhaseProgress();

  created = true;

  Function* FCalled = getCalledFunction(SI);
  SmallDenseMap<Function*, Function*>::iterator it = pass->modelFunctions.find(FCalled);
  bool isModel = it != pass->modelFunctions.end();
  if(isModel)
    FCalled = it->second;

  InlineAttempt* IA = new InlineAttempt(pass, *FCalled, SI, this->nesting_depth + 1);
  IA->isModel = isModel;
  SI->typeSpecificData = IA;

  checkTargetStack(SI, IA);

  LPDEBUG("Inlining " << FCalled->getName() << " at " << itcache(SI) << "\n");

  return IA;

}

// Check whether we now have evidence the loop terminates this time around.
void PeelIteration::checkFinalIteration() {

  ShadowBBInvar* LatchBB = getBBInvar(parentPA->L->latchIdx);
  ShadowBBInvar* HeaderBB = getBBInvar(parentPA->L->headerIdx);

  if(edgeIsDead(LatchBB, HeaderBB) || pass->assumeEndsAfter(&F, getBBInvar(L->headerIdx)->BB, iterationCount)) {

    iterStatus = IterationStatusFinal;

  }

}

PeelIteration* PeelAttempt::getIteration(unsigned iter) {

  if(Iterations.size() > iter)
    return Iterations[iter];

  return 0;

}

// Create a context for the next iteration of this loop.
PeelIteration* PeelAttempt::getOrCreateIteration(unsigned iter) {

  if(PeelIteration* PI = getIteration(iter))
    return PI;

  //  if(pass->maxContexts != 0 && pass->SeqNumber > pass->maxContexts)
  //    return 0;
  
  LPDEBUG("Peeling iteration " << iter << " of loop " << getLName() << "\n");

  mainPhaseProgress();

  assert(iter == Iterations.size());

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, iter, nesting_depth);
  Iterations.push_back(NewIter);
    
  return NewIter;

}

PeelIteration* PeelIteration::getNextIteration() {

  return parentPA->getIteration(this->iterationCount + 1);

}

// Do we know for sure this iteration cannot exit the loop?
bool PeelIteration::allExitEdgesDead() {

  for(std::vector<std::pair<uint32_t, uint32_t> >::const_iterator EI = parentPA->L->exitEdges.begin(), 
	EE = parentPA->L->exitEdges.end(); EI != EE; ++EI) {

    ShadowBBInvar* EStart = getBBInvar(EI->first);
    ShadowBBInvar* EEnd = getBBInvar(EI->second);

    if((!edgeIsDead(EStart, EEnd)) && !isExceptionEdge(EStart, EEnd))
      return false;

  }

  return true;

}

// Create a context for the next iteration, or return the existing one.
PeelIteration* PeelIteration::getOrCreateNextIteration() {

  if(PeelIteration* Existing = getNextIteration())
    return Existing;

  if(iterStatus == IterationStatusFinal) {
    LPDEBUG("Loop known to exit: will not create next iteration\n");
    return 0;
  }
  
  const std::pair<uint32_t, uint32_t>& OE = parentPA->L->optimisticEdge;

  bool willIterate = parentPA->L->alwaysIterate;

  if((!willIterate) && OE.first != 0xffffffff) {
    ShadowBBInvar* OE1 = getBBInvar(OE.first);
    ShadowBBInvar* OE2 = getBBInvar(OE.second);
    willIterate = edgeIsDead(OE1, OE2);
  }

  // Cancel iteration if the latch edge is outright killed.
  // Usually this is case due to optimistic edges and such, but could also result from
  // executing unreachable within the loop.
  if(willIterate) {
    ShadowBBInvar* latchBB = getBBInvar(parentPA->L->latchIdx);
    ShadowBBInvar* headerBB = getBBInvar(parentPA->L->headerIdx);
    if(edgeIsDead(latchBB, headerBB))
      return 0;
  }

  if(!willIterate)
    willIterate = allExitEdgesDead();

  if(!willIterate) {

    LPDEBUG("Won't peel loop " << getLName() << " yet because at least one exit edge is still alive\n");
    return 0;
      
  }

  iterStatus = IterationStatusNonFinal;
  LPDEBUG("Loop known to iterate: creating next iteration\n");
  return parentPA->getOrCreateIteration(this->iterationCount + 1);

}

// Find an existing specialisation context for loop L (an immediate child of this context).
PeelAttempt* IntegrationAttempt::getPeelAttempt(const ShadowLoopInvar* L) {

  DenseMap<const ShadowLoopInvar*, PeelAttempt*>::const_iterator it = peelChildren.find(L);
  if(it != peelChildren.end())
    return it->second;

  return 0;

}

// Find an existing loop specialisation, or else check if it's appropriate to specialise
// this loop per-iteration as opposed to analysing the general case of the loop body.
PeelAttempt* IntegrationAttempt::getOrCreatePeelAttempt(const ShadowLoopInvar* NewL) {

  if(pass->shouldIgnoreLoop(&F, getBBInvar(NewL->headerIdx)->BB))
    return 0;

  if(PeelAttempt* PA = getPeelAttempt(NewL))
    return PA;

  if(pass->maxContexts != 0 && pass->IAs.size() > pass->maxContexts)
    return 0;
 
  // Preheaders only have one successor (the header), so this is enough.
  
  ShadowBB* preheaderBB = getBB(NewL->preheaderIdx);
  if(!preheaderBB->isMarkedCertainOrAssumed()) {
   
    LPDEBUG("Will not expand loop " << getBBInvar(NewL->headerIdx)->BB->getName() << " because the preheader is not certain/assumed to execute\n");
    return 0;

  }

  LPDEBUG("Inlining loop with header " << getBBInvar(NewL->headerIdx)->BB->getName() << "\n");
  PeelAttempt* LPA = new PeelAttempt(pass, this, F, NewL, nesting_depth + 1);
  peelChildren[NewL] = LPA;

  return LPA;

}

// Functions that drop store references that were retained so that loop fixed points could be
// found. Exiting edges keep references in case this is the last iteration; the latch edge
// keeps a reference in case we have to iterate again; when it becomes clear which is the case
// one or other class of backup reference must be dropped.

void PeelIteration::dropExitingStoreRef(uint32_t fromIdx, uint32_t toIdx) {

  ShadowBB* BB = getBB(fromIdx);
  ShadowBBInvar* toBBI = getBBInvar(toIdx);
  if(BB && (!edgeIsDead(BB->invar, toBBI)) && !edgeBranchesToUnspecialisedCode(BB->invar, toBBI)) {

    if(BB->invar->naturalScope != L) {

      const ShadowLoopInvar* ChildL = immediateChildLoop(L, BB->invar->naturalScope);
      if(PeelAttempt* ChildPA = getPeelAttempt(ChildL)) {

	if(ChildPA->isTerminated()) {

	  // Exit directly from a child loop: drop each outgoing reference:
	  for(std::vector<PeelIteration*>::iterator it = ChildPA->Iterations.begin(),
		itend = ChildPA->Iterations.end(); it != itend; ++it) {

	    (*it)->dropExitingStoreRef(fromIdx, toIdx);

	  }

	  return;

	}

      }

    }

    SAFE_DROP_REF(BB->localStore);

  }

}

void PeelIteration::dropExitingStoreRefs() {

  // We will never exit -- drop store refs that belong to exiting edges.

  const ShadowLoopInvar* LInfo = parentPA->L;

  for(std::vector<std::pair<uint32_t, uint32_t> >::const_iterator it = LInfo->exitEdges.begin(),
	itend = LInfo->exitEdges.end(); it != itend; ++it) {
    
    dropExitingStoreRef(it->first, it->second);
    
  }

}

void PeelIteration::dropLatchStoreRef() {

  // If the last latch block was holding a store ref for the next iteration, drop it.
  ShadowBB* LatchBB = getBB(parentPA->L->latchIdx);
  ShadowBBInvar* HeaderBBI = getBBInvar(parentPA->L->headerIdx);
  
  if(!edgeIsDead(LatchBB->invar, HeaderBBI)) {
    SAFE_DROP_REF(LatchBB->localStore);
  }

}

void PeelAttempt::dropExitingStoreRefs() {

 for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->dropExitingStoreRefs();

}

// Drop store references that are no longer needed from a loop exploration
// that failed to terminate.
void PeelAttempt::dropNonterminatedStoreRefs() {

  dropExitingStoreRefs();
  Iterations.back()->dropLatchStoreRef();

}

