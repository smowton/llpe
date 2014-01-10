//===- LoopPeelHeuristics.cpp - Find loops that we might want to try peeling --------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass uses some heuristics to figure out loops that might be worth peeling.
// Basically this is simplistic SCCP plus some use of MemDep to find out how many instructions
// from the loop body would likely get evaluated if we peeled an iterations.
// We also consider the possibility of concurrently peeling a group of nested loops.
// The hope is that the information provided is both more informative and quicker to obtain than just speculatively
// peeling and throwing a round of -std-compile-opt at the result.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "looppeelheuristics"
#include "llvm/Pass.h"
#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/Module.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/PHITransAddr.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/DataLayout.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/FileSystem.h"

#include "dsa/DataStructure.h"

#include <sstream>
#include <string>
#include <algorithm>

#include <stdlib.h>

#include <openssl/sha.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

using namespace llvm;

char IntegrationHeuristicsPass::ID = 0;

static cl::opt<std::string> GraphOutputDirectory("intgraphs-dir", cl::init(""));
static cl::opt<std::string> RootFunctionName("intheuristics-root", cl::init("main"));
static cl::opt<std::string> EnvFileAndIdx("spec-env", cl::init(""));
static cl::opt<std::string> ArgvFileAndIdxs("spec-argv", cl::init(""));
static cl::opt<unsigned> MallocAlignment("int-malloc-alignment", cl::init(0));
static cl::list<std::string> SpecialiseParams("spec-param", cl::ZeroOrMore);
static cl::list<std::string> AlwaysInlineFunctions("int-always-inline", cl::ZeroOrMore);
static cl::list<std::string> OptimisticLoops("int-optimistic-loop", cl::ZeroOrMore);
static cl::list<std::string> AlwaysIterLoops("int-always-iterate", cl::ZeroOrMore);
static cl::list<std::string> AssumeEdges("int-assume-edge", cl::ZeroOrMore);
static cl::list<std::string> IgnoreLoops("int-ignore-loop", cl::ZeroOrMore);
static cl::list<std::string> ExpandCallsLoops("int-expand-loop-calls", cl::ZeroOrMore);
static cl::list<std::string> IgnoreLoopsWithChildren("int-ignore-loop-children", cl::ZeroOrMore);
static cl::list<std::string> AlwaysExploreFunctions("int-always-explore", cl::ZeroOrMore);
static cl::list<std::string> LoopMaxIters("int-loop-max", cl::ZeroOrMore);
static cl::list<std::string> IgnoreBlocks("int-ignore-block", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsInt("int-path-condition-int", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFptr("int-path-condition-fptr", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsString("int-path-condition-str", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsIntmem("int-path-condition-intmem", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFptrmem("int-path-condition-fptrmem", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFunc("int-path-condition-func", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsStream("int-path-condition-stream", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsGlobalInit("int-path-condition-global-unmodified", cl::ZeroOrMore);
static cl::opt<bool> SkipBenefitAnalysis("skip-benefit-analysis");
static cl::opt<bool> SkipDIE("skip-int-die");
static cl::opt<bool> SkipTL("skip-check-elim");
static cl::opt<unsigned> MaxContexts("int-stop-after", cl::init(0));
static cl::opt<bool> VerboseOverdef("int-verbose-overdef");
static cl::opt<bool> EnableFunctionSharing("int-enable-sharing");
static cl::opt<bool> VerboseFunctionSharing("int-verbose-sharing");
static cl::opt<bool> UseGlobalInitialisers("int-use-global-initialisers");
static cl::list<std::string> SpecialLocations("int-special-location", cl::ZeroOrMore);
static cl::list<std::string> ModelFunctions("int-model-function", cl::ZeroOrMore);
static cl::list<std::string> YieldFunctions("int-yield-function", cl::ZeroOrMore);
static cl::opt<bool> UseDSA("int-use-dsa");
static cl::list<std::string> TargetStack("int-target-stack", cl::ZeroOrMore);
static cl::list<std::string> SimpleVolatiles("int-simple-volatile-load", cl::ZeroOrMore);
static cl::list<std::string> LockDomains("int-lock-domain", cl::ZeroOrMore);
static cl::list<std::string> PessimisticLocks("int-pessimistic-lock", cl::ZeroOrMore);
static cl::opt<bool> DumpDSE("int-dump-dse");
static cl::opt<bool> DumpTL("int-dump-tl");
static cl::list<std::string> ForceNoAliasArgs("int-force-noalias-arg", cl::ZeroOrMore);
static cl::list<std::string> VarAllocators("int-allocator-fn", cl::ZeroOrMore);
static cl::list<std::string> ConstAllocators("int-allocator-fn-const", cl::ZeroOrMore);
static cl::opt<bool> VerbosePathConditions("int-verbose-path-conditions");
static cl::opt<std::string> LLIOPreludeFn("int-prelude-fn", cl::init(""));
static cl::opt<int> LLIOPreludeStackIdx("int-prelude-stackidx", cl::init(-1));
static cl::opt<std::string> LLIOConfFile("int-write-llio-conf", cl::init(""));
static cl::opt<std::string> StatsFile("int-stats-file", cl::init(""));
static cl::list<std::string> NeverInline("int-never-inline", cl::ZeroOrMore);
static cl::opt<bool> SingleThreaded("int-single-threaded");
static cl::opt<bool> OmitChecks("int-omit-checks");
static cl::list<std::string> SplitFunctions("int-force-split");

ModulePass *llvm::createIntegrationHeuristicsPass() {
  return new IntegrationHeuristicsPass();
}

static RegisterPass<IntegrationHeuristicsPass> X("intheuristics", "Score functions for pervasive integration benefit",
						 false /* Only looks at CFG */,
						 true /* Analysis Pass */);

InlineAttempt::InlineAttempt(IntegrationHeuristicsPass* Pass, Function& F, 
			     ShadowInstruction* _CI, int depth,
			     bool pathCond) : 
  IntegrationAttempt(Pass, F, 0, depth, 0)
{ 

  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);

  sharing = 0;
  enabled = true;
  isModel = false;
  isPathCondition = pathCond;
  hasVFSOps = false;
  registeredSharable = false;
  active = false;
  instructionsCommitted = false;
  emittedAlloca = false;
  blocksReachableOnFailure = 0;
  CommitF = 0;
  targetCallInfo = 0;
  integrationGoodnessValid = false;
  backupTlStore = 0;
  backupDSEStore = 0;
  isStackTop = false;
  DT = pass->DTs[&F];
  if(_CI) {
    Callers.push_back(_CI);
    uniqueParent = _CI->parent->IA;
  }
  else {
    uniqueParent = 0;
  }

  prepareShadows();

}

PeelIteration::PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, 
			     Function& F, int iter, int depth) :
  IntegrationAttempt(Pass, F, PP->L, depth, 0),
  iterationCount(iter),
  parentPA(PP),
  parent(P),
  iterStatus(IterationStatusUnknown)
{ 
  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);
  prepareShadows();
}

PeelAttempt::PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, 
			 const Loop* _L, int depth) 
  : pass(Pass), parent(P), F(_F), residualInstructions(-1), nesting_depth(depth), stack_depth(0), 
    enabled(true), L(_L), totalIntegrationGoodness(0), integrationGoodnessValid(false)
{

  invarInfo = parent->invarInfo->LInfo[L];
  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);

  getOrCreateIteration(0);

}

IntegrationAttempt::~IntegrationAttempt() {

  // !BBs indicates we've already been cleaned up (but not deallocated yet).
  if(!BBs)
    return;

  release_assert(pass->IAs.size() > SeqNumber);
  pass->IAs[SeqNumber] = 0;

  for(IAIterator II = child_calls_begin(this), IE = child_calls_end(this); II != IE; II++) {
    II->second->dropReferenceFrom(II->first);
  } 
  for(DenseMap<const Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(BBs[i]) {

      ShadowBB* BB = BBs[i];

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	if(BB->insts[j].i.PB)
	  deleteIV(BB->insts[j].i.PB);

      }

      delete BB;

    }

  }

  delete[] BBs;

}

InlineAttempt::~InlineAttempt() {
  
  if(!isUnsharable())
    pass->removeSharableFunction(this);

  for(uint32_t i = 0; i < argShadows.size(); ++i) {

    if(argShadows[i].i.PB)
      deleteIV(argShadows[i].i.PB);

  }

  delete[] &(argShadows[0]);

}

void InlineAttempt::dropReferenceFrom(ShadowInstruction* SI) {

  if(Callers.size() == 1) {

    delete this;

  }
  else {

    SmallVector<ShadowInstruction*, 1>::iterator findit = std::find(Callers.begin(), Callers.end(), SI);
    release_assert(findit != Callers.end() && "Caller not in callers list?");
    Callers.erase(findit);

  }

}

PeelAttempt::~PeelAttempt() {

  release_assert(pass->IAs.size() > SeqNumber);
  pass->IAs[SeqNumber] = 0;

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
    delete *it;
  }

}
static uint32_t mainPhaseProgressN = 0;
const uint32_t mainPhaseProgressLimit = 1000;

IntegrationAttempt* InlineAttempt::getUniqueParent() {

  return uniqueParent;

}

IntegrationAttempt* PeelIteration::getUniqueParent() {

  return parent;

}

static void mainPhaseProgress() {

  mainPhaseProgressN++;
  if(mainPhaseProgressN == mainPhaseProgressLimit) {

    errs() << ".";
    mainPhaseProgressN = 0;

  }

}

// Does this instruction count for accounting / performance measurement? Essentially: can this possibly be improved?
bool llvm::instructionCounts(Instruction* I) {

  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

Module& IntegrationAttempt::getModule() {

  return *(F.getParent());

}

const Loop* IntegrationHeuristicsPass::applyIgnoreLoops(const Loop* L) {

  if(!L)
    return 0;

  Function* F = L->getHeader()->getParent();
  
  while(L && shouldIgnoreLoop(F, L->getHeader())) {

    L = L->getParentLoop();

  }

  return L;

}

const Loop* IntegrationAttempt::applyIgnoreLoops(const Loop* InstL) {

  return pass->applyIgnoreLoops(InstL);

}

bool IntegrationAttempt::edgeIsDead(ShadowBBInvar* BB1I, ShadowBBInvar* BB2I) {

  bool BB1InScope;

  if(ShadowBB* BB1 = getBB(BB1I->idx, &BB1InScope)) {

    return BB1->edgeIsDead(BB2I);

  }
  else if(BB1InScope) {

    // Source block doesn't exist despite being in scope, edge must be dead.
    return true;

  }

  return false;

}

bool IntegrationAttempt::edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I, bool ignoreThisScope) {

  if((!ignoreThisScope) && edgeIsDead(&BB1I, &BB2I))
    return true;

  if(BB1I.naturalScope == L)
    return false;
  
  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, BB1I.naturalScope))) {

    if(LPA->isTerminated()) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	if(!LPA->Iterations[i]->edgeIsDeadRising(BB1I, BB2I))
	  return false;
	
      }

      return true;

    }

  }
    
  return false;

}

bool IntegrationAttempt::blockIsDeadRising(ShadowBBInvar& BBI) {

  if(getBB(BBI))
    return false;

  if(BBI.naturalScope == L)
    return true;

  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, BBI.naturalScope))) {

    if(LPA->isTerminated()) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	if(!LPA->Iterations[i]->blockIsDeadRising(BBI))
	  return false;
	
      }

      return true;

    }

  }

  return true;

}

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


void IntegrationHeuristicsPass::initBlacklistedFunctions(Module& M) {

  uint32_t nfns = sizeof(blacklistedFnNames) / sizeof(blacklistedFnNames[0]);

  for(uint32_t i = 0; i != nfns; ++i) {

    if(Function* F = M.getFunction(blacklistedFnNames[i]))
      blacklistedFunctions.insert(F);

  }
   
}

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

bool IntegrationAttempt::callCanExpand(ShadowInstruction* SI, InlineAttempt*& Result) {

  if(InlineAttempt* IA = getInlineAttempt(SI)) {
    Result = IA;
    return true;
  }

  Result = 0;
  
  if(MaxContexts != 0 && pass->IAs.size() > MaxContexts)
    return false;

  Function* FCalled = getCalledFunction(SI);
  if(!FCalled) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it's an uncertain indirect call\n");
    return false;
  }

  if(FCalled->isDeclaration()) {
    LPDEBUG("Ignored " << itcache(*CI) << " because we don't know the function body\n");
    return false;
  }

  if(!shouldInlineFunction(SI, FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it shouldn't be inlined (not on certain path, and would cause recursion)\n");
    return false;
  }

  if(pass->yieldFunctions.count(FCalled))
    return false;

  if(pass->specialLocations.count(FCalled))
    return false;
  
  if(SpecialFunctionMap.count(FCalled))
    return false;

  if(functionIsBlacklisted(FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it is a special function we are not allowed to inline\n");
    return false;
  }

  return true;

}

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(ShadowInstruction* SI, bool ignoreScope, bool& created, bool& needsAnalyse) {

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

  LPDEBUG("Inlining " << FCalled->getName() << " at " << itcache(*CI) << "\n");

  return IA;

}

void InlineAttempt::releaseBackupStores() {

  release_assert(backupTlStore);
  backupTlStore->dropReference();
  backupTlStore = 0;
  release_assert(backupDSEStore);
  backupDSEStore->dropReference();
  backupDSEStore = 0;

}

void IntegrationAttempt::releaseMemoryPostCommit() {

  if(commitState == COMMIT_FREED)
    return;

  // For the time being, retain all data if the user will inspect it.
  if(IHPSaveDOTFiles) {
    commitState = COMMIT_FREED;
    return;
  }

  for(IAIterator it = child_calls_begin(this),
	itend = child_calls_end(this); it != itend; ++it) {

    it->second->releaseMemoryPostCommit();
    // IAs may only be referenced from us at present
    it->second->dropReferenceFrom(it->first);

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i) {

      it->second->Iterations[i]->releaseMemoryPostCommit();

    }

    delete it->second;

  }

  peelChildren.clear();

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBB* BB = getBB(i);

    if(BB) {

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &BB->insts[j];
	if(SI->i.PB)
	  deleteIV(SI->i.PB);

	{
	  DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = pass->trackedStores.find(SI);
	  if(findit != pass->trackedStores.end()) {
	    findit->second->isCommitted = true;
	    pass->trackedStores.erase(findit);
	  }
	}

	{
	  DenseMap<ShadowInstruction*, TrackedAlloc*>::iterator findit = pass->trackedAllocs.find(SI);
	  if(findit != pass->trackedAllocs.end()) {
	    findit->second->isCommitted = true;
	    pass->trackedAllocs.erase(findit);
	  }
	}

	pass->indirectDIEUsers.erase(SI);
	pass->memcpyValues.erase(SI);
	pass->forwardableOpenCalls.erase(SI);
	pass->resolvedReadCalls.erase(SI);
	pass->resolvedSeekCalls.erase(SI);

      }

      delete BB;
      
    }

  }

  delete[] BBs;
  BBs = 0;

  commitState = COMMIT_FREED;

}

void InlineAttempt::finaliseAndCommit(bool inLoopAnalyser) {

  countTentativeInstructions();
  collectStats();
	
  // This call will disable the context if it's not a good idea.
  findProfitableIntegration();

  if(isEnabled()) {

    // The TL and DSE stores were backed up to deal with the possibility
    // that the context would not be committed: we don't need those after all.
    releaseBackupStores();

    // Create residual blocks for disabled loops
    prepareCommitCall();

    if(!StatsFile.empty())
      preCommitStats(true);

    // Note any tests that require failed blocks.
    addCheckpointFailedBlocks();

    // Decide whether to commit in or out of line:
    findSaveSplits();

    runDIE();

    // Save a DOT representation if need be, for the GUI to use.
    saveDOT();

    // Finally, do it!
    commitCFG();
    commitArgsAndInstructions();

    postCommitOptimise();

  }
  else {

    // Save a DOT representation if need be, for the GUI to use.
    saveDOT();

    commitState = COMMIT_DONE;

    // Allocations and FD creations in this scope should be marked
    // committed without canonical value.
    markAllocationsAndFDsCommitted();

    // Child contexts may have generated code that we no longer care
    // to use. Delete it if so.
    releaseCommittedChildren();

    // Must rerun tentative load and DSE analyses accounting
    // for the fact that the stage will not be committed.
    rerunTentativeLoads(activeCaller, this, inLoopAnalyser);

    // For now this is simply a barrier to DSE.
    setAllNeededTop(backupDSEStore);
    backupDSEStore->dropReference();
    if(activeCaller->parent->dseStore) {
      activeCaller->parent->dseStore = activeCaller->parent->dseStore->getEmptyMap();
      activeCaller->parent->dseStore->allOthersClobbered = true;
    }

    if(!StatsFile.empty())
      preCommitStats(true);

  }

  // Free all ShadowBBs, ShadowInstructions and similar.
  releaseMemoryPostCommit();

}

// Return true if we ended up with an InlineAttempt available for this call.
bool IntegrationAttempt::analyseExpandableCall(ShadowInstruction* SI, bool& changed, bool inLoopAnalyser, bool inAnyLoop) {

  changed = false;

  bool created, needsAnalyse;
  InlineAttempt* IA = getOrCreateInlineAttempt(SI, false, created, needsAnalyse);

  if(IA) {

    IA->activeCaller = SI;

    if(needsAnalyse) {

      changed |= created;
      
      // Setting active = true prevents incomplete dependency information from being used
      // to justify sharing the function node.
      IA->active = true;

      changed |= IA->analyseWithArgs(SI, inLoopAnalyser, inAnyLoop, stack_depth);
      readsTentativeData |= IA->readsTentativeData;
      containsCheckedReads |= IA->containsCheckedReads;
      
      inheritDiagnosticsFrom(IA);
      mergeChildDependencies(IA);

      if(created && !IA->isUnsharable())
	pass->addSharableFunction(IA);
      else if(IA->registeredSharable && IA->isUnsharable())
	pass->removeSharableFunction(IA);
     
      IA->active = false;

      if(changed && IA->hasFailedReturnPath()) {

	// Must create a copy of this block for failure paths, starting at the call successor.
	getFunctionRoot()->markBlockAndSuccsFailed(SI->parent->invar->idx, SI->invar->idx + 1);

      }

      doCallStoreMerge(SI);

      if(!inLoopAnalyser) {
	    
	doTLCallMerge(SI->parent, IA);
	doDSECallMerge(SI->parent, IA);

	IA->finaliseAndCommit(inLoopAnalyser);

      }
      
    }
    else {

      IA->executeCall(stack_depth);

    }

  }

  return !!IA;

}

void PeelIteration::dropExitingStoreRef(uint32_t fromIdx, uint32_t toIdx) {

  ShadowBB* BB = getBB(fromIdx);
  if(BB && !edgeIsDead(BB->invar, getBBInvar(toIdx))) {

    if(BB->invar->naturalScope != L) {

      const Loop* ChildL = immediateChildLoop(L, BB->invar->naturalScope);
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

    BB->localStore->dropReference();

  }

}

void PeelIteration::dropExitingStoreRefs() {

  // We will never exit -- drop store refs that belong to exiting edges.

  ShadowLoopInvar* LInfo = parentPA->invarInfo;

  for(std::vector<std::pair<uint32_t, uint32_t> >::iterator it = LInfo->exitEdges.begin(),
	itend = LInfo->exitEdges.end(); it != itend; ++it) {
    
    dropExitingStoreRef(it->first, it->second);
    
  }

}

void PeelIteration::dropLatchStoreRef() {

  // If the last latch block was holding a store ref for the next iteration, drop it.
  ShadowBB* LatchBB = getBB(parentPA->invarInfo->latchIdx);
  ShadowBBInvar* HeaderBBI = getBBInvar(parentPA->invarInfo->headerIdx);
  
  if(!edgeIsDead(LatchBB->invar, HeaderBBI))
    LatchBB->localStore->dropReference();

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

void PeelIteration::checkFinalIteration() {

  // Check whether we now have evidence the loop terminates this time around
  // If it does, queue consideration of each exit PHI; by LCSSA these must belong to our parent.

  ShadowBBInvar* LatchBB = getBBInvar(parentPA->invarInfo->latchIdx);
  ShadowBBInvar* HeaderBB = getBBInvar(parentPA->invarInfo->headerIdx);

  if(edgeIsDead(LatchBB, HeaderBB) || pass->assumeEndsAfter(&F, L->getHeader(), iterationCount)) {

    iterStatus = IterationStatusFinal;

  }

}

PeelIteration* PeelAttempt::getIteration(unsigned iter) {

  if(Iterations.size() > iter)
    return Iterations[iter];

  return 0;

}

PeelIteration* PeelAttempt::getOrCreateIteration(unsigned iter) {

  if(PeelIteration* PI = getIteration(iter))
    return PI;

  //  if(MaxContexts != 0 && pass->SeqNumber > MaxContexts)
  //    return 0;
  
  LPDEBUG("Peeling iteration " << iter << " of loop " << L->getHeader()->getName() << "\n");

  mainPhaseProgress();

  assert(iter == Iterations.size());

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, iter, nesting_depth);
  Iterations.push_back(NewIter);
    
  return NewIter;

}

PeelIteration* PeelIteration::getNextIteration() {

  return parentPA->getIteration(this->iterationCount + 1);

}

bool PeelIteration::allExitEdgesDead() {

  for(std::vector<std::pair<uint32_t, uint32_t> >::iterator EI = parentPA->invarInfo->exitEdges.begin(), EE = parentPA->invarInfo->exitEdges.end(); EI != EE; ++EI) {

    if(!edgeIsDead(getBBInvar(EI->first), getBBInvar(EI->second))) {
      return false;
    }
  
  }

  return true;

}

PeelIteration* PeelIteration::getOrCreateNextIteration() {

  if(PeelIteration* Existing = getNextIteration())
    return Existing;

  if(iterStatus == IterationStatusFinal) {
    LPDEBUG("Loop known to exit: will not create next iteration\n");
    return 0;
  }

  std::pair<uint32_t, uint32_t>& OE = parentPA->invarInfo->optimisticEdge;

  bool willIterate = parentPA->invarInfo->alwaysIterate;

  if((!willIterate) && OE.first != 0xffffffff) {
    ShadowBBInvar* OE1 = getBBInvar(OE.first);
    ShadowBBInvar* OE2 = getBBInvar(OE.second);
    willIterate = edgeIsDead(OE1, OE2);
  }

  // Cancel iteration if the latch edge is outright killed.
  // Usually this is case due to optimistic edges and such, but could also result from
  // executing unreachable within the loop.
  if(willIterate) {
    ShadowBBInvar* latchBB = getBBInvar(parentPA->invarInfo->latchIdx);
    ShadowBBInvar* headerBB = getBBInvar(parentPA->invarInfo->headerIdx);
    if(edgeIsDead(latchBB, headerBB))
      return 0;
  }

  if(!willIterate)
    willIterate = allExitEdgesDead();

  if(!willIterate) {

    LPDEBUG("Won't peel loop " << L->getHeader()->getName() << " yet because at least one exit edge is still alive\n");
    return 0;
      
  }
  /*
  else if(iterationCount > 1000) {

    LPDEBUG("Won't peel loop " << L->getHeader()->getName() << ": max iterations 1000\n");
    return 0;

  }
  */

  //errs() << "Peel loop " << L->getHeader()->getName() << "\n";

  iterStatus = IterationStatusNonFinal;
  LPDEBUG("Loop known to iterate: creating next iteration\n");
  return parentPA->getOrCreateIteration(this->iterationCount + 1);

}

PeelAttempt* IntegrationAttempt::getPeelAttempt(const Loop* L) {

  DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.find(L);
  if(it != peelChildren.end())
    return it->second;

  return 0;

}

PeelAttempt* IntegrationAttempt::getOrCreatePeelAttempt(const Loop* NewL) {

  if(pass->shouldIgnoreLoop(&F, NewL->getHeader()))
    return 0;

  if(PeelAttempt* PA = getPeelAttempt(NewL))
    return PA;

  if(MaxContexts != 0 && pass->IAs.size() > MaxContexts)
    return 0;
 
  // Preheaders only have one successor (the header), so this is enough.
  
  ShadowBB* preheaderBB = getBB(invarInfo->LInfo[NewL]->preheaderIdx);
  if(!blockAssumedToExecute(preheaderBB)) {
   
    LPDEBUG("Will not expand loop " << NewL->getHeader()->getName() << " because the preheader is not certain/assumed to execute\n");
    return 0;

  }

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, NewL, nesting_depth + 1);
    peelChildren[NewL] = LPA;

    return LPA;

  }
  else {

    LPDEBUG("Won't explore loop with header " << NewL->getHeader()->getName() << " because it lacks a preheader, a latch, or both, or has multiple backedges\n");
    return 0;

  }

}

void InlineAttempt::getLiveReturnVals(SmallVector<ShadowValue, 4>& Vals) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(ShadowBB* BB = BBs[i]) {

      ShadowInstruction* TI = &(BB->insts.back());

      // The localStore check determines whether this block was
      // abandoned due to e.g. a call that cannot return.

      if(inst_is<ReturnInst>(TI) && BB->localStore)
	Vals.push_back(TI->getOperand(0));

    }

  }

}

void InlineAttempt::visitLiveReturnBlocks(ShadowBBVisitor& V) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(ShadowBB* BB = BBs[i]) {

      ShadowInstruction* TI = &(BB->insts.back());
      if(inst_is<ReturnInst>(TI))
	V.visit(BB, 0, false);

    }

  }

}

// Store->Load forwarding helpers:

BasicBlock* InlineAttempt::getEntryBlock() {

  return &F.getEntryBlock();

}

BasicBlock* PeelIteration::getEntryBlock() {
  
  return L->getHeader();

}

bool InlineAttempt::isRootMainCall() {

  return (!Callers.size()) && F.getName() == RootFunctionName;

}

bool llvm::isGlobalIdentifiedObject(ShadowValue V) {
  
  switch(V.t) {
  case SHADOWVAL_PTRIDX:
    return true;
  case SHADOWVAL_ARG:
    return V.u.A->IA->isRootMainCall();
  case SHADOWVAL_GV:
    return true;
  case SHADOWVAL_OTHER:
    return isIdentifiedObject(V.u.V);
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return false;
  default:
    release_assert(0 && "Bad value type in isGlobalIdentifiedObject");
    llvm_unreachable();
  }

}

void InlineAttempt::getVarArg(int64_t idx, ImprovedValSet*& Result) {

  release_assert(idx >= ImprovedVal::first_any_arg && idx < ImprovedVal::max_arg);
  uint32_t argIdx = idx - ImprovedVal::first_any_arg;

  // Skip past the normal args:
  argIdx += F.arg_size();

  if(argIdx < argShadows.size())
     copyImprovedVal(ShadowValue(&argShadows[argIdx]), Result);
  else {
    
    LPDEBUG("Vararg index " << idx << ": out of bounds\n");
    Result = newOverdefIVS();

  }

}

void PeelIteration::getVarArg(int64_t idx, ImprovedValSet*& Result) {

  parent->getVarArg(idx, Result);

}

void PeelIteration::describe(raw_ostream& Stream) const {

  Stream << "(Loop " << L->getHeader()->getName() << "/" << iterationCount << "/" << SeqNumber << ")";

}


void InlineAttempt::describe(raw_ostream& Stream) const {

  Stream << "(" << F.getName() << "/" << SeqNumber << ")";

}

void PeelIteration::describeBrief(raw_ostream& Stream) const {

  Stream << iterationCount;

}

void InlineAttempt::describeBrief(raw_ostream& Stream) const {

  Stream << F.getName();

}

// GDB callable:
void IntegrationAttempt::dump() const {

  describe(outs());

}

void InlineAttempt::printHeader(raw_ostream& OS) const {
  
  OS << (Callers.empty() ? "Root " : "") << "Function " << F.getName();
  if(isPathCondition)
    OS << " pathcond at " << Callers[0]->parent->invar->BB->getName();
  else if((!Callers.empty()) && F.getFunctionType()->getReturnType()->isVoidTy())
    OS << " at " << itcache(Callers[0], true);
  OS << " / " << SeqNumber;

}

void PeelIteration::printHeader(raw_ostream& OS) const {

  OS << "Loop " << L->getHeader()->getName() << " iteration " << iterationCount;
  OS << " / " << SeqNumber;

}

void PeelAttempt::printHeader(raw_ostream& OS) const {
  
  OS << "Loop " << L->getHeader()->getName();
  OS << " / " << SeqNumber;

}

std::string IntegrationAttempt::getFunctionName() {

  return F.getName();

}

void PeelAttempt::print(raw_ostream& OS) const {

  OS << nestingIndent() << "Loop " << L->getHeader()->getName() << (Iterations.back()->iterStatus == IterationStatusFinal ? "(terminated)" : "(not terminated)") << "\n";

  for(std::vector<PeelIteration*>::const_iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->print(OS);

  }

}

void IntegrationAttempt::print(raw_ostream& OS) const {

  OS << nestingIndent();
  printHeader(OS);
  OS << ": improved " << improvedInstructions << "/" << improvableInstructions << "\n";

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {
    it->second->print(OS);
  }

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

}

unsigned IntegrationAttempt::getTotalInstructions() {

  return improvableInstructions;

}

unsigned IntegrationAttempt::getElimdInstructions() {

  return improvedInstructions;

}

int64_t IntegrationAttempt::getTotalInstructionsIncludingLoops() {
  
  return improvableInstructionsIncludingLoops;

}

bool InlineAttempt::canDisable() {

  return Callers.size() == 1;

}

bool PeelIteration::canDisable() {

  return false;

}

std::string IntegrationAttempt::nestingIndent() const {

  return ind(nesting_depth * 2);

}

std::string PeelAttempt::nestingIndent() const {

  return ind(nesting_depth * 2);

}

// Implement data export functions:

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

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
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

void IntegrationAttempt::dumpMemoryUsage(int indent) {

  errs() << ind(indent);
  describeBrief(errs());

  for(IAIterator II = child_calls_begin(this), IE = child_calls_end(this); II != IE; II++) {
    II->second->dumpMemoryUsage(indent+2);
  } 
  for(DenseMap<const Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    PI->second->dumpMemoryUsage(indent+1);
  }

}

void PeelAttempt::dumpMemoryUsage(int indent) {

  errs() << ind(indent) << "Loop " << L->getHeader()->getName() << " (" << Iterations.size() << " iterations)\n";
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->dumpMemoryUsage(indent+1);

}

std::string InlineAttempt::getShortHeader() {
 
  if(isCommitted())
    return pass->shortHeaders[this];
 
  std::string ret;
  raw_string_ostream ROS(ret);
  printHeader(ROS);
  ROS.flush();
  return ret;

}

std::string PeelIteration::getShortHeader() {

  std::string ret;
  raw_string_ostream ROS(ret);
  ROS << "Iteration " << iterationCount;
  ROS.flush();
  return ret;

}

std::string PeelAttempt::getShortHeader() {

  std::string ret;
  raw_string_ostream ROS(ret);
  printHeader(ROS);
  ROS.flush();
  return ret;

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

bool llvm::allowTotalDefnImplicitCast(Type* From, Type* To) {

  if(From == To)
    return true;

  if(From->isPointerTy() && To->isPointerTy())
    return true;

  return false;

}

bool llvm::allowTotalDefnImplicitPtrToInt(Type* From, Type* To, DataLayout* TD) {

  return From->isPointerTy() && To->isIntegerTy() && TD->getTypeSizeInBits(To) >= TD->getTypeSizeInBits(From);

}

// Target == 0 -> don't care about the returned type.
Constant* llvm::extractAggregateMemberAt(Constant* FromC, int64_t Offset, Type* Target, uint64_t TargetSize, DataLayout* TD) {

  Type* FromType = FromC->getType();
  uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

  if(Offset == 0 && TargetSize == FromSize) {
    if(!Target)
      return FromC;
    if(allowTotalDefnImplicitCast(FromType, Target))
      return (FromC);
    else if(allowTotalDefnImplicitPtrToInt(FromType, Target, TD))
      return ConstantExpr::getPtrToInt(FromC, Target);
    DEBUG(dbgs() << "Can't use simple element extraction because load implies cast from " << (*(FromType)) << " to " << (*Target) << "\n");
    return 0;
  }

  if(Offset < 0 || Offset + TargetSize > FromSize) {

    DEBUG(dbgs() << "Can't use element extraction because offset " << Offset << " and size " << TargetSize << " are out of bounds for object with size " << FromSize << "\n");
    return 0;

  }

  if(isa<ConstantAggregateZero>(FromC) && Offset + TargetSize <= FromSize) {

    // Wholly subsumed within a zeroinitialiser:
    if(!Target) {
      Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
    }
    return (Constant::getNullValue(Target));

  }

  if(isa<UndefValue>(FromC)) {

    if(!Target)
      Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
    return UndefValue::get(Target);

  }

  uint64_t StartE, StartOff, EndE, EndOff;
  bool mightWork = false;

  if(ConstantArray* CA = dyn_cast<ConstantArray>(FromC)) {

    mightWork = true;
    
    Type* EType = CA->getType()->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;
    
    StartE = Offset / ESize;
    StartOff = Offset % ESize;
    EndE = (Offset + TargetSize) / ESize;
    EndOff = (Offset + TargetSize) % ESize;

  }
  else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(FromC)) {

    mightWork = true;

    const StructLayout* SL = TD->getStructLayout(CS->getType());
    if(!SL) {
      DEBUG(dbgs() << "Couldn't get struct layout for type " << *(CS->getType()) << "\n");
      return 0;
    }

    StartE = SL->getElementContainingOffset(Offset);
    StartOff = Offset - SL->getElementOffset(StartE);
    EndE = SL->getElementContainingOffset(Offset + TargetSize);
    EndOff = (Offset + TargetSize) - SL->getElementOffset(EndE);

  }

  if(mightWork) {
    if(StartE == EndE || (StartE + 1 == EndE && !EndOff)) {
      // This is a sub-access within this element.
      return extractAggregateMemberAt(cast<Constant>(FromC->getOperand(StartE)), StartOff, Target, TargetSize, TD);
    }
    DEBUG(dbgs() << "Can't use simple element extraction because load spans multiple elements\n");
  }
  else {
    DEBUG(dbgs() << "Can't use simple element extraction because load requires sub-field access\n");
  }

  return 0;

}

Constant* llvm::constFromBytes(unsigned char* Bytes, Type* Ty, DataLayout* TD) {

  if(Ty->isVectorTy() || Ty->isFloatingPointTy() || Ty->isIntegerTy()) {

    uint64_t TyBits = TD->getTypeSizeInBits(Ty);
    uint64_t TySize = TyBits / 8;
    Constant* IntResult = intFromBytes((const uint64_t*)Bytes, (TySize + 7) / 8, TyBits, Ty->getContext());
      
    if(Ty->isIntegerTy()) {
      assert(Ty == IntResult->getType());
      return IntResult;
    }
    else {
      assert(TD->getTypeSizeInBits(IntResult->getType()) == TD->getTypeSizeInBits(Ty));
      // We know the target type does not contain non-null pointers

      Constant* Result = ConstantExpr::getBitCast(IntResult, Ty); // The bitcast might eval here
      if(ConstantExpr* CE = dyn_cast_or_null<ConstantExpr>(Result))
	Result = ConstantFoldConstantExpression(CE, TD);
      if(!Result) {
	DEBUG(dbgs() << "Failed to fold casting " << *(IntResult) << " to " << *(Ty) << "\n");
	return 0;
      }
      else {
	return Result;
      }
    }
	
  }
  else if(Ty->isPointerTy()) {

    uint64_t PtrSize = TD->getTypeStoreSize(Ty);
    for(unsigned i = 0; i < PtrSize; ++i) {
      
      // Only null pointers can be synth'd from bytes
      if(Bytes[i])
	return 0;

    }

    return Constant::getNullValue(Ty);

  }
  else if(ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    if(ECount == 0) {
      DEBUG(dbgs() << "Can't produce a constant array of 0 length\n");
      return 0;
    }

    // I *think* arrays are always dense, i.e. it's for the child type to specify padding.
    Type* EType = ATy->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;
    std::vector<Constant*> Elems;
    Elems.reserve(ECount);

    uint64_t Offset = 0;
    for(uint64_t i = 0; i < ECount; ++i, Offset += ESize) {

      Constant* NextE = constFromBytes(&(Bytes[Offset]), EType, TD);
      if(!NextE)
	return 0;
      Elems.push_back(NextE);

    }

    return ConstantArray::get(ATy, Elems);
    
  }
  else if(StructType* STy = dyn_cast<StructType>(Ty)) {

    const StructLayout* SL = TD->getStructLayout(STy);
    if(!SL) {
      DEBUG(dbgs() << "Couldn't get struct layout for type " << *STy << "\n");
      return 0;
    }
    
    uint64_t ECount = STy->getNumElements();
    std::vector<Constant*> Elems;
    Elems.reserve(ECount);

    uint64_t EIdx = 0;
    for(StructType::element_iterator EI = STy->element_begin(), EE = STy->element_end(); EI != EE; ++EI, ++EIdx) {

      Type* EType = *EI;
      uint64_t EOffset = SL->getElementOffset(EIdx);
      Constant* NextE = constFromBytes(&(Bytes[EOffset]), EType, TD);
      if(!NextE)
	return 0;
      Elems.push_back(NextE);

    }

    return ConstantStruct::get(STy, Elems);

  }
  else {

    DEBUG(dbgs() << "Can't build a constant containing unhandled type " << (*Ty) << "\n");
    return 0;

  }

}

void IntegrationHeuristicsPass::print(raw_ostream &OS, const Module* M) const {
  RootIA->print(OS);
}

void IntegrationHeuristicsPass::releaseMemory(void) {
  if(RootIA) {
    delete RootIA;
    RootIA = 0;
  }

  std::string command;
  raw_string_ostream ROS(command);
  ROS << "rm -rf " << ihp_workdir;
  ROS.flush();
  
  if(system(command.c_str()) != 0) {

    errs() << "Warning: failed to delete " << ihp_workdir << "\n";

  }
  
}

/*
static Value* getWrittenPointer(Instruction* I) {

  if(StoreInst* SI = dyn_cast<StoreInst>(I))
    return SI->getPointerOperand();
  else if(MemIntrinsic* MI = dyn_cast<MemIntrinsic>(I))
    return MI->getDest();
  return 0;

}
*/

namespace llvm {

  void DSEDump(IntegrationAttempt*);
  void TLDump(IntegrationAttempt*);

}

static bool getFileSha1(std::string& Filename, unsigned char* hash) {

  SHA_CTX hashctx;
  if(!SHA1_Init(&hashctx)) {

    errs() << "SHA1_Init\n";
    return false;

  }
	
  int filefd = open(Filename.c_str(), O_RDONLY);
  if(filefd == -1) {
	  
    errs() << "Cannot open " << Filename << "\n";
    return false;

  }
	
  char readbuf[4096];
  int thisread;

  while((thisread = read(filefd, readbuf, 4096)) > 0) {

    if(!SHA1_Update(&hashctx, readbuf, thisread)) {

      errs() << "SHA1_Update\n";
      return false;

    }

  }

  if(thisread == -1) {

    errs() << "Read failed for " << Filename << "\n";
    close(filefd);
    return false;

  }

  if(!SHA1_Final(hash, &hashctx)) {

    errs() << "SHA1_Final\n";
    close(filefd);
    return false;;

  }

  close(filefd);
  return true;

}

static time_t getFileMtime(std::string& filename) {

  struct stat st;
  int ret = ::stat(filename.c_str(), &st);
  if(ret == -1) {

    errs() << "Failed to stat " << filename << "\n";
    return 0;

  }

  return st.st_mtime;
  
}

void IntegrationHeuristicsPass::writeLliowdConfig() {

  raw_ostream* Outp;
  std::auto_ptr<raw_fd_ostream> Fdp;

  if(llioConfigFile.empty()) {

    errs() << "No config file specified, writing to stdout\n";
    Outp = &outs();

  }
  else {

    std::string openerror;
    Fdp.reset(new raw_fd_ostream(llioConfigFile.c_str(), openerror));
    if(openerror.size()) {

      errs() << "Failed to open " << llioConfigFile << ", using stdout\n";
      Fdp.reset();
      Outp = &outs();

    }
    else {

      Outp = Fdp.get();

    }

  }

  raw_ostream& Out = *Outp;

  for(std::vector<std::string>::iterator it = llioDependentFiles.begin(),
	itend = llioDependentFiles.end(); it != itend; ++it) {

    SmallVector<char, 256> relPath;
    for(unsigned i = 0, ilim = it->size(); i != ilim; ++i)
      relPath.push_back((*it)[i]);

    llvm::sys::fs::make_absolute(relPath);

    StringRef printPath(relPath.data(), relPath.size());

    Out << "\t" << printPath << " " << getFileMtime(*it) << " ";

    unsigned char hash[SHA_DIGEST_LENGTH];

    if(getFileSha1(*it, hash)) {

      for(int i = 0; i < SHA_DIGEST_LENGTH; ++i) {

	if(hash[i]/16 == 0)
	  Out << '0';
	Out.write_hex(hash[i]);

      }

      Out << "\n";

    }

  }

}

void IntegrationHeuristicsPass::commit() {

  if(!(omitChecks || llioDependentFiles.empty())) {

    writeLliowdConfig();

    BasicBlock* preludeBlock = 0;

    if(llioPreludeStackIdx == -1) {

      Function* writePreludeFn = llioPreludeFn;
      if(llioPreludeFn == &RootIA->F)
	writePreludeFn = RootIA->CommitF;

      if(writePreludeFn)
	preludeBlock = &writePreludeFn->getEntryBlock();

    }

    // Add an lliowd_init() prelude to the beginning of the requested function:
    if(preludeBlock) {

      BasicBlock::iterator it = preludeBlock->begin();
      while(it != preludeBlock->end() && isa<AllocaInst>(it))
	++it;

      Type* Void = Type::getVoidTy(preludeBlock->getContext());
      Constant* WDInit = getGlobalModule()->getOrInsertFunction("lliowd_init", Void, NULL);
      CallInst::Create(WDInit, ArrayRef<Value*>(), "", it);

    }

  }

  if(!StatsFile.empty()) {

    postCommitStats();

    std::string error;
    raw_fd_ostream RFO(StatsFile.c_str(), error);
    if(!error.empty())
      errs() << "Failed to open " << StatsFile << ": " << error << "\n";
    else
      stats.print(RFO);
  }

  RootIA->F.replaceAllUsesWith(RootIA->CommitF);

  // Also exchange names so that external users will use this new version:
  std::string oldFName;
  {
    raw_string_ostream RSO(oldFName);
    RSO << RootIA->F.getName() << ".old";
  }

  RootIA->CommitF->takeName(&(RootIA->F));
  RootIA->F.setName(oldFName);

  errs() << "\n";

}

static void dieEnvUsage() {

  errs() << "--spec-env must have form N,filename where N is an integer\n";
  exit(1);

}

static void dieArgvUsage() {

  errs() << "--spec-argv must have form M,N,filename where M and N are integers\n";
  exit(1);

}

static void dieSpecUsage() {

  errs() << "--spec-param must have form N,param-spec where N is an integer\n";
  exit(1);

}

static bool parseIntCommaString(const std::string& str, long& idx, std::string& rest) {

  size_t splitIdx = str.find(',');

  if(splitIdx == std::string::npos || splitIdx == 0 || splitIdx == EnvFileAndIdx.size() - 1) {
    return false;
  }
  
  rest = str.substr(splitIdx + 1);
  std::string idxstr = str.substr(0, splitIdx);
  char* IdxEndPtr;
  idx = strtol(idxstr.c_str(), &IdxEndPtr, 10);
  
  if(IdxEndPtr - idxstr.c_str() != (int64_t)idxstr.size()) {
    return false;
  }
  
  return true;

}

static void parseFB(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB1) {

  std::string FName, BB1Name;
  size_t firstComma = arg.find(',');
  if(firstComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BB1Name = arg.substr(firstComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB1 = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BB1Name) {
      BB1 = FI;
      break;
    }

  }

  if(!BB1) {
    errs() << "No such block " << BB1Name << " in " << FName << "\n";
    exit(1);
  }

}

static void parseFBB(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB1, BasicBlock*& BB2) {

  std::string FName, BB1Name, BB2Name;
  size_t firstComma = arg.find(',');
  size_t secondComma = std::string::npos;
  if(firstComma != std::string::npos)
    secondComma = arg.find(',', firstComma+1);
  if(firstComma == std::string::npos || secondComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname,bbname\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BB1Name = arg.substr(firstComma + 1, (secondComma - firstComma) - 1);
  BB2Name = arg.substr(secondComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB1 = BB2 = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BB1Name)
      BB1 = FI;
    if(FI->getName() == BB2Name)
      BB2 = FI;

  }

  if(!BB1) {
    errs() << "No such block " << BB1Name << " in " << FName << "\n";
    exit(1);
  }
  if(!BB2) {
    errs() << "No such block " << BB2Name << " in " << FName << "\n";
    exit(1);
  }

}

static void parseFBI(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB, uint64_t& IOut) {

  std::string FName, BBName, IStr;
  size_t firstComma = arg.find(',');
  size_t secondComma = std::string::npos;
  if(firstComma != std::string::npos)
    secondComma = arg.find(',', firstComma+1);
  if(firstComma == std::string::npos || secondComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname,int\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BBName = arg.substr(firstComma + 1, (secondComma - firstComma) - 1);
  IStr = arg.substr(secondComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BBName)
      BB = FI;

  }

  if(!BB) {
    errs() << "No such block " << BBName << " in " << FName << "\n";
    exit(1);
  }

  char* IdxEndPtr;
  IOut = strtol(IStr.c_str(), &IdxEndPtr, 10);
  
  if(IdxEndPtr - IStr.c_str() != (int64_t)IStr.size()) {
    errs() << "Couldn't parse " << IStr << " as an integer\n";
    exit(1);
  }

}

void IntegrationHeuristicsPass::setParam(InlineAttempt* IA, long Idx, Constant* Val) {

  Type* Target = IA->F.getFunctionType()->getParamType(Idx);

  if(Val->getType() != Target) {

    errs() << "Type mismatch: constant " << *Val << " supplied for parameter of type " << *Target << "\n";
    exit(1);

  }

  ImprovedValSetSingle* ArgPB = newIVS();
  getImprovedValSetSingle(ShadowValue(Val), *ArgPB);
  if(ArgPB->Overdef || ArgPB->Values.size() != 1) {

    errs() << "Couldn't get a PB for " << *Val << "\n";
    exit(1);

  }

  IA->argShadows[Idx].i.PB = ArgPB;

}

static void ignoreAllLoops(SmallSet<BasicBlock*, 1>& IgnHeaders, const Loop* L) {

  IgnHeaders.insert(L->getHeader());
  for(Loop::iterator it = L->begin(), itend = L->end(); it != itend; ++it)
    ignoreAllLoops(IgnHeaders, *it);

}

#define CHECK_ARG(i, c) if(((uint32_t)i) >= c.size()) { errs() << "Function " << F.getName() << " has does not have a (zero-based) argument #" << i << "\n"; exit(1); }

static int64_t getInteger(std::string& s, const char* desc) {

  char* end;
  int64_t instIndex = strtoll(s.c_str(), &end, 10);
  if(s.empty() || *end) {
    errs() << desc << " not an integer\n";
    exit(1);
  }
  return instIndex;

}

static bool tryGetInteger(std::string& s, int64_t& out) {

  char* end;
  out = strtoll(s.c_str(), &end, 10);
  return !(s.empty() || *end);

}

uint32_t llvm::findBlock(ShadowFunctionInvar* SFI, StringRef name) {

  for(uint32_t i = 0; i < SFI->BBs.size(); ++i) {
    if(SFI->BBs[i].BB->getName() == name)
      return i;
  }  

  errs() << "Block " << name << " not found\n";
  exit(1);

}

uint32_t llvm::findBlock(ShadowFunctionInvar* SFI, BasicBlock* BB) {

  for(uint32_t i = 0; i < SFI->BBs.size(); ++i) {
    if(SFI->BBs[i].BB == BB)
      return i;
  }  

  errs() << "Block " << BB->getName() << " not found\n";
  exit(1);  

}

static BasicBlock* findBlockRaw(Function* F, std::string& name) {

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {
    if(((BasicBlock*)FI)->getName() == name)
      return FI;
  }

  errs() << "Block " << name << " not found\n";
  exit(1);

}

void IntegrationHeuristicsPass::parseArgs(Function& F, std::vector<Constant*>& argConstants, uint32_t& argvIdxOut) {

  this->mallocAlignment = MallocAlignment;
  
  if(EnvFileAndIdx != "") {

    long idx;
    std::string EnvFile;
    if(!parseIntCommaString(EnvFileAndIdx, idx, EnvFile))
      dieEnvUsage();

    CHECK_ARG(idx, argConstants);
    Constant* Env = loadEnvironment(*(F.getParent()), EnvFile);
    argConstants[idx] = Env;

  }

  if(ArgvFileAndIdxs != "") {

    long argcIdx;
    std::string ArgvFileAndIdx;
    if(!parseIntCommaString(ArgvFileAndIdxs, argcIdx, ArgvFileAndIdx))
      dieArgvUsage();
    long argvIdx;
    std::string ArgvFile;
    if(!parseIntCommaString(ArgvFileAndIdx, argvIdx, ArgvFile))
      dieArgvUsage();

    unsigned argc;
    loadArgv(&F, ArgvFile, argvIdx, argc);
    CHECK_ARG(argcIdx, argConstants);
    argConstants[argcIdx] = ConstantInt::get(Type::getInt32Ty(F.getContext()), argc);
    argvIdxOut = argvIdx;

  }

  for(cl::list<std::string>::const_iterator ArgI = SpecialiseParams.begin(), ArgE = SpecialiseParams.end(); ArgI != ArgE; ++ArgI) {

    long idx;
    std::string Param;
    if(!parseIntCommaString(*ArgI, idx, Param))
      dieSpecUsage();

    Type* ArgTy = F.getFunctionType()->getParamType(idx);
    
    if(ArgTy->isIntegerTy()) {

      char* end;
      int64_t arg = strtoll(Param.c_str(), &end, 10);
      if(end != (Param.c_str() + Param.size())) {

	errs() << "Couldn't parse " << Param << " as in integer\n";
	exit(1);

      }

      Constant* ArgC = ConstantInt::getSigned(ArgTy, arg);
      CHECK_ARG(idx, argConstants);
      argConstants[idx] = ArgC;

    }
    else if(PointerType* ArgTyP = dyn_cast<PointerType>(ArgTy)) {

      Type* StrTy = Type::getInt8PtrTy(F.getContext());
      Type* ElemTy = ArgTyP->getElementType();
      
      if(ArgTyP == StrTy) {

	Constant* Str = ConstantDataArray::getString(F.getContext(), Param);
	Constant* GStr = new GlobalVariable(Str->getType(), true, GlobalValue::InternalLinkage, Str, "specstr");
	Constant* Zero = ConstantInt::get(Type::getInt64Ty(F.getContext()), 0);
	Constant* GEPArgs[] = { Zero, Zero };
	Constant* StrPtr = ConstantExpr::getGetElementPtr(GStr, GEPArgs, 2);
	CHECK_ARG(idx, argConstants);
	argConstants[idx] = StrPtr;

      }
      else if(ElemTy->isFunctionTy()) {

	Constant* Found = F.getParent()->getFunction(Param);

	if(!Found) {

	  // Check for a zero value, indicating a null pointer.
	  char* end;
	  int64_t arg = strtoll(Param.c_str(), &end, 10);

	  if(arg || end != Param.c_str() + Param.size()) {

	    errs() << "Couldn't find a function named " << Param << "\n";
	    exit(1);

	  }

	  Found = Constant::getNullValue(ArgTyP);

	}

	CHECK_ARG(idx, argConstants);
	argConstants[idx] = Found;

      }
      else {

	errs() << "Setting pointers other than char* not supported yet\n";
	exit(1);

      }

    }
    else {

      errs() << "Argument type " << *(ArgTy) << " not supported yet\n";
      exit(1);

    }

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysInlineFunctions.begin(), ArgE = AlwaysInlineFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* AlwaysF = F.getParent()->getFunction(*ArgI);
    if(!AlwaysF) {
      errs() << "No such function " << *ArgI << "\n";
      exit(1);
    }
    alwaysInline.insert(AlwaysF);

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysExploreFunctions.begin(), ArgE = AlwaysExploreFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* AlwaysF = F.getParent()->getFunction(*ArgI);
    if(!AlwaysF) {
      errs() << "No such function " << *ArgI << "\n";
      exit(1);
    }
    alwaysExplore.insert(AlwaysF);

  }

  for(cl::list<std::string>::const_iterator ArgI = OptimisticLoops.begin(), ArgE = OptimisticLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LoopF;
    BasicBlock *BB1, *BB2;

    parseFBB("int-optimistic-loop", *ArgI, *(F.getParent()), LoopF, BB1, BB2);

    const Loop* L = LIs[LoopF]->getLoopFor(BB1);
    if(!L) {
      errs() << "Block " << BB1->getName() << " in " << LoopF->getName() << " not in a loop\n";
      exit(1);
    }
    
    optimisticLoopMap[L] = std::make_pair(BB1, BB2);

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysIterLoops.begin(), ArgE = AlwaysIterLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LoopF;
    BasicBlock *BB;

    parseFB("int-always-iterate", *ArgI, *(F.getParent()), LoopF, BB);

    const Loop* L = LIs[LoopF]->getLoopFor(BB);
    if(!L || (L->getHeader() != BB)) {
      errs() << "Block " << BB->getName() << " in " << LoopF->getName() << " not a loop header\n";
      exit(1);
    }
    
    alwaysIterLoops.insert(L);

  }

  for(cl::list<std::string>::const_iterator ArgI = AssumeEdges.begin(), ArgE = AssumeEdges.end(); ArgI != ArgE; ++ArgI) {

    Function* AssF;
    BasicBlock *BB1, *BB2;
    
    parseFBB("int-assume-edge", *ArgI, *(F.getParent()), AssF, BB1, BB2);

    assumeEdges[AssF].insert(std::make_pair(BB1, BB2));

  }

  for(cl::list<std::string>::const_iterator ArgI = IgnoreLoops.begin(), ArgE = IgnoreLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;

    parseFB("int-ignore-loop", *ArgI, *(F.getParent()), LF, HBB);

    ignoreLoops[LF].insert(HBB);

  }

  for(cl::list<std::string>::const_iterator ArgI = ExpandCallsLoops.begin(), ArgE = ExpandCallsLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;

    parseFB("int-expand-loop-calls", *ArgI, *(F.getParent()), LF, HBB);

    expandCallsLoops[LF].insert(HBB);

  }

  for(cl::list<std::string>::const_iterator ArgI = IgnoreLoopsWithChildren.begin(), ArgE = IgnoreLoopsWithChildren.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;

    parseFB("int-ignore-loop", *ArgI, *(F.getParent()), LF, HBB);
    const Loop* L = LIs[LF]->getLoopFor(HBB);
    if(!L || (L->getHeader() != HBB)) {
      errs() << "Block " << HBB->getName() << " in " << LF->getName() << " not a loop header\n";
      exit(1);
    }
    
    ignoreAllLoops(ignoreLoops[LF], L);

  }

  for(cl::list<std::string>::const_iterator ArgI = LoopMaxIters.begin(), ArgE = LoopMaxIters.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;
    uint64_t Count;
    
    parseFBI("int-loop-max", *ArgI, *(F.getParent()), LF, HBB, Count);

    maxLoopIters[std::make_pair(LF, HBB)] = Count;

  }

  for(cl::list<std::string>::const_iterator ArgI = SpecialLocations.begin(), ArgE = SpecialLocations.end(); ArgI != ArgE; ++ArgI) {

    std::istringstream istr(*ArgI);
    std::string fName, sizeStr;
    std::getline(istr, fName, ',');
    std::getline(istr, sizeStr, ',');

    if(fName.empty() || sizeStr.empty()) {

      errs() << "-int-special-location must have form function_name,size\n";
      exit(1);

    }

    Function* SpecF = F.getParent()->getFunction(fName);
    if(!SpecF) {

      errs() << "-int-special-location: no such function " << fName << "\n";
      exit(1);

    }

    int64_t size = getInteger(sizeStr, "-int-special-location size");
    SpecialLocationDescriptor& sd = specialLocations[SpecF];
    sd.storeSize = (uint64_t)size;
    ImprovedValSetSingle* Init = new ImprovedValSetSingle(ValSetTypeScalar);
    Init->setOverdef();
    sd.store.store = Init;
   
  }

  for(cl::list<std::string>::const_iterator ArgI = ModelFunctions.begin(), ArgE = ModelFunctions.end(); ArgI != ArgE; ++ArgI) {

    std::istringstream istr(*ArgI);
    std::string realFName, modelFName;
    std::getline(istr, realFName, ',');
    std::getline(istr, modelFName, ',');

    if(modelFName.empty() || realFName.empty()) {

      errs() << "-int-model-function must have form original_name,new_name";
      exit(1);

    }

    Function* realF = F.getParent()->getFunction(realFName);
    Function* modelF = F.getParent()->getFunction(modelFName);
    if((!realF) || !modelF) {

      errs() << "-int-model-function: no such function " << realFName << " or " << modelFName << "\n";
      exit(1);

    }

    modelFunctions[realF] = modelF;

  }

  for(cl::list<std::string>::const_iterator ArgI = YieldFunctions.begin(), ArgE = YieldFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* YieldF = F.getParent()->getFunction(*ArgI);
    if(!YieldF) {

      errs() << "-int-yield-function: no such function " << *ArgI << "\n";
      exit(1);

    }
    yieldFunctions.insert(YieldF);

  }

  for(cl::list<std::string>::iterator it = TargetStack.begin(), 
	itend = TargetStack.end(); it != itend; ++it) {
    
    std::string& thisCall = *it;
    
    std::string fName, bbName, instIdxStr;

    std::istringstream istr(thisCall);
    std::getline(istr, fName, ',');
    std::getline(istr, bbName, ',');
    std::getline(istr, instIdxStr, ',');

    if(fName.empty() || bbName.empty() || instIdxStr.empty()) {
      errs() << "int-target-stack must have form functionName,blockName,index\n";
      exit(1);
    }

    Function* StackF = F.getParent()->getFunction(fName);
    if(!StackF) {
      errs() << "Bad function in int-target-stack\n";
      exit(1);
    }

    BasicBlock* BB = findBlockRaw(StackF, bbName);
    uint32_t instIdx = (uint32_t)getInteger(instIdxStr, "int-target-stack instruction index");

    if(instIdx >= BB->size()) {
      errs() << "int-target-stack: call instruction index out of range\n";
      exit(1);
    }

    BasicBlock::iterator TestBI = BB->begin();
    std::advance(TestBI, instIdx);
    if((!isa<CallInst>(TestBI)) && (!isa<InvokeInst>(TestBI))) {
      errs() << "int-target-stack: index does not refer to a call or invoke\n";
      exit(1);
    }
    
    targetCallStack.push_back(std::make_pair(BB, instIdx));
    
  }

  for(cl::list<std::string>::iterator it = SimpleVolatiles.begin(),
	itend = SimpleVolatiles.end(); it != itend; ++it) {

    Function* LoadF;
    BasicBlock* BB;
    uint64_t Offset;

    parseFBI("int-simple-volatile-load", *it, *(F.getParent()), LoadF, BB, Offset);

    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);
    LoadInst* LI = dyn_cast<LoadInst>(BI);

    if(!LI) {
      errs() << "int-simple-volatile-load: " << *it << " does not denote a load\n";
      exit(1);
    }

    simpleVolatileLoads.insert(LI);

  }

  for(cl::list<std::string>::iterator it = LockDomains.begin(),
	itend = LockDomains.end(); it != itend; ++it) {

    Function* LockF;
    BasicBlock* BB;
    uint64_t Offset;

    // TODO here: add a better specification of lock domain than just a list of globals!

    size_t pos = 0;
    for(uint32_t i = 0; i < 3; ++i) {

      pos = it->find(',', pos);
      if(pos == std::string::npos) {
	errs() << "int-lock-domain: usage: lockf,lockblock,lockoffset,global1,...,globaln\n";
	exit(1);
      }
      ++pos;

    }

    std::string FBI(*it, 0, pos - 1);

    parseFBI("int-lock-domain", FBI, *(F.getParent()), LockF, BB, Offset);
    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);
    CallInst* CI = dyn_cast<CallInst>(BI);
    
    if(!CI) {
      errs() << "int-lock-domain: " << *it << " does not denote a call\n";
      exit(1);
    }

    std::vector<GlobalVariable*>& thisDomain = lockDomains[CI];

    std::string globals(*it, pos);

    std::istringstream istr(globals);
    while(!istr.eof()) {
      
      std::string thisGlobal;
      std::getline(istr, thisGlobal, ',');
      if(thisGlobal.empty())
	continue;
      GlobalVariable* GV = F.getParent()->getGlobalVariable(thisGlobal, true);
      if(!GV) {

	errs() << "Global not found: " << thisGlobal << "\n";
	exit(1);

      }
      thisDomain.push_back(GV);

    }

  }

  for(cl::list<std::string>::iterator it = PessimisticLocks.begin(),
	itend = PessimisticLocks.end(); it != itend; ++it) {

    Function* LockF;
    BasicBlock* BB;
    uint64_t Offset;

    parseFBI("int-pessimistic-lock", *it, *(F.getParent()), LockF, BB, Offset);
    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);
    CallInst* CI = dyn_cast<CallInst>(BI);
    
    if(!CI) {
      errs() << "int-pessimistic-lock: " << *it << " does not denote a call\n";
      exit(1);
    }

    pessimisticLocks.insert(CI);

  }
  
  for(cl::list<std::string>::iterator it = ForceNoAliasArgs.begin(),
	itend = ForceNoAliasArgs.end(); it != itend; ++it) {

    uint32_t argIdx = (uint32_t)getInteger(*it, "int-force-noalias-arg parameter");
    forceNoAliasArgs.insert(argIdx);
    
  }

  for(cl::list<std::string>::iterator it = VarAllocators.begin(),
	itend = VarAllocators.end(); it != itend; ++it) {

    std::string fName, idxStr, freeName, freeIdxStr;

    std::istringstream istr(*it);
    std::getline(istr, fName, ',');
    std::getline(istr, idxStr, ',');
    std::getline(istr, freeName, ',');
    std::getline(istr, freeIdxStr, ',');

    Function* allocF = F.getParent()->getFunction(fName);
    if(!allocF) {

      errs() << "-int-allocator-fn: must specify a function\n";
      exit(1);

    }

    uint32_t sizeParam = getInteger(idxStr, "int-allocator-fn second param");

    allocatorFunctions[allocF] = AllocatorFn::getVariableSize(sizeParam);
    SpecialFunctionMap[allocF] = SF_MALLOC;

    if(!freeName.empty()) {

      Function* freeF = F.getParent()->getFunction(freeName);
      if(!freeF) {

	errs() << "-int-allocator-fn: bad release function " << freeName << "\n";
	exit(1);

      }
      
      uint32_t releaseArg = getInteger(freeIdxStr, "int-allocator-fn fourth param");
      deallocatorFunctions[freeF] = DeallocatorFn(releaseArg);
      SpecialFunctionMap[freeF] = SF_FREE;

    }

  }

  for(cl::list<std::string>::iterator it = ConstAllocators.begin(),
	itend = ConstAllocators.end(); it != itend; ++it) {

    std::string fName, sizeStr, freeName, freeIdxStr, reallocName, reallocPtrIdxStr, reallocSizeIdxStr;

    std::istringstream istr(*it);
    std::getline(istr, fName, ',');
    std::getline(istr, sizeStr, ',');
    std::getline(istr, freeName, ',');
    std::getline(istr, freeIdxStr, ',');
    std::getline(istr, reallocName, ',');
    std::getline(istr, reallocPtrIdxStr, ',');
    std::getline(istr, reallocSizeIdxStr, ',');


    Function* allocF = F.getParent()->getFunction(fName);
    if(!allocF) {

      errs() << "-int-allocator-fn-const: must specify a function\n";
      exit(1);

    }

    uint32_t size = getInteger(sizeStr, "int-allocator-fn-const second param");

    IntegerType* I32 = Type::getInt32Ty(F.getContext());

    allocatorFunctions[allocF] = AllocatorFn::getConstantSize(ConstantInt::get(I32, size));
    SpecialFunctionMap[allocF] = SF_MALLOC;

    if(!freeName.empty()) {

      Function* freeF = F.getParent()->getFunction(freeName);
      if(!freeF) {

	errs() << "-int-allocator-fn: bad release function " << freeName << "\n";
	exit(1);

      }

      uint32_t releaseArg = getInteger(freeIdxStr, "int-allocator-fn fourth param");
      deallocatorFunctions[freeF] = DeallocatorFn(releaseArg);
      SpecialFunctionMap[freeF] = SF_FREE;

    }

    if(!reallocName.empty()) {

      Function* reallocF = F.getParent()->getFunction(reallocName);
      if(!reallocF) {

	errs() << "-int-allocator-fn: bad realloc function " << reallocName << "\n";
	exit(1);

      }

      uint32_t reallocPtrIdx = getInteger(reallocPtrIdxStr, "int-allocator-fn sixth param");
      uint32_t reallocSizeIdx = getInteger(reallocPtrIdxStr, "int-allocator-fn seventh param");
      reallocatorFunctions[reallocF] = ReallocatorFn(reallocPtrIdx, reallocSizeIdx);
      SpecialFunctionMap[reallocF] = SF_REALLOC;

    }

  }

  for(cl::list<std::string>::iterator it = NeverInline.begin(), itend = NeverInline.end(); it != itend; ++it) {

    Function* IgnoreF = F.getParent()->getFunction(*it);
    if(!IgnoreF) {

      errs() << "int-never-inline: no such function " << *it << "\n";
      exit(1);

    }

    blacklistedFunctions.insert(IgnoreF);

  }

  for(cl::list<std::string>::iterator it = SplitFunctions.begin(), itend = SplitFunctions.end(); it != itend; ++it) {

    Function* SplitF = F.getParent()->getFunction(*it);
    if(!SplitF) {

      errs() << "int-force-split: no such function " << *it << "\n";
      exit(1);

    }

    splitFunctions.insert(SplitF);

  }

  if(Function* libcMalloc = F.getParent()->getFunction("malloc"))
    allocatorFunctions[libcMalloc] = AllocatorFn::getVariableSize(0);
  if(Function* libcFree = F.getParent()->getFunction("free"))
    deallocatorFunctions[libcFree] = DeallocatorFn(0);
  if(Function* libcRealloc = F.getParent()->getFunction("realloc")) {
    deallocatorFunctions[libcRealloc] = DeallocatorFn(0);
    reallocatorFunctions[libcRealloc] = ReallocatorFn(0, 1);
  }

  this->verboseOverdef = VerboseOverdef;
  this->enableSharing = EnableFunctionSharing;
  this->verboseSharing = VerboseFunctionSharing;
  this->useDSA = UseDSA;
  this->verbosePCs = VerbosePathConditions;
  this->programSingleThreaded = SingleThreaded;
  this->useGlobalInitialisers = UseGlobalInitialisers;
  this->omitChecks = OmitChecks;
  if(this->omitChecks && !this->programSingleThreaded) {

    errs() << "omit-checks currently requires single-threaded\n";
    exit(1);

  }

  if(LLIOPreludeStackIdx != -1) {

    this->llioPreludeStackIdx = LLIOPreludeStackIdx;
    this->llioPreludeFn = 0;

  }
  else {

    this->llioPreludeStackIdx = -1;    
    if(Function* preludeFn = F.getParent()->getFunction(LLIOPreludeFn))
      this->llioPreludeFn = preludeFn;
    else
      this->llioPreludeFn = &F;

  }

  this->llioConfigFile = LLIOConfFile;

}

unsigned IntegrationHeuristicsPass::getMallocAlignment() {

  return mallocAlignment;

}

void IntegrationHeuristicsPass::runDSEAndDIE() {

  errs() << "Killing memory instructions";
  RootIA->tryKillStores(false, false);

  DEBUG(dbgs() << "Finding dead VFS operations\n");
  RootIA->tryKillAllVFSOps();

  DEBUG(dbgs() << "Finding remaining dead instructions\n");
  
  errs() << "\nKilling other instructions";
  
  RootIA->runDIE();
  
  errs() << "\n";

}

static Type* getTypeAtOffset(Type* Ty, uint64_t Offset) {

  PointerType* Ptr = dyn_cast<PointerType>(Ty);
  if(!Ptr)
    return 0;

  Type* ElTy = Ptr->getElementType();

  if(StructType* ST = dyn_cast<StructType>(ElTy)) {

    const StructLayout* SL = GlobalTD->getStructLayout(ST);
    unsigned FieldNo = SL->getElementContainingOffset(Offset);
    release_assert(SL->getElementOffset(FieldNo) == Offset && "Bad path condition alignment");
    return ST->getElementType(FieldNo);
    
  }
  else {

    return ElTy;

  }

}

BasicBlock* IntegrationHeuristicsPass::parsePCBlock(Function* fStack, std::string& bbName) {

  if(bbName == "__globals__")
    return 0;
  else if(bbName == "__args__")
    return (BasicBlock*)ULONG_MAX;
  else
    return findBlockRaw(fStack, bbName);
  
}

int64_t IntegrationHeuristicsPass::parsePCInst(BasicBlock* bb, Module* M, std::string& instIndexStr) {

  if(!bb) {
    GlobalVariable* GV = M->getGlobalVariable(instIndexStr, true);
    if(!GV) {

      errs() << "No global variable " << instIndexStr << "\n";
      exit(1);

    }
    return (int64_t)getShadowGlobalIndex(GV);
  }
  else
    return getInteger(instIndexStr, "Instruction index");

}

void IntegrationHeuristicsPass::parsePathConditions(cl::list<std::string>& L, PathConditionTypes Ty, InlineAttempt* IA) {

  uint32_t newGVIndex = 0;
  if(Ty == PathConditionTypeString)
    newGVIndex = std::distance(IA->F.getParent()->global_begin(), IA->F.getParent()->global_end());

  for(cl::list<std::string>::iterator it = L.begin(), itend = L.end(); it != itend; ++it) {

    std::string fStackIdxStr;
    std::string bbName;
    std::string instIndexStr;
    std::string assumeStr;
    std::string assumeStackIdxStr;
    std::string assumeBlock;
    std::string offsetStr;

    {
      std::istringstream istr(*it);
      std::getline(istr, fStackIdxStr, ',');
      std::getline(istr, bbName, ',');
      std::getline(istr, instIndexStr, ',');
      std::getline(istr, assumeStr, ',');
      std::getline(istr, assumeStackIdxStr, ',');
      std::getline(istr, assumeBlock, ',');
      std::getline(istr, offsetStr, ',');
    }

    if(fStackIdxStr.empty() || bbName.empty() || instIndexStr.empty() || assumeStr.empty() || assumeStackIdxStr.empty() || assumeBlock.empty()) {

      errs() << "Bad int path condtion\n";
      exit(1);

    }

    Function* fStack;

    int64_t fStackIdx;
    if(tryGetInteger(fStackIdxStr, fStackIdx)) {
      
      if(fStackIdx >= ((int64_t)targetCallStack.size())) {
	
	errs() << "Bad stack index\n";
	exit(1);

      }

      fStack = targetCallStack[fStackIdx].first->getParent();

    }
    else {

      fStack = IA->F.getParent()->getFunction(fStackIdxStr);
      if(!fStack) {

	errs() << "No function " << fStackIdxStr << "\n";
	exit(1);

      }

      fStackIdx = UINT_MAX;

    }

    BasicBlock* bb = parsePCBlock(fStack, bbName);
    int64_t instIndex = parsePCInst(bb, IA->F.getParent(), instIndexStr);
   
    uint32_t assumeStackIdx;
    Function* assumeF;
    if(fStackIdx != UINT_MAX) {

      assumeStackIdx = getInteger(assumeStackIdxStr, "Assume stack index");     

      if(assumeStackIdx >= targetCallStack.size()) {
	
	errs() << "Bad stack index\n";
	exit(1);
	
      }

      assumeF = targetCallStack[assumeStackIdx].first->getParent();

    }
    else {

      if(assumeStackIdxStr != fStackIdxStr) {

	errs() << "Non-stack path conditions must not make assumptions that cross function boundaries\n";
	exit(1);
	
      }

      assumeStackIdx = UINT_MAX;
      assumeF = fStack;

    }

    if(Ty == PathConditionTypeInt && assumeStackIdx != fStackIdx) {

      errs() << "SSA assumptions cannot cross function boundaries (assume about an argument instead)\n";
      exit(1);

    }

    BasicBlock* assumeBB = findBlockRaw(assumeF, assumeBlock);

    uint64_t offset = 0;
    if(!offsetStr.empty())
      offset = getInteger(offsetStr, "Path condition offset");

    Constant* assumeC;
    switch(Ty) {
    case PathConditionTypeInt:
    case PathConditionTypeIntmem:
      {
	int64_t assumeInt = getInteger(assumeStr, "Integer path condition");

	Type* targetType;
	if(bb) {
	  BasicBlock::iterator it = bb->begin();
	  std::advance(it, instIndex);
	  Instruction* assumeInst = it;
	  targetType = assumeInst->getType();
	}
	else if(bb == (BasicBlock*)ULONG_MAX) {
	  Function::arg_iterator it = fStack->arg_begin();
	  std::advance(it, instIndex);
	  Argument* A = it;
	  targetType = A->getType();
	}
	else {
	  GlobalVariable* GV = IA->F.getParent()->getGlobalVariable(instIndexStr, true);
	  targetType = GV->getType();
	}
	Type* ConstType;
	if(Ty == PathConditionTypeInt)
	  ConstType = targetType;
	else {
	  ConstType = getTypeAtOffset(targetType, offset);
	  release_assert(ConstType && "Failed to find assigned type for path condition");
	}
	release_assert((ConstType->isIntegerTy() || (ConstType->isPointerTy() && !assumeInt)) && "Instructions with an integer assumption must be integer typed");
	if(ConstType->isIntegerTy())
	  assumeC = ConstantInt::get(ConstType, assumeInt);
	else
	  assumeC = Constant::getNullValue(ConstType);
	break;
      }
    case PathConditionTypeFptr:
    case PathConditionTypeFptrmem:
      {
	int64_t Offset = 0;
	size_t plusOffset = assumeStr.find('+');
	if(plusOffset != std::string::npos) {
	  std::string offsetStr(assumeStr, plusOffset + 1);
	  Offset = getInteger(offsetStr, "Global value path condition +offset");
	  assumeStr = std::string(assumeStr, 0, plusOffset);
	}
	
	assumeC = IA->F.getParent()->getNamedValue(assumeStr);
	if(!assumeC) {
	  errs() << "No such global value: " << assumeStr << "\n";
	  exit(1);
	}

	if(Offset != 0) {
	  
	  if(assumeC->getType() != GInt8Ptr)
	    assumeC = ConstantExpr::getBitCast(assumeC, GInt8Ptr);
	  assumeC = ConstantExpr::getGetElementPtr(assumeC, ConstantInt::get(GInt64, Offset));

	}

	break;
      }
    case PathConditionTypeString:
      {
	GlobalVariable* NewGV = getStringArray(assumeStr, *IA->F.getParent(), /*addNull=*/true);
	assumeC = NewGV;
	// Register the new global:
	shadowGlobals[newGVIndex].G = NewGV;
	shadowGlobalsIdx[NewGV] = newGVIndex;
	shadowGlobals[newGVIndex].storeSize = 0;
	++newGVIndex;
	break;
      }
    case PathConditionTypeStream:
      assumeC = (Constant*)strdup(assumeStr.c_str());
      break;
    case PathConditionTypeGlobalInit:
      {
	release_assert((!bb) && "Unmodified global assumption relating to a non-global?");
	GlobalVariable* GV = shadowGlobals[instIndex].G;
	assumeC = GV->getInitializer();
	break;
      }
    default:
      release_assert(0 && "Bad path condition type");
      llvm_unreachable();
    }

    PathCondition newCond((uint32_t)fStackIdx, 
			  bb, 
			  (uint32_t)instIndex, 
			  assumeStackIdx, 
			  assumeBB, 
			  assumeC, 
			  offset);

    if(fStackIdx == UINT_MAX) {

      // Path condition applies to all instances of some function -- attach it to the invarInfo
      // for that function.

      ShadowFunctionInvar* invarInfo = getFunctionInvarInfo(*fStack);
      if(!invarInfo->pathConditions)
	invarInfo->pathConditions = new PathConditions();
      invarInfo->pathConditions->addForType(newCond, Ty);

    }
    else {

      pathConditions.addForType(newCond, Ty);

    }

  }

}

static bool getAllocSitesFrom(Value* V, std::vector<Value*>& sites, DenseSet<Value*>& seenValues) {

  if(!seenValues.insert(V).second)
    return true;

  if(isa<GlobalVariable>(V)) {
    
    sites.push_back(V);
    return true;

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {

    Function* F = A->getParent();
    if(F->hasAddressTaken(0)) {

      sites.clear();
      return false;

    }

    for(Value::use_iterator it = F->use_begin(), itend = F->use_end(); it != itend; ++it) {

      if(Instruction* I = dyn_cast<Instruction>(*it)) {

	CallSite CS(I);
	if(!getAllocSitesFrom(CS.getArgument(A->getArgNo()), sites, seenValues))
	  return false;
	
      }

    }

    return true;

  }
  else if(Instruction* I = dyn_cast<Instruction>(V)) {

    switch(I->getOpcode()) {

    case Instruction::Alloca:
      sites.push_back(V);
      return true;
    case Instruction::Call:
    case Instruction::Invoke:
      {
	ImmutableCallSite CS(I);
	if(CS.paramHasAttr(0, Attributes::NoAlias)) {
	  sites.push_back(V);
	  return true;
	}
	break;
      }
    case Instruction::GetElementPtr:
    case Instruction::BitCast:
      return getAllocSitesFrom(I->getOperand(0), sites, seenValues);
    case Instruction::PHI:
      {
	PHINode* PN = cast<PHINode>(I);
	for(uint32_t i = 0, ilim = PN->getNumIncomingValues(); i != ilim; ++i)
	  if(!getAllocSitesFrom(PN->getIncomingValue(i), sites, seenValues))
	    return false;
	return true;
      }
    default:
      break;
    }

    sites.clear();
    return false;

  }
  else {

    sites.clear();
    return false;

  }

}

static void getAllocSites(Argument* A, std::vector<Value*>& sites) {

  DenseSet<Value*> seenValues;
  getAllocSitesFrom(A, sites, seenValues);

}

void IntegrationHeuristicsPass::createPointerArguments(InlineAttempt* IA) {

  // Try to establish if any incoming pointer arguments are known not to alias
  // the globals, or each other. If so, allocate each a heap slot.

  std::vector<std::vector<Value*> > argAllocSites;
  
  Function::arg_iterator AI = IA->F.arg_begin(), AE = IA->F.arg_end();
  for(uint32_t i = 0; AI != AE; ++i, ++AI) {

    argAllocSites.push_back(std::vector<Value*>());

    Argument* A = AI;
    if(A->getType()->isPointerTy()) {

      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IA->argShadows[i].i.PB);
      if(IVS->SetType == ValSetTypeOldOverdef) {

	std::vector<Value*>& allocs = argAllocSites.back();

	if(forceNoAliasArgs.count(i)) {

	  // Not an allocation site, but doesn't matter for this purpose:
	  // This will force us to conclude the argument doesn't alias globals
	  // or any other arguments.
	  allocs.push_back(A);

	}
	else {

	  // This will leave argAllocSites empty on failure:
	  getAllocSites(A, allocs);

	}

	if(!allocs.empty()) {

	  IVS->SetType = ValSetTypePB;

	  // Create a new heap location for this argument if it has any non-global constituents.
	  // Just note any globals in the alias list.
	  bool anyNonGlobals = false;
	  for(std::vector<Value*>::iterator it = allocs.begin(), itend = allocs.end(); it != itend; ++it) {
	    
	    if(GlobalVariable* GV = dyn_cast<GlobalVariable>(*it)) {
	      
	      ShadowGV* SGV = &shadowGlobals[getShadowGlobalIndex(GV)];
	      IVS->Values.push_back(ImprovedVal(ShadowValue(SGV), 0));

	    }
	    else if(!anyNonGlobals) {

	      // Create location:
	      argStores[i] = ArgStore(heap.size());
	      heap.push_back(AllocData());
	      heap.back().allocIdx = heap.size() - 1;
	      heap.back().isCommitted = false;
	      heap.back().allocValue = ShadowValue(&IA->argShadows[i]);
	      heap.back().allocType = IA->argShadows[i].getType();
	      anyNonGlobals = true;

	    }

	  }

	}

      }

    }
    
  }

  // Now for each argument for which we found a bounded set of alloc sites,
  // give it an initial pointer set corresponding to each other arg it may alias.

  for(uint32_t i = 0, ilim = IA->F.arg_size(); i != ilim; ++i) {

    ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IA->argShadows[i].i.PB);
    std::vector<Value*>& allocs = argAllocSites[i];
    if(!allocs.empty()) {

      // Add each pointer argument location this /may/ alias:
      for(uint32_t j = 0, jlim = IA->F.arg_size(); j != jlim; ++j) {
	
	if(!argAllocSites[j].empty()) {
	  
	  std::vector<Value*>& otherallocs = argAllocSites[j];
	  for(std::vector<Value*>::iterator it = otherallocs.begin(), itend = otherallocs.end(); it != itend; ++it) {
	    
	    if(isa<GlobalVariable>(*it))
	      continue;

	    if(std::find(allocs.begin(), allocs.end(), *it) != allocs.end()) {

	      // i and j share a non-global allocation site, so arg i may alias arg j.
	      
	      IVS->Values.push_back(ImprovedVal(ShadowValue(&IA->argShadows[j]), 0));
	      break;

	    }
    
	  }

	}

      }

    }

  }

}

void IntegrationHeuristicsPass::parseArgsPostCreation(InlineAttempt* IA) {

  for(cl::list<std::string>::iterator it = IgnoreBlocks.begin(), itend = IgnoreBlocks.end();
      it != itend; ++it) {

    std::string fName;
    std::string bbName;
    {
      std::istringstream istr(*it);
      std::getline(istr, fName, ',');
      std::getline(istr, bbName, ',');
    }

    if(fName != IA->F.getName()) {

      errs() << "int-ignore-block currently only supported in the root function\n";
      exit(1);

    }

    IA->addIgnoredBlock(bbName);

  }

  parsePathConditions(PathConditionsInt, PathConditionTypeInt, IA);
  parsePathConditions(PathConditionsFptr, PathConditionTypeFptr, IA);
  parsePathConditions(PathConditionsString, PathConditionTypeString, IA);
  parsePathConditions(PathConditionsIntmem, PathConditionTypeIntmem, IA);  
  parsePathConditions(PathConditionsFptrmem, PathConditionTypeFptrmem, IA);
  parsePathConditions(PathConditionsStream, PathConditionTypeStream, IA);
  parsePathConditions(PathConditionsGlobalInit, PathConditionTypeGlobalInit, IA);

  for(cl::list<std::string>::iterator it = PathConditionsFunc.begin(), 
	itend = PathConditionsFunc.end(); it != itend; ++it) {

    std::string fStackIdxStr;
    std::string bbName;
    std::string calledName;
    std::string verifyName;
    std::istringstream istr(*it);

    {
      std::getline(istr, fStackIdxStr, ',');
      std::getline(istr, bbName, ',');
      std::getline(istr, calledName, ',');
      std::getline(istr, verifyName, ',');
    }

    if(fStackIdxStr.empty() || bbName.empty() || calledName.empty() || verifyName.empty()) {

      errs() << "-int-path-condition-func usage: context-function,context-block,path-function,verify-function" << "\n";
      exit(1);

    }

    int64_t fStackIdx;
    Function* callerFunction;

    if(tryGetInteger(fStackIdxStr, fStackIdx)) {

      if(fStackIdx >= (int64_t)targetCallStack.size()) {
	errs() << "Bad stack index for path function\n";
	exit(1);
      }

      callerFunction = targetCallStack[fStackIdx].first->getParent();

    }
    else {

      callerFunction = IA->F.getParent()->getFunction(fStackIdxStr);
      if(!callerFunction) {

	errs() << "No such function " << fStackIdxStr << "\n";
	exit(1);

      }

      fStackIdx = UINT_MAX;

    }
    
    BasicBlock* assumeBlock = findBlockRaw(callerFunction, bbName);
    Function* CallF = IA->F.getParent()->getFunction(calledName);
    Function* VerifyF = IA->F.getParent()->getFunction(verifyName);

    if(!CallF) {
      
      errs() << "No such function " << calledName << "\n";
      exit(1);

    }
    
    if(!VerifyF) {

      errs() << "No such function " << verifyName << "\n";
      exit(1);

    }

    if(!VerifyF->getFunctionType()->getReturnType()->isIntegerTy()) {

      errs() << "Verification functions must return an integer\n";
      exit(1);

    }

    FunctionType* FType = CallF->getFunctionType();
    PathConditions* PC;

    if(fStackIdx == UINT_MAX) {

      ShadowFunctionInvar* SFI = getFunctionInvarInfo(*callerFunction);
      if(!SFI->pathConditions)
	SFI->pathConditions = new PathConditions();
      PC = SFI->pathConditions;

    }
    else {

      PC = &pathConditions;

    }

    PC->FuncPathConditions.push_back(PathFunc(fStackIdx, assumeBlock, CallF, VerifyF));
    PathFunc& newFunc = PC->FuncPathConditions.back();

    while(!istr.eof()) {

      std::string argStackIdxStr;
      std::string argBBStr;
      std::string argIdxStr;
      std::getline(istr, argStackIdxStr, ',');
      std::getline(istr, argBBStr, ',');
      std::getline(istr, argIdxStr, ',');

      uint32_t argStackIdx;
      Function* fStack;

      if(fStackIdx == UINT_MAX) {

	if(argStackIdxStr != fStackIdxStr) {

	  errs() << "Non-stack path functions can only use local arguments\n";
	  exit(1);

	}

	argStackIdx = UINT_MAX;
	fStack = callerFunction;

      }
      else {

	argStackIdx = getInteger(argStackIdxStr, "Path function argument stack index");
	fStack = targetCallStack[argStackIdx].first->getParent();

      }

      BasicBlock* argBB = parsePCBlock(fStack, argBBStr);
      int64_t argInstIdx = parsePCInst(argBB, IA->F.getParent(), argIdxStr);
      newFunc.args.push_back(PathFuncArg(argStackIdx, argBB, argInstIdx));

    }

    release_assert(FType->getNumParams() == newFunc.args.size() && "Path function with wrong arg count");
  
  }

}

void IntegrationHeuristicsPass::createSpecialLocations() {

  for(SmallDenseMap<Function*, SpecialLocationDescriptor>::iterator it = specialLocations.begin(),
	itend = specialLocations.end(); it != itend; ++it) {
    
    it->second.heapIdx = (int32_t)heap.size();
    heap.push_back(AllocData());
    heap.back().allocIdx = heap.size() - 1;
    heap.back().isCommitted = false;
    heap.back().allocValue = ShadowValue(it->first);
    heap.back().allocType = it->first->getFunctionType()->getReturnType();

  }

}

Type* llvm::GInt8Ptr;
Type* llvm::GInt8;
Type* llvm::GInt16;
Type* llvm::GInt32;
Type* llvm::GInt64;

char llvm::ihp_workdir[] = "/tmp/ihp_XXXXXX";

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  if(!mkdtemp(ihp_workdir)) {
    errs() << "Failed to create " << ihp_workdir << "\n";
    exit(1);
  }

  TD = getAnalysisIfAvailable<DataLayout>();
  GlobalTD = TD;
  AA = &getAnalysis<AliasAnalysis>();
  GlobalAA = AA;
  GlobalTLI = getAnalysisIfAvailable<TargetLibraryInfo>();
  if(UseDSA) {
    errs() << "Loading DSA...";
    GlobalDSA = &getAnalysis<EQTDDataStructures>();
    errs() << "done\n";
  }
  GlobalIHP = this;
  GInt8Ptr = Type::getInt8PtrTy(M.getContext());
  GInt8 = Type::getInt8Ty(M.getContext());
  GInt16 = Type::getInt16Ty(M.getContext());
  GInt32 = Type::getInt32Ty(M.getContext());
  GInt64 = Type::getInt64Ty(M.getContext());

  persistPrinter = getPersistPrinter(&M);

  initMRInfo(&M);
  
  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    if(!MI->isDeclaration()) {
      DominatorTree* NewDT = new DominatorTree();
      NewDT->runOnFunction(*MI);
      DTs[MI] = NewDT;
      LoopInfo* NewLI = new LoopInfo();
      NewLI->runOnFunction(*MI, NewDT);
      LIs[MI] = NewLI;
    }

  }

  Function* FoundF = M.getFunction(RootFunctionName);
  if((!FoundF) || FoundF->isDeclaration()) {

    errs() << "Function " << RootFunctionName << " not found or not defined in this module\n";
    return false;

  }

  Function& F = *FoundF;

  // Mark realloc as an identified object if the function is defined:
  if(Function* Realloc = M.getFunction("realloc")) {

    Realloc->setDoesNotAlias(0);

  }

  DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");

  std::vector<Constant*> argConstants(F.arg_size(), 0);
  uint32_t argvIdx = 0xffffffff;
  parseArgs(F, argConstants, argvIdx);

  populateGVCaches(&M);
  initSpecialFunctionsMap(M);
  // Last parameter: reserve extra GV slots for the constants that path condition parsing will produce.
  initShadowGlobals(M, PathConditionsString.size());
  initBlacklistedFunctions(M);

  InlineAttempt* IA = new InlineAttempt(this, F, 0, 0);
  if(targetCallStack.size()) {

    IA->setTargetCall(targetCallStack[0], 0);

  }

  // Note ignored blocks and path conditions:
  parseArgsPostCreation(IA);

  // Now that all globals have grabbed heap slots, insert extra locations per special function.
  createSpecialLocations();

  argStores = new ArgStore[F.arg_size()];
  
  for(unsigned i = 0; i < F.arg_size(); ++i) {

    if(argConstants[i])
      setParam(IA, i, argConstants[i]);
    else {
      ImprovedValSetSingle* IVS = newIVS();
      IVS->SetType = ValSetTypeOldOverdef;
      IA->argShadows[i].i.PB = IVS;
    }

  }

  if(argvIdx != 0xffffffff) {

    ImprovedValSetSingle* NewIVS = newIVS();
    NewIVS->set(ImprovedVal(ShadowValue(&IA->argShadows[argvIdx]), 0), ValSetTypePB);
    IA->argShadows[argvIdx].i.PB = NewIVS;
    argStores[argvIdx] = ArgStore(heap.size());
    heap.push_back(AllocData());
    heap.back().allocIdx = heap.size() - 1;
    heap.back().isCommitted = false;
    heap.back().allocValue = ShadowValue(&IA->argShadows[argvIdx]);
    heap.back().allocType = IA->argShadows[argvIdx].getType();

  }

  createPointerArguments(IA);
  initGlobalFDStore();

  RootIA = IA;

  errs() << "Interpreting";
  IA->analyse();
  IA->finaliseAndCommit(false);
  fixNonLocalUses();
  errs() << "\n";
  
  if(IHPSaveDOTFiles) {

    // Function sharing is now decided, and hence the graph structure, so create
    // graph tags for the GUI.
    rootTag = RootIA->createTag(0);

  }
    
  return false;

}

void IntegrationHeuristicsPass::getAnalysisUsage(AnalysisUsage &AU) const {
  
  AU.addRequired<AliasAnalysis>();
  AU.addRequired<DominatorTree>();
  AU.addRequired<LoopInfo>();
  const PassInfo* BAAInfo = lookupPassInfo(StringRef("basicaa"));
  if(!BAAInfo) {
    errs() << "Couldn't load Basic AA!";
  }
  else {
    AU.addRequiredID(BAAInfo->getTypeInfo());
  }
  if(UseDSA)
    AU.addRequired<EQTDDataStructures>();
  //AU.setPreservesAll();
  
}

Module* llvm::getGlobalModule() {

  return GlobalIHP->RootIA->F.getParent();

}

bool llvm::IHPSaveDOTFiles = true;
