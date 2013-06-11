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
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/PHITransAddr.h"
#include "llvm/Analysis/VFSCallModRef.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/DataLayout.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"

#include <string>
#include <algorithm>

#include <stdlib.h>

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
static cl::opt<bool> SkipBenefitAnalysis("skip-benefit-analysis");
static cl::opt<bool> SkipDIE("skip-int-die");
static cl::opt<unsigned> MaxContexts("int-stop-after", cl::init(0));
static cl::opt<bool> VerboseOverdef("int-verbose-overdef");

ModulePass *llvm::createIntegrationHeuristicsPass() {
  return new IntegrationHeuristicsPass();
}

static RegisterPass<IntegrationHeuristicsPass> X("intheuristics", "Score functions for pervasive integration benefit",
						 false /* Only looks at CFG */,
						 true /* Analysis Pass */);

IntegrationAttempt::~IntegrationAttempt() {
  for(DenseMap<CallInst*, InlineAttempt*>::iterator II = inlineChildren.begin(), IE = inlineChildren.end(); II != IE; II++) {
    delete (II->second);
  } 
  for(DenseMap<const Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }
}

InlineAttempt::InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, 
			     DenseMap<Function*, LoopInfo*>& LI, ShadowInstruction* _CI, int depth, int sdepth) : 
  IntegrationAttempt(Pass, P, F, 0, LI, depth, sdepth),
  CI(_CI)
  { 
    raw_string_ostream OS(HeaderStr);
    OS << (!CI ? "Root " : "") << "Function " << F.getName();
    if(CI && !CI->getType()->isVoidTy())
      OS << " at " << itcache(CI, true);
    SeqNumber = Pass->getSeq();
    OS << " / " << SeqNumber;
    prepareShadows();

    // If this function can't allocate stack memory don't give it a frame number.
    if(invarInfo->frameSize == -1)
      --stack_depth;


  }

PeelIteration::PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, 
			     Function& F, DenseMap<Function*, LoopInfo*>& _LI, int iter, int depth, int sdepth) :
  IntegrationAttempt(Pass, P, F, PP->L, _LI, depth, sdepth),
  iterationCount(iter),
  parentPA(PP),
  iterStatus(IterationStatusUnknown)
{ 
  raw_string_ostream OS(HeaderStr);
  OS << "Loop " << L->getHeader()->getName() << " iteration " << iterationCount;
  SeqNumber = Pass->getSeq();
  OS << " / " << SeqNumber;
  prepareShadows();
}

PeelAttempt::PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, 
			 DenseMap<Function*, LoopInfo*>& _LI, const Loop* _L, int depth, int sdepth) 
  : pass(Pass), parent(P), F(_F), LI(_LI), 
    residualInstructions(-1), nesting_depth(depth), stack_depth(sdepth), L(_L), totalIntegrationGoodness(0), nDependentLoads(0)
{

  this->tag.ptr = (void*)this;
  this->tag.type = IntegratorTypePA;

  raw_string_ostream OS(HeaderStr);
  OS << "Loop " << L->getHeader()->getName();
  SeqNumber = Pass->getSeq();
  OS << " / " << SeqNumber;
  
  invarInfo = parent->invarInfo->LInfo[L];

  getOrCreateIteration(0);

}

PeelAttempt::~PeelAttempt() {
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
    delete *it;
  }
}
static uint32_t mainPhaseProgressN = 0;
const uint32_t mainPhaseProgressLimit = 1000;

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

// Calls a given callback at the *parent* scope associated with loop LScope
void IntegrationAttempt::callWithScope(Callable& C, const Loop* LScope) {

  if(LScope == L)
    C.callback(this);
  else
    parent->callWithScope(C, LScope);

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

InlineAttempt* IntegrationAttempt::getInlineAttempt(CallInst* CI) {

  DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(const_cast<CallInst*>(CI));
  if(it != inlineChildren.end())
    return it->second;

  return 0;

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
   "uname"
   
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
  else if(!parent)
    return false;
  
  return parent->stackIncludesCallTo(FCalled);

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

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(ShadowInstruction* SI, bool ignoreScope, bool& created) {

  created = false;
  CallInst* CI = cast_inst<CallInst>(SI);

  if(ignoreIAs.count(CI))
    return 0;

  if(InlineAttempt* IA = getInlineAttempt(CI))
    return IA;

  if(MaxContexts != 0 && pass->SeqNumber > MaxContexts)
    return 0;

  Function* FCalled = getCalledFunction(SI);
  if(!FCalled) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it's an uncertain indirect call\n");
    return 0;
  }

  if(FCalled->isDeclaration()) {
    LPDEBUG("Ignored " << itcache(*CI) << " because we don't know the function body\n");
    return 0;
  }

  if(!shouldInlineFunction(SI, FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it shouldn't be inlined (not on certain path, and would cause recursion)\n");
    return 0;
  }

  //if(L != SI->invar->scope && !ignoreScope) {
    // This can happen with always-inline functions. Should really fix whoever tries to make the inappropriate call.
  //return 0;
  //}

  if(functionIsBlacklisted(FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it is a special function we are not allowed to inline\n");
    return 0;
  }

  //errs() << "Inline new fn " << FCalled->getName() << "\n";
  mainPhaseProgress();

  created = true;

  InlineAttempt* IA = new InlineAttempt(pass, this, *FCalled, this->LI, SI, this->nesting_depth + 1, this->stack_depth + 1);
  inlineChildren[CI] = IA;

  LPDEBUG("Inlining " << FCalled->getName() << " at " << itcache(*CI) << "\n");

  return IA;

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

  if(MaxContexts != 0 && pass->SeqNumber > MaxContexts)
    return 0;
  
  LPDEBUG("Peeling iteration " << iter << " of loop " << L->getHeader()->getName() << "\n");

  mainPhaseProgress();

  assert(iter == Iterations.size());

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, LI, iter, nesting_depth, stack_depth);
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

  if(ignorePAs.count(NewL))
    return 0;

  if(pass->shouldIgnoreLoop(&F, NewL->getHeader()))
    return 0;

  if(PeelAttempt* PA = getPeelAttempt(NewL))
    return PA;

  if(MaxContexts != 0 && pass->SeqNumber > MaxContexts)
    return 0;
 
  // Preheaders only have one successor (the header), so this is enough.
  
  ShadowBB* preheaderBB = getBB(invarInfo->LInfo[NewL]->preheaderIdx);
  if(!blockAssumedToExecute(preheaderBB)) {
   
    LPDEBUG("Will not expand loop " << NewL->getHeader()->getName() << " because the preheader is not certain/assumed to execute\n");
    return 0;

  }

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, LI, NewL, nesting_depth + 1, stack_depth);
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
      if(inst_is<ReturnInst>(TI))
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

bool IntegrationAttempt::hasParent() {

  return (parent != 0);

}

bool IntegrationAttempt::isRootMainCall() {

  return (!this->parent) && F.getName() == RootFunctionName;

}

bool llvm::isGlobalIdentifiedObject(ShadowValue V) {
  
  switch(V.t) {
  case SHADOWVAL_INST:
    return isIdentifiedObject(V.u.I->invar->I);
  case SHADOWVAL_ARG:
    return V.u.A->IA->isRootMainCall();
  case SHADOWVAL_GV:
    return true;
  case SHADOWVAL_OTHER:
    return isIdentifiedObject(V.u.V);
  default:
    release_assert(0 && "Bad value type in isGlobalIdentifiedObject");
    llvm_unreachable();
  }

}

void InlineAttempt::getVarArg(int64_t idx, ImprovedValSetSingle& Result) {

  release_assert(idx >= ImprovedVal::first_any_arg && idx < ImprovedVal::max_arg);
  uint32_t argIdx = idx - ImprovedVal::first_any_arg;

  CallInst* RawCI = cast_inst<CallInst>(CI);

  // Skip past the normal args:
  argIdx += F.arg_size();

  if(argIdx < RawCI->getNumArgOperands())
    getImprovedValSetSingle(CI->getCallArgOperand(argIdx), Result);
  else {
    
    LPDEBUG("Vararg index " << idx << ": out of bounds\n");
    Result = ImprovedValSetSingle();

  }

}

void PeelIteration::getVarArg(int64_t idx, ImprovedValSetSingle& Result) {

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

void IntegrationAttempt::printHeader(raw_ostream& OS) const {
  
  OS << HeaderStr;

}

void PeelAttempt::printHeader(raw_ostream& OS) const {
  
  OS << HeaderStr;

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
  if(unexploredLoops.size()) {
    OS << nestingIndent() << "Unexplored loops:\n";
    for(SmallVector<const Loop*, 4>::const_iterator it = unexploredLoops.begin(), it2 = unexploredLoops.end(); it != it2; ++it) {
      OS << nestingIndent() << "  " << (*it)->getHeader()->getName() << "\n";
    }
  }
  if(unexploredCalls.size()) {
    OS << nestingIndent() << "Unexplored calls:\n";
    for(SmallVector<CallInst*, 4>::const_iterator it = unexploredCalls.begin(), it2 = unexploredCalls.end(); it != it2; ++it) {
      OS << nestingIndent() << itcache(**it) << "\n";
    }
  }

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {
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

  return parent != 0;

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

  return inlineChildren.size() || peelChildren.size();

}

bool PeelAttempt::hasChildren() {
  
  return Iterations.size() != 0;

}

unsigned IntegrationAttempt::getNumChildren() {

  return inlineChildren.size() + peelChildren.size();

}

unsigned PeelAttempt::getNumChildren() {

  return Iterations.size();

}

IntegratorTag* IntegrationAttempt::getChildTag(unsigned idx) {

  if(idx < inlineChildren.size()) {
    DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin();
    for(unsigned i = 0; i < idx; ++i, ++it) {}
    return &(it->second->tag);
  }
  else {
    assert(idx < (inlineChildren.size() + peelChildren.size()) && "Child tag index out of range");
    DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin();
    for(unsigned i = 0; i < (idx - inlineChildren.size()); ++i, ++it) {}
    return &(it->second->tag);    
  }

}

void IntegrationAttempt::dumpMemoryUsage(int indent) {

  errs() << ind(indent);
  describeBrief(errs());
  errs() << ": "
	 << "foc " << forwardableOpenCalls.size()
	 << " rrc " << resolvedReadCalls.size() << " rsc " << resolvedSeekCalls.size()
	 << " rcc " << resolvedCloseCalls.size() << "\n";

  for(DenseMap<CallInst*, InlineAttempt*>::iterator II = inlineChildren.begin(), IE = inlineChildren.end(); II != IE; II++) {
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

IntegratorTag* PeelAttempt::getChildTag(unsigned idx) {

  assert(idx < Iterations.size() && "getChildTag index out of range");
  return &(Iterations[idx]->tag);

}

std::string InlineAttempt::getShortHeader() {
  
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

IntegratorTag* InlineAttempt::getParentTag() {

  if(!parent)
    return 0;
  else
    return &(parent->tag);

}

IntegratorTag* PeelIteration::getParentTag() {

  return &(parentPA->tag);

}

IntegratorTag* PeelAttempt::getParentTag() {

  return &(parent->tag);

}

IntegrationAttempt* IntegrationAttempt::searchFunctions(std::string& search, IntegrationAttempt*& startAt) {

  if(startAt == this) {
    
    startAt = 0;

  }
  else if(!startAt) {

    if(getShortHeader().find(search) != std::string::npos) {
      
      return this;

    }

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(IntegrationAttempt* SubRes = it->second->searchFunctions(search, startAt))
      return SubRes;

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i) {

      if(IntegrationAttempt* SubRes = it->second->Iterations[i]->searchFunctions(search, startAt))
	return SubRes;

    }

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
    EndOff = Offset - SL->getElementOffset(StartE);

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

void IntegrationHeuristicsPass::commit() {

  if(!SkipDIE)
    rerunDSEAndDIE();

  errs() << "Writing specialised module";

  std::string Name;
  {
    raw_string_ostream RSO(Name);
    RSO << RootIA->getCommittedBlockPrefix() << ".clone_root";
  }
  RootIA->CommitF = cloneEmptyFunction(&(RootIA->F), RootIA->F.getLinkage(), Name);
  RootIA->returnBlock = 0;
  RootIA->commitCFG();
  RootIA->commitArgsAndInstructions();
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

  ImprovedValSetSingle ArgPB;
  getImprovedValSetSingle(ShadowValue(Val), ArgPB);
  if(ArgPB.Overdef || ArgPB.Values.size() != 1) {

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

  this->verboseOverdef = VerboseOverdef;

}

unsigned IntegrationHeuristicsPass::getMallocAlignment() {

  return mallocAlignment;

}

void IntegrationHeuristicsPass::runDSEAndDIE() {

  errs() << "Killing memory instructions";

  DEBUG(dbgs() << "Finding dead MTIs\n");
  RootIA->tryKillAllMTIs();

  DEBUG(dbgs() << "Finding dead stores\n");
  RootIA->tryKillAllStores();

  DEBUG(dbgs() << "Finding dead allocations\n");
  RootIA->tryKillAllAllocs();

  DEBUG(dbgs() << "Finding dead VFS operations\n");
  RootIA->tryKillAllVFSOps();

  DEBUG(dbgs() << "Finding remaining dead instructions\n");
  
  errs() << "\nKilling other instructions";
  
  RootIA->runDIE();
  
  errs() << "\n";

}

LocStore& IntegrationHeuristicsPass::getArgStore(ShadowArg* A) {

  release_assert(A->IA == RootIA && "ShadowArg used as object but not root IA?");
  return argvStore;

}

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<DataLayout>();
  GlobalTD = TD;
  AA = &getAnalysis<AliasAnalysis>();
  GlobalAA = AA;
  GlobalVFSAA = &getAnalysis<VFSCallAliasAnalysis>();
  GlobalTLI = getAnalysisIfAvailable<TargetLibraryInfo>();
  GlobalIHP = this;
  
  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    if(!MI->isDeclaration()) {
      DominatorTree* NewDT = new DominatorTree();
      NewDT->runOnFunction(*MI);
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
  initShadowGlobals(M);
  initBlacklistedFunctions(M);

  argvStore.store = new ImprovedValSetSingle(ValSetTypeUnknown, true);

  InlineAttempt* IA = new InlineAttempt(this, 0, F, LIs, 0, 0, 0);

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    if(argConstants[i])
      setParam(IA, i, argConstants[i]);
    else 
      IA->argShadows[i].i.PB.setOverdef();

  }

  if(argvIdx != 0xffffffff) {

    IA->argShadows[argvIdx].i.PB = ImprovedValSetSingle(ImprovedVal(ShadowValue(&IA->argShadows[argvIdx]), 0), ValSetTypePB);

  }

  RootIA = IA;

  errs() << "Interpreting";
  IA->analyse();
  errs() << "\n";

  if(!SkipDIE) {

    runDSEAndDIE();

  }

  IA->collectStats();

  if(!SkipBenefitAnalysis) {
    errs() << "Picking integration candidates";
    estimateIntegrationBenefit();
    errs() << "\n";
  }

  IA->prepareCommit();

  if(!SkipDIE)
    rerunDSEAndDIE();

  if(!GraphOutputDirectory.empty()) {

    IA->describeTreeAsDOT(GraphOutputDirectory);

  }
    
  return false;

}

void IntegrationHeuristicsPass::getAnalysisUsage(AnalysisUsage &AU) const {
  
  AU.addRequired<AliasAnalysis>();
  AU.addRequired<LoopInfo>();
  const PassInfo* BAAInfo = lookupPassInfo(StringRef("basicaa"));
  if(!BAAInfo) {
    errs() << "Couldn't load Basic AA!";
  }
  else {
    AU.addRequiredID(BAAInfo->getTypeInfo());
  }
  AU.addRequired<VFSCallAliasAnalysis>();
  AU.setPreservesAll();
  
}

