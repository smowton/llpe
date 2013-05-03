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

ModulePass *llvm::createIntegrationHeuristicsPass() {
  return new IntegrationHeuristicsPass();
}

static RegisterPass<IntegrationHeuristicsPass> X("intheuristics", "Score functions for pervasive integration benefit",
						 false /* Only looks at CFG */,
						 true /* Analysis Pass */);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

IntegrationAttempt::~IntegrationAttempt() {
  for(DenseMap<CallInst*, InlineAttempt*>::iterator II = inlineChildren.begin(), IE = inlineChildren.end(); II != IE; II++) {
    delete (II->second);
  } 
  for(DenseMap<const Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }
}

InlineAttempt::InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, 
			     DenseMap<Function*, LoopInfo*>& LI, ShadowInstruction* _CI, int depth) : 
  IntegrationAttempt(Pass, P, F, 0, LI, depth),
  CI(_CI)
  { 
    raw_string_ostream OS(HeaderStr);
    OS << (!CI ? "Root " : "") << "Function " << F.getName();
    if(CI && !CI->getType()->isVoidTy())
      OS << " at " << itcache(CI, true);
    SeqNumber = Pass->getSeq();
    OS << " / " << SeqNumber;
    prepareShadows();
  }

PeelIteration::PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, 
			     Function& F, DenseMap<Function*, LoopInfo*>& _LI, int iter, int depth) :
  IntegrationAttempt(Pass, P, F, PP->L, _LI, depth),
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
			 DenseMap<Function*, LoopInfo*>& _LI, const Loop* _L, int depth) 
  : pass(Pass), parent(P), F(_F), LI(_LI), 
    residualInstructions(-1), nesting_depth(depth), L(_L), totalIntegrationGoodness(0), nDependentLoads(0)
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

bool IntegrationAttempt::edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I) {

  if(edgeIsDead(&BB1I, &BB2I))
    return true;

  if(BB1I.naturalScope == L)
    return false;
  
  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, BB1I.naturalScope))) {

    PeelIteration* FinalIter = LPA->Iterations.back();
    if(FinalIter->iterStatus == IterationStatusFinal) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	if(!LPA->Iterations[i]->edgeIsDeadRising(BB1I, BB2I))
	  return false;
	
      }

      return true;

    }

  }
    
  return false;

}

InlineAttempt* IntegrationAttempt::getInlineAttempt(CallInst* CI) {

  DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(const_cast<CallInst*>(CI));
  if(it != inlineChildren.end())
    return it->second;

  return 0;

}

bool llvm::functionIsBlacklisted(Function* F) {

  return (F->getName() == "malloc" || F->getName() == "free" ||
	  F->getName() == "realloc" || F->getName() == "ioctl" ||
	  F->getName() == "gettimeofday" || F->getName() == "clock_gettime" ||
	  F->getName() == "time" ||
	  F->getName() == "open" || F->getName() == "read" ||
	  F->getName() == "llseek" || F->getName() == "lseek" ||
	  F->getName() == "lseek64" || F->getName() == "close" ||
	  F->getName() == "write" || 
	  F->getName() == "__libc_fcntl" ||
	  F->getName() == "posix_fadvise" ||
	  F->getName() == "stat" ||
	  F->getName() == "isatty" ||
	  F->getName() == "__libc_sigaction" ||
	  F->getName() == "socket" || F->getName() == "bind" ||
	  F->getName() == "listen" || F->getName() == "setsockopt" ||
	  F->getName() == "_exit" || F->getName() == "__libc_accept" ||
	  F->getName() == "poll" || F->getName() == "shutdown" ||
	  F->getName() == "mkdir" ||
	  F->getName() == "__libc_nanosleep" ||
	  F->getName() == "rename" ||
	  F->getName() == "setgid" ||
	  F->getName() == "setuid" ||
	  F->getName() == "__fcntl_nocancel" ||
	  F->getName() == "closedir" ||
	  F->getName() == "opendir" ||
	  F->getName() == "getsockname" ||
	  F->getName() == "__libc_recvfrom" ||
	  F->getName() == "__libc_sendto" ||
	  F->getName() == "mmap" ||
	  F->getName() == "munmap" ||
	  F->getName() == "mremap" ||
	  F->getName() == "clock_getres" ||
	  F->getName() == "fstat" ||
	  F->getName() == "getegid" ||
	  F->getName() == "geteuid" ||
	  F->getName() == "getgid" ||
	  F->getName() == "getrlimit" ||
	  F->getName() == "getuid" ||
	  F->getName() == "rmdir" ||
	  F->getName() == "sigprocmask" ||
	  F->getName() == "unlink" ||
	  F->getName() == "__getdents64" ||
	  F->getName() == "brk" ||
	  F->getName() == "getpid" ||
	  F->getName() == "kill" ||
	  F->getName() == "uname");

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

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(ShadowInstruction* SI, bool ignoreScope) {

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

  if(L != SI->invar->scope && !ignoreScope) {
    // This can happen with always-inline functions. Should really fix whoever tries to make the inappropriate call.
    return 0;
  }

  if(functionIsBlacklisted(FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it is a special function we are not allowed to inline\n");
    return 0;
  }

  //errs() << "Inline new fn " << FCalled->getName() << "\n";
  mainPhaseProgress();

  InlineAttempt* IA = new InlineAttempt(pass, this, *FCalled, this->LI, SI, this->nesting_depth + 1);
  inlineChildren[CI] = IA;

  LPDEBUG("Inlining " << FCalled->getName() << " at " << itcache(*CI) << "\n");

  return IA;

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

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, LI, iter, nesting_depth);
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
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, LI, NewL, nesting_depth + 1);
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
  
  if(ShadowInstruction* SI = V.getInst()) {
    return isIdentifiedObject(SI->invar->I);
  }
  else if(ShadowArg* SA = V.getArg()) {
    return SA->IA->isRootMainCall();
  }
  else {
    return isIdentifiedObject(V.getVal());
  }

}

void InlineAttempt::getVarArg(int64_t idx, PointerBase& Result) {

  unsigned numNonFPArgs = 0;
  unsigned numFPArgs = 0;

  uint32_t argIdx = 0xffffffff;

  CallInst* RawCI = cast_inst<CallInst>(CI);

  for(unsigned i = F.arg_size(); i < CI->getNumArgOperands(); ++i) {

    Value* Arg = RawCI->getArgOperand(i);
    if(Arg->getType()->isPointerTy() || Arg->getType()->isIntegerTy()) {
      if(idx < ImprovedVal::first_fp_arg && idx == numNonFPArgs) {
	argIdx = i;
	break;
      }
      numNonFPArgs++;
    }
    else if(Arg->getType()->isFloatingPointTy()) {
      if(idx >= ImprovedVal::first_fp_arg && (idx - ImprovedVal::first_fp_arg) == numFPArgs) {
	argIdx = i;
	break;
      }
      numFPArgs++;
    }

  }

  if(argIdx < CI->getNumArgOperands())
    getPointerBase(CI->getCallArgOperand(argIdx), Result);
  else {
    
    LPDEBUG("Vararg index " << idx << ": out of bounds\n");
    Result = PointerBase();

  }

}

void PeelIteration::getVarArg(int64_t idx, PointerBase& Result) {

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

Constant* llvm::extractAggregateMemberAt(Constant* FromC, int64_t Offset, Type* Target, uint64_t TargetSize, DataLayout* TD) {

  Type* FromType = FromC->getType();
  uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

  if(Offset == 0 && TargetSize == FromSize) {
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

      assert(!Bytes[i]);

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

void IntegrationHeuristicsPass::createInvariantScopes(Function* F, DenseMap<Instruction*, const Loop*>*& pInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>*& pEdges, DenseMap<BasicBlock*, const Loop*>*& pBlocks) {

  pInsts = invariantInstScopes[F] = new DenseMap<Instruction*, const Loop*>();
  pEdges = invariantEdgeScopes[F] = new DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>();
  pBlocks = invariantBlockScopes[F] = new DenseMap<BasicBlock*, const Loop*>();

  LoopInfo* LI = LIs[F];

  DEBUG(dbgs() << "Discovering loop invariants for function " << F->getName() << "\n");

  bool improvedThisTime;

  do {

    improvedThisTime = false;

    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

      BasicBlock* BB = FI;
      const Loop* instLoop = LI->getLoopFor(BB);
      for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

	Instruction* I = BI;
	const Loop* innermostLoop = 0;

	// Skip instructions that can't be evaluated in any case, and loads because we'd need to do a bunch more analysis to establish that they're really invariant.
	// Also skip PHIs for now, since their invariance depends upon edge invariance.
	// TODO: fix this to interleave instruction invariance and edge invariance.
	if(I->mayReadFromMemory() || I->mayWriteToMemory() || isa<PHINode>(I) || isa<AllocaInst>(I))
	  continue;
	if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
	  if(!BI->isConditional())
	    continue;
	}
	if(isa<CallInst>(I) || isa<InvokeInst>(I)) {
	  // Invariant calls are very silly! Surely this means it is really variant thanks to side-effects via globals or the like.
	  // Possible future improvement: spot whether a call really is invariant (i.e. looks invariant and is pure) whilst expanding it for the first time and promote it.
	  continue;
	}

	for (unsigned i = 0, e = I->getNumOperands(); i != e; ++i) {
	  Value* Op = I->getOperand(i);
	  if(Instruction* OpI = dyn_cast<Instruction>(Op)) {
	    // LCSSA form means this loop must be somewhere in instLoop's ancestors (including instLoop itself), not a sibling.
	    DenseMap<Instruction*, const Loop*>::iterator Improved = pInsts->find(OpI);
	    const Loop* OpL;
	    if(Improved != pInsts->end())
	      OpL = Improved->second;
	    else
	      OpL = LI->getLoopFor(OpI->getParent());
	    if(OpL == instLoop) {
	      // Common case: this is a common or garden variant. Nothing to see here.
	      innermostLoop = instLoop;
	      break;
	    }
	    else if((!innermostLoop) || innermostLoop->contains(OpL)) {
	      innermostLoop = OpL;
	    }
	  }
	}

	if(((!innermostLoop) && instLoop) || (innermostLoop && (innermostLoop != instLoop) && innermostLoop->contains(instLoop))) {
	  
	  DenseMap<Instruction*, const Loop*>::iterator Existing = pInsts->find(I);
	  if(Existing != pInsts->end() && Existing->second == innermostLoop)
	    continue;
	  improvedThisTime = true;
	  // An interesting invariant! But which kind?
	  if(Existing != pInsts->end())
	    Existing->second = innermostLoop;
	  else
	    (*pInsts)[I] = innermostLoop;
	  DEBUG(dbgs() << "Instruction " << *I << " loop invariant: will evaluate in scope " << (innermostLoop ? innermostLoop->getHeader()->getName() : "'root'") << "\n");
	  if(TerminatorInst* TI = dyn_cast<TerminatorInst>(I)) {
	    unsigned NumSucc = TI->getNumSuccessors();
	    for (unsigned i = 0; i != NumSucc; ++i) {
	      DEBUG(dbgs() << "\tincluding edge " << BB->getName() << " -> " << TI->getSuccessor(i)->getName() << "\n");
	      (*pEdges)[std::make_pair(BB, TI->getSuccessor(i))] = innermostLoop;
	    }
	  }
	}

      }

    }

  } while(improvedThisTime);

  // Now figure out blocks which can be killed as an invariant, and consequently further edges, and so on.
  SmallVector<BasicBlock*, 4> WQ1;
  SmallVector<BasicBlock*, 4> WQ2;
  SmallVector<BasicBlock*, 4>* ConsumeQ = &WQ1;
  SmallVector<BasicBlock*, 4>* ProduceQ = &WQ2;

  for(DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>::iterator it = pEdges->begin(), it2 = pEdges->end(); it != it2; ++it) {

    ConsumeQ->push_back(it->first.second);

  }

  while(ConsumeQ->size()) {

    for(SmallVector<BasicBlock*, 4>::iterator WI = ConsumeQ->begin(), WE = ConsumeQ->end(); WI != WE; ++WI) {

      BasicBlock* CheckBB = *WI;
      const Loop* innermostPred = 0;
      bool shouldSkip = false;
      const Loop* CheckBBL = LI->getLoopFor(CheckBB);
      
      for(pred_iterator PI = pred_begin(CheckBB), PE = pred_end(CheckBB); PI != PE; ++PI) {

	DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>::iterator EdgeIt = pEdges->find(std::make_pair(*PI, CheckBB));
	if(EdgeIt == pEdges->end()) {
	  // The edge is a plain old variant, and so the block is too.
	  shouldSkip = true;
	  break;
	}
	else {
	  const Loop* edgeL = EdgeIt->second;
	  if((!CheckBBL) || CheckBBL->contains(edgeL)) {
	    // Edge is a local variant (or more variant than the block, e.g. an exit edge leading to an exit block), so the block is a plain old variant.
	    shouldSkip = true;
	    break;
	  }
	  if((!innermostPred) || (innermostPred->contains(edgeL)))
	    innermostPred = edgeL;
	}

      }

      if(!shouldSkip) {
	DenseMap<BasicBlock*, const Loop*>::iterator BlockIt = pBlocks->find(CheckBB);
	if(BlockIt == pBlocks->end() || BlockIt->second != innermostPred) {
	  if(BlockIt == pBlocks->end())
	    (*pBlocks)[CheckBB] = innermostPred;
	  else
	    BlockIt->second = innermostPred;
	  TerminatorInst* TI = CheckBB->getTerminator();
	  if(BranchInst* BI = dyn_cast<BranchInst>(TI)) {
	    if(!BI->isConditional()) {
	      BasicBlock* Succ = BI->getSuccessor(0);
	      (*pEdges)[std::make_pair(CheckBB, Succ)] = innermostPred;
	      ProduceQ->push_back(Succ);
	    }
	  }
	  else {
	    // For these conditional cases the edges will have been categorised as invariant by the terminator argument check above.
	    for(succ_iterator SI = succ_begin(CheckBB), SE = succ_end(CheckBB); SI != SE; ++SI) {
	      ProduceQ->push_back(*SI);
	    }
	  }
	}
      }

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, ProduceQ);

  }

  for(DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>::iterator EdgeIt = pEdges->begin(), EdgeItE = pEdges->end(); EdgeIt != EdgeItE; ++EdgeIt) {

    LPDEBUG("Edge " << EdgeIt->first.first->getName() << " -> " << EdgeIt->first.second->getName() << " is invariant; will evaluate at scope " << (EdgeIt->second ? EdgeIt->second->getHeader()->getName() : "root") << "\n");

  }

  for(DenseMap<BasicBlock*, const Loop*>::iterator BlockIt = pBlocks->begin(), BlockItE = pBlocks->end(); BlockIt != BlockItE; ++BlockIt) {

    LPDEBUG("Block " << BlockIt->first->getName() << " is invariant; will evaluate at scope " << (BlockIt->second ? BlockIt->second->getHeader()->getName() : "root") << "\n");

  }

}

DenseMap<Instruction*, const Loop*>& IntegrationHeuristicsPass::getInstScopes(Function* F) {

  DenseMap<Function*, DenseMap<Instruction*, const Loop*>* >::iterator it = invariantInstScopes.find(F);
  if(it != invariantInstScopes.end())
    return *(it->second);
  else {
    DenseMap<Instruction*, const Loop*>* instScopes;
    DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* edgeScopes;
    DenseMap<BasicBlock*, const Loop*>* blockScopes;
    createInvariantScopes(F, instScopes, edgeScopes, blockScopes);
    return *instScopes;
  }

}

DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& IntegrationHeuristicsPass::getEdgeScopes(Function* F) {

  DenseMap<Function*, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* >::iterator it = invariantEdgeScopes.find(F);
  if(it != invariantEdgeScopes.end())
    return *(it->second);
  else {
    DenseMap<Instruction*, const Loop*>* instScopes;
    DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* edgeScopes;
    DenseMap<BasicBlock*, const Loop*>* blockScopes;
    createInvariantScopes(F, instScopes, edgeScopes, blockScopes);
    return *edgeScopes;
  }

}

DenseMap<BasicBlock*, const Loop*>& IntegrationHeuristicsPass::getBlockScopes(Function* F) {

  DenseMap<Function*, DenseMap<BasicBlock*, const Loop*>* >::iterator it = invariantBlockScopes.find(F);
  if(it != invariantBlockScopes.end())
    return *(it->second);
  else {
    DenseMap<Instruction*, const Loop*>* instScopes;
    DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* edgeScopes;
    DenseMap<BasicBlock*, const Loop*>* blockScopes;
    createInvariantScopes(F, instScopes, edgeScopes, blockScopes);
    return *blockScopes;
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

  PointerBase ArgPB;
  getPointerBase(ShadowValue(Val), ArgPB);
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

void IntegrationHeuristicsPass::parseArgs(Function& F, std::vector<Constant*>& argConstants, uint32_t& argvIdxOut) {

  this->mallocAlignment = MallocAlignment;
  
  if(EnvFileAndIdx != "") {

    long idx;
    std::string EnvFile;
    if(!parseIntCommaString(EnvFileAndIdx, idx, EnvFile))
      dieEnvUsage();   

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

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<DataLayout>();
  GlobalTD = TD;
  AA = &getAnalysis<AliasAnalysis>();
  GlobalAA = AA;
  GlobalTLI = getAnalysisIfAvailable<TargetLibraryInfo>();
  
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

  InlineAttempt* IA = new InlineAttempt(this, 0, F, LIs, 0, 0);

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    if(argConstants[i])
      setParam(IA, i, argConstants[i]);

  }

  if(argvIdx != 0xffffffff) {

    IA->argShadows[argvIdx].i.PB = PointerBase::get(ImprovedVal(ShadowValue(&IA->argShadows[argvIdx]), 0), ValSetTypePB);

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

  IA->disableVarargsContexts();

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
  AU.addRequired<VFSCallAliasAnalysis>();
  AU.setPreservesAll();
  
}

