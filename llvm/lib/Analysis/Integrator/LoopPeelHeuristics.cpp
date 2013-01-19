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
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"

#include <string>
#include <algorithm>

#include <stdlib.h>

using namespace llvm;

bool instructionCounts(Instruction* I);

char IntegrationHeuristicsPass::ID = 0;

static cl::opt<std::string> GraphOutputDirectory("intgraphs-dir", cl::init(""));
static cl::opt<std::string> RootFunctionName("intheuristics-root", cl::init("main"));
static cl::opt<std::string> EnvFileAndIdx("spec-env", cl::init(""));
static cl::opt<std::string> ArgvFileAndIdxs("spec-argv", cl::init(""));
static cl::opt<unsigned> MallocAlignment("int-malloc-alignment", cl::init(0));
static cl::list<std::string> SpecialiseParams("spec-param", cl::ZeroOrMore);
static cl::list<std::string> AlwaysInlineFunctions("int-always-inline", cl::ZeroOrMore);
static cl::list<std::string> OptimisticLoops("int-optimistic-loop", cl::ZeroOrMore);
static cl::list<std::string> AssumeEdges("int-assume-edge", cl::ZeroOrMore);
static cl::list<std::string> IgnoreLoops("int-ignore-loop", cl::ZeroOrMore);
static cl::list<std::string> LoopMaxIters("int-loop-max", cl::ZeroOrMore);
static cl::opt<bool> SkipBenefitAnalysis("skip-benefit-analysis");

ModulePass *llvm::createIntegrationHeuristicsPass() {
  return new IntegrationHeuristicsPass();
}

INITIALIZE_PASS(IntegrationHeuristicsPass, "intheuristics", "Score functions for pervasive integration benefit", false, false);

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
			     DenseMap<Function*, LoopInfo*>& LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, 
			     DenseMap<Instruction*, const Loop*>& _invariantInsts, 
			     DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
			     DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth) : 
  IntegrationAttempt(Pass, P, F, LI, TD, AA, _invariantInsts, _invariantEdges, _invariantBlocks, depth),
  CI(_CI)
  { 
    UniqueReturnBlock = Pass->getUniqueReturnBlock(&F);

    raw_string_ostream OS(HeaderStr);
    OS << (!CI ? "Root " : "") << "Function " << F.getName();
    if(CI && !CI->getType()->isVoidTy())
      OS << " at " << itcache(*CI, true);
    SeqNumber = Pass->getSeq();
    OS << " / " << SeqNumber;
  }

PeelIteration::PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
	      AliasAnalysis* _AA, const Loop* _L, DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
	      DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int iter, int depth) :
  IntegrationAttempt(Pass, P, F, _LI, _TD, _AA, _invariantInsts, _invariantEdges, _invariantBlocks, depth),
  iterationCount(iter),
  L(_L),
  parentPA(PP),
  iterStatus(IterationStatusUnknown)
{ 

  raw_string_ostream OS(HeaderStr);
  OS << "Loop " << L->getHeader()->getName() << " iteration " << iterationCount;
  SeqNumber = Pass->getSeq();
  OS << " / " << SeqNumber;

}

PeelAttempt::PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
			 DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
			 DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, const Loop* _L, int depth) 
  : pass(Pass), parent(P), F(_F), LI(_LI), TD(_TD), AA(_AA), L(_L), invariantInsts(_invariantInsts), invariantEdges(_invariantEdges), invariantBlocks(_invariantBlocks), 
    residualInstructions(-1), nesting_depth(depth), totalIntegrationGoodness(0), nDependentLoads(0)
{

  this->tag.ptr = (void*)this;
  this->tag.type = IntegratorTypePA;

  raw_string_ostream OS(HeaderStr);
  OS << "Loop " << L->getHeader()->getName();
  SeqNumber = Pass->getSeq();
  OS << " / " << SeqNumber;
  
  L->getExitEdges(ExitEdges);
  LoopBlocks = L->getBlocks();

  OptimisticEdge = Pass->getOptimisticEdge(L);

  getOrCreateIteration(0);

}

PeelAttempt::~PeelAttempt() {
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
    delete *it;
  }
}

// Does this instruction count for accounting / performance measurement? Essentially: can this possibly be improved?
bool instructionCounts(Instruction* I) {

  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

AliasAnalysis* IntegrationAttempt::getAA() {

  return this->AA;

}

Module& IntegrationAttempt::getModule() {

  return *(F.getParent());

}

ValCtx IntegrationAttempt::getLocalReplacement(Value* V) {

  DenseMap<Value*, ValCtx >::iterator it = improvedValues.find(V);
  if(it == improvedValues.end())
    return make_vc(V, this);
  else
    return it->second;  

}

ValCtx IntegrationAttempt::getReplacement(Value* V) {

  // V is visible directly from within this loop. Therefore, due to LCSSA form, it's either a variant (in this loop)
  // or an invariant belonging to one of my parent loops, or the root function.
  // One exception: it's a variant, but we're being asked in the context of trying to load-forward through an unpeeled loop.
  // In that case it's never valid to resolve a variant so I just return the unresolved answer. The same applies to getDefaultVC.
  // The case for reading an exit PHI is taken care of by the PHI resolution code.

  if(Constant* C = dyn_cast<Constant>(V))
    return const_vc(C);

  const Loop* evalScope = getValueScope(V);
  const Loop* L = getLoopContext();

  if(L != evalScope && ((!L) || L->contains(evalScope))) {
    // The load-forwarding case mentioned above.
    return make_vc(V, this);
  }
  else {
    return getReplacementUsingScope(V, evalScope);
  }

}

// Calls a given callback at the *parent* scope associated with loop LScope
void IntegrationAttempt::callWithScope(Callable& C, const Loop* LScope) {

  if(LScope == getLoopContext())
    C.callback(this);
  else
    parent->callWithScope(C, LScope);

}

class GetReplacementCallback : public Callable {

  Value* V;

public:

  ValCtx Result;

  GetReplacementCallback(Value* _V) : V(_V) { }

  virtual void callback(IntegrationAttempt* Ctx) {

    Result = Ctx->getLocalReplacement(V);

  }

};

ValCtx IntegrationAttempt::getReplacementUsingScope(Value* V, const Loop* LScope) {

  GetReplacementCallback CB(V);
  callWithScope(CB, LScope);
  return CB.Result;

}

ValCtx IntegrationAttempt::getReplacementUsingScopeRising(Instruction* I, BasicBlock* ExitingBB, BasicBlock* ExitBB, const Loop* LScope) {

  const Loop* MyScope = getLoopContext();

  if(LScope == MyScope)
    return getLocalReplacement(I);

  // Read from child loop if appropriate:
  if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(MyScope, LScope))) {

    ValCtx OnlyDef = VCNull;

    if(PA->Iterations.back()->iterStatus == IterationStatusFinal) {

      for(unsigned i = 0; i < PA->Iterations.size(); ++i) {

	PeelIteration* Iter = PA->Iterations[i];
	if(Iter->edgeIsDead(ExitingBB, ExitBB))
	  continue;

	ValCtx ThisDef = Iter->getReplacementUsingScopeRising(I, ExitingBB, ExitBB, LScope);
	if(ThisDef == VCNull)
	  return ThisDef;

	if(OnlyDef == VCNull)
	  OnlyDef = ThisDef;
	else if(OnlyDef != ThisDef)
	  return VCNull;	

      }

      return OnlyDef;

    }
    else {
	    
      LPDEBUG("Unable to read from loop " << LScope->getHeader()->getName() << " because loop is not known to terminate yet\n");
      return VCNull;

    }

  }
  else {

    LPDEBUG("Unable to read from loop " << LScope->getHeader()->getName() << " because loop has not been peeled yet\n");
    return VCNull;

  }

}  

ValCtx IntegrationAttempt::getDefaultVC(Value* V) {

  if(Constant* C = dyn_cast<Constant>(V))
    return const_vc(C);
  
  const Loop* evalScope = getValueScope(V);
  const Loop* L = getLoopContext();

  if(L != evalScope && ((!L) || L->contains(evalScope))) {
    return make_vc(V, this);
  }
  else {
    return getDefaultVCWithScope(V, evalScope);
  }

}

ValCtx IntegrationAttempt::getDefaultVCWithScope(Value* V, const Loop* LScope) {

  if(LScope == getLoopContext())
    return make_vc(V, this);
  else
    return parent->getDefaultVCWithScope(V, LScope);

}

Constant* llvm::getConstReplacement(Value* V, IntegrationAttempt* Ctx) {

  if(Constant* C = dyn_cast<Constant>(V))
    return C;
  ValCtx Replacement = Ctx->getReplacement(V);
  if(Replacement.isPtrAsInt())
    return 0;
  if(Constant* C = dyn_cast<Constant>(Replacement.first))
    return C;
  return 0;

}

Constant* IntegrationAttempt::getConstReplacement(Value* V) {

  return llvm::getConstReplacement(V, this);

}

Function* IntegrationAttempt::getCalledFunction(CallInst* CI) {

  Constant* C = getConstReplacement(CI->getCalledValue()->stripPointerCasts());

  if(!C) {

    Constant* OnlyVal = 0;
    PointerBase PB;
    if(getPointerBaseFalling(CI->getCalledValue()->stripPointerCasts(), PB)) {
     
      if(!PB.Overdef) {

	for(unsigned i = 0; i < PB.Values.size(); ++i) {

	  Constant* ThisVal = dyn_cast<Constant>(PB.Values[i].first);
	  if(!ThisVal) {
	    OnlyVal = 0;
	    break;
	  }
	  if(ThisVal->isNullValue())
	    continue;
	  if(!OnlyVal)
	    OnlyVal = ThisVal;
	  else if(OnlyVal != ThisVal) {
	    OnlyVal = 0;
	    break;
	  }

	}

	if(OnlyVal)
	  C = OnlyVal;

      }

    }

  }

  if(!C)
    return 0;

  return dyn_cast<Function>(C->stripPointerCasts());

}

// Only ever called on things that belong in this scope, thanks to shouldIgnoreBlock et al.
void IntegrationAttempt::setReplacement(Value* V, ValCtx R) {

  assert(getValueScope(V) == getLoopContext());
  improvedValues[V] = R;

}

void IntegrationAttempt::eraseReplacement(Value* V) {

  improvedValues.erase(V);

}

const Loop* IntegrationAttempt::applyIgnoreLoops(const Loop* InstL) {

  const Loop* MyL = getLoopContext();

  if(MyL != InstL && ((!MyL) || MyL->contains(InstL))) {

    for(const Loop* L = InstL; L != MyL; L = L->getParentLoop()) {

      if(pass->shouldIgnoreLoop(&F, L->getHeader()))
	InstL = L->getParentLoop();

    }

  }

  return InstL;

}

// Get the loop scope at which a given instruction should be resolved.
const Loop* IntegrationAttempt::getValueScope(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {

    const Loop* InstL;
    DenseMap<Instruction*, const Loop*>::iterator it = invariantInsts.find(I);
    if(it != invariantInsts.end())
      InstL = it->second;
    else
      InstL = LI[&F]->getLoopFor(I->getParent());

    return applyIgnoreLoops(InstL);

  }
  else if(isa<Argument>(V)) {
    return 0;
  }
  else
    return getLoopContext();

}

bool IntegrationAttempt::isUnresolved(Value* V) {

  return (!shouldForwardValue(getDefaultVC(V))) && (getDefaultVC(V) == getReplacement(V));

}

bool IntegrationAttempt::edgeIsDead(BasicBlock* B1, BasicBlock* B2) {

  if(deadEdges.count(std::make_pair(B1, B2)))
    return true;

  const Loop* MyScope = getLoopContext();
  const Loop* EdgeScope = getEdgeScope(B1, B2);

  if((MyScope != EdgeScope) && ((!MyScope) || MyScope->contains(EdgeScope))) {

    return edgeIsDeadWithScopeRising(B1, B2, EdgeScope);

  }

  const Loop* B1Scope = getBlockScope(B1);

  const Loop* CheckScope;
  if((!EdgeScope) || EdgeScope->contains(B1Scope))
    CheckScope = EdgeScope;
  else
    CheckScope = B1Scope;

  // Check the edge's scope or the block's, whichever is further out, since our predecessor might
  // get outright killed even if his terminator branch is more variant.

  return edgeIsDeadWithScope(B1, B2, CheckScope);

}

bool IntegrationAttempt::edgeIsDeadWithScopeRising(BasicBlock* B1, BasicBlock* B2, const Loop* EdgeScope) {

  if(deadEdges.count(std::make_pair(B1, B2)))
    return true;

  const Loop* MyScope = getLoopContext();

  if(EdgeScope == MyScope)
    return edgeIsDeadWithScope(B1, B2, EdgeScope);
  
  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(MyScope, EdgeScope))) {

    PeelIteration* FinalIter = LPA->Iterations.back();
    if(FinalIter->iterStatus == IterationStatusFinal) {

      const Loop* B1Scope = getBlockScopeVariant(B1);
      const Loop* B2Scope = getBlockScopeVariant(B2);

      if(B1Scope != B2Scope && ((!B2Scope) || B2Scope->contains(B1Scope))) {
	// Exit edge: dead if no iteration takes it.

	for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	  if(!LPA->Iterations[i]->edgeIsDeadWithScopeRising(B1, B2, EdgeScope))
	    return false;

	}

	return true;

      }
      else if(FinalIter->isOnlyExitingIteration()) {

	// Edge within loop: check final iter if it's the sole exit iteration.
	return FinalIter->edgeIsDeadWithScopeRising(B1, B2, EdgeScope);

      }

    }

  }
    
  return false;

}

bool IntegrationAttempt::edgeIsDeadWithScope(BasicBlock* B1, BasicBlock* B2, const Loop* ScopeL) {

  if(deadEdges.count(std::make_pair(B1, B2)))
    return true;
  
  const Loop* MyScope = getLoopContext();

  if(ScopeL == MyScope)
    return false;

  return parent->edgeIsDeadWithScope(B1, B2, ScopeL);

}

void IntegrationAttempt::setEdgeDead(BasicBlock* B1, BasicBlock* B2) {

  std::pair<BasicBlock*, BasicBlock*> Edge = std::make_pair(B1, B2);
  deadEdges.insert(Edge);

}

const Loop* IntegrationAttempt::getEdgeScope(BasicBlock* B1, BasicBlock* B2) {

  DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>::iterator it = invariantEdges.find(std::make_pair(B1, B2));
  const Loop* L;
  if(it != invariantEdges.end())
    L = it->second;
  else
    L = LI[&F]->getLoopFor(B1);

  return applyIgnoreLoops(L);

}

bool IntegrationAttempt::blockIsDeadWithScope(BasicBlock* BB, const Loop* ScopeL) {

  if(deadBlocks.count(BB))
    return true;
  if(ScopeL == getLoopContext())
    return false;
  else
    return parent->blockIsDeadWithScope(BB, ScopeL);

}

bool IntegrationAttempt::blockIsDead(BasicBlock* BB) {

  DenseMap<BasicBlock*, const Loop*>::iterator it = invariantBlocks.find(BB);
  bool ret;
  if(it == invariantBlocks.end()) {
    ret = deadBlocks.count(BB);
    //errs() << "blockIsDead " << BB->getName() << " (1): " << ret << "\n";
  }
  else {
    const Loop* MyL = getLoopContext();
    // If this block's context contains ours it is an invariant to us.
    // Otherwise it is a variant and we cannot answer at this scope.
    if((!it->second) || (MyL && it->second->contains(MyL))) {
      ret = blockIsDeadWithScope(BB, it->second);
      //errs() << "blockIsDead " << BB->getName() << " (2): " << ret << "\n";
    }
    else {
      ret = false;
      //errs() << "blockIsDead " << BB->getName() << " (3): " << ret << "\n";
    }
  }

  return ret;

}

void IntegrationAttempt::setBlockDead(BasicBlock* BB) {

  deadBlocks.insert(BB);

}

const Loop* IntegrationAttempt::getBlockScope(BasicBlock* BB) {

  DenseMap<BasicBlock*, const Loop*>::iterator it = invariantBlocks.find(BB);
  const Loop* L;
  if(it == invariantBlocks.end())
    L = LI[&F]->getLoopFor(BB);
  else
    L = it->second;

  return applyIgnoreLoops(L);
  
}

const Loop* IntegrationAttempt::getBlockScopeVariant(BasicBlock* BB) {

  return applyIgnoreLoops(LI[&F]->getLoopFor(BB));

}

bool IntegrationAttempt::blockIsCertain(BasicBlock* BB) {

  const Loop* BlockL = getBlockScopeVariant(BB);
  const Loop* MyL = getLoopContext();

  if(((!MyL) && BlockL) || (MyL != BlockL && MyL->contains(BlockL))) {

    if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(MyL, BlockL))) {

      PeelIteration* FinalIter = LPA->Iterations[LPA->Iterations.size() - 1];
      if(FinalIter->isOnlyExitingIteration()) {

	return FinalIter->blockIsCertain(BB);

      }
      else {

	return false;

      }

    }

  }

  return certainBlocks.count(BB);

}

InlineAttempt* IntegrationAttempt::getInlineAttempt(CallInst* CI) {

  if(ignoreIAs.count(CI))
    return 0;

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
	  F->getName() == "posix_fadvise"/* ||
	  F->getName() == "exit" ||
	  F->getName() == "atexit"*/);

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

bool IntegrationAttempt::shouldInlineFunction(CallInst* CI) {

  Function* FCalled = getCalledFunction(CI);
  assert(FCalled && "shouldInlineFunction called on uncertain function pointer");

  if(certainBlocks.count(CI->getParent()))
    return true;

  if(pass->shouldAlwaysInline(FCalled))
    return true;

  // Inline if this wouldn't be a recursive call.
  if(!stackIncludesCallTo(FCalled))
    return true;
  
  return false;

}

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(CallInst* CI) {

  if(ignoreIAs.count(CI))
    return 0;

  if(InlineAttempt* IA = getInlineAttempt(CI))
    return IA;

  Function* FCalled = getCalledFunction(CI);
  if(!FCalled) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it's an uncertain indirect call\n");
    return 0;
  }

  if(FCalled->isDeclaration()) {
    LPDEBUG("Ignored " << itcache(*CI) << " because we don't know the function body\n");
    return 0;
  }

  if(!shouldInlineFunction(CI)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it shouldn't be inlined (not on certain path, and would cause recursion)\n");
    return 0;
  }
  
  if(getLoopContext() != getValueScope(CI)) {
    // This can happen with always-inline functions. Should really fix whoever tries to make the inappropriate call.
    return 0;
  }

  if(functionIsBlacklisted(FCalled)) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it is a special function we are not allowed to inline\n");
    return 0;
  }

  errs() << "Inline new fn " << FCalled->getName() << "\n";

  InlineAttempt* IA = new InlineAttempt(pass, this, *FCalled, this->LI, this->TD, this->AA, CI, pass->getInstScopes(FCalled), pass->getEdgeScopes(FCalled), pass->getBlockScopes(FCalled), this->nesting_depth + 1);
  inlineChildren[CI] = IA;

  LPDEBUG("Inlining " << FCalled->getName() << " at " << itcache(*CI) << "\n");

  return IA;

}

void PeelIteration::checkFinalIteration() {

  // Check whether we now have evidence the loop terminates this time around
  // If it does, queue consideration of each exit PHI; by LCSSA these must belong to our parent.

  if(edgeIsDead(L->getLoopLatch(), L->getHeader()) || pass->assumeEndsAfter(&F, L->getHeader(), iterationCount)) {

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
  
  LPDEBUG("Peeling iteration " << iter << " of loop " << L->getHeader()->getName() << "\n");

  assert(iter == Iterations.size());

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, LI, TD, AA, L, invariantInsts, invariantEdges, invariantBlocks, iter, nesting_depth);
  Iterations.push_back(NewIter);
    
  return NewIter;

}

PeelIteration* PeelIteration::getNextIteration() {

  return parentPA->getIteration(this->iterationCount + 1);

}

bool PeelIteration::allExitEdgesDead() {

  for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = parentPA->ExitEdges.begin(), EE = parentPA->ExitEdges.end(); EI != EE; ++EI) {

    if(!edgeIsDead(EI->first, EI->second)) {
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

  std::pair<BasicBlock*, BasicBlock*>& OE = parentPA->OptimisticEdge;

  bool willIterate = (OE.first && edgeIsDead(OE.first, OE.second)) || allExitEdgesDead();

  if(!willIterate) {

    LPDEBUG("Won't peel loop " << L->getHeader()->getName() << " yet because at least one exit edge is still alive\n");
    return 0;
      
  }
  else if(iterationCount > 1000) {

    LPDEBUG("Won't peel loop " << L->getHeader()->getName() << ": max iterations 1000\n");
    return 0;

  }

  errs() << "Peel loop " << L->getHeader()->getName() << "\n";

  iterStatus = IterationStatusNonFinal;
  LPDEBUG("Loop known to iterate: creating next iteration\n");
  return parentPA->getOrCreateIteration(this->iterationCount + 1);

}

PeelAttempt* IntegrationAttempt::getPeelAttempt(const Loop* L) {

  if(ignorePAs.count(L))
    return 0;

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
  
  // Preheaders only have one successor (the header), so this is enough.
  if(!certainBlocks.count(NewL->getLoopPreheader())) {
   
    LPDEBUG("Will not expand loop " << NewL->getHeader()->getName() << " because the preheader is not certain to execute\n");
    return 0;

  }

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, LI, TD, AA, invariantInsts, invariantEdges, invariantBlocks, NewL, nesting_depth + 1);
    peelChildren[NewL] = LPA;

    return LPA;

  }
  else {

    LPDEBUG("Won't explore loop with header " << NewL->getHeader()->getName() << " because it lacks a preheader, a latch, or both, or has multiple backedges\n");
    return 0;

  }

}


const Loop* InlineAttempt::getLoopContext() {

  return 0;

}

const Loop* PeelIteration::getLoopContext() {

  return L;

}

ValCtx InlineAttempt::tryGetReturnValue() {

  // Let's have a go at supplying a return value to our caller. Simple measure:
  // we know the value if all the 'ret' instructions except one are dead,
  // and we know that instruction's operand.

  if(F.getReturnType()->isVoidTy())
    return VCNull;

  ValCtx returnVal = VCNull;
  bool foundReturnInst = false;

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {
    if(blockIsDead(FI))
      continue;
    for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++) {
      if(ReturnInst* RI = dyn_cast<ReturnInst>(BI)) {
	if(foundReturnInst) {
	  LPDEBUG("Can't determine return value: more than one 'ret' is live\n");
	  returnVal = VCNull;
	  break;
	}
	else
	  foundReturnInst = true;
	Value* ThisRet = RI->getReturnValue();
	returnVal = getReplacement(ThisRet);
	if(!returnVal.first) {
	  LPDEBUG("Can't determine return value: live instruction " << itcache(*RI) << " has non-forwardable value " << itcache(*(RI->getReturnValue())) << "\n");
	  break;
	}
      }
    }
  }
  
  if(returnVal.first) {
    LPDEBUG("Found return value: " << itcache(returnVal) << "\n");
  }
  
  return returnVal;

}

// Store->Load forwarding helpers:

BasicBlock* InlineAttempt::getEntryBlock() {

  return &F.getEntryBlock();

}

BasicBlock* PeelIteration::getEntryBlock() {
  
  return L->getHeader();

}

Instruction* InlineAttempt::getEntryInstruction() {

  return CI;

}

Instruction* PeelIteration::getEntryInstruction() {

  return L->getLoopPreheader()->getTerminator();

}

bool IntegrationAttempt::hasParent() {

  return (parent != 0);

}

bool IntegrationAttempt::isRootMainCall() {

  return (!this->parent) && F.getName() == RootFunctionName;

}

ValCtx InlineAttempt::getImprovedCallArgument(Argument* A) {

  return parent->getReplacement(CI->getArgOperand(A->getArgNo()));

}

bool llvm::isGlobalIdentifiedObject(ValCtx VC) {

  return isIdentifiedObject(VC.first) && ((VC.second && VC.second->isRootMainCall()) || !isa<Argument>(VC.first));

}

ValCtx IntegrationAttempt::getUltimateUnderlyingObject(Value* V) {

  ValCtx Ultimate = getDefaultVC(V);
  while(!isGlobalIdentifiedObject(Ultimate)) {

    ValCtx New;
    New = make_vc(Ultimate.first->getUnderlyingObject(), Ultimate.second, ValCtx::noOffset, Ultimate.va_arg);
    if(New.second)
      New = New.second->getReplacement(New.first);
 
    if(New == Ultimate)
      break;

    Ultimate = New;

  }

  return Ultimate;

}

void InlineAttempt::getVarArg(int64_t idx, ValCtx& Result) {

  unsigned numNonFPArgs = 0;
  unsigned numFPArgs = 0;

  Value* Found = 0;

  for(unsigned i = F.arg_size(); i < CI->getNumArgOperands(); ++i) {

    Value* Arg = CI->getArgOperand(i);
    if(Arg->getType()->isPointerTy() || Arg->getType()->isIntegerTy()) {
      if(idx < ValCtx::first_fp_arg && idx == numNonFPArgs) {
	Found = Arg;
	break;
      }
      numNonFPArgs++;
    }
    else if(Arg->getType()->isFloatingPointTy()) {
      if(idx >= ValCtx::first_fp_arg && (idx - ValCtx::first_fp_arg) == numFPArgs) {
	Found = Arg;
	break;
      }
      numFPArgs++;
    }

  }

  if(Found)
    Result = parent->getReplacement(Found);
  else {
    
    LPDEBUG("Vararg index " << idx << ": out of bounds\n");
    Result = VCNull;

  }

}

void PeelIteration::getVarArg(int64_t idx, ValCtx& Result) {

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

void IntegrationAttempt::collectBlockStats(BasicBlock* BB) {

  const Loop* MyL = getLoopContext();

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; BI++) {
      
    const Loop* L = getValueScope(BI);
    if(MyL != L && ((!MyL) || MyL->contains(L))) {

      // Count unexplored loops as part of my own context.
      if(!peelChildren.count(immediateChildLoop(MyL, L)))
	L = MyL;

    }

    if(MyL != L) {

      if(instructionCounts(BI))
	improvableInstructionsIncludingLoops++;

    }
    else {

      if(instructionCounts(BI)) { 

	//if(BB == getEntryBlock() && isa<PHINode>(BI))
	//  continue;

	improvableInstructions++;
	improvableInstructionsIncludingLoops++;

	if(blockIsDead(BB))
	  improvedInstructions++;
	else if(improvedValues.find(BI) != improvedValues.end())
	  improvedInstructions++;
	else if(deadValues.count(BI))
	  improvedInstructions++;
	else if(BranchInst* BrI = dyn_cast<BranchInst>(BI)) {
	  if(BrI->isConditional() && (improvedValues.find(BrI->getCondition()) != improvedValues.end()))
	    improvedInstructions++;
	}

      }

      if(CallInst* CI = dyn_cast<CallInst>(BI)) {
	DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(CI);
	if(it == inlineChildren.end())
	  unexploredCalls.push_back(CI);
      }

    }

  }

}

void IntegrationAttempt::collectLoopStats(const Loop* LoopI) {

  DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.find(LoopI);

  if(it == peelChildren.end()) {
    unexploredLoops.push_back(LoopI);
    for(Loop::block_iterator BI = LoopI->block_begin(), BE = LoopI->block_end(); BI != BE; ++BI)
      collectBlockStats(*BI);
  }

}

void IntegrationAttempt::collectAllBlockStats() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {
    const Loop* MyL = getLoopContext();
    if((!MyL) || MyL->contains(FI)) {
      collectBlockStats(FI);
    }
  }

}

void InlineAttempt::collectAllLoopStats() {

  for(LoopInfo::iterator LoopI = LI[&F]->begin(), LoopE = LI[&F]->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelIteration::collectAllLoopStats() {

  for(Loop::iterator LoopI = L->begin(), LoopE = L->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelAttempt::collectStats() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->collectStats();

}

void IntegrationAttempt::collectStats() {

  unexploredCalls.clear();
  unexploredLoops.clear();
  improvedInstructions = 0;
  improvableInstructions = 0;
  improvableInstructionsIncludingLoops = 0;

  collectAllBlockStats();
  collectAllLoopStats();

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->collectStats();

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->collectStats();

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
  for(DenseMap<Value*, ValCtx>::const_iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {
    OS << nestingIndent() << itcache(*(it->first)) << " -> " << itcache(it->second) << "\n";
  }
  for(DenseSet<Value*>::const_iterator it = deadValues.begin(), it2 = deadValues.end(); it != it2; ++it) {
    OS << nestingIndent() << itcache((**it)) << ": dead\n";
  }
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
  errs() << ": ";
  errs() << "imp " << improvedValues.size() << " db " << deadBlocks.size() << " de " << deadEdges.size()
	 << " cb " << certainBlocks.size() << " dv " << deadValues.size() << " uw " << unusedWriters.size()
	 << " uwttc " << unusedWritersTraversingThisContext.size()
	 << " foc " << forwardableOpenCalls.size()
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

bool llvm::allowTotalDefnImplicitCast(const Type* From, const Type* To) {

  if(From == To)
    return true;

  if(From->isPointerTy() && To->isPointerTy())
    return true;

  return false;

}

bool llvm::allowTotalDefnImplicitPtrToInt(const Type* From, const Type* To, TargetData* TD) {

  return From->isPointerTy() && To->isIntegerTy() && TD->getTypeSizeInBits(To) >= TD->getTypeSizeInBits(From);

}

ValCtx llvm::getAsPtrAsInt(ValCtx VC, const Type* Target) {

  assert(VC.first->getType()->isPointerTy());

  if(Constant* C = dyn_cast<Constant>(VC.first)) {

    if(C->isNullValue())
      return const_vc(Constant::getNullValue(Target));

  }

  return make_vc(VC.first, VC.second, 0);

}

ValCtx llvm::extractAggregateMemberAt(Constant* FromC, int64_t Offset, const Type* Target, uint64_t TargetSize, TargetData* TD) {

  const Type* FromType = FromC->getType();
  uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

  if(Offset == 0 && TargetSize == FromSize) {
    if(allowTotalDefnImplicitCast(FromType, Target))
      return const_vc(FromC);
    else if(allowTotalDefnImplicitPtrToInt(FromType, Target, TD))
      return getAsPtrAsInt(const_vc(FromC), Target);
    DEBUG(dbgs() << "Can't use simple element extraction because load implies cast from " << (*(FromType)) << " to " << (*Target) << "\n");
    return VCNull;
  }

  if(Offset < 0 || Offset + TargetSize > FromSize) {

    DEBUG(dbgs() << "Can't use element extraction because offset " << Offset << " and size " << TargetSize << " are out of bounds for object with size " << FromSize << "\n");
    return VCNull;

  }

  if(isa<ConstantAggregateZero>(FromC) && Offset + TargetSize <= FromSize) {

    // Wholly subsumed within a zeroinitialiser:
    return const_vc(Constant::getNullValue(Target));

  }

  uint64_t StartE, StartOff, EndE, EndOff;
  bool mightWork = false;

  if(ConstantArray* CA = dyn_cast<ConstantArray>(FromC)) {

    mightWork = true;
    
    const Type* EType = CA->getType()->getElementType();
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
      return VCNull;
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

  return VCNull;

}

Constant* llvm::constFromBytes(unsigned char* Bytes, const Type* Ty, TargetData* TD) {

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
      // We know the target type does not contain pointers

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
  else if(const ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    if(ECount == 0) {
      DEBUG(dbgs() << "Can't produce a constant array of 0 length\n");
      return 0;
    }

    // I *think* arrays are always dense, i.e. it's for the child type to specify padding.
    const Type* EType = ATy->getElementType();
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
  else if(const StructType* STy = dyn_cast<StructType>(Ty)) {

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

      const Type* EType = *EI;
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

BasicBlock* IntegrationHeuristicsPass::getUniqueReturnBlock(Function* F) {

  DenseMap<Function*, BasicBlock*>::iterator it = uniqueReturnBlocks.find(F);
  
  if(it != uniqueReturnBlocks.end())
    return it->second;

  BasicBlock* uniqueReturnBlock = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    BasicBlock* BB = FI;

    if(isa<ReturnInst>(BB->getTerminator())) {
      if(!uniqueReturnBlock)
	uniqueReturnBlock = BB;
      else {
	uniqueReturnBlock = 0;
	break;
      }
    }

  }

  uniqueReturnBlocks[F] = uniqueReturnBlock;

  return uniqueReturnBlock;

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
	if(I->mayReadFromMemory() || I->mayWriteToMemory() || isa<PHINode>(I))
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

    DEBUG(dbgs() << "Edge " << EdgeIt->first.first->getName() << " -> " << EdgeIt->first.second->getName() << " is invariant; will evaluate at scope " << (EdgeIt->second ? EdgeIt->second->getHeader()->getName() : "root") << "\n");

  }

  for(DenseMap<BasicBlock*, const Loop*>::iterator BlockIt = pBlocks->begin(), BlockItE = pBlocks->end(); BlockIt != BlockItE; ++BlockIt) {

    DEBUG(dbgs() << "Block " << BlockIt->first->getName() << " is invariant; will evaluate at scope " << (BlockIt->second ? BlockIt->second->getHeader()->getName() : "root") << "\n");

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

void IntegrationHeuristicsPass::queueDIE(IntegrationAttempt* ctx, Value* val) {
  assert(val && "Queued a null value");
  produceDIEQueue->push_back(make_vc(val, ctx));
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

void IntegrationHeuristicsPass::runDIEQueue() {

  SmallVector<ValCtx, 64>* consumeDIEQueue = (produceDIEQueue == &dieQueue1) ? &dieQueue2 : &dieQueue1;

  while(dieQueue1.size() || dieQueue2.size()) {

    for(SmallVector<ValCtx, 64>::iterator it = consumeDIEQueue->begin(), it2 = consumeDIEQueue->end(); it != it2; ++it) {

      it->second->tryKillValue(it->first);

    }

    consumeDIEQueue->clear();
    std::swap(produceDIEQueue, consumeDIEQueue);

  }

}

void IntegrationHeuristicsPass::commit() {
  RootIA->commit();
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

void IntegrationHeuristicsPass::setParam(IntegrationAttempt* IA, Function& F, long Idx, Constant* Val) {

  const Type* Target = F.getFunctionType()->getParamType(Idx);

  if(Val->getType() != Target) {

    errs() << "Type mismatch: constant " << *Val << " supplied for parameter of type " << *Target << "\n";
    exit(1);

  }

  Function::arg_iterator Arg = F.arg_begin();
  for(long i = 0; i < Idx && Arg != F.arg_end(); ++i)
    ++Arg;

  if(Arg != F.arg_end()) {
    IA->setReplacement(Arg, const_vc(Val));
  }
  // Else it's varargs, which are discovered through LF rather than direct propagation

}

void IntegrationHeuristicsPass::parseArgs(InlineAttempt* RootIA, Function& F) {

  this->mallocAlignment = MallocAlignment;
  
  if(EnvFileAndIdx != "") {

    long idx;
    std::string EnvFile;
    if(!parseIntCommaString(EnvFileAndIdx, idx, EnvFile))
      dieEnvUsage();   

    Constant* Env = loadEnvironment(*(F.getParent()), EnvFile);
    setParam(RootIA, F, idx, Env);

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
    setParam(RootIA, F, argcIdx, ConstantInt::get(Type::getInt32Ty(F.getContext()), argc));

  }

  for(cl::list<std::string>::const_iterator ArgI = SpecialiseParams.begin(), ArgE = SpecialiseParams.end(); ArgI != ArgE; ++ArgI) {

    long idx;
    std::string Param;
    if(!parseIntCommaString(*ArgI, idx, Param))
      dieSpecUsage();

    const Type* ArgTy = F.getFunctionType()->getParamType(idx);
    
    if(ArgTy->isIntegerTy()) {

      char* end;
      int64_t arg = strtoll(Param.c_str(), &end, 10);
      if(end != (Param.c_str() + Param.size())) {

	errs() << "Couldn't parse " << Param << " as in integer\n";
	exit(1);

      }

      Constant* ArgC = ConstantInt::getSigned(ArgTy, arg);
      setParam(RootIA, F, idx, ArgC);

    }
    else if(const PointerType* ArgTyP = dyn_cast<PointerType>(ArgTy)) {

      const Type* StrTy = Type::getInt8PtrTy(F.getContext());
      const Type* ElemTy = ArgTyP->getElementType();
      
      if(ArgTyP == StrTy) {

	Constant* Str = ConstantArray::get(F.getContext(), Param);
	Constant* GStr = new GlobalVariable(Str->getType(), true, GlobalValue::PrivateLinkage, Str, "specstr");
	Constant* Zero = ConstantInt::get(Type::getInt64Ty(F.getContext()), 0);
	Constant* GEPArgs[] = { Zero, Zero };
	Constant* StrPtr = ConstantExpr::getGetElementPtr(GStr, GEPArgs, 2);
	setParam(RootIA, F, idx, StrPtr);

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

	setParam(RootIA, F, idx, Found);

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

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<TargetData>();
  AA = &getAnalysis<AliasAnalysis>();
  
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

  DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");

  InlineAttempt* IA = new InlineAttempt(this, 0, F, LIs, TD, AA, 0, getInstScopes(&F), getEdgeScopes(&F), getBlockScopes(&F), 0);

  RootIA = IA;

  parseArgs(IA, F);

  IA->analyse();

  DEBUG(dbgs() << "Finding dead MTIs\n");
  IA->tryKillAllMTIs();

  DEBUG(dbgs() << "Finding dead stores\n");
  IA->tryKillAllStores();

  DEBUG(dbgs() << "Finding dead allocations\n");
  IA->tryKillAllAllocs();

  DEBUG(dbgs() << "Finding dead VFS operations\n");
  IA->tryKillAllVFSOps();

  DEBUG(dbgs() << "Finding remaining dead instructions\n");

  IA->queueAllLiveValues();

  runDIEQueue();

  IA->collectStats();
  
  if(!SkipBenefitAnalysis)
    estimateIntegrationBenefit();

  IA->disableVarargsContexts();

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
