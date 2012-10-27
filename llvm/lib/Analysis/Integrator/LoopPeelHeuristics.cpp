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
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/PHITransAddr.h"
#include "llvm/Analysis/VFSCallModRef.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/System/Path.h"

#include <string>
#include <algorithm>

#include <stdlib.h>
#include <fcntl.h> // For O_RDONLY et al
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>

using namespace llvm;

bool instructionCounts(Instruction* I);

char IntegrationHeuristicsPass::ID = 0;

static cl::opt<std::string> GraphOutputDirectory("intgraphs-dir", cl::init(""));
static cl::opt<std::string> RootFunctionName("intheuristics-root", cl::init("main"));
static cl::opt<std::string> EnvFileAndIdx("spec-env", cl::init(""));
static cl::opt<std::string> ArgvFileAndIdxs("spec-argv", cl::init(""));
static cl::list<std::string> SpecialiseParams("spec-param", cl::ZeroOrMore);
static cl::list<std::string> AlwaysInlineFunctions("int-always-inline", cl::ZeroOrMore);
static cl::list<std::string> OptimisticLoops("int-optimistic-loop", cl::ZeroOrMore);
static cl::list<std::string> AssumeEdges("int-assume-edge", cl::ZeroOrMore);

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

}

PeelAttempt::PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
			 DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
			 DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, const Loop* _L, int depth) 
  : pass(Pass), parent(P), F(_F), LI(_LI), TD(_TD), AA(_AA), L(_L), invariantInsts(_invariantInsts), invariantEdges(_invariantEdges), invariantBlocks(_invariantBlocks), nesting_depth(depth)
{

  this->tag.ptr = (void*)this;
  this->tag.type = IntegratorTypePA;

  raw_string_ostream OS(HeaderStr);
  OS << "Loop " << L->getHeader()->getName();
  
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

ValCtx IntegrationAttempt::getReplacementUsingScopeRising(Value* V, const Loop* LScope) {

  const Loop* MyScope = getLoopContext();

  if(LScope == MyScope)
    return getLocalReplacement(V);

  // Read from child loop if appropriate:
  if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(MyScope, LScope))) {

    PeelIteration* finalIter = PA->Iterations[PA->Iterations.size() - 1];
    if(finalIter->isOnlyExitingIteration()) {

      return finalIter->getReplacementUsingScopeRising(V, LScope);

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
  if(!C)
    return 0;

  return dyn_cast<Function>(C->stripPointerCasts());

}

// Only ever called on things that belong in this scope, thanks to shouldIgnoreBlock et al.
void IntegrationAttempt::setReplacement(Value* V, ValCtx R) {

  improvedValues[V] = R;

}

void IntegrationAttempt::eraseReplacement(Value* V) {

  improvedValues.erase(V);

}

// Get the loop scope at which a given instruction should be resolved.
const Loop* IntegrationAttempt::getValueScope(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {
    DenseMap<Instruction*, const Loop*>::iterator it = invariantInsts.find(I);
    if(it != invariantInsts.end())
      return it->second;
    else
      return LI[&F]->getLoopFor(I->getParent());
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
    if(FinalIter->isOnlyExitingIteration()) {
      return FinalIter->edgeIsDeadWithScopeRising(B1, B2, EdgeScope);
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
  if(it != invariantEdges.end())
    return it->second;
  else
    return LI[&F]->getLoopFor(B1);

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
  if(it == invariantBlocks.end())
    return deadBlocks.count(BB);
  else {
    const Loop* MyL = getLoopContext();
    // If this block's context contains ours it is an invariant to us.
    // Otherwise it is a variant and we cannot answer at this scope.
    if((!it->second) || (MyL && it->second->contains(MyL)))
      return blockIsDeadWithScope(BB, it->second);
    else
      return false;
  }

}

void IntegrationAttempt::setBlockDead(BasicBlock* BB) {

  deadBlocks.insert(BB);

}

const Loop* IntegrationAttempt::getBlockScope(BasicBlock* BB) {

  DenseMap<BasicBlock*, const Loop*>::iterator it = invariantBlocks.find(BB);
  if(it == invariantBlocks.end())
    return LI[&F]->getLoopFor(BB);
  else
    return it->second;
  
}

bool IntegrationAttempt::blockIsCertain(BasicBlock* BB) {

  const Loop* BlockL = LI[&F]->getLoopFor(BB);
  const Loop* MyL = getLoopContext();

  if(((!MyL) && BlockL) || (MyL != BlockL && MyL->contains(BlockL))) {

    if(PeelAttempt* LPA = getPeelAttempt(BlockL)) {

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
	  F->getName() == "__time_localtime_tzi" ||
	  F->getName() == "fwrite" ||
	  F->getName() == "memset_byte_fn" ||
	  F->getName() == "nl_langinfo");

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

  if((!pass->shouldAlwaysInline(FCalled)) && !certainBlocks.count(CI->getParent())) {
    LPDEBUG("Ignored " << itcache(*CI) << " because it is not yet certain to execute\n");
    return 0;
  }

  if(getLoopContext() != LI[&F]->getLoopFor(CI->getParent())) {
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

  pass->queueCheckBlock(IA, &(FCalled->getEntryBlock()));
  // Check every argument, for natural constants or for variables that have already been established.
      
  for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	  
    pass->queueTryEvaluate(IA, &*AI /* Iterator to pointer */);

  }

  IA->queueInitialWork();

  // Recheck any loads that were clobbered by this call
  queueWorkBlockedOn(CI);

  // Try reading the return value right away, in case it's constant.
  pass->queueTryEvaluate(this, CI);

  return IA;

}

class CheckBlockCallback : public Callable {
  BasicBlock* BB;
  IntegrationHeuristicsPass* IHP;
public:
  CheckBlockCallback(BasicBlock* _BB, IntegrationHeuristicsPass* _IHP) : BB(_BB), IHP(_IHP) { }
  virtual void callback(IntegrationAttempt* Ctx) {
    IHP->queueCheckBlock(Ctx, BB);
    Ctx->checkBlockPHIs(BB);
  }
};

void PeelIteration::queueCheckExitBlock(BasicBlock* BB) {

  // Only called if the exit edge is a local variant
  CheckBlockCallback CBC(BB, pass);
  callWithScope(CBC, LI[&F]->getLoopFor(BB));

}

void PeelIteration::checkExitEdge(BasicBlock* FromBB, BasicBlock* ToBB) {

  const Loop* EScope = getEdgeScope(FromBB, ToBB);
  if(EScope && L->contains(EScope)) {
    queueCheckExitBlock(ToBB);
  }
  else {
    LPDEBUG("Ignoring exit edge " << FromBB->getName() << " -> " << ToBB->getName() << " at this scope (invariant)\n");
  }

}

void PeelIteration::checkFinalIteration() {

  // Check whether we now have evidence the loop terminates this time around
  // If it does, queue consideration of each exit PHI; by LCSSA these must belong to our parent.

  if(edgeIsDead(L->getLoopLatch(), L->getHeader())) {

    iterStatus = IterationStatusFinal;

    if(isOnlyExitingIteration()) {

      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = parentPA->ExitEdges.begin(), EE = parentPA->ExitEdges.end(); EI != EE; ++EI) {
      
	checkExitEdge(EI->first, EI->second);
	
      }
    
      // Loads might now be able to be raised through this loop. They will be blocked at parent scope.
      parent->queueCFGBlockedLoads();

    }

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
    
  BasicBlock* Header = L->getHeader();
   
  pass->queueCheckBlock(NewIter, L->getHeader());
  NewIter->checkBlockPHIs(L->getHeader());

  for(BasicBlock::iterator BI = Header->begin(), BE = Header->end(); BI != BE && isa<PHINode>(BI); ++BI) {
	
    pass->queueTryEvaluate(NewIter, BI);

  }
  
  NewIter->queueInitialWork();

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

  if(PeelAttempt* PA = getPeelAttempt(NewL))
    return PA;
  
  // Preheaders only have one successor (the header), so this is enough.
  if(!certainBlocks.count(NewL->getLoopPreheader())) {
   
    LPDEBUG("Will not expand loop " << NewL->getHeader()->getName() << " at this time because the preheader is not certain to execute\n");
    return 0;

  }

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, LI, TD, AA, invariantInsts, invariantEdges, invariantBlocks, NewL, nesting_depth + 1);
    peelChildren[NewL] = LPA;

    queueCFGBlockedLoads();

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

// Given a MemDep Def, get the value loaded or stored.
void IntegrationAttempt::getDefn(const MemDepResult& Res, ValCtx& improved) {
  
  IntegrationAttempt* QueryCtx = Res.getCookie() ? ((IntegrationAttempt*)Res.getCookie()) : this;
  improved = VCNull;
  if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
    improved = QueryCtx->getReplacement(SI->getOperand(0));
  }
  else {
    LPDEBUG("Defined by " << itcache(*(Res.getInst())) << " which is not a simple load or store\n");
    return;
  }

  if(improved.first != Res.getInst() || improved.second != QueryCtx) {
    LPDEBUG("Definition improved to " << itcache(improved) << "\n");
    return;
  }
  else {
    improved = VCNull;
    LPDEBUG("Definition not improved\n");
    return;
  }

}

static bool shouldBlockOnInst(Instruction* I, IntegrationAttempt* ICtx) {

  if(!I)
    return false;

  if(CallInst* CI = dyn_cast<CallInst>(I)) {

    // An apparent dependence on the call site means either (a) we couldn't build a symbolic expression,
    // only fixable by improving the loaded pointer, or (b) the call is not expanded (in which case this
    // test fails), or (c) multiple results within the call (in which case the appropriate queueing is
    // done elsewhere)

    return !ICtx->getInlineAttempt(CI);

  }
  else if(I->mayWriteToMemory()) {

    return true;

  }

  return false;

}

void IntegrationAttempt::getDependencies(LFAQueryable& LFA, bool startNonLocal, bool PBMode, SmallVector<NonLocalDepResult, 4>& NLResults) {

  MemoryDependenceAnalyser MD;
  MD.init(AA, this, &(LFA.getLFA()), true /* Ignore dependencies on load instructions */, PBMode);

  LoadInst* QueryInst = LFA.getQueryInst();

  if(!startNonLocal)
    NLResults.push_back(NonLocalDepResult(QueryInst->getParent(), MD.getDependency(QueryInst), QueryInst->getOperand(0)));

  if(startNonLocal || NLResults[0].getResult().isNonLocal()) {

    Value* LPointer = QueryInst->getOperand(0);
    const Type *EltTy = cast<PointerType>(LPointer->getType())->getElementType();
    uint64_t PointeeSize = AA->getTypeStoreSize(EltTy);
    PHITransAddr LAddr(LPointer, TD, this);
    DenseMap<BasicBlock*, Value*> Visited;
    Visited.insert(std::make_pair(QueryInst->getParent(), LPointer));

    if(MD.getNonLocalPointerDepFromBB(LAddr, PointeeSize, true, QueryInst->getParent(), NLResults, Visited, !startNonLocal)) {

      NLResults.clear();
      NLResults.push_back(NonLocalDepResult(QueryInst->getParent(),
					    MemDepResult::getClobber(QueryInst->getParent()->begin()),
					    LPointer));

    }

  }

}

void IntegrationAttempt::addPBResults(LoadForwardAttempt& RealLFA, SmallVector<NonLocalDepResult, 4>& NLResults) {

  // Integrate the defs and clobbers found with the pointer base result.

  for(unsigned int i = 0; i < NLResults.size() && !RealLFA.PBIsOverdef(); i++) {

    const MemDepResult& Res = NLResults[i].getResult();

    if(Res.isDef()) {

      if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
	PointerBase NewPB;
	if(getPointerBase(SI->getOperand(0), NewPB, SI))
	  RealLFA.addPBDefn(NewPB);
	else
	  RealLFA.setPBOverdef();
      }
      else {
	RealLFA.setPBOverdef();
      }

    }
    else if(Res.isClobber() && !Res.isEntryNonLocal()) {

      IntegrationAttempt* ResCtx = Res.getCookie() ? (IntegrationAttempt*)Res.getCookie() : this;
      Instruction* Inst = Res.getInst();
      if(CallInst* CI = dyn_cast<CallInst>(Inst)) {
	
	// Expanded calls that clobber the concrete result don't clobber the pointer base
	// unless it was already explicitly clobbered whilst investigating within the call.
	if(ResCtx->getInlineAttempt(CI))
	  continue;

      }
      RealLFA.setPBOverdef();

    }

  }

}

// Find the unique definer or clobberer for a given Load.
// The startNonLocal parameter means that we should use getNonLocalPointerDepFromBB from the outset
// rather than using getDependency first.
// On the one hand that means checking the block from the beginning (so this wouldn't make sense
// if we were asking about a load in the middle of the block), but on the other hand it means we're
// capable of immediately calling back into tryForwardLoadThroughLoopFromBB if appropriate.
// This is used to handle the case that we try to LFA over a loop with an exit edge that exits
// more than one loop: then we call this with startNonLocal = true, which calls tryForwardThroughLoop,
// which calls this again... for each nested loop. That way we neatly mirror the situation when loops
// have a more pedestrian nesting situation.

// Notes about our use of MD: we call it twice, first in order to find out the unique dependency of the given LFA,
// then again to gather pointer base results. MD is flipped into 2 different modes for these cases.
// In its first, "normal" mode, MD regards any defs or clobbers in a scope as a cue to explore no further.
// In its second, "pointer base" mode, MD will look through loops and calls which "may define" the pointer base.
// That is, contexts which are known to either (a) set the pointer to have a known base, or (b) not modify it.
// Using the pointer result after running "normal" mode is actually incorrect, as you might have something like
// store %x, %y ; Clobbers all memory
// call @somefun ( ... ) ; Clobbers in normal mode, but maybe-defines the pointer
// In this situation the correct answer is that the pointer is overdefined (maybe somefun affects it, but the store
// overdefines it), but normal mode will stop looking at the call and call it a clobber.
MemDepResult IntegrationAttempt::getUniqueDependency(LFAQueryable& LFA, bool startNonLocal, bool& MayDependOnParent, bool& OnlyDependsOnParent, LoadForwardMode LFM) {

  MemDepResult Seen;
  LoadInst* OriginalInst = LFA.getOriginalInst();
  LoadForwardAttempt& RealLFA = LFA.getLFA();

  if(LFM != LFMPB) {

    SmallVector<NonLocalDepResult, 4> InstResults;
    getDependencies(LFA, startNonLocal, false, InstResults);
  
    if(InstResults.size() == 0) {

      // Probably we're in a block which is dead, but has yet to be diagnosed as such.
      LFA.getLFA().setPBOverdef();
      return MemDepResult();

    }

    for(unsigned int i = 0; i < InstResults.size(); i++) {

      bool isParentDep = false;

      const MemDepResult& Res = InstResults[i].getResult();

      if(Res.isNonLocal())
	continue;

      if(Res.isClobber() && parent && (Res.getInst()->getParent() == getEntryBlock())) {
	BasicBlock::iterator TestII(Res.getInst());
	if(TestII == getEntryBlock()->begin()) {
	  isParentDep = true;
	}
      }

      if(Res == Seen)
	continue;
      else if(Seen == MemDepResult()) { // Nothing seen yet
	if(isParentDep)
	  OnlyDependsOnParent = true;
	Seen = Res;
      }
      else {
	
	LPDEBUG(itcache(*OriginalInst) << " is overdefined: depends on at least " << itcache(Seen) << " and " << itcache(Res) << "\n");
	IntegrationAttempt* OrigCtx = LFA.getOriginalCtx();
	OrigCtx->setLoadOverdef(OriginalInst, InstResults);

	for(unsigned int i = 0; i < InstResults.size(); i++) {
		
	  // If there are two clobbers, or a clobber and a def, improvement of a clobber might
	  // yield 1-def or 1-clobber. Defs will always Def unless edges get killed.
	  const MemDepResult& Res = InstResults[i].getResult();
	  if(Res.isClobber() && !Res.isEntryNonLocal()) {

	    IntegrationAttempt* BlockCtx = Res.getCookie() ? ((IntegrationAttempt*)Res.getCookie()) : this;

	    if(shouldBlockOnInst(Res.getInst(), BlockCtx)) {
	      BlockCtx->addBlockedLoad(Res.getInst(), OrigCtx, OriginalInst);
	      //errs() << "Block load " << itcache(*LFA.getOriginalInst()) << " on " << itcache(*(Res.getInst())) << "\n";
	    }

	  }
	  
	}

	OnlyDependsOnParent = false;
	Seen = MemDepResult();
	break;

      }

    }

    if(Seen != MemDepResult())
      LPDEBUG(itcache(*OriginalInst) << " defined by " << itcache(Seen) << "\n");

    addPBResults(RealLFA, InstResults);
  
    // Do we need to investigate the pointer base result more carefully?
    // Easy case 1: only depends on parent. Then PB result = normal result = no local defs or clobbers.
    if(OnlyDependsOnParent)
      return Seen;

    // Easy case 2: The pointer is a no-hoper at this point.
    if(!RealLFA.PBIsViable())
      return Seen;
    
  }

  if(LFM != LFMNormal) {

    // If the pointer base result isn't conclusive yet, run MD again looking over calls and loops that may-define.
    // Note we *cannot* calculate MayDependOnParent yet as the above result includes e.g. truncation due to
    // calls that clobber the concrete result.

    SmallVector<NonLocalDepResult, 4> PBResults;
    getDependencies(LFA, startNonLocal, true, PBResults);

    for(unsigned int i = 0; i < PBResults.size(); i++) {

      const MemDepResult& Res = PBResults[i].getResult();
      if(Res.isClobber() && parent && (Res.getInst()->getParent() == getEntryBlock())) {
	BasicBlock::iterator TestII(Res.getInst());
	if(TestII == getEntryBlock()->begin()) {
	  MayDependOnParent = true;
	}
      }

    }

    addPBResults(RealLFA, PBResults);

  }

  return Seen;

}

void IntegrationAttempt::setLoadOverdef(LoadInst* LI, SmallVector<NonLocalDepResult, 4>& Res) {

  LastLoadOverdefs[LI] = Res;

}

ValCtx IntegrationAttempt::getUltimateUnderlyingObject(Value* V) {

  ValCtx Ultimate = getDefaultVC(V);
  while(!isIdentifiedObject(Ultimate.first)) {

    ValCtx New;
    if(Ultimate.second)
      New = Ultimate.second->getReplacement(Ultimate.first);
    else
      New = Ultimate;
    New = make_vc(New.first->getUnderlyingObject(), New.second);
 
    if(New == Ultimate)
      break;

    Ultimate = New;

  }

  return Ultimate;

}

void IntegrationAttempt::blockVA(ValCtx LoadVC) {

  BlockedVALoads.push_back(LoadVC);

}

void IntegrationAttempt::queueBlockedVAs() {
  
  for(SmallVector<ValCtx, 1>::iterator it = BlockedVALoads.begin(), it2 = BlockedVALoads.end(); it != it2; ++it) {

    pass->queueCheckLoad(it->second, cast<LoadInst>(it->first));

  }

  BlockedVALoads.clear();

}

void InlineAttempt::getVarArg(uint64_t idx, ValCtx& Result) {

  if(idx >= (CI->getNumArgOperands() - F.arg_size())) {
    
    errs() << "Vararg index " << idx << ": out of bounds\n";
    Result = VCNull;

  }
  else {

    Result = parent->getReplacement(CI->getArgOperand(F.arg_size() + idx));

  }

}

void PeelIteration::getVarArg(uint64_t idx, ValCtx& Result) {

  parent->getVarArg(idx, Result);

}

bool IntegrationAttempt::tryResolveLoadFromConstant(LoadInst* LoadI, ValCtx& Result) {

  // A special case: loading from a symbolic vararg:

  ValCtx LPtr = getReplacement(LoadI->getPointerOperand());
  LPtr = make_vc(LPtr.first->stripPointerCasts(), LPtr.second, LPtr.offset, LPtr.va_arg);

  if(LPtr.isVaArg()) {
    
    LPtr.second->getVarArg(LPtr.va_arg, Result);
    errs() << "va_arg " << itcache(LPtr) << " " << LPtr.va_arg << " yielded " << itcache(Result) << "\n";
    // Is this va_arg read out of bounds?
    if(Result == VCNull)
      return true;

    if(!shouldForwardValue(Result)) {

      Result = VCNull;
      LPtr.second->blockVA(make_vc(LoadI, this));

    }
    return true;

  }

  int64_t Offset = 0;
  ValCtx Base = GetBaseWithConstantOffset(LoadI->getPointerOperand(), this, Offset);

  if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(Base.first)) {
    if(GV->isConstant()) {

      uint64_t LoadSize = (TD->getTypeSizeInBits(LoadI->getType()) + 7) / 8;

      Result = extractAggregateMemberAt(GV->getInitializer(), Offset, LoadI->getType(), LoadSize, TD);
      if(Result != VCNull)
	return true;

      int64_t CSize = TD->getTypeAllocSize(GV->getInitializer()->getType());
      if(CSize < Offset) {

	LPDEBUG("Can't forward from constant: read from global out of range\n");
	Result = VCNull;
	return true;

      }

      unsigned char* buf = (unsigned char*)alloca(LoadSize);
      memset(buf, 0, LoadSize);
      if(ReadDataFromGlobal(GV->getInitializer(), Offset, buf, LoadSize, *TD)) {

	Result = const_vc(constFromBytes(buf, LoadI->getType(), TD));
	return true;

      }
      else {

	LPDEBUG("ReadDataFromGlobal failed\n");
	Result = VCNull;
	return true;

      }

    }
  }

  // Check whether pursuing alises is pointless -- this is true if we're certain that the ultimate underlying object is a constant.
  // If it is, our attempt above was likely foiled only by uncertainty about the specific bit of the constant (e.g. index within a const string)
  // and the only way the situation will improve is if those offsets become clear.
  // Note this isn't as redundant as it looks, since GUUO doesn't give up when it hits an uncertain GEP,
  // unlike GBWCO above.

  ValCtx Ultimate = getUltimateUnderlyingObject(LoadI->getPointerOperand());

  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(Ultimate.first)) {

    if(GV->isConstant()) {
      LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
      Result = VCNull;
      return true;
    }

  }

  return false;

}

// Main load forwarding entry point:
// Try to forward the load locally (within this loop or function), or otherwise build a symbolic expression
// and ask our parent to continue resolving the load.
ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LoadI) {

  LPDEBUG("Trying to forward load: " << itcache(*LoadI) << "\n");

  LoadForwardAttempt Attempt(LoadI, this, TD);

  ValCtx ConstResult;
  if(tryResolveLoadFromConstant(LoadI, ConstResult))
    return ConstResult;

  MemDepResult Res = tryResolveLoad(Attempt);

  if(Attempt.PBIsViable()) {

    LPDEBUG("Load PB " << itcache(*LoadI) << " defined to base " << itcache(Attempt.PB.Base) << "\n");

    resolvePointerBase(LoadI, Attempt.PB.Base);

    PointerBase OldPB;
    bool OldPBValid = getPointerBaseFalling(LoadI, OldPB);
    if((!OldPBValid) || OldPB.Base != Attempt.PB.Base || OldPB.Overdef != Attempt.PB.Overdef) {

      pointerBases[LoadI] = Attempt.PB;
      queueUsersUpdatePB(LoadI, !Attempt.PB.Overdef);

    }

  }
  else {

    LPDEBUG("Load PB " << itcache(*LoadI) << " overdefined\n");

  }

  return getForwardedValue(Attempt, Res);

}

// Alternative entry point for users who've pre-created a symbolic expression
ValCtx IntegrationAttempt::tryForwardLoad(LoadForwardAttempt& LFA, Instruction* StartBefore) {

  ValCtx ConstVC = VCNull;

  MemDepResult Res = tryResolveLoad(LFA, StartBefore, ConstVC);

  if(ConstVC != VCNull && Res == MemDepResult()) {
    return ConstVC;
  }
  else {
    return getForwardedValue(LFA, Res);
  }

}

ValCtx IntegrationAttempt::getForwardedValue(LoadForwardAttempt& LFA, MemDepResult Res) {

  LoadInst* LoadI = LFA.getOriginalInst();
  IntegrationAttempt* ResAttempt = (Res.getCookie() ? (IntegrationAttempt*)Res.getCookie() : this);
  ValCtx Result = VCNull;
  PartialVal PV = PVNull;

  if(Res.isClobber()) {
    // See if we can do better for clobbers by misaligned stores, memcpy, read calls, etc.
    PV = tryResolveClobber(LFA, make_vc(Res.getInst(), ResAttempt), Res.isEntryNonLocal());
  }
  else if(Res.isDef()) {
    ValCtx DefResult;
    getDefn(Res, DefResult);

    if(DefResult == VCNull) {
      Result = VCNull;
      goto out;
    }
    PV = PartialVal::getTotal(DefResult);
  }

  if(PV == PVNull) {
    Result = VCNull;
    goto out;
  }

  // Might fail if it turns out the constant is unreadable,
  // for example because it contains global variable of function pointers.
  if(!LFA.addPartialVal(PV)) {
    Result = VCNull;
    goto out;
  }

  if(LFA.isComplete()) {
      
    // Extract the bytes and try to bitcast to the appropriate type
    Result = LFA.getResult();

  }
  else {

    BasicBlock* ResBB = Res.getInst()->getParent();
    if(ResBB == &(ResBB->getParent()->getEntryBlock()) && Res.getInst() == ResBB->begin() && !ResAttempt->hasParent()) {

      LPDEBUG("This does not complete the load, and there are no further predecessors\n");
      return VCNull;

    }
    else {

      LPDEBUG("This does not complete the load: requerying starting at " << itcache(*(Res.getInst())) << "\n");
      return ResAttempt->tryForwardLoad(LFA, Res.getInst());

    }
  }

 out:
  
  if(Result == VCNull || !shouldForwardValue(Result)) {

    if(Result == VCNull) {
      if(Res.isDef())
	LPDEBUG("Load resolved successfully, but we couldn't retrieve a value from the defining instruction\n");
    }
    else {
      LPDEBUG("Load resolved successfully, but " << itcache(Result) << " is not a forwardable value\n");
    }

    IntegrationAttempt* BlockCtx = Res.getCookie() ? ((IntegrationAttempt*)Res.getCookie()) : this;
    if(shouldBlockOnInst(Res.getInst(), BlockCtx)) {
      ResAttempt->addBlockedLoad(Res.getInst(), this, LoadI);
    // Otherwise we're stuck due to a PHI translation failure. That'll only improve when the load pointer is improved.
    }

    if(Res.getInst() && Res.getCookie()) {
      
      Res.getCookie()->queueLoopExpansionBlockedLoad(Res.getInst(), this, LoadI);

    }

    LastLoadFailures[LoadI] = Res;

    return VCNull;

  }
  else {
    LastLoadFailures.erase(LoadI);
    return Result;
  }

}

MemDepResult IntegrationAttempt::tryResolveLoad(LoadForwardAttempt& Attempt) {

  MemDepResult Result;
  bool OnlyDependsOnParent;
  bool MayDependOnParent = false;

  OnlyDependsOnParent = forwardLoadIsNonLocal(Attempt, Result, false, MayDependOnParent, LFMBoth);

  if(OnlyDependsOnParent || (MayDependOnParent && Attempt.PBIsViable())) {

    if((!parent) || !Attempt.canBuildSymExpr()) {
      Attempt.setPBOverdef();
      return MemDepResult();
    }

    LPDEBUG("Will resolve ");
    DEBUG(Attempt.describeSymExpr(dbgs()));
    DEBUG(dbgs() << "\n");

    MemDepResult SubResult = tryForwardExprFromParent(Attempt);
    if(OnlyDependsOnParent)
      return SubResult;
    else
      return Result;

  }
  else {
    if(Result != MemDepResult()) {
      LPDEBUG("Forwarded " << itcache(*(Attempt.getOriginalInst())) << " locally: got " << itcache(Result) << "\n");
    }
    return Result;
  }

}

// Alternative entry point for users which externally prepare a symbolic expression
// and specify a start point.
// Use normal mode since we can't do pointer base analysis across this kind of subsidiary
// investigation yet.

MemDepResult IntegrationAttempt::tryResolveLoad(LoadForwardAttempt& Attempt, Instruction* StartBefore, ValCtx& ConstVC) {

  MemDepResult Result;
  bool MayDependOnParent = false;
  bool OnlyDependsOnParent;

  OnlyDependsOnParent = tryResolveExprFrom(Attempt, StartBefore, Result, ConstVC, LFMNormal, MayDependOnParent);

  if(OnlyDependsOnParent || (MayDependOnParent && Attempt.PBIsViable())) {
    MemDepResult SubResult = tryForwardExprFromParent(Attempt);
    if(OnlyDependsOnParent)
      return SubResult;
    else
      return Result;
  }
  else {
    return Result;
  }
  
}

// Pursue a load further. Current context is a function body; ask our caller to pursue further.
MemDepResult InlineAttempt::tryForwardExprFromParent(LoadForwardAttempt& LFA) {

  if(!parent) {
    LPDEBUG("Unable to pursue further; this function is the root\n");
    LFA.setPBOverdef();
    return MemDepResult();
  }
  else {
    if(LFA.getBaseContext() == this) {
      LPDEBUG("Can't pursue LFA further because this is its base context\n");
      LFA.setPBOverdef();
      return MemDepResult();
    }
    else {
      LPDEBUG("Resolving load at call site\n");
      return parent->tryResolveLoadAtChildSite(this, LFA);
    }
  }

}

bool PeelAttempt::tryForwardExprFromIter(LoadForwardAttempt& LFA, int originIter, MemDepResult& Result, bool& MayDependOnParent, LoadForwardMode LFM) {

  // First of all, try winding backwards through our sibling iterations. We can use a single realisation
  // of the LFA for all of these checks, since the instructions are always the same.

  LFARealization LFAR(LFA, Iterations[0], L->getLoopLatch()->getTerminator());
  
  LPDEBUG("Trying to resolve by walking backwards through loop " << L->getHeader()->getName() << "\n");

  bool OnlyDependsOnParent = true;

  for(int iter = originIter - 1; iter >= 0; iter--) {

    LPDEBUG("Trying to resolve in iteration " << iter << "\n");

    bool IterMayDependOnParent = false;

    if(!(Iterations[iter]->tryResolveExprUsing(LFAR, Result, false, IterMayDependOnParent, LFM))) {
      OnlyDependsOnParent = false;
    }

    if((!OnlyDependsOnParent) && (LFM == LFMNormal || (!IterMayDependOnParent) || !LFA.PBIsViable())) {
      // Shouldn't pursue further -- the result is either defined or conclusively clobbered here
      // and either we shouldn't look at PBs, or not even they could depend on definers further afield,
      // or the PB result is hopeless anyway.
      if(Result.isDef()) {
	LPDEBUG("Resolved to " << itcache(Result) << "\n");
      }
      else {
	LPDEBUG("Clobbered by " << itcache(Result) << "\n");
      }
      return false;
    }
    else {
      // Go round the loop and try the next iteration.
    }

    if(LFA.getBaseContext() == Iterations[iter]) {
      LPDEBUG("Abandoning resolution: " << itcache(LFA.getBaseVC()) << " is out of scope\n");
      Result = MemDepResult();
      LFA.setPBOverdef();
      MayDependOnParent = false;
      return false;
    }

  }
  
  MayDependOnParent = true;
  return OnlyDependsOnParent;

}

// Pursue a load further. Current context is a loop body -- try resolving it in previous iterations,
// then ask our enclosing loop or function body to look further.
MemDepResult PeelAttempt::tryForwardExprFromParent(LoadForwardAttempt& LFA, int originIter) {

  MemDepResult Result;
  bool MayDependOnParent = false;
  bool OnlyDependsOnParent = tryForwardExprFromIter(LFA, originIter, Result, MayDependOnParent, LFMBoth);
  if(OnlyDependsOnParent || (MayDependOnParent && LFA.PBIsViable())) {
    LPDEBUG("Resolving out the preheader edge; deferring to parent\n");
    MemDepResult SubResult = parent->tryResolveLoadAtChildSite(Iterations[0], LFA);
    if(OnlyDependsOnParent)
      return SubResult;
    else
      return Result;
  }
  else {
    return Result;
  }

}

// Helper: loop iterations defer the resolution process to the abstract loop.
MemDepResult PeelIteration::tryForwardExprFromParent(LoadForwardAttempt& LFA) {

  if(LFA.getBaseContext() == this) {
    LPDEBUG("Can't pursue LFA further because this is its base context\n");
    LFA.setPBOverdef();
    return MemDepResult();
  }
  else {
    return parentPA->tryForwardExprFromParent(LFA, this->iterationCount);
  }

}

// Try forwarding a load locally; return true if it is nonlocal or false if not, in which case
// Result is set to the resolution result.
bool IntegrationAttempt::forwardLoadIsNonLocal(LFAQueryable& LFAQ, MemDepResult& Result, bool startNonLocal, bool& MayDependOnParent, LoadForwardMode LFM) {

  bool OnlyDependsOnParent = false;
  Result = getUniqueDependency(LFAQ, startNonLocal, MayDependOnParent, OnlyDependsOnParent, LFM);

  if(OnlyDependsOnParent)
    return true;

  if(Result == MemDepResult()) {
    // The definition or clobber was not unique. Edges need to be killed before this can be resolved.
    addCFGBlockedLoad(LFAQ.getOriginalCtx(), LFAQ.getOriginalInst());
  }

  if(Result != MemDepResult() && (!Result.getCookie())) {
    // This result is generated by MD, not one of our callbacks for handling child contexts
    // Tag it as originating here
    Result.setCookie(this);
  }

  return false;

}

bool IntegrationAttempt::tryResolveExprUsing(LFARealization& LFAR, MemDepResult& Result, bool startNonLocal, bool& MayDependOnParent, LoadForwardMode LFM) {

  LFARMapping LFARM(LFAR, this);

  return forwardLoadIsNonLocal(LFAR, Result, startNonLocal, MayDependOnParent, LFM);

}

bool IntegrationAttempt::tryResolveExprFrom(LoadForwardAttempt& LFA, Instruction* Where, MemDepResult& Result, bool startNonLocal, LoadForwardMode LFM, bool& MayDependOnParent) {

  LFARealization LFAR(LFA, this, Where);
  
  return tryResolveExprUsing(LFAR, Result, startNonLocal, MayDependOnParent, LFM);

}

bool IntegrationAttempt::tryResolveExprFrom(LoadForwardAttempt& LFA, Instruction* Where, MemDepResult& Result, ValCtx& ConstResult, LoadForwardMode LFM, bool& MayDependOnParent) {

  LFARealization LFAR(LFA, this, Where);

  if(tryResolveLoadFromConstant(LFAR.getQueryInst(), ConstResult)) {
    Result = MemDepResult();
    return false;
  }

  return tryResolveExprUsing(LFAR, Result, false, MayDependOnParent, LFM);

}

// Entry point for a child loop or function that wishes us to continue pursuing a load.
// Find the instruction before the child begins (so loop preheader or call site), realise the given symbolic
// expression, and try ordinary load forwarding from there.
MemDepResult IntegrationAttempt::tryResolveLoadAtChildSite(IntegrationAttempt* IA, LoadForwardAttempt& LFA) {

  MemDepResult Result;
  bool MayDependOnParent = false;

  LPDEBUG("Continuing resolution from entry point " << itcache(*(IA->getEntryInstruction())) << "\n");

  bool OnlyDependsOnParent = tryResolveExprFrom(LFA, IA->getEntryInstruction(), Result, false, LFMBoth, MayDependOnParent);
  if(OnlyDependsOnParent) {
    LPDEBUG("Still nonlocal, passing to our parent scope\n");
    return tryForwardExprFromParent(LFA);
  }
  else if(LFA.PBIsViable() && MayDependOnParent) {
    LPDEBUG("Load forwarding forestalled, passing to our parent scope for pointer base analysis only\n");
    tryForwardExprFromParent(LFA);
    return Result;
  }
  else {
    LPDEBUG("Resolved at this scope: " << itcache(Result) << "\n");
    return Result;
  }

}

bool InlineAttempt::tryForwardLoadFromExit(LoadForwardAttempt& LFA, MemDepResult& Result, bool& MayDependOnParent) {

  BasicBlock* RetBB = pass->getUniqueReturnBlock(&F);

  if(!RetBB) {

    LPDEBUG("Can't investigate because this function has no unique return block! Run -mergereturn\n");
    return false;

  }

  MayDependOnParent = false;
  bool OnlyDependsOnParent = tryResolveExprFrom(LFA, RetBB->getTerminator(), Result, false, LFMBoth, MayDependOnParent);

  if(OnlyDependsOnParent) {
    Result = MemDepResult::getNonLocal();
    return true;
  }
  else {
    return Result.isDef() || Result.isClobber();
  }

}

bool IntegrationAttempt::tryForwardLoadThroughCall(LoadForwardAttempt& LFA, CallInst* CI, MemDepResult& Result, bool& MayDependOnParent) {

  InlineAttempt* IA = getInlineAttempt(CI);

  if(!IA) {
    // Our caller is responsible for e.g. trying plain old getModRefInfo to circumvent this restriction
    LPDEBUG("Unable to pursue load through call " << itcache(*CI) << " as it has not yet been explored\n");
    return false;
  }

  LPDEBUG("Trying to forward load " << itcache(*(LFA.getOriginalInst())) << " through call " << itcache(*CI) << ":\n");
  
  bool ret;

  if(!LFA.canBuildSymExpr())
    return false;

  ret = IA->tryForwardLoadFromExit(LFA, Result, MayDependOnParent);

  if(!ret) {
    LPDEBUG("Call " << itcache(*CI) << " clobbers " << itcache(*(LFA.getOriginalInst())) << "\n");
  }
  else if(Result.isNonLocal()) {
    LPDEBUG("Call " << itcache(*CI) << " doesn't affect " << itcache(*(LFA.getOriginalInst())) << "\n");
  }
  else {
    LPDEBUG("Call " << itcache(*CI) << " defines " << itcache(*(LFA.getOriginalInst())) << "\n");
  }

  return ret;

}

bool PeelAttempt::tryForwardLoadThroughLoopFromBB(BasicBlock* BB, LoadForwardAttempt& LFA, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result, bool PBMode) {

  // MDA has just traversed an exit edge. Pursue the load from the exiting block to the header,
  // then from latch to preheader like the forward-from-parent case. Cache in the LFA object
  // which exit block -> header paths and which Loops' main bodies have already been investigated.

  PreheaderOut = 0;

  if(!(Iterations.back()->isOnlyExitingIteration())) {
    
    LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " through loop " << (L->getHeader()->getName()) << " without per-iteration knowledge as it is not yet known to terminate\n");
    return false;

  }
  
  /*
  std::pair<DenseMap<std::pair<BasicBlock*, const Loop*>, MemDepResult>::iterator, bool> LastIterEntry = LFA.getLastIterCache(BB, L);
  MemDepResult& LastIterResult = LastIterEntry.first->second;

  if(!LastIterEntry.second) {
    LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " from exit block " << BB->getName() << " to header of " << L->getHeader()->getName() << " (cached: " << itcache(LastIterResult) << ")\n");
    if(!LastIterResult.isNonLocal()) {
      Result.push_back(NonLocalDepResult(BB, LastIterResult, 0)); // Hack -- NLDRs should contain the true BB where a relationship was discovered and the PHI translated address.
      return true;
    }
  }
  else {
  */

  MemDepResult LastIterResult;

  LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " from exit block " << BB->getName() << " to header of " << L->getHeader()->getName() << "\n");

  // Use startNonLocal so that if this exiting block is actually the exiting block of a nested child loop
  // as well, MDA will immediately recurse into tryForwardLoadThroughLoopFromBB.
  bool mayDependOnParent = false;
  LoadForwardMode mode = PBMode ? LFMPB : LFMNormal;
  if(Iterations.back()->tryResolveExprFrom(LFA, BB->getTerminator(), LastIterResult, /* startNonLocal = */ true, mode, mayDependOnParent)) {
    LastIterResult = MemDepResult::getNonLocal();
  }
  else {
    if(LastIterResult.isClobber()) {
      LPDEBUG(itcache(*(LFA.getOriginalInst())) << " clobbered in last iteration of " << L->getHeader()->getName() << "\n");
    }
    else {
      LPDEBUG(itcache(*(LFA.getOriginalInst())) << " defined in last iteration of " << L->getHeader()->getName() << "\n");
    }
    Result.push_back(NonLocalDepResult(BB, LastIterResult, 0));
    if((!PBMode) || (!mayDependOnParent) || !LFA.PBIsViable())
      return true;
  }

  // OK, try raising the load through the iterations before the last.
  /*
  std::pair<DenseMap<const Loop*, MemDepResult>::iterator, bool> OtherItersEntry = LFA.getOtherItersCache(L);
  MemDepResult& OtherItersResult = OtherItersEntry.first->second;

  if(!OtherItersEntry.second) { 
    LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " through main body of " << L->getHeader()->getName() << " (cached: " << itcache(OtherItersResult) << ")\n");
    if(!OtherItersResult.isNonLocal()) {
      Result.push_back(NonLocalDepResult(BB, OtherItersResult, 0));
      return true;
    }
  }
  else {
  */

  MemDepResult OtherItersResult;

  LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " through main body of " << L->getHeader()->getName() << "\n");
  bool itersMayDependOnParent = false;
  if(tryForwardExprFromIter(LFA, Iterations.size() - 1, OtherItersResult, itersMayDependOnParent, mode)) {
    OtherItersResult = MemDepResult::getNonLocal();
  }
  else {
    if(OtherItersResult.isClobber()) {
      LPDEBUG(itcache(*(LFA.getOriginalInst())) << " clobbered in non-final iteration of " << L->getHeader()->getName() << "\n");
    }
    else {
      LPDEBUG(itcache(*(LFA.getOriginalInst())) << " defined in non-final iteration of " << L->getHeader()->getName() << "\n");
    }
    Result.push_back(NonLocalDepResult(BB, OtherItersResult, 0));
    if((!PBMode) || (!LFA.PBIsViable()) || (!itersMayDependOnParent))
      return true;
  }

  // Made it here: the instruction propagates through the entire loop.
  PreheaderOut = L->getLoopPreheader();
  return true;

}

bool IntegrationAttempt::tryForwardLoadThroughLoopFromBB(BasicBlock* BB, LoadForwardAttempt& LFA, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result, bool PBMode) {

  const Loop* BBL = LI[&F]->getLoopFor(BB);

  if(BBL != getLoopContext() && ((!getLoopContext()) || getLoopContext()->contains(BBL))) {

    BBL = immediateChildLoop(getLoopContext(), BBL);

    PeelAttempt* LPA = getPeelAttempt(BBL);
    if(!LPA) {
      LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " through loop " << (BBL->getHeader()->getName()) << " without per-iteration knowledge as it has not yet been explored\n");
      return false;
    }

    if(!LFA.canBuildSymExpr()) {
      LPDEBUG("Raising " << itcache(*(LFA.getOriginalInst())) << " through loop " << (BBL->getHeader()->getName()) << " without per-iteration knowledge because the pointer cannot be represented simply\n");
      return false;
    }

    return LPA->tryForwardLoadThroughLoopFromBB(BB, LFA, PreheaderOut, Result, PBMode);

  }
  else {
    return false;
  }

}

void IntegrationAttempt::addBlockedLoad(Instruction* BlockedOn, IntegrationAttempt* RetryCtx, LoadInst* RetryLI) {

  InstBlockedLoads[BlockedOn].push_back(std::make_pair(RetryCtx, RetryLI));

}

void IntegrationAttempt::addCFGBlockedLoad(IntegrationAttempt* RetryCtx, LoadInst* RetryLI) {

  CFGBlockedLoads.push_back(std::make_pair(RetryCtx, RetryLI));

}

// Consider whether the forwarding of a given load might have failed due to the need to expand a loop.
// If so, queue it.
void IntegrationAttempt::queueLoopExpansionBlockedLoad(Instruction* BlockedOn, IntegrationAttempt* RetryCtx, LoadInst* RetryLI) {

  if(getLoopContext() != getValueScope(BlockedOn)) {

    LPDEBUG("Looks like this failure might be due to not having expanded a loop yet. Queueing.\n");
    addCFGBlockedLoad(RetryCtx, RetryLI);

  }

}

void IntegrationAttempt::tryPromoteOpenCall(CallInst* CI) {
  
  if(!certainBlocks.count(CI->getParent())) {
    LPDEBUG("Won't promote open call " << itcache(*CI) << " yet: not certain to execute\n");
    return;
  }

  if(forwardableOpenCalls.count(CI)) {
    LPDEBUG("Open call " << itcache(*CI) << ": already promoted\n");
    return;
  }
  
  if(Function *SysOpen = F.getParent()->getFunction("open")) {
    const FunctionType *FT = SysOpen->getFunctionType();
    if (FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
        FT->getParamType(0)->isPointerTy() &&
        FT->getParamType(1)->isIntegerTy(32) &&
	FT->isVarArg()) {

      if(Function* FCalled = getCalledFunction(CI)) {

	if(FCalled == SysOpen) {

	  ValCtx ModeArg = getReplacement(CI->getArgOperand(1));
	  if(ConstantInt* ModeValue = dyn_cast<ConstantInt>(ModeArg.first)) {
	    int RawMode = (int)ModeValue->getLimitedValue();
	    if(RawMode & O_RDWR || RawMode & O_WRONLY) {
	      LPDEBUG("Can't promote open call " << itcache(*CI) << " because it is not O_RDONLY\n");
	      return;
	    }
	  }
	  else {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its mode argument can't be resolved\n");
	    return;
	  }
	  
	  ValCtx NameArg = getReplacement(CI->getArgOperand(0));
	  std::string Filename;
	  if (!GetConstantStringInfo(NameArg.first, Filename)) {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its filename argument is unresolved\n");
	    return;
	  }

	  bool FDEscapes = false;
	  for(Value::use_iterator UI = CI->use_begin(), UE = CI->use_end(); (!FDEscapes) && (UI != UE); ++UI) {

	    if(Instruction* I = dyn_cast<Instruction>(*UI)) {

	      if(I->mayWriteToMemory()) {
		
		LPDEBUG("Marking open call " << itcache(*CI) << " escaped due to user " << itcache(*I) << "\n");
		FDEscapes = true;

	      }

	    }

	  }
	  
	  bool exists = sys::Path(Filename).exists();
	  forwardableOpenCalls[CI] = new OpenStatus(make_vc(CI, this), Filename, exists, FDEscapes);
	  if(exists) {
	    LPDEBUG("Successfully promoted open of file " << Filename << ": queueing initial forward attempt\n");
	    pass->queueOpenPush(make_vc(CI, this), make_vc(CI, this));
	  }
	  else {
	    LPDEBUG("Marking open of " << Filename << " as not existing\n");
	  }

	  // Also investigate users, since we now know it'll emit non-negative FD or return -1 with ENOENT.
	  investigateUsers(CI);
      
	}
	else {
	  
	  LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because it calls something else\n");

	}

      }
      else {
	
	LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because its target is unknown\n");

      }

    }
    else {

      LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because the symbol 'open' resolves to something with inappropriate type!\n");

    }

  }
  else {

    LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because no symbol 'open' is in scope\n");

  }

}

void IntegrationAttempt::tryPushOpen(CallInst* OpenI, ValCtx OpenProgress) {

  OpenStatus& OS = *(forwardableOpenCalls[OpenI]);

  if(OS.LatestResolvedUser != OpenProgress) {

    LPDEBUG("Skipping as call has been pushed in the meantime\n");
    return;

  }

  // Try to follow the trail from LastResolvedUser forwards.

  LPDEBUG("Trying to extend VFS op chain for " << itcache(*OpenI) << " from " << itcache(OpenProgress) << "\n");

  ValCtx NextStart = OpenProgress;
  bool skipFirst = true;

  while(NextStart.second->tryPushOpenFrom(NextStart, make_vc(OpenI, this), OpenProgress, OS, skipFirst)) {
    LPDEBUG("Continuing from " << itcache(NextStart) << "\n");
    skipFirst = false;
  }

}

ValCtx IntegrationAttempt::getSuccessorVC(BasicBlock* BB) {

  BasicBlock* UniqueSuccessor = 0;
  for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {

    if(edgeIsDead(BB, *SI))
      continue;
    else if(UniqueSuccessor) {
      UniqueSuccessor = 0;
      break;
    }
    else {
      UniqueSuccessor = *SI;
    }

  }

  if(UniqueSuccessor) {

    ValCtx Start;
    if(checkLoopIterationOrExit(BB, UniqueSuccessor, Start))
      return Start;

    Loop* SuccLoop = LI[&F]->getLoopFor(UniqueSuccessor);
    if(SuccLoop != getLoopContext()) {

      if((!getLoopContext()) || getLoopContext()->contains(SuccLoop)) {

	if(PeelAttempt* LPA = getPeelAttempt(SuccLoop)) {

	  assert(SuccLoop->getHeader() == UniqueSuccessor);
	  return make_vc(UniqueSuccessor->begin(), LPA->Iterations[0]);

	}
	else {
	      
	  LPDEBUG("Progress blocked by unexpanded loop " << SuccLoop->getHeader()->getName() << "\n");
	  return VCNull;

	}

      }
      else {

	return make_vc(UniqueSuccessor->begin(), parent);

      }

    }
    else {
	  
      if(!certainBlocks.count(UniqueSuccessor)) {

	LPDEBUG("Progress blocked because block " << UniqueSuccessor->getName() << " not yet marked certain\n");
	return VCNull;

      }
      else {

	return make_vc(UniqueSuccessor->begin(), this);

      }

    }

  }
  else {

    if(isa<ReturnInst>(BB->getTerminator())) {

      if(!parent) {

	LPDEBUG("Instruction chain reaches end of main!\n");
	return VCNull;

      }
      BasicBlock::iterator CallIt(getEntryInstruction());
      ++CallIt;
      return make_vc(CallIt, parent);

    }

    LPDEBUG("Progress blocked because block " << BB->getName() << " has no unique successor\n");
    return VCNull;

  }

}

// Called in the context of Start.second. OpenInst is the open instruction we're pursuing, and the context where OS is stored.
// ReadInst is the entry in the chain of VFS operations that starts at OpenInst.
bool IntegrationAttempt::tryPushOpenFrom(ValCtx& Start, ValCtx OpenInst, ValCtx ReadInst, OpenStatus& OS, bool skipFirst) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  while(1) {

    if(!skipFirst) {

      if(CallInst* CI = dyn_cast<CallInst>(BI)) {

	bool isVFSCall, shouldRequeue;
	if(vfsCallBlocksOpen(CI, OpenInst, ReadInst, OS, isVFSCall, shouldRequeue)) {
	  if(shouldRequeue) {
	    // Queue to retry when we know more about the call.
	    LPDEBUG("Inst blocked on " << itcache(*CI) << "\n");
	    InstBlockedOpens[CI].push_back(std::make_pair(OpenInst, ReadInst));
	  }
	  return false;
	}

	if(!isVFSCall) {

	  // This call cannot affect the FD we're pursuing unless (a) it uses the FD, or (b) the FD escapes (is stored) and the function is non-pure.
	  bool callMayUseFD = false;

	  Function* calledF = getCalledFunction(CI);

	  if(OS.FDEscapes && ((!calledF) || !calledF->doesNotAccessMemory()))
	    callMayUseFD = true;

	  if(!callMayUseFD) {

	    for(unsigned i = 0; i < CI->getNumArgOperands() && !callMayUseFD; ++i) {

	      ValCtx ArgVC = getReplacement(CI->getArgOperand(i));
	      if(ArgVC == OpenInst)
		callMayUseFD = true;
	      if(isUnresolved(CI->getArgOperand(i))) {
		LPDEBUG("Assuming " << itcache(*CI) << " may use " << itcache(OpenInst) << " due to unresolved argument " << itcache(ArgVC) << "\n");
		callMayUseFD = true;
	      }

	    }
	    
	  }

	  if(callMayUseFD) {

	    if(InlineAttempt* IA = getInlineAttempt(CI)) {

	      Start = make_vc(IA->getEntryBlock()->begin(), IA);
	      return true;

	    }
	    else {

	      LPDEBUG("Unexpanded call " << itcache(*CI) << " may affect FD from " << itcache(OpenInst) << "\n");
	      InstBlockedOpens[CI].push_back(std::make_pair(OpenInst, ReadInst));
	      return false;

	    }

	  }

	}

      }

    }

    skipFirst = false;

    ++BI;
    if(BI == BB->end()) {

      Start = getSuccessorVC(BB);

      if(Start == VCNull) {

	LPDEBUG("CFG blocked: " << BB->getName() << " has no unique successor\n");
	addBlockedOpen(OpenInst, ReadInst);
	return false;

      }
      else if(Start.second != this) {

	return true;

      }
      else {

	StartI = cast<Instruction>(Start.first);
	BB = StartI->getParent();
	BI = BasicBlock::iterator(StartI);

      }

    }

  }

}

bool InlineAttempt::checkLoopIterationOrExit(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) {

  return false;

}

bool PeelIteration::checkLoopIterationOrExit(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) {

  if(PresentBlock == L->getLoopLatch() && NextBlock == L->getHeader()) {

    PeelIteration* nextIter = getNextIteration();
    if(!nextIter) {

      LPDEBUG("Can't continue to pursue open call because loop " << L->getHeader()->getName() << " does not yet have iteration " << iterationCount+1 << "\n");
      Start = VCNull;
      return true;

    }
    else {

      Start = make_vc(L->getHeader()->begin(), nextIter);
      return true;

    }

  }
  else if(!L->contains(NextBlock)) {

    // LCSSA, so this must be our parent
    Start = make_vc(NextBlock->begin(), parent);
    return true;

  }

  return false;

}

int64_t IntegrationAttempt::tryGetIncomingOffset(Value* V) {

  CallInst* CI = cast<CallInst>(V);

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return it->second.incomingOffset + it->second.readSize;
  else {
    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end())
      return it->second.newOffset;
  }
  
  return -1;

}

ReadFile* IntegrationAttempt::tryGetReadFile(CallInst* CI) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return &it->second;
  else
    return 0;

}

void IntegrationAttempt::setNextUser(CallInst* CI, ValCtx U) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end()) {

    it->second.NextUser = U;

  }
  else {

    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end()) {

      it->second.NextUser = U;

    }
    else {

      assert(0 && "CI wasn't resolved after all?");

    }

  }

}

void IntegrationAttempt::setNextUser(OpenStatus& OS, ValCtx U) {

  if(OS.FirstUser == VCNull)
    OS.FirstUser = U;
  else
    OS.LatestResolvedUser.second->setNextUser(cast<CallInst>(OS.LatestResolvedUser.first), U);

}

bool IntegrationAttempt::vfsCallBlocksOpen(CallInst* VFSCall, ValCtx OpenInst, ValCtx LastReadInst, OpenStatus& OS, bool& isVfsCall, bool& shouldRequeue) {

  // Call to read() or close()?

  isVfsCall = false;
  shouldRequeue = false;

  Function* Callee = getCalledFunction(VFSCall);
  StringRef CalleeName = Callee->getName();
  if(CalleeName == "read") {

    const FunctionType *FT = Callee->getFunctionType();
    if (FT->getNumParams() != 3 || !FT->getParamType(0)->isIntegerTy(32) ||
	!FT->getParamType(1)->isPointerTy() || !FT->getParamType(2)->isIntegerTy() ||
	!FT->getReturnType()->isIntegerTy()) {
      LPDEBUG("Assuming call to " << *Callee << " is not 'read' due to its weird signature\n");
      return false;
    }

    isVfsCall = true;

    Value* readFD = VFSCall->getArgOperand(0);
    if(isUnresolved(readFD)) {

      LPDEBUG("Can't forward open because FD argument of " << itcache(*VFSCall) << " is unresolved\n");
      shouldRequeue = true;
      return true;

    }
    else if(getReplacement(readFD) != OpenInst) {

      LPDEBUG("Ignoring " << itcache(*VFSCall) << " which references a different file\n");
      return false;

    }

    Value* readBytes = VFSCall->getArgOperand(2);

    ConstantInt* intBytes = dyn_cast<ConstantInt>(getConstReplacement(readBytes));
    if(!intBytes) {
      LPDEBUG("Can't push " << itcache(OpenInst) << " further: read amount uncertain\n");
      shouldRequeue = true;
      return true;
    }

    // OK, we know what this read operation does. Record that and queue another exploration from this point.
    int64_t incomingOffset;
    if(LastReadInst == OpenInst)
      incomingOffset = 0;
    else {
      incomingOffset = LastReadInst.second->tryGetIncomingOffset(LastReadInst.first);
    }

    int cBytes = (int)intBytes->getLimitedValue();

    struct stat file_stat;
    if(::stat(OS.Name.c_str(), &file_stat) == -1) {
      
      LPDEBUG("Failed to stat " << OS.Name << "\n");
      return true;

    }
    
    int bytesAvail = file_stat.st_size - incomingOffset;
    if(cBytes > bytesAvail) {
      LPDEBUG("Desired read of " << cBytes << " truncated to " << bytesAvail << " (EOF)\n");
      cBytes = bytesAvail;
    }

    // OK, we know what this read operation does. Record that and queue another exploration from this point.

    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which reads " << cBytes << " bytes\n");

    resolveReadCall(VFSCall, ReadFile(&OS, incomingOffset, cBytes));
    ValCtx thisReader = make_vc(VFSCall, this);
    setNextUser(OS, thisReader);
    OS.LatestResolvedUser = thisReader;
    pass->queueOpenPush(OpenInst, thisReader);

    // Investigate anyone that refs the buffer
    investigateUsers(VFSCall->getArgOperand(1));

    // The number of bytes read is also the return value of read.
    setReplacement(VFSCall, const_vc(ConstantInt::get(Type::getInt64Ty(VFSCall->getContext()), cBytes)));
    investigateUsers(VFSCall);
    
    return true;

  }
  else if(CalleeName == "close") {
    const FunctionType *FT = Callee->getFunctionType();
    if(FT->getNumParams() != 1 || !FT->getParamType(0)->isIntegerTy(32)) {
      LPDEBUG("Assuming call to " << itcache(*Callee) << " is not really 'close' due to weird signature\n");
      return false;
    }

    isVfsCall = true;

    Value* closeFD = VFSCall->getArgOperand(0);
    if(isUnresolved(closeFD)) {
      shouldRequeue = true;
      return true;
    }
    else if(getReplacement(closeFD) != OpenInst) {
      return false;
    }

    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which closes the file\n");

    ValCtx ThisCall = make_vc(VFSCall, this);
    setNextUser(OS, ThisCall);
    OS.LatestResolvedUser = ThisCall;
    resolvedCloseCalls[VFSCall] = CloseFile(&OS);

    setReplacement(VFSCall, const_vc(ConstantInt::get(FT->getReturnType(), 0)));
    investigateUsers(VFSCall);

    return true;

  }
  else if(CalleeName == "llseek" || CalleeName == "lseek" || CalleeName == "llseek64") {

    const FunctionType* FT = Callee->getFunctionType();
    if(FT->getNumParams() != 3 || (!FT->getParamType(0)->isIntegerTy(32)) || (!FT->getParamType(1)->isIntegerTy()) || (!FT->getParamType(2)->isIntegerTy(32))) {
      LPDEBUG("Assuming call to " << itcache(*Callee) << " is not really an [l]lseek due to weird signature\n");
      return false;
    }

    isVfsCall = true;

    Value* seekFD = VFSCall->getArgOperand(0);
    if(isUnresolved(seekFD)) {
      shouldRequeue = true;
      return true;
    }
    else if(getReplacement(seekFD) != OpenInst) {
      return false;
    }

    Constant* whence = getConstReplacement(VFSCall->getArgOperand(2));
    Constant* newOffset = getConstReplacement(VFSCall->getArgOperand(1));
    
    if((!newOffset) || (!whence)) {
      LPDEBUG("Unable to push " << itcache(OpenInst) << " further due to uncertainty of " << itcache(*VFSCall) << " seek offset or whence");
      shouldRequeue = true;
      return true;
    }

    uint64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    int32_t seekWhence = (int32_t)cast<ConstantInt>(whence)->getSExtValue();

    switch(seekWhence) {
    case SEEK_CUR:
      {
	int64_t incomingOffset;
	if(LastReadInst == OpenInst)
	  incomingOffset = 0;
	else {
	  incomingOffset = LastReadInst.second->tryGetIncomingOffset(LastReadInst.first);
	}      
	intOffset += incomingOffset;
      }
      break;
    case SEEK_END:
      {
	struct stat file_stat;
	if(::stat(OS.Name.c_str(), &file_stat) == -1) {
	  
	  LPDEBUG("Failed to stat " << OS.Name << "\n");
	  return true;
	  
	}
	intOffset += file_stat.st_size;
	break;
      }  
    case SEEK_SET:
      break;
    default:
      LPDEBUG("Seek whence parameter is unknown value " << seekWhence << "!");
      return true;
    }

    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which seeks to offset " << intOffset << "\n");

    // Seek's return value is the new offset.
    setReplacement(VFSCall, const_vc(ConstantInt::get(FT->getParamType(1), intOffset)));
    investigateUsers(VFSCall);

    resolveSeekCall(VFSCall, SeekFile(&OS, intOffset));

    ValCtx seekCall = make_vc(VFSCall, this);
    setNextUser(OS, seekCall);
    OS.LatestResolvedUser = seekCall;
    pass->queueOpenPush(OpenInst, seekCall);

    return true;

  }

  return false;

}

ValCtx IntegrationAttempt::getNextVFSUser(CallInst* CI) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return it->second.NextUser;

  DenseMap<CallInst*, SeekFile>::iterator it2 = resolvedSeekCalls.find(CI);
  if(it2 != resolvedSeekCalls.end())
    return it2->second.NextUser;

  return VCNull;

}

bool IntegrationAttempt::isCloseCall(CallInst* CI) {

  return resolvedCloseCalls.count(CI);

}

void IntegrationAttempt::resolveReadCall(CallInst* CI, struct ReadFile RF) {

  resolvedReadCalls[CI] = RF;

}

void IntegrationAttempt::resolveSeekCall(CallInst* CI, struct SeekFile SF) {

  resolvedSeekCalls[CI] = SF;

}

void IntegrationAttempt::addBlockedOpen(ValCtx OpenInst, ValCtx ReadInst) {

  CFGBlockedOpens.push_back(std::make_pair(OpenInst, ReadInst));

}

bool IntegrationAttempt::isResolvedVFSCall(const Instruction* I) {
  
  if(CallInst* CI = dyn_cast<CallInst>(const_cast<Instruction*>(I))) {

    return forwardableOpenCalls.count(CI) || resolvedReadCalls.count(CI) || resolvedSeekCalls.count(CI) || resolvedCloseCalls.count(CI);

  }

  return false;

}

bool IntegrationAttempt::isSuccessfulVFSCall(const Instruction* I) {
  
  if(CallInst* CI = dyn_cast<CallInst>(const_cast<Instruction*>(I))) {

    DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.find(CI);
    if(it != forwardableOpenCalls.end() && !it->second->success)
      return false;

    return forwardableOpenCalls.count(CI) || resolvedReadCalls.count(CI) || resolvedSeekCalls.count(CI) || resolvedCloseCalls.count(CI);

  }

  return false;

}

bool IntegrationAttempt::isUnusedReadCall(CallInst* CI) {

  // Return true if CI is a read instruction that won't be in the final committed program:
  // this is true if it's zero-length or if there are no live users of the buffer it writes.
  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end()) {

    return unusedWriters.count(CI) || !it->second.readSize;

  }

  return false;

}

void PeelIteration::describe(raw_ostream& Stream) const {

  Stream << "(Loop " << L->getHeader()->getName() << "/" << iterationCount << ")";

}


void InlineAttempt::describe(raw_ostream& Stream) const {

  Stream << "(" << F.getName() << ")";

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
    
    if(MyL != L)
      continue;

    if(instructionCounts(BI)) { 

      //if(BB == getEntryBlock() && isa<PHINode>(BI))
      //  continue;

      improvableInstructions++;

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
	 << " uwttc " << unusedWritersTraversingThisContext.size() << " cbl " << CFGBlockedLoads.size()
	 << " ibl " << InstBlockedLoads.size() << " cbo " << CFGBlockedOpens.size() 
	 << " ibo " << InstBlockedOpens.size() << " foc " << forwardableOpenCalls.size()
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

// Implement LoadForwardAttempt

 LoadForwardAttempt::LoadForwardAttempt(LoadInst* _LI, IntegrationAttempt* C, TargetData* _TD, const Type* target) : LI(_LI), originalCtx(C), ExprValid(false), Result(VCNull), partialBuf(0), partialValidBuf(0), TD(_TD) {

  if(!target)
    targetType = _LI->getType();
  else
    targetType = target;

  mayBuildFromBytes = !containsPointerTypes(targetType);
  PBValid = false;

}

bool llvm::containsPointerTypes(const Type* Ty) {

  if(Ty->isPointerTy())
    return true;

  for(Type::subtype_iterator it = Ty->subtype_begin(), it2 = Ty->subtype_end(); it != it2; ++it) {

    if(containsPointerTypes(*it))
      return true;

  }

  return false;

}

const Type* LoadForwardAttempt::getTargetTy() {

  return targetType;
  
}

void LoadForwardAttempt::describeSymExpr(raw_ostream& Str) {
  
  if(!tryBuildSymExpr())
    return;

  for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
    if(it != Expr.begin())
      Str << " of ";
    (*it)->describe(Str, originalCtx);
  }
  
}

// Make a symbolic expression for a given load instruction if it depends solely on one pointer
// with many constant offsets.
bool LoadForwardAttempt::buildSymExpr(Value* RootPtr, IntegrationAttempt* RootCtx) {

  if(!RootPtr)
    RootPtr = LI->getPointerOperand();
  if(!RootCtx)
    RootCtx = originalCtx;
  
  ValCtx Ptr = RootCtx->getDefaultVC(RootPtr);

  LPDEBUG("Trying to describe " << itcache(Ptr) << " as a simple symbolic expression\n");

  // Check that we're trying to fetch a cast-of-constGEP-of-cast-of... an identified object, and
  // build a symbolic expression representing the derived expression if so.
 
  bool success = true;
  int64_t Offset = 0;

  unsigned PtrSize = TD->getPointerSizeInBits();

  while(1) {

    if(Operator* Op = dyn_cast<Operator>(Ptr.first)) {
      if(GEPOperator* GEP = dyn_cast<GEPOperator>(Op)) {
	SmallVector<Value*, 4> idxs;
	gep_type_iterator GTI = gep_type_begin(GEP);
	for (unsigned i = 1, e = GEP->getNumOperands(); i != e; ++i, ++GTI) {
	  Value* idx = GEP->getOperand(i);
	  ConstantInt* Cidx = cast_or_null<ConstantInt>(getConstReplacement(idx, Ptr.second));
	  if(Cidx) {
	    idxs.push_back(Cidx);
	    if(!Cidx->isZero()) {
	      if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
		Offset += TD->getStructLayout(STy)->getElementOffset(Cidx->getZExtValue());
	      } else {
		uint64_t Size = TD->getTypeAllocSize(GTI.getIndexedType());
		Offset += Cidx->getSExtValue()*Size;
	      }
	      // Re-extend the pointer if we really should be using a type other than int64 to measure offset.
	      if (PtrSize < 64)
		Offset = (Offset << (64-PtrSize)) >> (64-PtrSize);
	    }
	  }
	  else {
	    LPDEBUG("Can't describe pointer with non-const offset " << itcache(*idx) << "\n");
	    success = false; 
	    break;
	  }
	}
	Expr.push_back((new SymGEP(idxs)));
	Ptr = make_vc(GEP->getPointerOperand(), Ptr.second);
	continue;
      }
      else if(Op->getOpcode() == Instruction::BitCast) {
	Expr.push_back((new SymCast(Op->getType())));
	Ptr = make_vc(Op->getOperand(0), Ptr.second);
	continue;
      }
    }
    else if (Constant* C = dyn_cast<Constant>(Ptr.first)) {
      Expr.push_back(new SymThunk(const_vc(C)));
      break;
    }

    ValCtx Repl = Ptr.second->getReplacement(Ptr.first);
    if(isIdentifiedObject(Repl.first)) {
      Expr.push_back((new SymThunk(Repl)));
      break;
    }
    else if(Repl == Ptr) {
      LPDEBUG("Can't describe due to unresolved pointer " << itcache(Ptr) << "\n");
      success = false; 
      break;
    }
    else {
      Ptr = Repl; // Must continue resolving!
    }
    
  }

  if(success) {
    ExprOffset = Offset;
  }
  else {
    Expr.clear();
  }

  return success;

}

bool LoadForwardAttempt::tryBuildSymExpr(Value* Ptr, IntegrationAttempt* Ctx) {

  if(ExprValid)
    return (Expr.size() > 0);
  else {
    bool ret = buildSymExpr(Ptr, Ctx);
    ExprValid = true;
    return ret;
  }

}

bool LoadForwardAttempt::canBuildSymExpr(Value* Ptr, IntegrationAttempt* Ctx) {

  // Perhaps we could do some quickier checks than just making the thing right away?
  return tryBuildSymExpr(Ptr, Ctx);

}

SmallVector<SymExpr*, 4>* LoadForwardAttempt::getSymExpr() {
  
  assert(ExprValid && "getSymExpr without buildSymExpr");
  return &Expr;
  
}

LoadForwardAttempt& LoadForwardAttempt::getLFA() {

  return *this;

}

IntegrationAttempt* LoadForwardAttempt::getOriginalCtx() {

  return originalCtx;

}

LoadInst* LoadForwardAttempt::getOriginalInst() {

  return LI;

}

LoadInst* LoadForwardAttempt::getQueryInst() {

  return LI;

}

uint64_t LoadForwardAttempt::markPaddingBytes(bool* validBuf, const Type* Ty) {

  uint64_t marked = 0;

  if(const StructType* STy = dyn_cast<StructType>(Ty)) {
    
    const StructLayout* SL = TD->getStructLayout(STy);
    if(!SL) {
      LPDEBUG("Couldn't get struct layout for type " << *STy << "\n");
      return 0;
    }

    uint64_t EIdx = 0;
    for(StructType::element_iterator EI = STy->element_begin(), EE = STy->element_end(); EI != EE; ++EI, ++EIdx) {

      marked += markPaddingBytes(&(validBuf[SL->getElementOffset(EIdx)]), *EI);
      uint64_t ThisEStart = SL->getElementOffset(EIdx);
      uint64_t ESize = (TD->getTypeSizeInBits(*EI) + 7) / 8;
      uint64_t NextEStart = (EIdx + 1 == STy->getNumElements()) ? SL->getSizeInBytes() : SL->getElementOffset(EIdx + 1);
      for(uint64_t i = ThisEStart + ESize; i < NextEStart; ++i, ++marked) {
	
	validBuf[i] = true;

      }

    }

  }
  else if(const ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    const Type* EType = ATy->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;

    uint64_t Offset = 0;
    for(uint64_t i = 0; i < ECount; ++i, Offset += ESize) {

      marked += markPaddingBytes(&(validBuf[Offset]), EType);

    }

  }

  return marked;

}

unsigned char* LoadForwardAttempt::getPartialBuf(uint64_t nbytes) {

  if(partialBuf) {
    assert(partialBufBytes == nbytes);
  }
  else {

    uint64_t nqwords = (nbytes + 7) / 8;
    partialBuf = new uint64_t[nqwords];
    partialValidBuf = new bool[nbytes];
    for(uint64_t i = 0; i < nbytes; ++i)
      partialValidBuf[i] = false;
    uint64_t marked = markPaddingBytes(partialValidBuf, targetType);
    if(marked != 0) {
      LPDEBUG("Marked " << marked << " bytes of struct padding\n");
    }
    partialBufBytes = nbytes;

  }

  return (unsigned char*)partialBuf;

}

bool* LoadForwardAttempt::getBufValid() {

  assert(partialValidBuf);
  return partialValidBuf;

}

bool* LoadForwardAttempt::tryGetBufValid() {

  if(partialBuf)
    return partialValidBuf;
  else
    return 0;

}

LoadForwardAttempt::~LoadForwardAttempt() {

  for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
    delete (*it);
  }

  if(partialBuf)
    delete[] partialBuf;
  if(partialValidBuf)
    delete[] partialValidBuf;

}

// Precondition for both: checked Expr is a real thing already.

ValCtx LoadForwardAttempt::getBaseVC() { 
  return (cast<SymThunk>(Expr.back()))->RealVal; 
}

IntegrationAttempt* LoadForwardAttempt::getBaseContext() { 
  return getBaseVC().second; 
}

std::pair<DenseMap<std::pair<BasicBlock*, const Loop*>, MemDepResult>::iterator, bool> LoadForwardAttempt::getLastIterCache(BasicBlock* FromBB, const Loop* L) {
  return lastIterCache.insert(std::make_pair(std::make_pair(FromBB, L), MemDepResult()));
}

std::pair<DenseMap<const Loop*, MemDepResult>::iterator, bool> LoadForwardAttempt::getOtherItersCache(const Loop* L) {
  return otherItersCache.insert(std::make_pair(L, MemDepResult()));
}

int64_t LoadForwardAttempt::getSymExprOffset() {

  if(ExprValid)
    return ExprOffset;
  else
    return -1;

}

void LoadForwardAttempt::setSymExprOffset(int64_t newOffset) {

  assert(ExprValid);
  ExprOffset = newOffset;

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

static ValCtx getAsPtrAsInt(ValCtx VC, const Type* Target) {

  assert(VC.first->getType()->isPointerTy());

  if(Constant* C = dyn_cast<Constant>(VC.first)) {

    if(C->isNullValue())
      return const_vc(Constant::getNullValue(Target));

  }

  return make_vc(VC.first, VC.second, 0);

}

ValCtx llvm::extractAggregateMemberAt(Constant* FromC, uint64_t Offset, const Type* Target, uint64_t TargetSize, TargetData* TD) {

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

  if(Offset + TargetSize > FromSize) {

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

bool LoadForwardAttempt::addPartialVal(PartialVal& PV) {

  if(PV.isTotal() && !partialBuf) {

    const Type* sourceType = PV.TotalVC.first->getType();

    if(PV.TotalVC.isVaArg() || allowTotalDefnImplicitCast(sourceType, targetType)) {
      LPDEBUG("Accepting " << itcache(PV.TotalVC) << " as a total definition\n");
      Result = PV.TotalVC;
      return true;
    }
    else if(allowTotalDefnImplicitPtrToInt(sourceType, targetType, TD)) {
      LPDEBUG("Accepting " << itcache(PV.TotalVC) << " implicit ptrtoint to " << *(targetType) << "\n");
      Result = getAsPtrAsInt(PV.TotalVC, targetType);
      return true;
    }

  }

  // Try to salvage a total definition from a partial if this is a load clobbered by a store
  // of a larger aggregate type. This is to permit pointers and other non-constant forwardable values
  // to be moved about. In future ValCtx needs to get richer to become a recursive type like
  // ConstantStruct et al.

  // Note that because you can't write an LLVM struct literal featuring a non-constant,
  // the only kinds of pointers this permits to be moved around are globals, since they are constant pointers.

  Constant* SalvageC = PV.isTotal() ? dyn_cast<Constant>(PV.TotalVC.first) : PV.C;
  uint64_t LoadSize = (TD->getTypeSizeInBits(targetType) + 7) / 8;

  if(SalvageC && (PV.isTotal() || (PV.FirstDef == 0 && PV.FirstNotDef == LoadSize)) && !partialBuf) {
    uint64_t Offset = PV.isTotal() ? 0 : PV.ReadOffset;

    Result = extractAggregateMemberAt(SalvageC, Offset, targetType, LoadSize, TD);
    if(Result != VCNull) {
      LPDEBUG("Successfully extracted an entire field: " << itcache(Result) << "\n");
      return true;
    }
  }

  if(!mayBuildFromBytes) {
    LPDEBUG("Won't accept partial definition because target type " << *targetType << " contains pointers\n");
    return false;
  }

  // Otherwise we need to build our result byte-wise.
  if(PV.isTotal()) {
    Constant* TotalC = dyn_cast<Constant>(PV.TotalVC.first);
    if(!TotalC) {
      LPDEBUG("Unable to use total definition " << itcache(PV.TotalVC) << " because it is not constant but we need to perform byte operations on it\n");
      return false;
    }
    PV.C = TotalC;
  }

  uint64_t StoreSize = (TD->getTypeSizeInBits(PV.C->getType()) + 7) / 8;

  if(PV.isTotal()) {
    PV.FirstDef = 0;
    PV.FirstNotDef = std::min(LoadSize, StoreSize);
    PV.ReadOffset = 0;
  }

  // Fall through to the partial definition case.

  LPDEBUG("This store can satisfy bytes (" << PV.FirstDef << "-" << PV.FirstNotDef << "] of the source load\n");

  // Store defined some of the bytes we need! Grab those, then perhaps complete the load.
  unsigned char* partialBuf = getPartialBuf(LoadSize);
  bool* bufValid = getBufValid(); // Same size as partialBuf

  unsigned char* tempBuf = (unsigned char*)alloca(PV.FirstNotDef - PV.FirstDef);
  // ReadDataFromGlobal assumes a zero-initialised buffer!
  memset(tempBuf, 0, PV.FirstNotDef - PV.FirstDef);

  if(!ReadDataFromGlobal(PV.C, PV.ReadOffset, tempBuf, PV.FirstNotDef - PV.FirstDef, *TD)) {
    LPDEBUG("ReadDataFromGlobal failed; perhaps the source " << *(PV.C) << " can't be bitcast?\n");
    return false;
  }
  else {
    // Avoid rewriting bytes which have already been defined
    for(uint64_t i = 0; i < (PV.FirstNotDef - PV.FirstDef); ++i) {
      if(!bufValid[PV.FirstDef + i])
	partialBuf[PV.FirstDef + i] = tempBuf[i];
    }
  }

  bool loadFinished = true;
  // Meaning of the predicate: stop at the boundary, or bail out if there's no more setting to do
  // and there's no hope we've finished.
  for(uint64_t i = 0; i < LoadSize && (loadFinished || i < PV.FirstNotDef); ++i) {

    if(i >= PV.FirstDef && i < PV.FirstNotDef) {
      bufValid[i] = true;
    }
    else {
      if(!bufValid[i]) {
	loadFinished = false;
      }
    }

  }

  if(loadFinished) {

    Result = const_vc(constFromBytes(partialBuf, targetType, TD));
    if(Result == VCNull) {
      LPDEBUG("Failed to convert result to target type " << *targetType << "\n");
      return false;
    }
    else {
      LPDEBUG("This store completes the load (final value: " << itcache(Result) << ")\n");
      return true;
    }

  }

  return true;

}

bool LoadForwardAttempt::isComplete() {

  return Result != VCNull;

}

ValCtx LoadForwardAttempt::getResult() {

  return Result;

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

// Implement LFARealisation

// Realise a symbolic expression at a given location. 
// Temporary instructions are created and recorded for later deletion.
LFARealization::LFARealization(LoadForwardAttempt& _LFA, IntegrationAttempt* IA, Instruction* InsertPoint) : LFA(_LFA) {

  // Build it backwards: the in chain should end in a defined object, in or outside our scope.
  // Start with that, then wrap it incrementally in operators.
  // Precondition: LFA.canBuildSymExpr()
  
  SmallVector<SymExpr*, 4>& in = *(LFA.getSymExpr());
  SmallVector<SymExpr*, 4>::iterator SI = in.end(), SE = in.begin();
  
  Value* lastPtr;
  
  SI--;
  SymThunk* th = cast<SymThunk>(*SI);

  LLVMContext& ctx = InsertPoint->getContext();
  BasicBlock::iterator BI(InsertPoint);
  IRBuilder<> Builder(ctx);
  Builder.SetInsertPoint(InsertPoint->getParent(), *BI);

  // I make up a fake location that we're supposedly accessing. The structure is
  // %pointless = alloca()
  // %junk = load %pointless
  // %expr_0 = gep(%junk, ...)
  // %expr_1 = bitcast(%expr_0)
  // ...
  // %expr_n = gep(%expr_n_1, ...)
  // %accessor = load %expr_n
  // Then our caller should set his local improvedValues so that junk resolves to
  // the base pointer he wishes to query (i.e. the base pointer from the SymExpr),
  // and then issue a MemDep query against accessor.

  Instruction* FakeLoc = Builder.CreateAlloca(th->RealVal.first->getType());
  tempInstructions.push_back(FakeLoc);
  lastPtr = FakeBase = Builder.CreateLoad(FakeLoc);
  tempInstructions.push_back(FakeBase);

  while(SI != SE) {
    SI--;
    if(SymGEP* GEP = dyn_cast<SymGEP>(*SI)) {
      lastPtr = Builder.CreateGEP(lastPtr, GEP->Offsets.begin(), GEP->Offsets.end());
    }
    else if(SymCast* Cast = dyn_cast<SymCast>(*SI)) {
      lastPtr = Builder.CreateBitCast(lastPtr, Cast->ToType);
    }
    else {
      assert(0 && "Investigated expression should only contain GEPs and Casts except at the end\n");
    }
    //    LPDEBUG("Created temporary instruction: " << *lastPtr << "\n");
    tempInstructions.push_back(cast<Instruction>(lastPtr));
  }

  // Make up a fake load, since MD wants an accessor.
  QueryInst = Builder.CreateLoad(lastPtr);
  tempInstructions.push_back(QueryInst);

  //  LPDEBUG("Temporarily augmented parent block:\n");
  //  DEBUG(dbgs() << *InsertPoint->getParent());

}

LFARealization::~LFARealization() {

  for(SmallVector<Instruction*, 4>::iterator II = tempInstructions.end(), IE = tempInstructions.begin(); II != IE; ) {
    Instruction* I = *(--II);
    I->eraseFromParent();
  }

}

LoadInst* LFARealization::getQueryInst() {

  return QueryInst;

}

LoadInst* LFARealization::getOriginalInst() {

  return LFA.getOriginalInst();

}

IntegrationAttempt* LFARealization::getOriginalCtx() {

  return LFA.getOriginalCtx();

}

LoadForwardAttempt& LFARealization::getLFA() {

  return LFA;

}

Instruction* LFARealization::getFakeBase() {

  return FakeBase;

}

// Implement LFARMapping

// Precondition: LFAR.getLFA().canBuildSymExpr()
LFARMapping::LFARMapping(LFARealization& _LFAR, IntegrationAttempt* _Ctx) : LFAR(_LFAR), Ctx(_Ctx) {

  SymThunk* Th = cast<SymThunk>(LFAR.getLFA().getSymExpr()->back());
  Ctx->setReplacement(LFAR.getFakeBase(), Th->RealVal);

}

LFARMapping::~LFARMapping() {

  Ctx->eraseReplacement(LFAR.getFakeBase());

}

void IntegratorWQItem::execute() { 
  switch(type) {
  case TryEval:
    ctx->tryEvaluate(u.V);
    break;
  case CheckBlock:
    ctx->checkBlock(u.BB);
    break;
  case CheckLoad:
    ctx->checkLoad(u.LI);
    break;
  case OpenPush:
    ctx->tryPushOpen(u.OpenArgs.OpenI, u.OpenArgs.OpenProgress);
    break;
  case PBSolve:
    u.IHP->runPointerBaseSolver();
    break;
  }
}

void IntegratorWQItem::describe(raw_ostream& s) {

  switch(type) {
  case TryEval:
    s << "Try-eval ";
    ctx->printWithCache(u.V, s);
    break;
  case CheckBlock:
    s << "Check-BB-status " << u.BB->getName();
    break;
  case CheckLoad:
    s << "Check-load ";
    ctx->printWithCache(make_vc(u.LI, ctx), s);
    break;
  case OpenPush:
    s << "Push-VFS-chain ";
    ctx->printWithCache(make_vc(u.OpenArgs.OpenI, ctx), s);
    break;
  case PBSolve:
    s << "Run-PB-solver";
    break;
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
	  if(edgeL == CheckBBL) {
	    // Edge is a local variant; so is the block
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

void IntegrationHeuristicsPass::queueTryEvaluate(IntegrationAttempt* ctx, Value* val) {

  assert(ctx && val && "Queued a null value");
  produceQueue->push_back(IntegratorWQItem(ctx, val));
     
}

void IntegrationHeuristicsPass::queueCheckBlock(IntegrationAttempt* ctx, BasicBlock* BB) {

  assert(ctx && BB && "Queued a null block");
  produceQueue->push_back(IntegratorWQItem(ctx, BB));

}

void IntegrationHeuristicsPass::queueCheckLoad(IntegrationAttempt* ctx, LoadInst* LI) {

  assert(ctx && LI && "Queued a null load");
  produceQueue->push_back(IntegratorWQItem(ctx, LI));

}

void IntegrationHeuristicsPass::queueOpenPush(ValCtx OpenInst, ValCtx OpenProgress) {

  assert(OpenInst.first && OpenInst.second && OpenProgress.first && OpenProgress.second && "Queued an invalid open push");
  produceQueue->push_back(IntegratorWQItem((IntegrationAttempt*)OpenInst.second, cast<CallInst>(OpenInst.first), OpenProgress));

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

namespace llvm {

inline bool operator==(IntegratorWQItem W1, IntegratorWQItem W2) {

  if(W1.ctx != W2.ctx || W1.type != W2.type)
    return false;

  switch(W1.type) {
  case TryEval:
    return W1.u.V == W2.u.V;
  case CheckBlock:
    return W1.u.BB == W2.u.BB;
  case CheckLoad:
    return W1.u.LI == W2.u.LI;
  case OpenPush:
    return (W1.u.OpenArgs.OpenI == W2.u.OpenArgs.OpenI && W1.u.OpenArgs.OpenProgress == W2.u.OpenArgs.OpenProgress);
  case PBSolve:
    return true;
  default:
    assert(0 && "Bad WQ item type!");
  }

}

inline bool operator!=(IntegratorWQItem W1, IntegratorWQItem W2) {
  return !(W1 == W2);
}

inline bool operator<(IntegratorWQItem W1, IntegratorWQItem W2) {
  if(W1.ctx != W2.ctx)
    return W1.ctx < W2.ctx;
  if(W1.type != W2.type)
    return W1.type < W2.type;
  switch(W1.type) {
  case TryEval:
    return W1.u.V < W2.u.V;
  case CheckBlock:
    return W1.u.BB < W2.u.BB;
  case CheckLoad:
    return W1.u.LI < W2.u.LI;
  case OpenPush:
    if(W1.u.OpenArgs.OpenI != W2.u.OpenArgs.OpenI)
      return W1.u.OpenArgs.OpenI < W2.u.OpenArgs.OpenI;
    return W1.u.OpenArgs.OpenProgress < W2.u.OpenArgs.OpenProgress;
  case PBSolve:
    return false;
  default:
    assert(0 && "Bad WQ item type!");
  }
}

inline bool operator<=(IntegratorWQItem W1, IntegratorWQItem W2) {
  return W1 < W2 || W1 == W2;
}

inline bool operator>(IntegratorWQItem W1, IntegratorWQItem W2) {
  return !(W1 <= W2);
}

inline bool operator>=(IntegratorWQItem W1, IntegratorWQItem W2) {
  return !(W1 < W2);
}

}

void IntegrationHeuristicsPass::runQueue() {

  SmallVector<IntegratorWQItem, 64>* consumeQueue = (produceQueue == &workQueue1) ? &workQueue2 : &workQueue1;

  while(workQueue1.size() || workQueue2.size()) {
    
    std::sort(consumeQueue->begin(), consumeQueue->end());

    SmallVector<IntegratorWQItem, 64>::iterator it, itend;
    itend = std::unique(consumeQueue->begin(), consumeQueue->end());

    for(it = consumeQueue->begin(); it != itend; ++it) {

      DEBUG(dbgs() << "Dequeue: ");
      DEBUG(it->describe(dbgs()));
      DEBUG(dbgs() << "\n");
      it->execute();

    }

    consumeQueue->clear();
    std::swap(consumeQueue, produceQueue);

  }

}

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

void IntegrationHeuristicsPass::revertLoadsFromFoldedContexts() {

  RootIA->revertLoadsFromFoldedContexts();

}

void IntegrationHeuristicsPass::retryLoadsFromFoldedContexts() {

  RootIA->retryLoadsFromFoldedContexts();

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

static void parseFBB(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB1, BasicBlock*& BB2) {

  std::string FName, BB1Name, BB2Name;
  size_t firstComma = arg.find(',');
  size_t secondComma;
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
    IA->investigateUsers(Arg);
  }
  // Else it's varargs, and loads get investigated anyway.

}

void IntegrationHeuristicsPass::parseArgs(InlineAttempt* RootIA, Function& F) {

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

  queueCheckBlock(IA, &(F.getEntryBlock()));
  IA->queueInitialWork();

  parseArgs(IA, F);

  runQueue();

  DEBUG(dbgs() << "Finding dead MTIs\n");
  IA->tryKillAllMTIs();

  DEBUG(dbgs() << "Finding dead stores\n");
  IA->tryKillAllStores();

  DEBUG(dbgs() << "Finding dead allocations\n");
  IA->tryKillAllAllocs();

  DEBUG(dbgs() << "Finding remaining dead instructions\n");

  IA->queueAllLiveValues();

  runDIEQueue();

  IA->collectStats();

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
