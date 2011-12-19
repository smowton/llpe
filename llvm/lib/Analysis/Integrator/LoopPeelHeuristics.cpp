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
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRBuilder.h"

#include <string>
#include <algorithm>

#define LPDEBUG(x) DEBUG(dbgs() << dbgind() << x)

using namespace llvm;

bool instructionCounts(Instruction* I);

namespace {

  class InlineAttempt;
  class PeelAttempt;

  class IntegrationAttempt : public HCFParentCallbacks {

  protected:

    LoopInfo* LI;
    TargetData* TD;
    AliasAnalysis* AA;

    Function& F;

    IntegrationAttempt* parent;
    int nesting_depth;
    
    DenseMap<CallInst*, InlineAttempt*> inlineChildren;
    DenseMap<Loop*, PeelAttempt*> peelChildren;
    
    int debugIndent;
    
    DenseMap<Value*, ValCtx > improvedValues;
    SmallVector<Value*, 8> newLocalImprovedValues;
    SmallVector<std::pair<Value*, Constant*>, 1> newNonLocalImprovedValues;

    SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> deadEdges;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> newlyDeadEdges;

    HypotheticalConstantFolder H;

    std::string dbgind() const;

  public:

    IntegrationAttempt(IntegrationAttempt* P, Function& _F, LoopInfo* _LI, TargetData* _TD, AliasAnalysis* _AA, 
		       int depth, int indent) : 
      LI(_LI),
      TD(_TD), 
      AA(_AA), 
      F(_F),
      parent(P),
      nesting_depth(depth), 
      debugIndent(indent), 
      H(&_F, _AA, _TD, *this)
    {

      H.setDebugIndent(indent);

    }

    ~IntegrationAttempt();

    void setNonLocalReplacement(Value* V, Constant* C);
    void setNonLocalEdgeDead(BasicBlock* B1, BasicBlock* B2);
    Constant* getConstReplacement(Value* V, int frameIndex = 0);
    virtual Loop* getLoopContext() = 0;
    virtual Instruction* getEntryInstruction() = 0;
    virtual BasicBlock* getEntryBlock() = 0;
    void tryImproveChildren(Value* Improved);
    virtual void tryImproveParent();
    void localImprove(Value* From, ValCtx To);
    virtual void considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I);
    InlineAttempt* getOrCreateInlineAttempt(CallInst* CI, bool force = false);
    PeelAttempt* getOrCreatePeelAttempt(Loop*);

    bool buildSymExpr(LoadInst* LoadI, SmallVector<std::auto_ptr<SymExpr>, 4>& Expr);
    void realiseSymExpr(SmallVector<std::auto_ptr<SymExpr>, 4>& in, Instruction* Where, SmallVector<Instruction*, 4>& tempInstructions);
    virtual ValCtx tryForwardExprFromParent(SmallVector<std::auto_ptr<SymExpr>, 4>& Expr);
    bool forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result);
    ValCtx getDefn(const MemDepResult& Res);
    MemDepResult getUniqueDependency(LoadInst* LI);
    ValCtx tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<std::auto_ptr<SymExpr>, 4>& Expr);
    void print(raw_ostream &OS) const;

    // Overrides:

    virtual ValCtx getReplacement(Value* V, int frameIndex = 0);
    virtual void setReplacement(Value*, ValCtx);
    virtual bool edgeIsDead(BasicBlock*, BasicBlock*);
    virtual void setEdgeDead(BasicBlock*, BasicBlock*);
    virtual bool shouldIgnoreBlock(BasicBlock*);
    virtual bool shouldIgnoreInstruction(Instruction*);
    virtual bool blockIsDead(BasicBlock*);

  };

  class PeelIteration : public IntegrationAttempt {

    int iterationCount;
    Loop* L;
    PeelAttempt* parentPA;
    bool terminated;

    PeelIteration* getOrCreateNextIteration();

  public:

    PeelIteration(IntegrationAttempt* P, PeelAttempt* PP, Function& F, LoopInfo* _LI, TargetData* _TD,
		  AliasAnalysis* _AA, Loop* _L, int iter, int depth, int dbind) :
      IntegrationAttempt(P, F, _LI, _TD, _AA, depth, dbind),
      iterationCount(iter),
      L(_L),
      parentPA(PP),
      terminated(false)
    {

      BasicBlock* HB = L->getHeader();

      if(!iterationCount) {
	BasicBlock* LB = L->getLoopLatch();
	H.killEdge(LB, HB);
      }
      // Don't kill the preheader edge for nonzero iterations -- that would cause
      // them to feed of their *own* backedge rather than their predecessor iteration.

    }

    void giveInvariantsTo(PeelIteration* NewIter);
    void foldValue(Value* Improved, ValCtx ImprovedTo);
    virtual ValCtx getReplacement(Value* V, int frameIndex = 0);
    virtual bool shouldIgnoreBlock(BasicBlock*);
    virtual bool shouldIgnoreInstruction(Instruction*);
    virtual Instruction* getEntryInstruction();
    virtual BasicBlock* getEntryBlock();
    virtual ValCtx tryForwardLoad(LoadInst* LoadI);
    virtual void considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I);
    virtual Loop* getLoopContext();
    virtual void tryImproveParent();

  };

  class PeelAttempt {
    // Not a subclass of IntegrationAttempt -- this is just a helper.

    IntegrationAttempt* parent;
    Function& F;

    LoopInfo* LI;
    TargetData* TD;
    AliasAnalysis* AA;

    Loop* L;
    std::vector<PeelIteration*> Iterations;
    int nesting_depth;
    int debugIndent;

  public:

    PeelAttempt(IntegrationAttempt* P, Function& _F, LoopInfo* _LI, TargetData* _TD, AliasAnalysis* _AA, 
		Loop* _L, int depth, int dbind) :
      parent(P),
      F(_F),
      LI(_LI),
      TD(_TD),
      AA(_AA),
      L(_L),
      nesting_depth(depth),
      debugIndent(dbind)
    {
      getOrCreateIteration(0);
    }

    ~PeelAttempt() {
      for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
	delete *it;
      }
    }

    PeelIteration* getOrCreateIteration(unsigned iter);
    ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);
    void foldValue(Value* Improved, ValCtx ImprovedTo);

  };

  class InlineAttempt : public IntegrationAttempt { 

    int totalInstructions;
    int residualCalls;
    Constant* returnVal;
    CallInst* CI;

  public:

    InlineAttempt(IntegrationAttempt* P, Function& F, LoopInfo* LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, int depth, int dbind) 
      : 
      IntegrationAttempt(P, F, LI, TD, AA, depth, dbind),
      CI(_CI)
    { }

    void foldArgument(Argument* A, ValCtx V);
    virtual Instruction* getEntryInstruction();
    virtual BasicBlock* getEntryBlock();
    virtual ValCtx tryForwardLoad(LoadInst* LoadI);
    virtual Loop* getLoopContext();
    virtual void tryImproveParent();

  };

  class IntegrationHeuristicsPass : public ModulePass {

    LoopInfo* LI;
    TargetData* TD;
    AliasAnalysis* AA;

    SmallVector<InlineAttempt*, 4> rootAttempts;

  public:

    static char ID;

    explicit IntegrationHeuristicsPass() : ModulePass(ID) { }
    bool runOnModule(Module& M);

    void print(raw_ostream &OS, const Module* M) const {
      for(SmallVector<InlineAttempt*, 4>::const_iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
	(*II)->print(OS);
    }

    void releaseMemory(void) {
      for(SmallVector<InlineAttempt*, 4>::iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
	delete *II;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {

      AU.addRequired<AliasAnalysis>();
      AU.addRequired<LoopInfo>();
      AU.setPreservesAll();

    }

  };

  char IntegrationHeuristicsPass::ID = 0;
  
}

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
  for(DenseMap<Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }
}

static std::string ind(int i) {

  char* arr = (char*)alloca(i+1);
  for(int j = 0; j < i; j++)
    arr[j] = ' ';
  arr[i] = '\0';
  return std::string(arr);

}

bool instructionCounts(Instruction* I) {

  if(isa<PHINode>(I))
    return false;
  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

// Implement HCFParentCallbacks, except for tryForwardLoad which comes later

ValCtx IntegrationAttempt::getReplacement(Value* V, int frameIndex) {

  if(!frameIndex) {
    DenseMap<Value*, ValCtx >::iterator it = improvedValues.find(V);
    if(it == improvedValues.end())
      return make_vc(V, 0);
    else
      return it->second;
  }
  else {
    if(parent) {
      ValCtx Result =  parent->getReplacement(V, frameIndex - 1);
      return make_vc(Result.first, Result.second + 1);
    }
    else {
      LPDEBUG("Anomaly: asked to resolve " << *V << "@" << frameIndex << " whose frame is out of range\n");
      return make_vc(V, 0);
    }
  }

}

ValCtx PeelIteration::getReplacement(Value* V, int frameIndex) {

  // frameIndex for us refers to previous iterations for a while, then once they bottom out to our parent
  // loop, then *his* previous iterations, then eventually the base function. Avoid a massive stack by
  // taking a shortcut.
  // The exception is values directly referenced from outside this loop. Their frame index is an offset from
  // *their* innermost loop iteration.

  Instruction* I;
  if((I = dyn_cast<Instruction>(V)) && !L->contains(V)) {
    return parent->getReplacement(I, frameIndex);
  }
  else if(!frameIndex) {
    DenseMap<Value*, ValCtx >::iterator it = improvedValues.find(V);
    if(it == improvedValues.end())
      return make_vc(V, 0);
    else
      return it->second;
  }
  else {
    return parentPA->getReplacement(V, frameIndex, this->iterationCount);
  }

}

ValCtx PeelAttempt::getReplacement(Value* V, int frameIndex, int sourceIteration) {

  int targetIteration = sourceIteration - frameIndex;

  if(targetIteration >= 0) {
    return Iterations[targetIteration]->getReplacement(V, 0);
  }
  else {
    return parent->getReplacement(V, frameIndex - sourceIteration);
  }

}

Constant* IntegrationAttempt::getConstReplacement(Value* V, int frameIndex) {

  if(Constant* C = dyn_cast<Constant>(V))
    return C;
  ValCtx Replacement = getReplacement(V, frameIndex);
  if(Constant* C = dyn_cast<Constant>(Replacement.first))
    return C;
  return 0;

}

void IntegrationAttempt::setReplacement(Value* V, ValCtx R) {

  newLocalImprovedValues.push_back(V);
  improvedValues[V] = R;

}

void IntegrationAttempt::setNonLocalReplacement(Value* V, Constant* C) {

  newNonLocalImprovedValues.push_back(std::make_pair(V, C));

}

bool IntegrationAttempt::edgeIsDead(BasicBlock* B1, BasicBlock* B2) {

  return deadEdges.count(std::make_pair(B1, B2));

}

void IntegrationAttempt::setEdgeDead(BasicBlock* B1, BasicBlock* B2) {

  std::pair<BasicBlock*, BasicBlock*> Edge = std::make_pair(B1, B2);
  deadEdges.insert(Edge);

}

void IntegrationAttempt::setNonLocalEdgeDead(BasicBlock* B1, BasicBlock* B2) {
  
  std::pair<BasicBlock*, BasicBlock*> Edge = std::make_pair(B1, B2);
  newlyDeadEdges.push_back(Edge);

}

bool IntegrationAttempt::shouldIgnoreBlock(BasicBlock* BB) {

  return LI->getLoopFor(BB) != 0;

}

bool PeelIteration::shouldIgnoreBlock(BasicBlock* BB) {

  return LI->getLoopFor(BB) != L;

}

bool IntegrationAttempt::shouldIgnoreInstruction(Instruction* I) { 

  return false;

}

bool PeelIteration::shouldIgnoreInstruction(Instruction* I) {

  return (I->getParent() == L->getHeader() && isa<PHINode>(I));

}

bool IntegrationAttempt::blockIsDead(BasicBlock* BB) {

  if(&(BB->getParent()->getEntryBlock()) == BB)
    return false;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; PI++) {
      
    if(!edgeIsDead(*PI, BB))
      return false;

  }

  return true;

}

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(CallInst* CI, bool force) {

  DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(CI);
  if(it != inlineChildren.end())
    return it->second;

  if(Function* FCalled = CI->getCalledFunction()) {

    if((!FCalled->isDeclaration()) && (!FCalled->isVarArg())) {

      InlineAttempt* IA = new InlineAttempt(this, F, this->LI, this->TD, this->AA, CI, this->nesting_depth + 1, this->debugIndent + 2);
      inlineChildren[CI] = IA;

      // Feed the inline attempt any 'natural' constants; any improvements will be delivered by our caller.
      
      for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	Argument* A = AI;
	Value* AVal = CI->getArgOperand(A->getArgNo());
	if(shouldForwardValue(AVal))
	  IA->foldArgument(A, make_vc(AVal, 1));
      }

      return IA;

    }
    else {
      LPDEBUG("Ignored " << *CI << " because we don't know the function body, or it's vararg\n");
    }

  }
  else {
    LPDEBUG("Ignored " << *CI << " because it's an uncertain indirect call\n");
  }

  return 0;

}

void PeelIteration::giveInvariantsTo(PeelIteration* NewIter) {

  // Feed the new iteration any loop-invariant constants we know. 
  // TODO: Share the invariant parts somehow.

  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    bool shouldProp = false;

    if(Instruction* I = dyn_cast<Instruction>(it->first)) {
      Loop* VLoop = LI->getLoopFor(I->getParent());
      if(!L->contains(VLoop))
	shouldProp = true;
    }
    else if(isa<Argument>(it->first))
      shouldProp = true;

    if(shouldProp)
      NewIter->foldValue(it->first, make_vc(it->second.first, it->second.second + 1));

  }

}

PeelIteration* PeelAttempt::getOrCreateIteration(unsigned iter) {

  if(Iterations.size() > iter)
    return Iterations[iter];
  else {
    assert(iter == Iterations.size());
    PeelIteration* OldIter = 0;
    if(Iterations.size())
      OldIter = Iterations.back();
    PeelIteration* NewIter = new PeelIteration(parent, this, F, LI, TD, AA, L, iter, nesting_depth, debugIndent);
    Iterations.push_back(NewIter);
    
    if(OldIter)
      OldIter->giveInvariantsTo(NewIter);

    return NewIter;
  }

}

PeelIteration* PeelIteration::getOrCreateNextIteration() {

  return parentPA->getOrCreateIteration(this->iterationCount + 1);

}

PeelAttempt* IntegrationAttempt::getOrCreatePeelAttempt(Loop* NewL) {

  DenseMap<Loop*, PeelAttempt*>::iterator it = peelChildren.find(NewL);
  if(it != peelChildren.end())
    return it->second;

  if(NewL->getLoopPreheader() && NewL->getLoopLatch()) {

    PeelAttempt* LPA = new PeelAttempt(this, F, LI, TD, AA, NewL, nesting_depth + 1, debugIndent + 2);
    peelChildren[NewL] = LPA;
    return LPA;

  }
  else {

    LPDEBUG("Won't explore loop with header " << NewL->getHeader()->getName() << " because it lacks a preheader, a latch, or both\n");
    return 0;

  }

}

void PeelIteration::foldValue(Value* Improved, ValCtx ImprovedTo) {

  localImprove(Improved, ImprovedTo);

}

void PeelAttempt::foldValue(Value* Improved, ValCtx ImprovedTo) {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->foldValue(Improved, ImprovedTo);

  }

}

void PeelIteration::considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I) {

  // Check whether this defines an entry PHI for the next iteration

  if(PHINode* PN = dyn_cast<PHINode>(I)) {

    if(PN->getParent() == L->getHeader()) {

      if(Improved == PN->getIncomingValueForBlock(L->getLoopLatch())) {
	PeelIteration* PI = getOrCreateNextIteration();
	PI->foldValue(PN, ImprovedTo);
	return;
      }

    }

  }

  IntegrationAttempt::considerInlineOrPeel(Improved, ImprovedTo, I);

}

Loop* InlineAttempt::getLoopContext() {

  return 0;

}

Loop* PeelIteration::getLoopContext() {

  return L;

}

void IntegrationAttempt::considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I) {

  Loop* L = LI->getLoopFor(I->getParent());
  Loop* MyL = getLoopContext();

  if(L == MyL) {
  
    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      InlineAttempt* IA = getOrCreateInlineAttempt(CI);
      if(IA) {
	      
	Function* FCalled = CI->getCalledFunction();
	for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	  Argument* A = AI;
	  Value* AVal = CI->getArgOperand(A->getArgNo());
	  if(AVal == AI) {
	    IA->foldArgument(A, make_vc(ImprovedTo.first, ImprovedTo.second + 1));
	  }
	}

      }

    }

  }
  else {

    Loop* outermostChildLoop = L;
    while(outermostChildLoop->getParentLoop() != MyL)
      outermostChildLoop = outermostChildLoop->getParentLoop();

    PeelAttempt* LPA = getOrCreatePeelAttempt(L);
    if(LPA)
      LPA->foldValue(Improved, ImprovedTo);

  }

}

void IntegrationAttempt::tryImproveChildren(Value* Improved) {

  ValCtx ImprovedTo = getReplacement(Improved, 0);
      
  for (Value::use_iterator UI = Improved->use_begin(), UE = Improved->use_end(); UI != UE;++UI) {

    if(Instruction* I = dyn_cast<Instruction>(*UI)) {

      if(blockIsDead(I->getParent()))
	continue;
      if(shouldIgnoreBlock(I->getParent()))
	continue;
      considerInlineOrPeel(Improved, ImprovedTo, I);

    }

  }

}

void IntegrationAttempt::localImprove(Value* From, ValCtx To) {

  H.getBenefit(From, To);

  while(newLocalImprovedValues.size() || newNonLocalImprovedValues.size() || newlyDeadEdges.size()) {

    SmallVector<std::pair<Value*, Constant*>, 1> newNLVals = newNonLocalImprovedValues;
    newNonLocalImprovedValues.clear();
    
    for(SmallVector<std::pair<Value*, Constant*>, 1>::iterator it = newNLVals.begin(), it2 = newNLVals.end(); it != it2; it++) {

      H.getBenefit(it->first, make_vc(it->second, 0));

    }

    SmallVector<Value*, 8> newVals = newLocalImprovedValues;
    newLocalImprovedValues.clear();

    for(SmallVector<Value*, 4>::iterator it = newVals.begin(), it2 = newVals.end(); it != it2; it++) {

      tryImproveChildren(*it);

    }

    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> newlyDEs = newlyDeadEdges;
    newlyDeadEdges.clear();

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = newlyDEs.begin(), it2 = newlyDEs.end(); it != it2; it++) {

      H.killEdge(it->first, it->second);

    }

  }

  if(parent)
    tryImproveParent();

}

void InlineAttempt::tryImproveParent() {

  // Let's have a go at supplying a return value to our caller. Simple measure:
  // we know the value if all the 'ret' instructions except one are dead,
  // and we know that instruction's operand.

  if((!returnVal) && (!F.getReturnType()->isVoidTy())) {
    bool foundReturnInst = false;
    for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {
      if(blockIsDead(FI))
	continue;
      for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++) {
	if(ReturnInst* RI = dyn_cast<ReturnInst>(BI)) {
	  if(foundReturnInst) {
	    LPDEBUG("Can't determine return value: more than one 'ret' is live\n");
	    returnVal = 0;
	    break;
	  }
	  else
	    foundReturnInst = true;
	  Value* ThisRet = RI->getReturnValue();
	  Constant* C = getConstReplacement(ThisRet, 0);
	  if(C)
	    returnVal = C;
	  else {
	    LPDEBUG("Can't determine return value: live instruction " << *RI << " has non-constant value " << *(RI->getReturnValue()) << "\n");
	    break;
	  }
	}
      }
    }
    
    if(returnVal) {
      LPDEBUG("Found return value: " << *returnVal << "\n");
      parent->setNonLocalReplacement(this->CI, returnVal);
    }
  }

}

void PeelIteration::tryImproveParent() {

  if(!terminated) {

    BasicBlock* Latch = L->getLoopLatch();
    BasicBlock* Header = L->getHeader();
    if(deadEdges.count(std::make_pair(Latch, Header))) {

      // The loop won't iterate again -- export local constants and dead edges to the next loop/function out.

      for(DenseMap<Value*, ValCtx >::iterator VI = improvedValues.begin(), VE = improvedValues.end(); VI != VE; VI++) {

	if(Constant* C = dyn_cast<Constant>(VI->second.first)) {
	  
	  parent->setNonLocalReplacement(VI->first, C);
	  
	}

      }

      SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;
      L->getExitEdges(ExitEdges);
      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = ExitEdges.begin(), EE = ExitEdges.end(); EI != EE; EI++) {

	if(deadEdges.count(*EI))
	  parent->setEdgeDead(EI->first, EI->second);

      }

      terminated = true;

    }

  }

}

void InlineAttempt::foldArgument(Argument* A, ValCtx V) {

  localImprove(A, V);

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

// Given a MemDep Def, get the value loaded or stored.
ValCtx IntegrationAttempt::getDefn(const MemDepResult& Res) {

  if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
    return getReplacement(SI->getOperand(0));
  }
  else if(LoadInst* DefLI= dyn_cast<LoadInst>(Res.getInst())) {
    ValCtx improvedLoad = getReplacement(DefLI);
    if(improvedLoad.first != DefLI || improvedLoad.second > 0) {
      LPDEBUG("Defined by " << *(improvedLoad.first) << "\n");
      return improvedLoad;
    }
  }
  else {
    LPDEBUG("Defined by " << *(Res.getInst()) << " which is not a simple load or store\n");
  }

  return VCNull;

}

// Find the unique definer or clobberer for a given Load.
MemDepResult IntegrationAttempt::getUniqueDependency(LoadInst* LoadI) {

  MemoryDependenceAnalyser MD;
  MD.init(AA, &this->parent);

  MemDepResult Seen;

  Seen = MD.getDependency(LoadI);

  if(Seen.isNonLocal()) {

    Seen = MemDepResult();
    Value* LPointer = LoadI->getOperand(0);

    SmallVector<NonLocalDepResult, 4> NLResults;

    MD.getNonLocalPointerDependency(LPointer, true, LoadI->getParent(), NLResults);
    assert(NLResults.size() > 0);

    for(unsigned int i = 0; i < NLResults.size(); i++) {
		
      const MemDepResult& Res = NLResults[i].getResult();
      if(Res.isNonLocal())
	continue;
      else if(Res == Seen)
	continue;
      else if(Seen == MemDepResult()) // Nothing seen yet
	Seen = Res;
      else {
	LPDEBUG(*LoadI << " is overdefined: depends on at least " << Seen << " and " << Res << "\n");
	return MemDepResult();
      }

    }

  }

  return Seen;

}

// Make a symbolic expression for a given load instruction if it depends solely on one pointer
// with many constant offsets.
bool IntegrationAttempt::buildSymExpr(LoadInst* LoadI, SmallVector<std::auto_ptr<SymExpr>, 4>& Expr) {

  // Precondition: LoadI is clobbered in exactly one place: the entry instruction to the enclosing context.
  // This might mean that instruction actually clobbers it, or it's defined by instructions outside this function.
  
  if(!parent)
    return false;

  Value* Ptr = LoadI->getPointerOperand();

  LPDEBUG("Trying to resolve load from " << *LoadI << " by exploring parent contexts\n");

  // Check that we're trying to fetch a cast-of-constGEP-of-cast-of... an argument or an outer object,
  // and construct a symbolic expression to pass to our parent as we go.

  while(1) {

    if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
      SmallVector<Value*, 4> idxs;
      for (unsigned i = 1, e = GEP->getNumOperands(); i != e; ++i) {
	Value* idx = GEP->getOperand(i);
	Constant* Cidx = getConstReplacement(idx);
	if(Cidx)
	  idxs.push_back(Cidx);
	else {
	  LPDEBUG("Can't investigate external dep with non-const index " << *idx << "\n");
	  return false;
	}
      }
      Expr.push_back(std::auto_ptr<SymExpr>(new SymGEP(idxs)));
      Ptr = GEP->getPointerOperand();
    }
    else if(BitCastInst* C = dyn_cast<BitCastInst>(Ptr)) {
      Expr.push_back(std::auto_ptr<SymExpr>(new SymCast(C->getType())));
      Ptr = C->getOperand(0);
    }
    else {
      ValCtx Repl = getReplacement(Ptr);
      if(Repl.first == Ptr && Repl.second == 0) {
	LPDEBUG("Won't investigate load from parent function due to unresolved pointer " << *Ptr << "\n");
	return false;
      }
      else if(Repl.second > 0) {
	Expr.push_back(std::auto_ptr<SymExpr>(new SymThunk(Repl)));
	break;
      }
      else {
	Ptr = Repl.first; // Must continue resolving!
      }
    }
    
  }

  return true;

}

// Realise a symbolic expression at a given location. 
// Temporary instructions are created and recorded for later deletion.
void IntegrationAttempt::realiseSymExpr(SmallVector<std::auto_ptr<SymExpr>, 4>& in, Instruction* Where, SmallVector<Instruction*, 4>& tempInstructions) {

  // Build it backwards: the in chain should end in a defined object, in or outside our scope.
  // Start with that, then wrap it incrementally in operators.
  
  SmallVector<std::auto_ptr<SymExpr>, 4>::iterator SI = in.end(), SE = in.begin();
  
  Value* lastPtr;
  
  SI--;
  SymThunk* th = cast<SymThunk>(SI);

  LLVMContext& ctx = F.getContext();
  BasicBlock::iterator BI(Where);
  IRBuilder<> Builder(ctx);
  Builder.SetInsertPoint(Where->getParent(), *BI);

  if(!th->RealVal.second) {
    // Access against a local value
    lastPtr = th->RealVal.first;
  }
  else {
    // Access against a nonlocal value: make up an 'ambiguous' load and temporarily map it.
    // This is just a trick so that MemDep will try to resolve the pointer and find its true target.
    Instruction* FakeLoc = Builder.CreateAlloca(th->RealVal->getType());
    lastPtr = Builder.CreateLoad(FakeLoc);
    tempInstructions.push_back(lastPtr);
    tempInstructions.push_back(FakeLoc);
  }

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
    //LPDEBUG("Created temporary instruction: " << *lastPtr << "\n");
    tempInstructions.push_back(cast<Instruction>(lastPtr));
  }

  // Make up a fake load, since MD wants an accessor.
  LoadInst* Accessor = Builder.CreateLoad(lastPtr);
  tempInstructions.push_back(Accessor);

  //LPDEBUG("Temporarily augmented parent block:\n");
  //DEBUG(dbgs() << *CS->getParent());

}

// Main load forwarding entry point, called by the hypothetical constant folder:
// Try to forward the load locally (within this loop or function), or otherwise build a symbolic expression
// and ask our parent to continue resolving the load.
ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LoadI) {

  ValCtx Result;
  if(forwardLoadIsNonLocal(LoadI, Result)) {
    SmallVector<std::auto_ptr<SymExpr>, 4> Expr;
    if(!buildSymExpr(LI, Expr))
      return VCNull; 

    LPDEBUG("Will resolve ");

    for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
      if(it != Expr.begin())
	DEBUG(dbgs() << " of ");
      DEBUG((*it)->describe(dbgs()));
    }

    DEBUG(dbgs() << "\n");

    return tryForwardExprFromParent(Expr);
  }
  else
    return Result;

}

// Pursue a load further. Current context is a function body; ask our caller to pursue further.
ValCtx InlineAttempt::tryForwardExprFromParent(SmallVector<std::auto_ptr<SymExpr>, 4>& Expr) {

  SymThunk* Th = cast<SymThunk>(Expr.back());
  Th->frame--;
  ValCtx Result = parent->tryResolveLoadAtChildSite(this, Expr);
  if(Result.first)
    return make_vc(Result.first, Result.second + 1);
  else
    return VCNull;

}

// Pursue a load further. Current context is a loop body -- try resolving it in previous iterations,
// then ask our enclosing loop or function body to look further.
ValCtx PeelAttempt::tryForwardExprFromParent(SmallVector<std::auto_ptr<SymExpr>, 4>& Expr, int originIter) {

  // First of all, try winding backwards through our sibling iterations. We can use a single realisation
  // of Expr for all of these checks, since the instructions are always the same.

  SmallVector<Instruction*, 4> tempInstructions;
  realiseSymExpr(Expr, L->getLoopLatch()->getTerminator(), tempInstructions);
  LoadInst* testLoad = cast<LoadInst>(tempInstructions.back());
  SymThunk* Th = cast<SymThunk>(Expr.back());

  ValCtx Result;

  for(int iter = originIter - 1; iter >= 0; iter--) {

    if((originIter - iter) > Th->frame) {
      LPDEBUG("Can't pursue this expression further, as it resolves to a value out of scope\n");
      return VCNull;
    }
    improvedValues[testLoad] = make_vc(Th->RealVal, Th->frame - (originIter - iter));
    if(!Iterations[iter].forwardLoadIsNonLocal(testLoad, Result)) {
      if(Result.first)
	return make_vc(Result.first, Result.second + (originIter - iter));
      else
	return VCNull;
    }

  }

  improvedValues.erase(testLoad);

  for(SmallVector<Instruction*, 4>::iterator II = tempInstructions.end(), IE = tempInstructions.begin(); II != IE; ) {
    Instruction* I = *(--II);
    I->eraseFromParent();
  }

  Th->frame -= originIter;
  return parent->tryResolveLoadAtChildSite(Iterations[0], Expr);

}

// Helper: loop iterations defer the resolution process to the abstract loop.
ValCtx PeelIteration::tryForwardExprFromParent(SmallVector<std::auto_ptr<SymExpr>, 4>& Expr) {

  return parentPA->tryForwardExprFromParent(Expr, this->iterationCount);

}

// Try forwarding a load locally; return true if it is nonlocal or false if not, in which case
// Result is set to the resolution result.
bool IntegrationAttempt::forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result) {

  MemDepResult Res = getUniqueDependency(LoadI);

  if(Res.isClobber()) {
    LPDEBUG(*LoadI << " is clobbered by " << Res.getInst() << "\n");
    if(BB == getEntryBlock()) {
      BasicBlock::iterator TestII(Res.getInst());
      if(TestII == BB->begin()) {
	return true;
      }
    }
    Result = VCNull;
  }
  else if(Res.isDef()) {
    Result = getDefn(Res);
  }

  retun false;

}

// Entry point for a child loop or function that wishes us to continue pursuing a load.
// Find the instruction before the child begins (so loop preheader or call site), realise the given symbolic
// expression, and try ordinary load forwarding from there.
ValCtx IntegrationAttempt::tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<std::auto_ptr<SymExpr>, 4>& Expr) {

  SmallVector<Instruction*, 4> tempInstructions;
  realiseSymExpr(Expr, IA->getEntryInstruction(), tempInstructions);
  
  SymThunk* Th = cast<SymThunk>(Expr.back());
  improvedValues[*tempInstructions.begin()] = make_vc(Th->RealVal, Th->frame);
  ValCtx Result;
  bool shouldPursueFurther = fowardLoadIsNonLocal(Expr.back());

  improvedValues.erase(*tempInstructions.begin());

  for(SmallVector<Instruction*, 4>::iterator II = tempInstructions.end(), IE = tempInstructions.begin(); II != IE; ) {
    Instruction* I = *(--II);
    I->eraseFromParent();
  }

  if(shouldPursueFurther)
    return tryForwardExprFromParent(Expr);
  else
    return Result;

}

void IntegrationAttempt::countResidualCalls() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {
    
    for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++) {
      
      if(CallInst* CI = dyn_cast<CallInst>(BI)) {
	DenseMap<CallInst*, InlineAttempt*>::iterator II = subAttempts.find(CI);
	if(II == subAttempts.end()) {
	  residualCalls++;
	}
	else {
	  II->second->countResidualCalls();
	}
      }

    }

  }

}

void IntegrationAttempt::print(raw_ostream& OS) const {

  OS << dbgind() << F.getName() << ": eliminated " << eliminatedInstructions.size() << "/" << totalInstructions << " instructions, " << residualCalls << " residual uninlined calls\n";

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator CII = subAttempts.begin(), CIE = subAttempts.end(); CII != CIE; CII++) {
    CII->second->print(OS);
  }

}

std::string IntegrationAttempt::dbgind() const {

  return ind(debugIndent);

}

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<TargetData>();
  AA = &getAnalysis<AliasAnalysis>();
  LI = &getAnalysis<LoopInfo>();

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    Function& F = *MI;

    DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");
    rootAttempts.push_back(new InlineAttempt(0, TD, AA, F, 0, 2));
    rootAttempts.back()->considerCalls(true);
    rootAttempts.back()->countResidualCalls();

  }

  return false;

}
