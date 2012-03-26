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

class InlineAttempt;
class PeelAttempt;

  class IntegrationAttempt : public HCFParentCallbacks {

  protected:

    DenseMap<Function*, LoopInfo*> LI;
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

    SmallSet<BasicBlock*, 4> deadBlocks;
    SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> deadEdges;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> newlyDeadEdges;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> newlyDeadEdgesNL;

    HypotheticalConstantFolder H;

    int improvableInstructions;
    int improvedInstructions;
    SmallVector<CallInst*, 4> unexploredCalls;
    SmallVector<Loop*, 4> unexploredLoops;

    std::string dbgind() const;

  public:

    IntegrationAttempt(IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
		       int depth, int indent) : 
      LI(_LI),
      TD(_TD), 
      AA(_AA), 
      F(_F),
      parent(P),
      nesting_depth(depth), 
      debugIndent(indent), 
      H(&_F, _AA, _TD, *this),
      improvableInstructions(0),
      improvedInstructions(0)
    {

      H.setDebugIndent(indent);

    }

    ~IntegrationAttempt();

    void setNonLocalReplacement(Value* V, Constant* C);
    void setNonLocalEdgeDead(BasicBlock* B1, BasicBlock* B2);
    Constant* getConstReplacement(Value* V);
    virtual Loop* getLoopContext() = 0;
    virtual Instruction* getEntryInstruction() = 0;
    void tryImproveChildren(Value* Improved);
    virtual void tryImproveChildrenDE(std::pair<BasicBlock*, BasicBlock*>);
    virtual void tryImproveParent(Value*) = 0;
    virtual void tryImproveParentDE(std::pair<BasicBlock*, BasicBlock*>);
    void localImprove(Value* From, ValCtx To);
    void killEdge(BasicBlock* From, BasicBlock* To);
    virtual void considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I);
    InlineAttempt* getOrCreateInlineAttempt(CallInst* CI);
    PeelAttempt* getOrCreatePeelAttempt(Loop*);

    bool buildSymExpr(LoadInst* LoadI, SmallVector<SymExpr*, 4>& Expr);
    void realiseSymExpr(SmallVector<SymExpr*, 4>& in, Instruction* Where, Instruction*& FakeBaseObject, LoadInst*& Accessor, SmallVector<Instruction*, 4>& tempInstructions);
    void destroySymExpr(SmallVector<Instruction*, 4>& tempInstructions);

    virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr) = 0;
    bool forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result);
    ValCtx getDefn(const MemDepResult& Res);
    MemDepResult getUniqueDependency(LoadInst* LI);
    ValCtx tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<SymExpr*, 4>& Expr);
    bool tryResolveExprFrom(SmallVector<SymExpr*, 4>& Expr, Instruction* Where, ValCtx& Result);
    bool tryResolveExprUsing(SmallVector<SymExpr*, 4>& Expr, Instruction* FakeBase, LoadInst* Accessor, ValCtx& Result);
    void forceExploreChildren();
    void improveParentAndChildren();

    void collectBlockStats(BasicBlock* BB);
    virtual void collectAllBlockStats() = 0;
    void collectLoopStats(Loop*);
    void collectStats();
    void print(raw_ostream& OS) const;
    virtual void printHeader(raw_ostream& OS) const = 0;

    // Overrides:

    virtual ValCtx getDefaultVC(Value*);
    virtual ValCtx getReplacement(Value* V);
    virtual void setReplacement(Value*, ValCtx);
    virtual bool edgeIsDead(BasicBlock*, BasicBlock*);
    virtual void setEdgeDead(BasicBlock*, BasicBlock*);
    virtual bool shouldIgnoreEdge(BasicBlock*, BasicBlock*);
    virtual bool shouldIgnoreBlockForConstProp(BasicBlock*);
    virtual bool shouldIgnoreBlockForDCE(BasicBlock*);
    virtual bool shouldIgnoreInstruction(Instruction*);
    virtual bool blockIsDead(BasicBlock*);
    virtual void setBlockDead(BasicBlock*);
    virtual ValCtx tryForwardLoad(LoadInst*);

  };

  class PeelIteration : public IntegrationAttempt {

    int iterationCount;
    Loop* L;
    PeelAttempt* parentPA;

    PeelIteration* getOrCreateNextIteration();

  public:

    PeelIteration(IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
		  AliasAnalysis* _AA, Loop* _L, int iter, int depth, int dbind) :
      IntegrationAttempt(P, F, _LI, _TD, _AA, depth, dbind),
      iterationCount(iter),
      L(_L),
      parentPA(PP),
      terminated(false)
    { }

    bool terminated;

    void giveInvariantsTo(PeelIteration* NewIter);
    void foldValue(Value* Improved, ValCtx ImprovedTo);
    virtual ValCtx getReplacement(Value* V);
    virtual ValCtx getDefaultVC(Value* V);
    virtual bool shouldIgnoreBlockForConstProp(BasicBlock*);
    virtual bool shouldIgnoreBlockForDCE(BasicBlock*);
    virtual bool shouldIgnoreEdge(BasicBlock*, BasicBlock*);
    virtual bool shouldIgnoreInstruction(Instruction*);
    virtual Instruction* getEntryInstruction();
    virtual BasicBlock* getEntryBlock();
    virtual void considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I);
    virtual Loop* getLoopContext();
    virtual void tryImproveChildrenDE(std::pair<BasicBlock*, BasicBlock*>);
    virtual void tryImproveParent(Value*);
    virtual void tryImproveParentDE(std::pair<BasicBlock*, BasicBlock*>);
    virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr);
    virtual void describe(raw_ostream& Stream) const {
      Stream << "(Loop " << L->getHeader()->getName() << "/" << iterationCount << ")";
    }

    virtual void collectAllBlockStats();
    virtual void printHeader(raw_ostream&) const;

  };

  class PeelAttempt {
    // Not a subclass of IntegrationAttempt -- this is just a helper.

    IntegrationAttempt* parent;
    Function& F;

    DenseMap<Function*, LoopInfo*>& LI;
    TargetData* TD;
    AliasAnalysis* AA;

    Loop* L;
    std::vector<PeelIteration*> Iterations;
    int nesting_depth;
    int debugIndent;

    std::string dbgind() const;

  public:

    PeelAttempt(IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
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

      L->getExitEdges(ExitEdges);
      getOrCreateIteration(0);

      BasicBlock* HB = L->getHeader();
      BasicBlock* PB = L->getLoopPreheader();

      for(BasicBlock::iterator BI = HB->begin(), BE = HB->end(); BI != BE && isa<PHINode>(BI); ++BI) {
	
	PHINode* PN = cast<PHINode>(BI);
	ValCtx PHVal = parent->getDefaultVC(PN->getIncomingValueForBlock(PB));
	ValCtx Incoming = parent->getReplacement(PHVal.first);
	if(Incoming != PHVal || shouldForwardValue(PHVal.first)) {
	  LPDEBUG("Propagating a value from the loop preheader:\n");
	  Iterations[0]->foldValue(PN, Incoming);
	}
      
      }

    }

    ~PeelAttempt() {
      for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
	delete *it;
      }
    }

    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;

    PeelIteration* getOrCreateIteration(unsigned iter);
    ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);
    void foldValue(Value* Improved, ValCtx ImprovedTo);
    ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, int originIter);

    void collectStats();
    void print(raw_ostream& OS) const;

  };

  class InlineAttempt : public IntegrationAttempt { 

    Constant* returnVal;
    CallInst* CI;

  public:

    InlineAttempt(IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, int depth, int dbind) 
      : 
      IntegrationAttempt(P, F, LI, TD, AA, depth, dbind),
      returnVal(0),
      CI(_CI)
    { }

    void foldArgument(Argument* A, ValCtx V);
    virtual Instruction* getEntryInstruction();
    virtual BasicBlock* getEntryBlock();
    virtual Loop* getLoopContext();
    virtual void tryImproveParent(Value*);
    virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr);
    virtual void describe(raw_ostream& Stream) const {

      Stream << "(" << F.getName() << ")";

    }

    virtual void collectAllBlockStats();
    virtual void printHeader(raw_ostream&) const;

  };

  class IntegrationHeuristicsPass : public ModulePass {

    DenseMap<Function*, LoopInfo*> LIs;
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

  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

// Implement HCFParentCallbacks, except for tryForwardLoad which comes later

ValCtx IntegrationAttempt::getReplacement(Value* V) {

  if(Constant* C = dyn_cast<Constant>(V))
    return const_vc(C);

  DenseMap<Value*, ValCtx >::iterator it = improvedValues.find(V);
  if(it == improvedValues.end())
    return make_vc(V, this);
  else
    return it->second;

}

ValCtx PeelIteration::getReplacement(Value* V) {

  // V is visible directly from within this loop. Therefore, due to LCSSA form, it's either a variant (in this loop)
  // or an invariant belonging to one of my parent loops, or the root function.
  // Exception to this rule: it might be from a child loop whose constants have been exported.
  // This should probably be fixed in the long term -- people propagating from out of a loop shouldn't
  // copy constants from its last iteration but should query that last iteration at an appropriate time.

  if(Instruction* I = dyn_cast<Instruction>(V)) {
    if(!L->contains(I->getParent())) 
      return parent->getReplacement(V);
  }

  return IntegrationAttempt::getReplacement(V);

}

ValCtx IntegrationAttempt::getDefaultVC(Value* V) {

  if(Constant* C = dyn_cast<Constant>(V))
    return const_vc(C);
  
  return make_vc(V, this);

}

ValCtx PeelIteration::getDefaultVC(Value* V) {

  if(Instruction* I = dyn_cast<Instruction>(V)) {
    Loop* VL = LI[&F]->getLoopFor(I->getParent());
    if(VL != L)
      return parent->getDefaultVC(V);
  }

  return IntegrationAttempt::getDefaultVC(V);

}

Constant* IntegrationAttempt::getConstReplacement(Value* V) {

  if(Constant* C = dyn_cast<Constant>(V))
    return C;
  ValCtx Replacement = getReplacement(V);
  if(Constant* C = dyn_cast<Constant>(Replacement.first))
    return C;
  return 0;

}

// Only ever called on things that belong in this scope, thanks to shouldIgnoreBlock et al.
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
  if(deadEdges.insert(Edge))
    newlyDeadEdges.push_back(Edge);

}

void IntegrationAttempt::setNonLocalEdgeDead(BasicBlock* B1, BasicBlock* B2) {
  
  std::pair<BasicBlock*, BasicBlock*> Edge = std::make_pair(B1, B2);
  newlyDeadEdgesNL.push_back(Edge);

}

bool IntegrationAttempt::shouldIgnoreBlockForConstProp(BasicBlock* BB) {

  return LI[&F]->getLoopFor(BB) != 0;

}

bool PeelIteration::shouldIgnoreBlockForConstProp(BasicBlock* BB) {

  return LI[&F]->getLoopFor(BB) != L;

}

bool IntegrationAttempt::shouldIgnoreBlockForDCE(BasicBlock* BB) {

  return false;

}

bool PeelIteration::shouldIgnoreBlockForDCE(BasicBlock* BB) {

  return !L->contains(BB);

}

bool IntegrationAttempt::shouldIgnoreEdge(BasicBlock* BB1, BasicBlock* BB2) {

  return false;

}

bool PeelIteration::shouldIgnoreEdge(BasicBlock* BB1, BasicBlock* BB2) {

  return (iterationCount != 0 && BB1 == L->getLoopLatch() && BB2 == L->getHeader());
  // This identifies the unique backedge, since we already require that n_backedges = 1

}

bool IntegrationAttempt::shouldIgnoreInstruction(Instruction* I) { 

  return false;

}

bool PeelIteration::shouldIgnoreInstruction(Instruction* I) {

  return (I->getParent() == L->getHeader() && isa<PHINode>(I));

}

bool IntegrationAttempt::blockIsDead(BasicBlock* BB) {

  return deadBlocks.count(BB);

}

void IntegrationAttempt::setBlockDead(BasicBlock* BB) {

  deadBlocks.insert(BB);

}

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(CallInst* CI) {

  DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(CI);
  if(it != inlineChildren.end())
    return it->second;

  if(Function* FCalled = CI->getCalledFunction()) {

    if((!FCalled->isDeclaration()) && (!FCalled->isVarArg())) {

      InlineAttempt* IA = new InlineAttempt(this, *FCalled, this->LI, this->TD, this->AA, CI, this->nesting_depth + 1, this->debugIndent + 2);
      inlineChildren[CI] = IA;

      LPDEBUG("Considering inlining " << FCalled->getName() << " at " << *CI << "\n");

      // Feed the inline attempt any 'natural' constants; any improvements will be delivered by our caller.
      
      for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	Argument* A = AI;
	Value* AVal = CI->getArgOperand(A->getArgNo());
	if(shouldForwardValue(AVal)) {
	  LPDEBUG("Propagating a natural constant argument:\n");
	  IA->foldArgument(A, getDefaultVC(AVal));
	}
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
      Loop* VLoop = LI[&F]->getLoopFor(I->getParent());
      if(!L->contains(VLoop))
	shouldProp = true;
    }
    else if(isa<Argument>(it->first))
      shouldProp = true;

    if(shouldProp) {
      LPDEBUG("Propagating a loop invariant to new iteration:\n");
      NewIter->foldValue(it->first, it->second);
    }

  }

}

PeelIteration* PeelAttempt::getOrCreateIteration(unsigned iter) {

  if(Iterations.size() > iter)
    return Iterations[iter];
  else {
    LPDEBUG("Considering peeling iteration " << iter << " of loop " << L->getHeader()->getName() << "\n");
    assert(iter == Iterations.size());
    PeelIteration* OldIter = 0;
    if(Iterations.size()) {

      OldIter = Iterations.back();

      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = ExitEdges.begin(), it2 = ExitEdges.end(); it != it2; ++it) {

	if(!OldIter->edgeIsDead(it->first, it->second)) {

	  LPDEBUG("Won't peel yet because exit edge " << it->first->getName() << " -> " << it->second->getName() << " is still alive\n");
	  return 0;

	}

      }

      LPDEBUG("All exit edges are dead; creating next iteration\n");
      
    }
    PeelIteration* NewIter = new PeelIteration(parent, this, F, LI, TD, AA, L, iter, nesting_depth, debugIndent);
    Iterations.push_back(NewIter);
    
    if(OldIter) {

      BasicBlock* Header = L->getHeader();
      BasicBlock* Latch = L->getLoopLatch();
    
      for(BasicBlock::iterator BI = Header->begin(), BE = Header->end(); BI != BE && isa<PHINode>(BI); ++BI) {
	
	PHINode* PN = cast<PHINode>(BI);
	
	ValCtx LatchVal = OldIter->getDefaultVC(PN->getIncomingValueForBlock(Latch));
	ValCtx Incoming = LatchVal.second->getReplacement(LatchVal.first);
	if(Incoming != LatchVal || shouldForwardValue(LatchVal.first)) {
	  LPDEBUG("Propagating a value across the loop latch:\n");
	  NewIter->foldValue(PN, Incoming);
	}
      
      }

    OldIter->giveInvariantsTo(NewIter);

    }

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

  if(blockIsDead(NewL->getHeader()))
    return 0;

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Considering inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(this, F, LI, TD, AA, NewL, nesting_depth + 1, debugIndent + 2);
    peelChildren[NewL] = LPA;

    // No need to propagate natural constant arguments, the killing of the latch edge on iteration
    // 0 does that for us.

    return LPA;

  }
  else {

    LPDEBUG("Won't explore loop with header " << NewL->getHeader()->getName() << " because it lacks a preheader, a latch, or both, or has multiple backedges\n");
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

  // Check for preheader PHI definitions, special cases not seen by the HCF:

  for(BasicBlock::iterator BI = L->getHeader()->begin(), BE = L->getHeader()->end(); BI != BE && isa<PHINode>(BI); ++BI) {
    PHINode* PN = cast<PHINode>(BI);
    if(PN->getIncomingValueForBlock(L->getLoopPreheader()) == Improved) {
      Iterations[0]->foldValue(PN, ImprovedTo);
    }
  }  

}

void PeelIteration::considerInlineOrPeel(Value* Improved, ValCtx ImprovedTo, Instruction* I) {

  // Check whether this defines an entry PHI for the next iteration

  if(!terminated) { // Otherwise there's no point as the next iteration shouldn't exist!

    if(PHINode* PN = dyn_cast<PHINode>(I)) {

      if(PN->getParent() == L->getHeader()) {

	if(Improved == PN->getIncomingValueForBlock(L->getLoopLatch())) {
	  PeelIteration* PI = getOrCreateNextIteration();
	  if(PI) {
	    LPDEBUG("Forwarding constant across loop " << L->getHeader()->getName() << "'s latch\n");
	    PI->foldValue(PN, ImprovedTo);
	  }
	  return;
	}

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

  Loop* L = LI[&F]->getLoopFor(I->getParent());
  Loop* MyL = getLoopContext();

  if(L == MyL) {
  
    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      LPDEBUG("Improved value is used by a loop-local call " << *CI << ":\n");
      InlineAttempt* IA = getOrCreateInlineAttempt(CI);
      if(IA) {
	      
	Function* FCalled = CI->getCalledFunction();
	for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	  Argument* A = AI;
	  Value* AVal = CI->getArgOperand(A->getArgNo());
	  if(AVal == Improved) {
	    IA->foldArgument(A, ImprovedTo);
	  }
	}

      }

    }

  }
  else {
    
    Loop* outermostChildLoop = L;
    while(outermostChildLoop && (outermostChildLoop->getParentLoop() != MyL))
      outermostChildLoop = outermostChildLoop->getParentLoop();

    if(!outermostChildLoop) // Use is in a sibling or parent scope
      return;

    LPDEBUG("Improved value is used in loop " << L->getHeader()->getName() << ", (immediate child " << outermostChildLoop->getHeader()->getName() << "), handing off:\n");
    PeelAttempt* LPA = getOrCreatePeelAttempt(outermostChildLoop);
    if(LPA)
      LPA->foldValue(Improved, ImprovedTo);

  }

}

void IntegrationAttempt::tryImproveChildren(Value* Improved) {

  ValCtx ImprovedTo = getReplacement(Improved);
  LPDEBUG("Considering passing " << *Improved << " -> " << ImprovedTo << " to child calls and loops:\n");
      
  for (Value::use_iterator UI = Improved->use_begin(), UE = Improved->use_end(); UI != UE;++UI) {

    if(Instruction* I = dyn_cast<Instruction>(*UI)) {

      if(blockIsDead(I->getParent()))
	continue;
      considerInlineOrPeel(Improved, ImprovedTo, I);

    }

  }

}

void IntegrationAttempt::tryImproveChildrenDE(std::pair<BasicBlock*, BasicBlock*> Edge) {

  return;

}

void PeelIteration::tryImproveChildrenDE(std::pair<BasicBlock*, BasicBlock*> Edge) {

  for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = parentPA->ExitEdges.begin(), it2 = parentPA->ExitEdges.end(); it != it2; ++it) {

    if(*it == Edge) {
      LPDEBUG("Edge " << Edge.first->getName() << "->" << Edge.second->getName() << " is an exit edge; considering creating the next iteration\n");
      getOrCreateNextIteration();
    }

  }

}

void IntegrationAttempt::localImprove(Value* From, ValCtx To) {

  H.getBenefit(From, To);
  improveParentAndChildren();

}

void IntegrationAttempt::killEdge(BasicBlock* BB1, BasicBlock* BB2) {

  H.killEdge(BB1, BB2);
  improveParentAndChildren();

}

void IntegrationAttempt::improveParentAndChildren() {

  while(newLocalImprovedValues.size() || newNonLocalImprovedValues.size() || newlyDeadEdges.size() || newlyDeadEdgesNL.size()) {

    SmallVector<std::pair<Value*, Constant*>, 1> newNLVals = newNonLocalImprovedValues;
    newNonLocalImprovedValues.clear();
    
    for(SmallVector<std::pair<Value*, Constant*>, 1>::iterator it = newNLVals.begin(), it2 = newNLVals.end(); it != it2; it++) {

      if(improvedValues.find(it->first) == improvedValues.end()) {
	LPDEBUG("Integrating nonlocal improvement " << *(it->first) << " -> " << *(it->second) << "\n");
	H.getBenefit(it->first, const_vc(it->second));
      }

    }

    SmallVector<Value*, 8> newVals = newLocalImprovedValues;
    newLocalImprovedValues.clear();

    for(SmallVector<Value*, 4>::iterator it = newVals.begin(), it2 = newVals.end(); it != it2; it++) {
      
      // Did this just come from one of our children?
      bool cameFromChild = false;
      for(SmallVector<std::pair<Value*, Constant*>, 1>::iterator it3 = newNLVals.begin(), it4 = newNLVals.end(); it3 != it4; it3++) {
	if(it3->first == *it) {
	  cameFromChild = true;
	  break;
	}
      }
      if(!cameFromChild)
	tryImproveChildren(*it);
      tryImproveParent(*it);

    }

    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> newlyDEs = newlyDeadEdgesNL;
    newlyDeadEdgesNL.clear();

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = newlyDEs.begin(), it2 = newlyDEs.end(); it != it2; it++) {

      LPDEBUG("Integrating nonlocally killed edge " << it->first->getName() << " -> " << it->second->getName() << "\n");
      H.killEdge(it->first, it->second);

    }

    newlyDEs = newlyDeadEdges;
    newlyDeadEdges.clear();

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = newlyDEs.begin(), it2 = newlyDEs.end(); it != it2; it++) {
    
      tryImproveChildrenDE(*it);
      tryImproveParentDE(*it);

    }

  }

}

void InlineAttempt::tryImproveParent(Value* Improved) {

  if((!parent) || returnVal || F.getReturnType()->isVoidTy())
    return;

  bool usedByRet = false;

  for (Value::use_iterator UI = Improved->use_begin(), UE = Improved->use_end(); UI != UE;++UI) {
    
    if(isa<ReturnInst>(*UI))
      usedByRet = true;

  }

  if(!usedByRet)
    return;

  // Let's have a go at supplying a return value to our caller. Simple measure:
  // we know the value if all the 'ret' instructions except one are dead,
  // and we know that instruction's operand.

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
	Constant* C = getConstReplacement(ThisRet);
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

void PeelIteration::tryImproveParent(Value* Improved) {

  if(terminated) {

    for (Value::use_iterator UI = Improved->use_begin(), UE = Improved->use_end(); UI != UE; ++UI) {
      if(PHINode* PN = dyn_cast<PHINode>(*UI)) {
	BasicBlock* BB = PN->getParent();
	if(LI[&F]->getLoopFor(BB) == L->getParentLoop()) {
	  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
	    if(LI[&F]->getLoopFor(*PI) == L) {
	      Instruction* Outgoing = dyn_cast<Instruction>(PN->getIncomingValueForBlock(*PI));
	      if(Outgoing) {
		Constant* C = getConstReplacement(Outgoing);
		if(C) {
		  LPDEBUG("Exporting " << *(Outgoing) << " -> "  << *C << "\n");
		  parent->setNonLocalReplacement(Outgoing, C);
		}
	      }    
	      break;
	    }
	  }
	}
      }
    }

  }

}

void PeelIteration::tryImproveParentDE(std::pair<BasicBlock*, BasicBlock*> Edge) {

  if(!terminated) {

    BasicBlock* Latch = L->getLoopLatch();
    BasicBlock* Header = L->getHeader();
    if(Edge == std::make_pair(Latch, Header)) {

      LPDEBUG("Loop " << L->getHeader()->getName() << " backedge was killed: exporting loop variants to parent context:\n");

      // The loop won't iterate again -- export local constants and dead edges to the next loop/function out.

      SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;
      L->getExitEdges(ExitEdges);
      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = ExitEdges.begin(), EE = ExitEdges.end(); EI != EE; EI++) {

	if(deadEdges.count(*EI)) {
	  LPDEBUG("Exporting dead exit edge " << EI->first->getName() << " -> "  << EI->second->getName() << "\n");
	  parent->setEdgeDead(EI->first, EI->second);
	}
	else {
	  
	  for(BasicBlock::iterator BI = EI->second->begin(), BE = EI->second->end(); BI != BE && isa<PHINode>(BI); ++BI) {	  

	    // We only push values out that are used in exit PHIs. So: use LCSSA form!
	    PHINode* PN = cast<PHINode>(BI);
	    Instruction* Outgoing = dyn_cast<Instruction>(PN->getIncomingValueForBlock(EI->first));
	    if(Outgoing) {
	      Constant* C = getConstReplacement(Outgoing);
	      if(C) {
		LPDEBUG("Exporting " << *(Outgoing) << " -> "  << *C << "\n");
		parent->setNonLocalReplacement(Outgoing, C);
	      }
	    }
	  
	  }

	}

      }

      terminated = true;

    }

  }  

}

void IntegrationAttempt::tryImproveParentDE(std::pair<BasicBlock*, BasicBlock*> Edge) {

  return;

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

void IntegrationAttempt::forceExploreChildren() {

  for(LoopInfo::iterator it = LI[&F]->begin(), it2 = LI[&F]->end(); it != it2; ++it) {

    if(!blockIsDead((*it)->getHeader()))
      getOrCreatePeelAttempt(*it);

  }

  for(Function::iterator it = F.begin(), it2 = F.end(); it != it2; it++) {

    if(blockIsDead(it))
      continue;

    for(BasicBlock::iterator II = it->begin(), IE = it->end(); II != IE; ++II) {

      if(CallInst* CI = dyn_cast<CallInst>(II)) {

	getOrCreateInlineAttempt(CI);

      }

    }

  }

}

// Given a MemDep Def, get the value loaded or stored.
ValCtx IntegrationAttempt::getDefn(const MemDepResult& Res) {

  ValCtx improved = VCNull;
  if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
    improved = getReplacement(SI->getOperand(0));
  }
  else if(LoadInst* DefLI= dyn_cast<LoadInst>(Res.getInst())) {
    improved = getReplacement(DefLI);
  }
  else {
    LPDEBUG("Defined by " << *(Res.getInst()) << " which is not a simple load or store\n");
    return VCNull;
  }

  if(improved.first != Res.getInst() || improved.second != this) {
    LPDEBUG("Definition improved to " << improved << "\n");
    return improved;
  }
  else {
    LPDEBUG("Definition not improved\n");
    return VCNull;
  }

}

// Find the unique definer or clobberer for a given Load.
MemDepResult IntegrationAttempt::getUniqueDependency(LoadInst* LoadI) {

  MemoryDependenceAnalyser MD;
  MD.init(AA, this);

  MemDepResult Seen = MD.getDependency(LoadI);

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

    LPDEBUG(*LoadI << " nonlocally defined by " << Seen << "\n");

  }
  else {
    LPDEBUG(*LoadI << " locally defined by " << Seen << "\n");
  }

  return Seen;

}

// Make a symbolic expression for a given load instruction if it depends solely on one pointer
// with many constant offsets.
bool IntegrationAttempt::buildSymExpr(LoadInst* LoadI, SmallVector<SymExpr*, 4>& Expr) {

  // Precondition: LoadI is clobbered in exactly one place: the entry instruction to the enclosing context.
  // This might mean that instruction actually clobbers it, or it's defined by instructions outside this function.
  
  if(!parent)
    return false;

  Value* Ptr = LoadI->getPointerOperand();

  LPDEBUG("Trying to resolve load from " << *LoadI << " by exploring parent contexts\n");

  // Check that we're trying to fetch a cast-of-constGEP-of-cast-of... an identified object, and
  // build a symbolic expression representing the derived expression if so.
 
  bool success = true;

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
	  success = false; break;
	}
      }
      Expr.push_back((new SymGEP(idxs)));
      Ptr = GEP->getPointerOperand();
    }
    else if(BitCastInst* C = dyn_cast<BitCastInst>(Ptr)) {
      Expr.push_back((new SymCast(C->getType())));
      Ptr = C->getOperand(0);
    }
    else {
      ValCtx Repl = getReplacement(Ptr);
      if(isIdentifiedObject(Repl.first) || Repl.second > 0) {
	Expr.push_back((new SymThunk(Repl)));
	break;
      }
      else if(Repl.first == Ptr && Repl.second == 0) {
	LPDEBUG("Won't investigate load from parent context due to unresolved pointer " << *Ptr << "\n");
	success = false; break;
      }
      else {
	Ptr = Repl.first; // Must continue resolving!
      }
    }
    
  }


  if(!success) {
    for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
      delete (*it);
    }
    Expr.clear();
  }

  return success;

}

// Realise a symbolic expression at a given location. 
// Temporary instructions are created and recorded for later deletion.
void IntegrationAttempt::realiseSymExpr(SmallVector<SymExpr*, 4>& in, Instruction* Where, Instruction*& FakeBaseObject, LoadInst*& Accessor, SmallVector<Instruction*, 4>& tempInstructions) {

  // Build it backwards: the in chain should end in a defined object, in or outside our scope.
  // Start with that, then wrap it incrementally in operators.
  
  SmallVector<SymExpr*, 4>::iterator SI = in.end(), SE = in.begin();
  
  Value* lastPtr;
  
  SI--;
  SymThunk* th = cast<SymThunk>(*SI);

  LLVMContext& ctx = F.getContext();
  BasicBlock::iterator BI(Where);
  IRBuilder<> Builder(ctx);
  Builder.SetInsertPoint(Where->getParent(), *BI);

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
  lastPtr = FakeBaseObject = Builder.CreateLoad(FakeLoc);
  tempInstructions.push_back(FakeBaseObject);

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
  Accessor = Builder.CreateLoad(lastPtr);
  tempInstructions.push_back(Accessor);

  LPDEBUG("Temporarily augmented parent block:\n");
  DEBUG(dbgs() << *Where->getParent());

}

// Main load forwarding entry point, called by the hypothetical constant folder:
// Try to forward the load locally (within this loop or function), or otherwise build a symbolic expression
// and ask our parent to continue resolving the load.
ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LoadI) {

  LPDEBUG("Trying to forward load: " << *LoadI << "\n");

  ValCtx Result;
  if(forwardLoadIsNonLocal(LoadI, Result)) {
    SmallVector<SymExpr*, 4> Expr;
    if(!buildSymExpr(LoadI, Expr))
      return VCNull; 

    LPDEBUG("Will resolve ");

    for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
      if(it != Expr.begin())
	DEBUG(dbgs() << " of ");
      DEBUG((*it)->describe(dbgs()));
    }

    DEBUG(dbgs() << "\n");

    ValCtx SubcallResult = tryForwardExprFromParent(Expr);
   
    for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
      delete (*it);
    }

    return SubcallResult;
  }
  else {
    if(Result != VCNull) {
      LPDEBUG("Forwarded " << *LoadI << " locally: got " << Result << "\n");
    }
    return Result;
  }

}

// Pursue a load further. Current context is a function body; ask our caller to pursue further.
ValCtx InlineAttempt::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr) {

  LPDEBUG("Resolving load at call site\n");
  return parent->tryResolveLoadAtChildSite(this, Expr);

}

// Pursue a load further. Current context is a loop body -- try resolving it in previous iterations,
// then ask our enclosing loop or function body to look further.
ValCtx PeelAttempt::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, int originIter) {

  // First of all, try winding backwards through our sibling iterations. We can use a single realisation
  // of Expr for all of these checks, since the instructions are always the same.

  SmallVector<Instruction*, 4> tempInstructions;
  Instruction* FakeBase;
  LoadInst* Accessor;
  Iterations[0]->realiseSymExpr(Expr, L->getLoopLatch()->getTerminator(), FakeBase, Accessor, tempInstructions);
  
  SymThunk* Th = cast<SymThunk>(Expr.back());
  ValCtx Result;
  bool resultValid = false;

  LPDEBUG("Trying to resolve by walking backwards through " << L->getHeader()->getName() << "\n");

  for(int iter = originIter - 1; iter >= 0; iter--) {

    LPDEBUG("Trying to resolve in iteration " << iter << "\n");

    if(Iterations[iter]->tryResolveExprUsing(Expr, FakeBase, Accessor, Result)) {
      if(Result.first) {
	LPDEBUG("Resolved to " << Result << "\n");
      }
      else {
	Result = VCNull;
	LPDEBUG("Resolution failed\n");
      }
      resultValid = true;
      break;
    }

    if(Th->RealVal.second == Iterations[iter]) {
      LPDEBUG("Abandoning resolution: " << Th->RealVal << " is out of scope\n");
      Result = VCNull;
      resultValid = true;
      break;
    }

  }

  LPDEBUG("*** Destroy from PeelAttempt\n");
  Iterations[0]->destroySymExpr(tempInstructions);

  if(resultValid)
    return Result;

  LPDEBUG("Resolving out the preheader edge; deferring to parent\n");

  return parent->tryResolveLoadAtChildSite(Iterations[0], Expr);

}

// Helper: loop iterations defer the resolution process to the abstract loop.
ValCtx PeelIteration::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr) {

  return parentPA->tryForwardExprFromParent(Expr, this->iterationCount);

}

// Try forwarding a load locally; return true if it is nonlocal or false if not, in which case
// Result is set to the resolution result.
bool IntegrationAttempt::forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result) {

  MemDepResult Res = getUniqueDependency(LoadI);

  if(Res.isClobber()) {
    if(Res.getInst()->getParent() == getEntryBlock()) {
      BasicBlock::iterator TestII(Res.getInst());
      if(TestII == getEntryBlock()->begin()) {
	return true;
      }
    }
    Result = VCNull;
  }
  else if(Res.isDef()) {
    Result = getDefn(Res);
  }

  return false;

}

void IntegrationAttempt::destroySymExpr(SmallVector<Instruction*, 4>& tempInstructions) {

  for(SmallVector<Instruction*, 4>::iterator II = tempInstructions.end(), IE = tempInstructions.begin(); II != IE; ) {
    Instruction* I = *(--II);
    I->eraseFromParent();
  }

}

 bool IntegrationAttempt::tryResolveExprUsing(SmallVector<SymExpr*, 4>& Expr, Instruction* FakeBase, LoadInst* Accessor, ValCtx& Result) {

  SymThunk* Th = cast<SymThunk>(Expr.back());

  improvedValues[FakeBase] = Th->RealVal;
  //LPDEBUG("Set fake base pointer " << *FakeBase << " --> " << Th->RealVal << "\n");
  bool shouldPursueFurther = forwardLoadIsNonLocal(Accessor, Result);
  improvedValues.erase(FakeBase);

  return shouldPursueFurther;

}

bool IntegrationAttempt::tryResolveExprFrom(SmallVector<SymExpr*, 4>& Expr, Instruction* Where, ValCtx& Result) {

  Instruction* FakeBase;
  LoadInst* Accessor;
  SmallVector<Instruction*, 4> tempInstructions;
  realiseSymExpr(Expr, Where, FakeBase, Accessor, tempInstructions);
  
  bool shouldPursueFurther = tryResolveExprUsing(Expr, FakeBase, Accessor, Result);

  LPDEBUG("*** Erase from tryResolveExprFrom\n");
  destroySymExpr(tempInstructions);

  return shouldPursueFurther;

}

// Entry point for a child loop or function that wishes us to continue pursuing a load.
// Find the instruction before the child begins (so loop preheader or call site), realise the given symbolic
// expression, and try ordinary load forwarding from there.
ValCtx IntegrationAttempt::tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<SymExpr*, 4>& Expr) {

  ValCtx Result;

  LPDEBUG("Continuing resolution from entry point " << *(IA->getEntryInstruction()) << "\n");

  if(tryResolveExprFrom(Expr, IA->getEntryInstruction(), Result)) {
    LPDEBUG("Still nonlocal, passing to our parent scope\n");
    return tryForwardExprFromParent(Expr);
  }
  else {
    LPDEBUG("Resolved at this scope: " << Result << "\n");
    return Result;
  }

}

void IntegrationAttempt::collectBlockStats(BasicBlock* BB) {

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; BI++) {
      
    if(instructionCounts(BI)) { 

      if(BB == getEntryBlock() && isa<PHINode>(BI))
	continue;

      improvableInstructions++;

      if(blockIsDead(BB))
	improvedInstructions++;
      else if(improvedValues.find(BI) != improvedValues.end())
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

void IntegrationAttempt::collectLoopStats(Loop* LoopI) {

  DenseMap<Loop*, PeelAttempt*>::iterator it = peelChildren.find(LoopI);

  if(it == peelChildren.end()) {
    unexploredLoops.push_back(LoopI);
    for(Loop::block_iterator BI = LoopI->block_begin(), BE = LoopI->block_end(); BI != BE; ++BI)
      collectBlockStats(*BI);
  }

}

void InlineAttempt::collectAllBlockStats() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI)
    if(!LI[&F]->getLoopFor(FI))
      collectBlockStats(FI);

  for(LoopInfo::iterator LoopI = LI[&F]->begin(), LoopE = LI[&F]->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelIteration::collectAllBlockStats() {

  for(Loop::block_iterator BI = L->block_begin(), BE = L->block_end(); BI != BE; ++BI) {
    if(LI[&F]->getLoopFor(*BI) == L)
      collectBlockStats(*BI);
  }

  for(Loop::iterator LoopI = L->begin(), LoopE = L->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelAttempt::collectStats() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->collectStats();

}

void IntegrationAttempt::collectStats() {

  collectAllBlockStats();

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->collectStats();

  for(DenseMap<Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->collectStats();

}

void InlineAttempt::printHeader(raw_ostream& OS) const {

  OS << (!CI ? "Root " : "") << "Function " << F.getName();
  if(CI)
    OS << " at " << *CI;

}

void PeelIteration::printHeader(raw_ostream& OS) const {

  OS << "Iteration " << iterationCount;

}

void PeelAttempt::print(raw_ostream& OS) const {

  OS << dbgind() << "Loop " << L->getHeader()->getName() << (Iterations.back()->terminated ? "(terminated)" : "(not terminated)") << "\n";

  for(std::vector<PeelIteration*>::const_iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->print(OS);

  }

}

void IntegrationAttempt::print(raw_ostream& OS) const {

  OS << dbgind();
  printHeader(OS);
  OS << ": improved " << improvedInstructions << "/" << improvableInstructions << "\n";
  for(DenseMap<Value*, ValCtx>::const_iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {
    OS << dbgind() << *(it->first) << " -> " << it->second << "\n";
  }
  if(unexploredLoops.size()) {
    OS << dbgind() << "Unexplored loops:\n";
    for(SmallVector<Loop*, 4>::const_iterator it = unexploredLoops.begin(), it2 = unexploredLoops.end(); it != it2; ++it) {
      OS << dbgind() << "  " << (*it)->getHeader()->getName() << "\n";
    }
  }
  if(unexploredCalls.size()) {
    OS << dbgind() << "Unexplored calls:\n";
    for(SmallVector<CallInst*, 4>::const_iterator it = unexploredCalls.begin(), it2 = unexploredCalls.end(); it != it2; ++it) {
      OS << dbgind() << **it << "\n";
    }
  }

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

  for(DenseMap<Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

}

std::string IntegrationAttempt::dbgind() const {

  return ind(debugIndent);

}

std::string PeelAttempt::dbgind() const {

  return ind(debugIndent);

}

bool IntegrationHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<TargetData>();
  AA = &getAnalysis<AliasAnalysis>();
  
  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    if(!MI->isDeclaration())
      LIs[MI] = &getAnalysis<LoopInfo>(*MI);

  }

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    if(MI->isDeclaration())
      continue;

    Function& F = *MI;

    DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");
    rootAttempts.push_back(new InlineAttempt(0, F, LIs, TD, AA, 0, 0, 2));
    rootAttempts.back()->forceExploreChildren();
    rootAttempts.back()->improveParentAndChildren();
    rootAttempts.back()->collectStats();
    
    //    rootAttempts.back()->considerCalls(true);
    //    rootAttempts.back()->countResidualCalls();

  }

  return false;

}
