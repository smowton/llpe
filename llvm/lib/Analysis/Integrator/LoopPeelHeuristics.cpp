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
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRBuilder.h"

#include <string>
#include <algorithm>

using namespace llvm;

bool instructionCounts(Instruction* I);

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
  for(DenseMap<const Loop*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }
}

PeelAttempt::PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, const Loop* _L, int depth) 
  : pass(Pass), parent(P), F(_F), LI(_LI), TD(_TD), AA(_AA), L(_L), nesting_depth(depth)
{
  
  L->getExitEdges(ExitEdges);
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

  improvedValues[V] = R;

}

bool IntegrationAttempt::edgeIsDead(BasicBlock* B1, BasicBlock* B2) {

  return deadEdges.count(std::make_pair(B1, B2));

}

void IntegrationAttempt::setEdgeDead(BasicBlock* B1, BasicBlock* B2) {

  std::pair<BasicBlock*, BasicBlock*> Edge = std::make_pair(B1, B2);
  deadEdges.insert(Edge);

}

bool IntegrationAttempt::blockIsDead(BasicBlock* BB) {

  return deadBlocks.count(BB);

}

void IntegrationAttempt::setBlockDead(BasicBlock* BB) {

  deadBlocks.insert(BB);

}

InlineAttempt* IntegrationAttempt::getInlineAttempt(CallInst* CI) {

  DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(const_cast<CallInst*>(CI));
  if(it != inlineChildren.end())
    return it->second;

  return 0;

}

InlineAttempt* IntegrationAttempt::getOrCreateInlineAttempt(CallInst* CI) {

  if(InlineAttempt* IA = getInlineAttempt(CI))
    return IA;

  if(Function* FCalled = CI->getCalledFunction()) {

    if((!FCalled->isDeclaration()) && (!FCalled->isVarArg())) {

      if(certainBlocks.count(CI->getParent())) {

	InlineAttempt* IA = new InlineAttempt(pass, this, *FCalled, this->LI, this->TD, this->AA, CI, this->nesting_depth + 1);
	inlineChildren[CI] = IA;

	LPDEBUG("Inlining " << FCalled->getName() << " at " << *CI << "\n");

	// Check every argument, for natural constants or for variables that have already been established.
      
	for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
	  
	  pass->queueTryEvaluate(IA, &*AI /* Iterator to pointer */);

	}

	IA->queueCheckAllLoads();

	return IA;

      }
      else {
	LPDEBUG("Ignored " << *CI << " because it is not yet certain to execute\n");
      }

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

void PeelIteration::queueCheckExitBlock(BasicBlock* BB) {

  pass->queueCheckBlock(parent, BB);

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE && isa<PHINode>(BI); ++BI) {

    pass->queueTryEvaluate(parent, BI);
	
  }

}

void PeelIteration::checkFinalIteration() {

  // Check whether we now have evidence the loop terminates this time around
  // If it does, queue consideration of each exit PHI; by LCSSA these must belong to our parent.

  if(deadEdges.count(std::make_pair(L->getLoopLatch(), L->getHeader()))) {

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = parentPA->ExitEdges.begin(), EE = parentPA->ExitEdges.end(); EI != EE; ++EI) {

      queueCheckExitBlock(EI->second);

    }
    
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

  PeelIteration* NewIter = new PeelIteration(pass, parent, this, F, LI, TD, AA, L, iter, nesting_depth);
  Iterations.push_back(NewIter);
    
  BasicBlock* Header = L->getHeader();
   
  pass->queueCheckBlock(NewIter, L->getHeader());
 
  for(BasicBlock::iterator BI = Header->begin(), BE = Header->end(); BI != BE && isa<PHINode>(BI); ++BI) {
	
    pass->queueTryEvaluate(NewIter, BI);

  }

  NewIter->queueCheckAllLoads();

  return NewIter;

}

PeelIteration* PeelIteration::getNextIteration() {

  return parentPA->getIteration(this->iterationCount + 1);

}

PeelIteration* PeelIteration::getOrCreateNextIteration() {

  if(PeelIteration* Existing = getNextIteration())
    return Existing;

  if(iterStatus == IterationStatusFinal) {
    LPDEBUG("Loop known to exit: will not create next iteration\n");
    return 0;
  }

  bool willIterate = true;

  for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = parentPA->ExitEdges.begin(), EE = parentPA->ExitEdges.end(); EI != EE; ++EI) {

    if(!deadEdges.count(*EI)) {
      willIterate = false;
    }

  }
  
  if(!willIterate) {

    LPDEBUG("Won't peel loop " << L->getHeader()->getName() << " yet because at least one exit edge is still alive\n");
    return 0;
      
  }

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

  if(PeelAttempt* PA = getPeelAttempt(NewL))
    return PA;
  
  // Preheaders only have one successor (the header), so this is enough.
  if(!certainBlocks.count(NewL->getLoopPreheader())) {
   
    LPDEBUG("Will not expand loop " << NewL->getHeader()->getName() << " at this time because the preheader is not certain to execute\n");
    return 0;

  }

  if(NewL->getLoopPreheader() && NewL->getLoopLatch() && (NewL->getNumBackEdges() == 1)) {

    LPDEBUG("Considering inlining loop with header " << NewL->getHeader()->getName() << "\n");
    PeelAttempt* LPA = new PeelAttempt(pass, this, F, LI, TD, AA, NewL, nesting_depth + 1);
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
	  LPDEBUG("Can't determine return value: live instruction " << *RI << " has non-forwardable value " << *(RI->getReturnValue()) << "\n");
	  break;
	}
      }
    }
  }
  
  if(returnVal.first) {
    LPDEBUG("Found return value: " << returnVal << "\n");
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

ValCtx InlineAttempt::getImprovedCallArgument(Argument* A) {

  return parent->getReplacement(CI->getArgOperand(A->getArgNo()));

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

    if(NLResults.size() == 0) {

      // Probably we're in a block which is dead, but has yet to be diagnosed as such.
      return MemDepResult();

    }

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

    if(GEPOperator* GEP = dyn_cast<GEPOperator>(Ptr)) {
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
      if(isIdentifiedObject(Repl.first)) {
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

  //  LPDEBUG("Temporarily augmented parent block:\n");
  //  DEBUG(dbgs() << *Where->getParent());

}

// Main load forwarding entry point:
// Try to forward the load locally (within this loop or function), or otherwise build a symbolic expression
// and ask our parent to continue resolving the load.
ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LoadI) {

  LPDEBUG("Trying to forward load: " << *LoadI << "\n");

  ValCtx Result;

  if(Constant* C = getConstReplacement(LoadI->getPointerOperand())) {

    // Try ordinary constant folding first! Might not work because globals constitute constant expressions.
    // For them we should do the ordinary alias analysis task.
    Constant* ret = ConstantFoldLoadFromConstPtr(C, this->TD);
    LPDEBUG("Resolved load as a constant expression\n");
    if(ret)
      return const_vc(ret);

  }

  // Check whether pursuing alises is pointless -- this is true if we're certain that the ultimate underlying object is a constant.
  // If it is, our attempt above was likely foiled only by uncertainty about the specific bit of the constant (e.g. index within a const string)
  // and the only way the situation will improve is if those offsets become clear.

  ValCtx Ultimate = getDefaultVC(LoadI->getPointerOperand());
  while(!isIdentifiedObject(Ultimate.first)) {

    ValCtx New = Ultimate.second->getReplacement(Ultimate.first);
    New = make_vc(New.first->getUnderlyingObject(), New.second);
  
    if(New == Ultimate)
      break;

    Ultimate = New;

  }

  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(Ultimate.first)) {

    if(GV->isConstant()) {
      LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
      return VCNull;
    }

  }

  if(forwardLoadIsNonLocal(LoadI, Result, this)) {
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

    ValCtx SubcallResult = tryForwardExprFromParent(Expr, this);
   
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
ValCtx InlineAttempt::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx) {

  if(!parent) {
    LPDEBUG("Unable to pursue further; this function is the root\n");
    return VCNull;
  }
  else {
    LPDEBUG("Resolving load at call site\n");
    return parent->tryResolveLoadAtChildSite(this, Expr, originCtx);
  }

}

// Pursue a load further. Current context is a loop body -- try resolving it in previous iterations,
// then ask our enclosing loop or function body to look further.
ValCtx PeelAttempt::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, int originIter, IntegrationAttempt* originCtx) {

  // First of all, try winding backwards through our sibling iterations. We can use a single realisation
  // of Expr for all of these checks, since the instructions are always the same.

  SmallVector<Instruction*, 4> tempInstructions;
  Instruction* FakeBase;
  LoadInst* Accessor;
  Iterations[0]->realiseSymExpr(Expr, L->getLoopLatch()->getTerminator(), FakeBase, Accessor, tempInstructions);
  
  SymThunk* Th = cast<SymThunk>(Expr.back());
  ValCtx Result;
  bool resultValid = false;

  LPDEBUG("Trying to resolve by walking backwards through loop " << L->getHeader()->getName() << "\n");

  for(int iter = originIter - 1; iter >= 0; iter--) {

    LPDEBUG("Trying to resolve in iteration " << iter << "\n");

    if(!(Iterations[iter]->tryResolveExprUsing(Expr, FakeBase, Accessor, Result, originCtx))) {
      // Shouldn't pursue further -- the result is either defined or conclusively clobbered here.
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
    else {
      // Go round the loop and try the next iteration.
    }

    if(Th->RealVal.second == Iterations[iter]) {
      LPDEBUG("Abandoning resolution: " << Th->RealVal << " is out of scope\n");
      Result = VCNull;
      resultValid = true;
      break;
    }

  }

  Iterations[0]->destroySymExpr(tempInstructions);

  if(resultValid)
    return Result;

  LPDEBUG("Resolving out the preheader edge; deferring to parent\n");

  return parent->tryResolveLoadAtChildSite(Iterations[0], Expr, originCtx);

}

// Helper: loop iterations defer the resolution process to the abstract loop.
ValCtx PeelIteration::tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx) {

  return parentPA->tryForwardExprFromParent(Expr, this->iterationCount, originCtx);

}

// Try forwarding a load locally; return true if it is nonlocal or false if not, in which case
// Result is set to the resolution result.
bool IntegrationAttempt::forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result, IntegrationAttempt* originCtx) {

  MemDepResult Res = getUniqueDependency(LoadI);

  if(Res.isClobber()) {
    if(Res.getInst()->getParent() == getEntryBlock()) {
      BasicBlock::iterator TestII(Res.getInst());
      if(TestII == getEntryBlock()->begin()) {
	return true;
      }
    }
    else {
      assert(Res.getInst()->mayWriteToMemory());
      InstBlockedLoads[Res.getInst()].push_back(std::make_pair(originCtx, LoadI));
    }
    Result = VCNull;
  }
  else if(Res.isDef()) {
    Result = getDefn(Res);
  }
  else if(Res == MemDepResult()) {
    // The definition or clobber was not unique. Edges need to be killed before this can be resolved.
    CFGBlockedLoads.push_back(std::make_pair(originCtx, LoadI));
  }

  return false;

}

void IntegrationAttempt::destroySymExpr(SmallVector<Instruction*, 4>& tempInstructions) {

  for(SmallVector<Instruction*, 4>::iterator II = tempInstructions.end(), IE = tempInstructions.begin(); II != IE; ) {
    Instruction* I = *(--II);
    I->eraseFromParent();
  }

}

bool IntegrationAttempt::tryResolveExprUsing(SmallVector<SymExpr*, 4>& Expr, Instruction* FakeBase, LoadInst* Accessor, ValCtx& Result, IntegrationAttempt* originCtx) {

  SymThunk* Th = cast<SymThunk>(Expr.back());

  improvedValues[FakeBase] = Th->RealVal;
  //LPDEBUG("Set fake base pointer " << *FakeBase << " --> " << Th->RealVal << "\n");
  bool shouldPursueFurther = forwardLoadIsNonLocal(Accessor, Result, originCtx);
  improvedValues.erase(FakeBase);

  return shouldPursueFurther;

}

bool IntegrationAttempt::tryResolveExprFrom(SmallVector<SymExpr*, 4>& Expr, Instruction* Where, ValCtx& Result, IntegrationAttempt* originCtx) {

  Instruction* FakeBase;
  LoadInst* Accessor;
  SmallVector<Instruction*, 4> tempInstructions;
  realiseSymExpr(Expr, Where, FakeBase, Accessor, tempInstructions);
  
  bool shouldPursueFurther = tryResolveExprUsing(Expr, FakeBase, Accessor, Result, originCtx);

  destroySymExpr(tempInstructions);

  return shouldPursueFurther;

}

// Entry point for a child loop or function that wishes us to continue pursuing a load.
// Find the instruction before the child begins (so loop preheader or call site), realise the given symbolic
// expression, and try ordinary load forwarding from there.
ValCtx IntegrationAttempt::tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx) {

  ValCtx Result;

  LPDEBUG("Continuing resolution from entry point " << *(IA->getEntryInstruction()) << "\n");

  if(tryResolveExprFrom(Expr, IA->getEntryInstruction(), Result, originCtx)) {
    LPDEBUG("Still nonlocal, passing to our parent scope\n");
    return tryForwardExprFromParent(Expr, originCtx);
  }
  else {
    LPDEBUG("Resolved at this scope: " << Result << "\n");
    return Result;
  }

}

void PeelIteration::describe(raw_ostream& Stream) const {

  Stream << "(Loop " << L->getHeader()->getName() << "/" << iterationCount << ")";

}


void InlineAttempt::describe(raw_ostream& Stream) const {

  Stream << "(" << F.getName() << ")";

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

void IntegrationAttempt::collectLoopStats(const Loop* LoopI) {

  DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.find(LoopI);

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

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->collectStats();

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->collectStats();

}

void InlineAttempt::printHeader(raw_ostream& OS) const {

  OS << (!CI ? "Root " : "") << "Function " << F.getName();
  if(CI)
    OS << " at " << *CI;

}

void PeelIteration::printHeader(raw_ostream& OS) const {

  OS << "Loop " << L->getHeader()->getName() << " iteration " << iterationCount;

}

void PeelAttempt::printHeader(raw_ostream& OS) const {

  OS << "Loop " << L->getHeader()->getName();

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
    OS << nestingIndent() << *(it->first) << " -> " << it->second << "\n";
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
      OS << nestingIndent() << **it << "\n";
    }
  }

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

}

std::string IntegrationAttempt::nestingIndent() const {

  return ind(nesting_depth * 2);

}

std::string PeelAttempt::nestingIndent() const {

  return ind(nesting_depth * 2);

}

void IntegratorWQItem::execute() { 
  switch(type) {
  case TryEval:
    ctx->tryEvaluate((Value*)operand);
    break;
  case CheckBlock:
    ctx->checkBlock((BasicBlock*)operand);
    break;
  case CheckLoad:
    ctx->checkLoad((LoadInst*)operand);
    break;
  }
}

void IntegratorWQItem::describe(raw_ostream& s) {

  switch(type) {
  case TryEval:
    s << "Try-eval " << *((Value*)operand);
    break;
  case CheckBlock:
    s << "Check-BB-status " << ((BasicBlock*)operand)->getName();
    break;
  case CheckLoad:
    s << "Check-load " << make_vc((LoadInst*)operand, ctx);
    break;
  }

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

    InlineAttempt* IA = new InlineAttempt(this, 0, F, LIs, TD, AA, 0, 0);

    rootAttempts.push_back(IA);

    SmallVector<IntegratorWQItem, 64>* consumeQueue = &workQueue1;
    produceQueue = &workQueue2;

    queueCheckBlock(IA, &(F.getEntryBlock()));
    IA->queueCheckAllLoads();

    while(workQueue1.size() || workQueue2.size()) {

      for(SmallVector<IntegratorWQItem, 64>::iterator it = consumeQueue->begin(), itend = consumeQueue->end(); it != itend; ++it) {

	DEBUG(dbgs() << "Dequeue: ");
	DEBUG(it->describe(dbgs()));
	DEBUG(dbgs() << "\n");
	it->execute();

      }

      consumeQueue->clear();
      if(consumeQueue == &workQueue1) {
	consumeQueue = &workQueue2;
	produceQueue = &workQueue1;
      }
      else {
	consumeQueue = &workQueue1;
	produceQueue = &workQueue2;
      }

    }
    
    IA->collectStats();
    
    //    rootAttempts.back()->considerCalls(true);
    //    rootAttempts.back()->countResidualCalls();

  }

  return false;

}

void IntegrationHeuristicsPass::getAnalysisUsage(AnalysisUsage &AU) const {

  AU.addRequired<AliasAnalysis>();
  AU.addRequired<LoopInfo>();
  AU.setPreservesAll();
  
}
