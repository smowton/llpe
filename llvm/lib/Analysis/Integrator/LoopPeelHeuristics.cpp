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

#include <string>
#include <algorithm>

#define LPDEBUG(x) DEBUG(dbgs() << dbgind() << x)

using namespace llvm;

bool instructionCounts(Instruction* I);

namespace {
  
  class PeelHeuristicsLoopRunStats {

  public:

    unsigned int exitEdges;
    unsigned int exitEdgesEliminated;
    unsigned int blocksKilled;
    unsigned int totalBlocks;
    unsigned int headerPhis;
    unsigned int headerPhisDefined;
    unsigned int nonPhiInstructionsEliminated;
    unsigned int totalNonPhiInstructions;
    bool latchBranchEliminated;
    bool allPhisConstantFromPreheader;

    PeelHeuristicsLoopRunStats() {
      exitEdges = 0;
      exitEdgesEliminated = 0;
      blocksKilled = 0;
      totalBlocks = 0;
      headerPhis = 0;
      headerPhisDefined = 0;
      nonPhiInstructionsEliminated = 0;
      totalNonPhiInstructions = 0;
      latchBranchEliminated = false;
      allPhisConstantFromPreheader = false;
    }

  };

  class PeelHeuristicsLoopRun {

    LoopInfo* LI;
    TargetData* TD;

    DenseMap<Loop*, PeelHeuristicsLoopRun> childLoops;

    std::string loopHeaderName;
    bool doConstProp;

    int debugIndent;

    void accountElimInstruction(Instruction*);
    void doForAllLoops(void (*callback)(PeelHeuristicsLoopRun*), llvm::Instruction*);

    std::string dbgind();

  public:

    Loop* L;
    PeelHeuristicsLoopRun* parentRun;

    PeelHeuristicsLoopRunStats stats;
    PeelHeuristicsLoopRunStats statsBefore;

    PeelHeuristicsLoopRun() : doConstProp(true) { }

    bool doSimulatedPeel(DenseMap<Value*, Constant*>&, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>&, PeelHeuristicsLoopRun* parent, TargetData*, AliasAnalysis*);
    void getAllChildren(std::vector<PeelHeuristicsLoopRun*>&, bool topLevel);
    void doInitialStats(Loop*, LoopInfo*);
    void setDebugIndent(int);
    void print(raw_ostream &OS, int indent) const;

  };

  class LoopPeelHeuristicsPass : public FunctionPass {

    DenseMap<Loop*, PeelHeuristicsLoopRun> topLevelLoops;

  public:

    static char ID;

    explicit LoopPeelHeuristicsPass() : FunctionPass(ID) { }
    bool runOnFunction(Function& F);
    void print(raw_ostream &OS, const Module* M) const {
      for(DenseMap<Loop*, PeelHeuristicsLoopRun>::const_iterator LI = topLevelLoops.begin(), LE = topLevelLoops.end(); LI != LE; LI++) {
	LI->second.print(OS, 0);
      }
    }
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {

      AU.addRequired<LoopInfo>();
      AU.addRequired<AliasAnalysis>();
      AU.setPreservesAll();

    }

  };

  char LoopPeelHeuristicsPass::ID = 0;

  class InlineAttempt { 

    TargetData* TD;
    AliasAnalysis* AA;

    Function& F;

    int nested_calls;

    DenseMap<CallInst*, InlineAttempt*> subAttempts;
    
    int debugIndent;

    int totalInstructions;
    int residualCalls;

    DenseMap<Value*, Constant*> initialConsts; // No initial constants except the root values
    SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> initialIgnoreEdges; // All edges considered to exist
    SmallSet<BasicBlock*, 4> outerBlocks; // All blocks are of interest
    
    SmallVector<Instruction*, 16> eliminatedInstructions;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> eliminatedEdges;

    HypotheticalConstantFolder H;

  public:

    SmallVector<bool, 4> argsAlreadyKnown;
    bool returnValueAlreadyKnown;
    Constant* returnVal;

    InlineAttempt(TargetData* _TD, AliasAnalysis* _AA, Function& _F, 
		  int ncalls, int indent) : TD(_TD), 
					    AA(_AA), 
					    F(_F), 
					    nested_calls(ncalls), 
					    debugIndent(indent), 
					    totalInstructions(0), 
					    residualCalls(0),
					    initialConsts(), 
					    initialIgnoreEdges(), 
					    outerBlocks(), 
					    eliminatedInstructions(),
					    eliminatedEdges(), 
					    H(&_F, initialConsts, initialIgnoreEdges, outerBlocks, eliminatedInstructions, eliminatedEdges, _AA, _TD),
					    argsAlreadyKnown(), 
					    returnValueAlreadyKnown(false), 
					    returnVal(0)
    {

      H.setDebugIndent(ncalls * 2);
      for(unsigned i = 0; i < F.arg_size(); i++) {
	argsAlreadyKnown.push_back(false);
      }

      for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {
	for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++) {
	  if(instructionCounts(BI))
	    totalInstructions++;
	}
      }

    }

    ~InlineAttempt() {
      for(DenseMap<CallInst*, InlineAttempt*>::iterator II = subAttempts.begin(), IE = subAttempts.end(); II != IE; II++) {
	delete (II->second);
      }
    }

    void considerSubAttempt(CallInst* CI, Function* FCalled, bool force);
    void localFoldConstants(SmallVector<std::pair<Value*, Constant*>, 4>& args);
    void foldArguments(SmallVector<std::pair<Value*, Constant*>, 4>& args);
    void countResidualCalls();
    void considerCalls(bool force);
    void considerCallInst(CallInst* CI, bool force);

    std::string dbgind() const;

    void print(raw_ostream &OS) const;

  };

  class InlineHeuristicsPass : public ModulePass {

    TargetData* TD;
    AliasAnalysis* AA;

    SmallVector<InlineAttempt*, 4> rootAttempts;

  public:

    static char ID;

    explicit InlineHeuristicsPass() : ModulePass(ID) { }
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
      AU.setPreservesAll();

    }

  };
  
  char InlineHeuristicsPass::ID = 0;

}

FunctionPass *llvm::createLoopPeelHeuristicsPass() {
  return new LoopPeelHeuristicsPass();
}

INITIALIZE_PASS(LoopPeelHeuristicsPass, "peelheuristics", "Score loops for peeling benefit", false, false);

ModulePass *llvm::createInlineHeuristicsPass() {
  return new InlineHeuristicsPass();
}

INITIALIZE_PASS(InlineHeuristicsPass, "inlineheuristics", "Score call sites for inlining benefit", false, false);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

static std::string ind(int i) {

  char* arr = (char*)alloca(i+1);
  for(int j = 0; j < i; j++)
    arr[j] = ' ';
  arr[i] = '\0';
  return std::string(arr);

}

void incBlocksElim(PeelHeuristicsLoopRun* run) {

  run->stats.blocksKilled++;

}

void incElimInstructions(PeelHeuristicsLoopRun* run) {

  run->stats.nonPhiInstructionsEliminated++;

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

std::string PeelHeuristicsLoopRun::dbgind() {

  return ind(debugIndent);

}

void PeelHeuristicsLoopRun::doForAllLoops(void (*callback)(PeelHeuristicsLoopRun*), Instruction* I) {

  Loop* innermostLoop = LI->getLoopFor(I->getParent());
  Loop* thisL = innermostLoop;
  SmallVector<Loop*, 4> elimLoops;
  while(thisL != L) {
    elimLoops.push_back(thisL);
    thisL = thisL->getParentLoop();
  }
  PeelHeuristicsLoopRun* currentRun = this;
  callback(this);
      
  for(int i = elimLoops.size() - 1; i >= 0; i--) {
    currentRun = &(currentRun->childLoops[elimLoops[i]]);
    callback(currentRun);
  }

}

void PeelHeuristicsLoopRun::accountElimInstruction(Instruction* I) {

  if(instructionCounts(I))
    doForAllLoops(&incElimInstructions, I);

}

void PeelHeuristicsLoopRun::doInitialStats(Loop* L, LoopInfo* LI) {

  this->L = L;
  this->LI = LI;

  for(LoopInfo::iterator LIt = L->begin(), LE = L->end(); LIt != LE; LIt++) {

    Loop* thisLoop = *LIt;
    PeelHeuristicsLoopRun& thisRun = childLoops[thisLoop];
    thisRun.doInitialStats(thisLoop, LI);
    stats.totalNonPhiInstructions += thisRun.stats.totalNonPhiInstructions;
    stats.totalBlocks += thisRun.stats.totalBlocks;

  }

  std::vector<BasicBlock*> blocks = L->getBlocks();

  for(std::vector<BasicBlock*>::iterator BI = blocks.begin(), BE = blocks.end(); BI != BE; BI++) {

    BasicBlock* BB = *BI;

    if(LI->getLoopFor(BB) == L) { 

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; II++) {
	if(instructionCounts(II))
	  stats.totalNonPhiInstructions++;
      }

      stats.totalBlocks++;

    }

  }

  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> exitEdges;
  L->getExitEdges(exitEdges);
  
  stats.exitEdges = exitEdges.size();

}

void PeelHeuristicsLoopRun::getAllChildren(std::vector<PeelHeuristicsLoopRun*>& children, bool topLevel) {

  for(LoopInfo::iterator LIt = L->begin(), LE = L->end(); LIt != LE; LIt++) {
    
    Loop* thisLoop = *LIt;
    PeelHeuristicsLoopRun& thisRun = childLoops[thisLoop];
    thisRun.getAllChildren(children, false);

  }

  if(!topLevel)
    children.push_back(this);

}

bool PeelHeuristicsLoopRun::doSimulatedPeel(DenseMap<Value*, Constant*>& outerConsts, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& outerIgnoreEdges, PeelHeuristicsLoopRun* parentRun, TargetData* TD, AliasAnalysis* AA) {
  
  // Deep copies to avoid work on this loop affecting our parent loops.
  this->TD = TD;
  DenseMap<Value*, Constant*> constInstructions = outerConsts;
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> ignoreEdges = outerIgnoreEdges;
  statsBefore = stats;

  this->parentRun = parentRun;

  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();
  BasicBlock* loopLatch = L->getLoopLatch();

  if(loopHeader)
    loopHeaderName = loopHeader->getNameStr();
  else
    loopHeaderName = "Unknown";

  if((!loopHeader) || (!loopPreheader) || (!loopLatch)) {
    LPDEBUG("Can't evaluate loop " << *L << " because it doesn't have a header, preheader or latch" << "\n");
    return false;
  }

  LPDEBUG("Peeling loop with header '" << loopHeader->getName() << "'\n");

  ignoreEdges.insert(std::make_pair(loopLatch, loopHeader));

  // Is it worth doing constant prop here at all? We say it is if any PHI nodes are rendered constant by peeling
  // which would not have been if it weren't for our parent. That is, peeling is especially effective if conducted
  // in concert with our parent loop. If this loop would yield a constant regardless, we will find that out later
  // as the pass considers all loops as a root at top level.

  if(parentRun) {
    
    bool anyPhiImproved = false;

    for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

      PHINode* PI = cast<PHINode>(I);
      Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
      if(!preheaderVal)
	continue;
      Constant* preheaderConst = dyn_cast<Constant>(preheaderVal);
      if(preheaderConst)
	continue;
      Instruction* preheaderInst = cast<Instruction>(preheaderVal);
      DenseMap<Value*, Constant*>::iterator outerConst = constInstructions.find(preheaderInst);
      if(outerConst != constInstructions.end()) {
	anyPhiImproved = true;
	break;
      }

    }

    if(!anyPhiImproved) {

      LPDEBUG("Not peeling loop with header " << L->getHeader()->getName() << " because none of its PHI nodes are improved by concurrent unrolling of its parents\n");
      doConstProp = false;

    }

  }

  // Proceed to push the frontier of instructions with all-constant operands!

  if(doConstProp) {

    stats.allPhisConstantFromPreheader = true;
    SmallVector<std::pair<Value*, Constant*>, 4> rootInstructions;

    SmallSet<Instruction*, 4> headerLatchInputs;

    for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

      PHINode* PI = cast<PHINode>(I);
      stats.headerPhis++;
      Value* latchValue = PI->getIncomingValueForBlock(loopLatch);
      if(Instruction* latchInstruction = dyn_cast<Instruction>(latchValue))
	headerLatchInputs.insert(latchInstruction);
      else
	stats.headerPhisDefined++; // This PHI is already defined! It's an almost-invariant (different on the first run, i.e. 'bool firsttime')
      Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
      if(!preheaderVal) {
	stats.allPhisConstantFromPreheader = false;
	LPDEBUG("Top level: " << *PI << ": no value on preheader incoming edge??\n");
	continue;
      }

      Constant* preheaderConst = dyn_cast<Constant>(preheaderVal);
      if(!preheaderConst) {
	Instruction* I = cast<Instruction>(preheaderVal);
	DenseMap<Value*, Constant*>::iterator outerConst = constInstructions.find(I);
	if(outerConst != constInstructions.end())
	  preheaderConst = outerConst->second;
      }

      if(preheaderConst) {
	LPDEBUG("Top level setting constant PHI node\n");
	rootInstructions.push_back(std::make_pair(PI, preheaderConst));
      }
      else {
	stats.allPhisConstantFromPreheader = false;
	LPDEBUG("Top level: " << *PI << " not constant on edge from preheader\n");
      }

    }

    Function* F = loopHeader->getParent();
    SmallSet<BasicBlock*, 4> outerBlocks;
    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; FI++) {
      if(!L->contains(FI))
	outerBlocks.insert(FI);
    }

    SmallVector<Instruction*, 16> eliminatedInstructions;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> eliminatedEdges;

    HypotheticalConstantFolder H(F, constInstructions, ignoreEdges, outerBlocks, eliminatedInstructions, eliminatedEdges, AA, TD);
    H.setDebugIndent(debugIndent);
    H.getBenefit(rootInstructions);

    for(SmallVector<Instruction*, 16>::iterator II = eliminatedInstructions.begin(), IE = eliminatedInstructions.end(); II != IE; II++) {

      Instruction* I = *II;
      accountElimInstruction(I);
      if(headerLatchInputs.count(I))
	stats.headerPhisDefined++;

    }

    SmallVector<BasicBlock*, 4> blocksKilled;

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = eliminatedEdges.begin(), EE = eliminatedEdges.end(); EI != EE; EI++) {

      if(HypotheticalConstantFolder::blockIsDead(EI->second, ignoreEdges))
	blocksKilled.push_back(EI->second);

      if(!L->contains(EI->second)) {
	Loop* outsideLimit = LI->getLoopFor(EI->second);
	PeelHeuristicsLoopRun* thisRun = this;
	while(thisRun && thisRun->L != outsideLimit) {
	  thisRun->stats.exitEdgesEliminated++;
	  thisRun = thisRun->parentRun;
	}
      }

      if((*EI) == std::make_pair(loopLatch, loopHeader)) {

	stats.latchBranchEliminated = true;

      }

    }

    std::sort(blocksKilled.begin(), blocksKilled.end());
    std::unique(blocksKilled.begin(), blocksKilled.end());
    for(SmallVector<BasicBlock*, 4>::iterator BI = blocksKilled.begin(), BE = blocksKilled.end(); BI != BE; BI++) {
      doForAllLoops(&incBlocksElim, (*BI)->begin());
    }

  }

  // Try concurrently peeling child loops

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator CI = childLoops.begin(), CE = childLoops.end(); CI != CE; CI++) {

    LPDEBUG("======>\n");
    CI->second.doSimulatedPeel(constInstructions, ignoreEdges, this, TD, AA);
    LPDEBUG("<======\n");

  }

  return false;

}

void PeelHeuristicsLoopRun::setDebugIndent(int x) {

  debugIndent = x;
  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator CI = childLoops.begin(), CE = childLoops.end(); CI != CE; CI++) {

    CI->second.setDebugIndent(x+2);

  }

}

void PeelHeuristicsLoopRun::print(raw_ostream &OS, int indent) const {

  if(doConstProp) {
    OS << ind(indent) << "Peeling loop " << loopHeaderName << ":\n";
    OS << ind(indent+2) << "Killed " << statsBefore.blocksKilled << "->" << stats.blocksKilled << "/" << stats.totalBlocks << " blocks\n";
    OS << ind(indent+2) << "Eliminated " << statsBefore.nonPhiInstructionsEliminated << "->" << stats.nonPhiInstructionsEliminated << "/" << stats.totalNonPhiInstructions << " non-PHI instructions\n";
    if(!stats.allPhisConstantFromPreheader)
      OS << ind(indent+2) << "Not all header PHIs were constant\n";
    OS << ind(indent+2) << "Defined " << statsBefore.headerPhisDefined << "->" << stats.headerPhisDefined << "/" << stats.headerPhis << " next-iteration PHIs\n";
    OS << ind(indent+2) << "Eliminated " << statsBefore.exitEdgesEliminated << "->" << stats.exitEdgesEliminated << "/" << stats.exitEdges << " exit edges\n";
    if(stats.latchBranchEliminated)
      OS << ind(indent+2) << "Latch branch eliminated!\n";
    indent += 4;
  }

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::const_iterator LI = childLoops.begin(), LE = childLoops.end(); LI != LE; LI++)
    LI->second.print(OS, indent);

}

bool LoopPeelHeuristicsPass::runOnFunction(Function& F) {

  LoopInfo& LI = getAnalysis<LoopInfo>();
  TargetData* TD = getAnalysisIfAvailable<TargetData>();

  // No initial constants at top level
  DenseMap<Value*, Constant*> initialConsts;

  // Ignore no edges at top level
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> initialIgnoreEdges;

  // Count blocks and instructions in all loops
  for(LoopInfo::iterator L = LI.begin(), LE = LI.end(); L != LE; L++) {

    Loop* thisLoop = *L;
    topLevelLoops[thisLoop].doInitialStats(thisLoop, &LI);

  }

  // Copy all children so that we can consider unrolling child loops in isolation or in combination with their parent
  for(LoopInfo::iterator L = LI.begin(), LE = LI.end(); L != LE; L++) {

    std::vector<PeelHeuristicsLoopRun*> childRuns;
    Loop* thisLoop = *L;
    topLevelLoops[thisLoop].getAllChildren(childRuns, true);
    for(std::vector<PeelHeuristicsLoopRun*>::iterator CI = childRuns.begin(), CE = childRuns.end(); CI != CE; CI++)
      topLevelLoops[(*CI)->L] = **CI;

  }

  AliasAnalysis* AA = &getAnalysis<AliasAnalysis>();

  // Now finally simulate peeling on each top-level target. The targets will recursively peel their child loops if it seems warranted.
  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator RI = topLevelLoops.begin(), RE = topLevelLoops.end(); RI != RE; RI++) {
   
    RI->second.setDebugIndent(0);
    RI->second.doSimulatedPeel(initialConsts, initialIgnoreEdges, 0, TD, AA);

  }

  return false;

}

#define MAX_NESTING 20

void InlineAttempt::considerSubAttempt(CallInst* CI, Function* FCalled, bool force) {

  InlineAttempt* IA = 0;
  SmallVector<std::pair<Value*, Constant*>, 4> rootValues;

  DenseMap<CallInst*, InlineAttempt*>::iterator it = subAttempts.find(CI);
  if(it == subAttempts.end()) {

    // This call hasn't been explored before. Consider it if we've anything to offer above what the function gave before we did any local folding:

    bool improved = false;

    for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
      Argument* A = AI;
      Value* AVal = CI->getArgOperand(A->getArgNo());
      Constant* C = dyn_cast<Constant>(AVal);
      if(!C) {
	DenseMap<Value*, Constant*>::const_iterator it = initialConsts.find(AVal);
	if(it != initialConsts.end()) {
	  improved = true;
	  C = it->second;
	}
      }
      if(C)
	rootValues.push_back(std::make_pair(A, C));
    }

    // If we can do better inlining CI in our context of nested inlining, as compared to considering CI a root itself
    // Or, if this is the root context currently considered, which sets force = true the first time around.
    if(improved || (rootValues.size() > 0 && force)) {

      IA = new InlineAttempt(this->TD, this->AA, *FCalled, this->nested_calls + 1, this->debugIndent + 2);
      subAttempts[CI] = IA;

    }

  }
  else {

    // This call has been explored before -- give it any constant arguments it hasn't seen before.

    IA = it->second;
    bool improved = false;

    for(Function::arg_iterator AI = FCalled->arg_begin(), AE = FCalled->arg_end(); AI != AE; AI++) {
      Argument* A = AI;
      if(!IA->argsAlreadyKnown[A->getArgNo()]) {
	Value* AVal = CI->getArgOperand(A->getArgNo());
	DenseMap<Value*, Constant*>::const_iterator it = initialConsts.find(AVal);
	if(it != initialConsts.end()) {
	  improved = true;
	  rootValues.push_back(std::make_pair(A, it->second));
	}
      }
    }
    
    if(!improved) {
      IA = 0; // Don't do anything.
    }

  }

  if(IA) {

    LPDEBUG("Considering improving call " << *CI << "\n");

    for(SmallVector<std::pair<Value*, Constant*>, 4>::iterator VI = rootValues.begin(), VE = rootValues.end(); VI != VE; VI++) {
      LPDEBUG("  " << *(VI->first) << " -> " << *(VI->second) << "\n");
      Argument* A = cast<Argument>(VI->first);      
      IA->argsAlreadyKnown[A->getArgNo()] = true;
    }

    IA->foldArguments(rootValues);

    if(!IA->returnValueAlreadyKnown) {
      if(IA->returnVal) {
	IA->returnValueAlreadyKnown = true;
	SmallVector<std::pair<Value*, Constant*>, 4> newLocalRoots;
	newLocalRoots.push_back(std::make_pair(CI, IA->returnVal));
	LPDEBUG("Integrating call's return value locally\n");
	localFoldConstants(newLocalRoots);
      }
    }
  }
  else {
    LPDEBUG("Couldn't improve " << *CI << "\n");
  }

}

void InlineAttempt::considerCallInst(CallInst* CI, bool force) {

  if(Function* FCalled = CI->getCalledFunction()) {

    if((!FCalled->isDeclaration()) && (!FCalled->isVarArg())) {
      considerSubAttempt(CI, FCalled, force);
    }
    else {
      LPDEBUG("Ignored " << *CI << " because we don't know the function body, or it's vararg\n");
    }
  }
  else {
    LPDEBUG("Ignored " << *CI << " because it's an uncertain indirect call\n");
  }

}

void InlineAttempt::considerCalls(bool force = false) {

  LPDEBUG("Considering if any calls are improved\n");

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {

    if(HypotheticalConstantFolder::blockIsDead(FI, initialIgnoreEdges))
      continue;

    BasicBlock& BB = *FI;
    
    for(BasicBlock::iterator BI = BB.begin(), BE = BB.end(); BI != BE; BI++) {

      if(CallInst* CI = dyn_cast<CallInst>(BI)) {
	considerCallInst(CI, force);
      }

    }

  }

}

void InlineAttempt::localFoldConstants(SmallVector<std::pair<Value*, Constant*>, 4>& args) {

  H.getBenefit(args);

  considerCalls();

  // Let's have a go at supplying a return value to our caller. Simple measure: we know the value if all the 'ret' instructions except one are dead,
  // and we know that instruction's operand.

  if((!returnVal) && (!F.getReturnType()->isVoidTy())) {
    bool foundReturnInst = false;
    for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {
      if(HypotheticalConstantFolder::blockIsDead(FI, initialIgnoreEdges))
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
	  Constant* C = dyn_cast<Constant>(RI->getReturnValue());
	  if(!C) {
	    DenseMap<Value*, Constant*>::iterator CI;
	    if((CI = initialConsts.find(RI->getReturnValue())) != initialConsts.end())
	      C = CI->second;
	  }
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
    }
  }

}

void InlineAttempt::foldArguments(SmallVector<std::pair<Value*, Constant*>, 4>& args) {

  localFoldConstants(args);

}

void InlineAttempt::countResidualCalls() {

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

void InlineAttempt::print(raw_ostream& OS) const {

  OS << dbgind() << F.getName() << ": eliminated " << eliminatedInstructions.size() << "/" << totalInstructions << " instructions, " << residualCalls << " residual uninlined calls\n";

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator CII = subAttempts.begin(), CIE = subAttempts.end(); CII != CIE; CII++) {
    CII->second->print(OS);
  }

}

std::string InlineAttempt::dbgind() const {

  return ind(debugIndent);

}

bool InlineHeuristicsPass::runOnModule(Module& M) {

  TD = getAnalysisIfAvailable<TargetData>();
  AA = &getAnalysis<AliasAnalysis>();

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    Function& F = *MI;

    DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");
    rootAttempts.push_back(new InlineAttempt(TD, AA, F, 0, 2));
    rootAttempts.back()->considerCalls(true);
    rootAttempts.back()->countResidualCalls();

  }

  return false;

}
