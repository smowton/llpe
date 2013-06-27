// A pass that takes a target in terms of a callstack and some assumptions and emits a single function
// that has a path that leads inexorably to the target, plus another that is unmodified.
// Branches that would circumvent the target at any level lead to the unmodified path;
// assumptions also result in guards that govern branches to the unmodified code.

#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/Argument.h"
#include "llvm/Constants.h"
#include "llvm/Pass.h"
#include "llvm/DataLayout.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <vector>
#include <sstream>
#include <algorithm>

#include <stdlib.h>

using namespace llvm;

namespace {

  struct CloneForSpecPass : public ModulePass {

    std::vector<CallInst*> targetStack;

    DenseMap<std::pair<uint32_t, Value*>, Constant*> intAssumptions;
    DenseMap<std::pair<uint32_t, Value*>, Constant*> stringAssumptions;
    DenseMap<Value*, Constant*> intAssumptionsFlat;
    DenseMap<Value*, Constant*> stringAssumptionsFlat;

    SmallPtrSet<BasicBlock*, 8> mayReachTarget;
    SmallPtrSet<BasicBlock*, 8> mayFollowTarget;
    SmallPtrSet<BasicBlock*, 8> willNotReachTarget;

    CallInst* TargetCI;

    DataLayout* DL;
    
    void parseArgs(Module&);

    static char ID; // Pass identification
    CloneForSpecPass() : ModulePass(ID) {
      DL = &getAnalysis<DataLayout>();      
    }

    bool runOnModule(Module&);

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      AU.addRequired<DataLayout>();
    }

    bool blockHasAssumptions(BasicBlock*);
    Function* inlineStack(CallInst*&);
    void splitBlockForAssumptions(BasicBlock*, std::vector<BasicBlock*>);
    void splitBlocksForAssumptions(Function*);
    void insertMergePHIs(BasicBlock*, DominatorTree&);
    void insertMergePHIs(Function*);
    void insertAssumptionTests(Function* NewF, ValueToValueMapTy& cloneMap);
    void redirectBranchesToMayFollow(Function* F, ValueToValueMapTy& cloneMap);
    void rewriteAssumptions(uint32_t stackIdx, ValueToValueMapTy& Map);

  };

  char CloneForSpecPass::ID = 0;

} // end anonymous namespace

static cl::list<std::string> TargetStack("clone-target-stack", cl::OneOrMore);
static cl::list<std::string> IntAssumptions("clone-assume-int", cl::ZeroOrMore);
static cl::list<std::string> StringAssumptions("clone-assume-string", cl::ZeroOrMore);

static RegisterPass<CloneForSpecPass> X("clone-for-spec", "Directed cloning in preparation for guarded specialisation", false, false);

ModulePass* llvm::createCloneForSpecPass() {
  return new CloneForSpecPass();
}

static void dieMessage(const char* msg) {

  errs() << "Fatal: " << msg << "\n";
  exit(1);
  
}

class matchesName {

  std::string& name;

public:
  matchesName(std::string& n) : name(n) {}
  bool operator()(BasicBlock& BB) {

    return BB.getName() == name;

  }

};

static void addBlockAndSuccs(BasicBlock* BB, SmallPtrSet<BasicBlock*, 8>& Set, bool skipFirst) {

  if(!skipFirst) {
    if(!Set.insert(BB))
      return;
  }

  for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI)
    addBlockAndSuccs(*SI, Set, false);

}

static void addBlockAndPreds(BasicBlock* BB, SmallPtrSet<BasicBlock*, 8>& Set) {

  if(!Set.insert(BB))
    return;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI)
    addBlockAndPreds(*PI, Set);

}

bool CloneForSpecPass::blockHasAssumptions(BasicBlock* BB) {

  for(BasicBlock::iterator it = BB->begin(), itend = BB->end(); it != itend; ++it) {

    if(intAssumptionsFlat.count(it) || stringAssumptionsFlat.count(it))
      return true;

  }

  return false;

}

struct WNRFinder {

  SmallPtrSet<BasicBlock*, 8> seenMRBlocks;
  CloneForSpecPass* parent;

  WNRFinder(CloneForSpecPass* p) : parent(p) { }
  void findWillNotReachBlocks(BasicBlock* BB, bool BBMayReach);

};
  
void WNRFinder::findWillNotReachBlocks(BasicBlock* BB, bool BBMayReach) {

  if(BBMayReach) {
    
    if(!seenMRBlocks.insert(BB))
      return;

  }
  else {

    if(!parent->willNotReachTarget.insert(BB))
      return;

  }

  if(BBMayReach && BB == parent->TargetCI->getParent())
    return;

  // We'll need will-not-reach versions of successor blocks if an assumption test will exist here.
  bool forceWNRSuccs = BBMayReach && parent->blockHasAssumptions(BB);

  for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
    
    BasicBlock* SBB = *SI;

    if(BBMayReach && parent->mayReachTarget.count(SBB)) {
      findWillNotReachBlocks(SBB, true);
      if(forceWNRSuccs)
	findWillNotReachBlocks(SBB, false);
    }
    else {
      findWillNotReachBlocks(SBB, false);
    }

  }

}

static void rewriteAssumptionMap(uint32_t stackIdx, DenseMap<std::pair<uint32_t, Value*>, Constant*>& rewrite, DenseMap<Value*, Constant*>& flat, ValueToValueMapTy& Map) {

  for(DenseMap<std::pair<uint32_t, Value*>, Constant*>::iterator it = rewrite.begin(), itend = rewrite.end(); it != itend; ++it) {

    if(it->first.first == stackIdx) {

      Value* newVal = Map[it->first.second];
      flat[newVal] = it->second;

    }

  }

}

void CloneForSpecPass::rewriteAssumptions(uint32_t stackIdx, ValueToValueMapTy& Map) {

  rewriteAssumptionMap(stackIdx, intAssumptions, intAssumptionsFlat, Map);
  rewriteAssumptionMap(stackIdx, stringAssumptions, stringAssumptionsFlat, Map);

}

Function* CloneForSpecPass::inlineStack(CallInst*& TargetCI) {

  ValueToValueMapTy CloneVals;

  // Plain old clone the bottommost call.
  Function* OrigRoot = targetStack[0]->getCalledFunction();
  Function* NewF = CloneFunction(OrigRoot, CloneVals, false);
  NewF->setName(OrigRoot->getName() + ".spec_clone");
  OrigRoot->getParent()->getFunctionList().push_back(NewF);

  // Rewrite assumptions about values and arguments in that function.
  rewriteAssumptions(1, CloneVals);

  // For each successive call except the last one, inline and repeat the procedure.

  for(uint32_t i = 1; i < targetStack.size() - 1; ++i) {

    CallInst* inlineCI = cast<CallInst>(CloneVals[targetStack[i]]);
    CloneVals.clear();

    inlineCI->getParent()->splitBasicBlock(BasicBlock::iterator(inlineCI), "argbb");

    // Replace constant arguments with single-arg PHIs that can be used as insertion points
    // for assumption checks rooted on arguments.
    Function* NextF = inlineCI->getCalledFunction();

    Function::arg_iterator argit = NextF->arg_begin();
    for(uint32_t j = 0; j < inlineCI->getNumArgOperands(); ++j, ++argit) {

      std::pair<uint32_t, Value*> key(i + 1, argit);
      DenseMap<std::pair<uint32_t, Value*>, Constant*>::iterator intit = intAssumptions.find(key);
      DenseMap<std::pair<uint32_t, Value*>, Constant*>::iterator stringit = stringAssumptions.find(key);

      if(intit == intAssumptions.end() && stringit == stringAssumptions.end())
	continue;

      // Rewrite the assumptions to be in terms of the new instruction instead of an argument.

      Value* V = inlineCI->getArgOperand(j);
      if(isa<Constant>(V)) {

	PHINode* newNode = PHINode::Create(V->getType(), 1, "argtemp", inlineCI);
	if(intit != intAssumptions.end()) {
	  Constant* C = intit->second;
	  intAssumptionsFlat[newNode] = C;
	}
	else {
	  Constant* C = stringit->second;
	  stringAssumptionsFlat[newNode] = C;
	}

      }

    }

    InlineFunctionInfo IFI(0, DL);
    if(!InlineFunction(inlineCI, IFI, true, &CloneVals))
      dieMessage("Inlining failed");
    rewriteAssumptions(i + 1, CloneVals);

  }

  TargetCI = cast<CallInst>(CloneVals[targetStack.back()]);
  return NewF;

}

void CloneForSpecPass::splitBlockForAssumptions(BasicBlock* BB, std::vector<BasicBlock*> newBlocks) { 

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
    
    if(intAssumptionsFlat.count(BI) || stringAssumptionsFlat.count(BI)) {
      BasicBlock* newBlock = BB->splitBasicBlock(BI, BB->getName() + ".assumption_split");
      newBlocks.push_back(newBlock);
      splitBlockForAssumptions(newBlock, newBlocks);
      return;
    }

  }  

}

void CloneForSpecPass::splitBlocksForAssumptions(Function* F) {

  std::vector<BasicBlock*> newBlocks;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI)
    splitBlockForAssumptions(FI, newBlocks);

  for(std::vector<BasicBlock*>::iterator it = newBlocks.begin(), itend = newBlocks.end(); it != itend; ++it)
    F->getBasicBlockList().push_back(*it);

}

void CloneForSpecPass::insertMergePHIs(BasicBlock* BB, DominatorTree& DT) {

  // This block will be a merge point: insert explicit PHI forwarding wherever we or a block we dominate
  // will use a value that we do not contain/dominate.
  // We (and blocks we dominate) can use any value in our dominator blocks.

  DomTreeNode* Node = DT.getNode(BB);
  Node = Node->getIDom();
  uint32_t BBPreds = std::distance(pred_begin(BB), pred_end(BB));

  for(; Node; Node = Node->getIDom()) {

    BasicBlock* ThisBB = Node->getBlock();

    // If there will only be one version of this block then we can use its values as usual as they will
    // continue to dominate even duplicated users.
    if(!(mayReachTarget.count(ThisBB) && willNotReachTarget.count(ThisBB)))
      break;

    for(BasicBlock::iterator BI = ThisBB->begin(), BE = BB->end(); BI != BE; ++BI) {
      
      SmallVector<Use*, 8> replaceUses;

      for(Instruction::use_iterator UI = BI->use_begin(), UE = BI->use_end(); UI != UE; ++UI) {

	Instruction* UseInst = cast<Instruction>(*UI);
	BasicBlock* UseBB = UseInst->getParent();
	if(DT.dominates(BB, UseBB)) {
	  if(!(UseBB == BB && isa<PHINode>(UseInst)))
	    replaceUses.push_back(&UI.getUse());
	}
	
      }
      
      if(replaceUses.size()) {
	
	PHINode* NewNode = PHINode::Create(BI->getType(), BBPreds, "clonemerge", BB->begin());
	for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI)
	  NewNode->addIncoming(BI, *PI);

	for(SmallVector<Use*, 8>::iterator it = replaceUses.begin(), 
	      itend = replaceUses.end(); it != itend; ++it)
	  (*it)->set(NewNode);
			     
      }

    }

  }

}

void CloneForSpecPass::insertMergePHIs(Function* F) {

  DominatorTree& DT = getAnalysis<DominatorTree>(*F);

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    BasicBlock* BB = FI;

    if(blockHasAssumptions(BB) && willNotReachTarget.count(BB)) {

      if(std::distance(succ_begin(BB), succ_end(BB)) != 1)
	dieMessage("BB with assumptions ends in conditional branch?");
      insertMergePHIs(*succ_begin(BB), DT);

    }
    else {

      if(!mayReachTarget.count(BB)) {

	for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {

	  BasicBlock* PredBB = *PI;

	  if(mayReachTarget.count(PredBB) && willNotReachTarget.count(PredBB)) {
	    insertMergePHIs(BB, DT);
	    break;
	  }

	}

      }
      
    }

  }

}

struct Cloner {

  ValueToValueMapTy& cloneMap;
  CloneForSpecPass* parent;

  Cloner(ValueToValueMapTy& cm, CloneForSpecPass* p) : cloneMap(cm), parent(p) {}

  void cloneBBs(Function*);
  void remapBBs();

};

void Cloner::cloneBBs(Function* F) {

  std::vector<BasicBlock*> newBlocks;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {
    
    if((parent->mayReachTarget.count(FI) || parent->mayFollowTarget.count(FI)) 
       && !parent->willNotReachTarget.count(FI)) {

      BasicBlock* NewBB = CloneBasicBlock(FI, cloneMap, ".spec_clone");
      newBlocks.push_back(NewBB);
      cloneMap[FI] = NewBB;

    }

  }

  for(std::vector<BasicBlock*>::iterator it = newBlocks.begin(), itend = newBlocks.end(); it != itend; ++it)
    F->getBasicBlockList().push_back(*it);

}

void Cloner::remapBBs() {

  // Straightforward remapping: wherever a block has a clone we will refer to that;
  // where it doesn't we'll refer to the one and only version which might be in the off-target
  // or on-target paths.

  for(ValueToValueMapTy::iterator it = cloneMap.begin(), itend = cloneMap.end(); it != itend; ++it) {

    BasicBlock* BB = const_cast<BasicBlock*>(dyn_cast<BasicBlock>(it->first));
    if(!BB)
      continue;

    BasicBlock* CloneBB = cast<BasicBlock>(it->second);

    bool isMergeBlock = false;
    BasicBlock* UniquePred = BB->getUniquePredecessor();
    if(UniquePred && parent->blockHasAssumptions(UniquePred))
      isMergeBlock = true;
    else if(parent->willNotReachTarget.count(BB) && !parent->mayReachTarget.count(BB))
      isMergeBlock = true;

    for(BasicBlock::iterator BI = CloneBB->begin(), BE = CloneBB->end(); BI != BE; ++BI) {

      PHINode* PN = dyn_cast<PHINode>(BI);
      if(isMergeBlock && PN) {

	// Where there are now two versions of the incoming value use both; where there
	// aren't use the remapped version (might be a no-op).
	
	SmallVector<std::pair<Value*, BasicBlock*>, 4> newPreds;
	for(uint32_t i = 0, ilim = PN->getNumIncomingValues(); i != ilim; ++i) {

	  BasicBlock* existingPred = PN->getIncomingBlock(i);
	  if(parent->mayReachTarget.count(existingPred)) {

	    if(parent->willNotReachTarget.count(existingPred)) {

	      // Add both possibilities to the PHI. If the value turned out not to need
	      // cloning then this simply specifies the same value for each branch
	      // which will be simplified away in due time.
	      Value* NewV = MapValue(PN->getIncomingValue(i), cloneMap, RF_None, 0);
	      BasicBlock* NewBB = cast<BasicBlock>(MapValue(existingPred, cloneMap, RF_None, 0));
	      newPreds.push_back(std::make_pair(NewV, NewBB));

	    }
	    else {

	      // Leave unmodified: use the incoming value as-is.

	    }

	  }
	  else {

	    // Ordinary remap: we use the cloned values if they exist or the normal ones otherwise.
	    PN->setIncomingValue(i, MapValue(PN->getIncomingValue(i), cloneMap, RF_None, 0));

	  }

	}

	for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator it = newPreds.begin(),
	      itend = newPreds.end(); it != itend; ++it) {
	  
	  PN->addIncoming(it->first, it->second);

	}

      }
      else {

	RemapInstruction(BI, cloneMap, RF_IgnoreMissingEntries);

      }

    }

  }

}

void CloneForSpecPass::insertAssumptionTests(Function* NewF, ValueToValueMapTy& cloneMap) {

  for(Function::iterator FI = NewF->begin(), FE = NewF->end(); FI != FE; ++FI) {

    BasicBlock* BB = FI;
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

      Instruction* I = BI;
      Instruction* TestInst = 0;
      DenseMap<Value*, Constant*>::iterator intfindit = intAssumptionsFlat.find(I);
      BasicBlock::iterator insertit = BI;
      ++insertit;

      if(intfindit != intAssumptionsFlat.end()) {

	Value* testVal = intfindit->first;

	if(testVal->getType() != intfindit->second->getType()) {
	  
	  if(!testVal->getType()->isIntegerTy())
	    dieMessage("Integer assumption against non-integer?");

	  testVal = new SExtInst(testVal, intfindit->second->getType(), "assume_ext", insertit);

	}

	TestInst = new ICmpInst(insertit, CmpInst::ICMP_EQ, intfindit->second, testVal, "assume_test");

      }
      else {

	DenseMap<Value*, Constant*>::iterator stringfindit = stringAssumptionsFlat.find(I);
	if(stringfindit != stringAssumptionsFlat.end()) {

	  Type* IntTy = Type::getInt32Ty(NewF->getContext());
	  Type* CharPtr = Type::getInt8PtrTy(NewF->getContext());
	  Type* StrcmpArgTys[2] = { CharPtr, CharPtr };
	  FunctionType* StrcmpType = FunctionType::get(IntTy, ArrayRef<Type*>(StrcmpArgTys, 2), false);

	  Constant* StrcmpFun = NewF->getParent()->getOrInsertFunction("strcmp", StrcmpType);
	  
	  Value* TestArg = I;
	  if(TestArg->getType() != CharPtr) {
	    
	    new BitCastInst(TestArg, CharPtr, "assume_cast", insertit);
	    
	  }
	 
	  Value* StrcmpArgs[2] = { stringfindit->second, TestArg };
	  CallInst* CmpCall = CallInst::Create(StrcmpFun, ArrayRef<Value*>(StrcmpArgs, 2), "assume_test", insertit);
	  TestInst = new ICmpInst(insertit, CmpInst::ICMP_EQ, CmpCall, Constant::getNullValue(CmpCall->getType()), "assume_cmp");

	}

      }

      if(TestInst) {

	// If TestInst is true, branch to existing destination; otherwise go to the destination's
	// clone, which must exist since it's the (unique) successor to an assumption block.
	if(std::distance(succ_begin(BB), succ_end(BB)) != 1)
	  dieMessage("No unique successor for an assumption block?");

	BasicBlock* CurrentSucc = *succ_begin(BB);
	Value* Cl = cloneMap[CurrentSucc];
	if(!Cl)
	  dieMessage("Assumption block not cloned?");

	TerminatorInst* existingTerm = BB->getTerminator();
	existingTerm->eraseFromParent();
	BranchInst::Create(CurrentSucc, cast<BasicBlock>(Cl), TestInst, BB);

	// Skip rest of the BB; earlier splitting means one assumption per BB.
	continue;

      }

    }

  }

}

void CloneForSpecPass::redirectBranchesToMayFollow(Function* F, ValueToValueMapTy& cloneMap) {

  // When a mayReachTarget, non-target block branches to a mayFollowBlock,
  // or a doesNotReachTarget block without a mayReachTarget companion does similar,
  // those branch targets should be updated to the block's clone partner.

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    BasicBlock* BB = FI;
    if(BB == TargetCI->getParent())
      continue;

    if(mayReachTarget.count(BB) || (willNotReachTarget.count(BB) && !mayReachTarget.count(BB))) {

      TerminatorInst* TI = BB->getTerminator();
      for(uint32_t i = 0, ilim = TI->getNumSuccessors(); i != ilim; ++i) {

	SmallPtrSet<BasicBlock*, 4> alreadyRemoved;

	BasicBlock* CurrentSucc = TI->getSuccessor(i);
	if(mayFollowTarget.count(CurrentSucc)) {
	  
	  ValueToValueMapTy::iterator findit = cloneMap.find(CurrentSucc);
	  if(findit == cloneMap.end())
	    dieMessage("Uncloned mayfollow block reachable from mayReach / doesNotReach");

	  BasicBlock* SuccClone = cast<BasicBlock>(cloneMap[CurrentSucc]);

	  if(alreadyRemoved.insert(CurrentSucc))
	    CurrentSucc->removePredecessor(BB, true);
	  TI->setSuccessor(i, SuccClone);

	}

      }

    }

  }

}

bool CloneForSpecPass::runOnModule(Module& M) {

  parseArgs(M);

  // TargetStack is now a series of call instructions. The bottommost should be redirected to call a large inlined function
  // such that all paths that call the topmost function /and/ meet the given assumptions use one version of blocks that
  // come after the topmost ("the target function") whilst other paths use a different version.
  // The two clones converge when returning at the bottommost callsite.

  if(TargetStack.size() < 2)
    dieMessage("Must specify at least 2 clone-target-stack parameters");

  for(uint32_t i = 1, ilim = TargetStack.size(); i != ilim; ++i) {
    if(targetStack[i]->getParent()->getParent()->isVarArg())
      dieMessage("Varargs fuctions in the target stack not supported yet");
    if(!targetStack[i]->getCalledFunction())
      dieMessage("Indirect calls not supported yet");
  }

  // Step 1: inline each function in turn to yield a large function and the remapped target CI.
  Function* NewF = inlineStack(TargetCI);
  BasicBlock* TargetBB = TargetCI->getParent();

  // Step 2: split blocks wherever assumption tests, branches and consequent PHIs will be needed.
  splitBlocksForAssumptions(NewF);
  // All points where mayReach and willNotReach paths will converge are now block headers.

  // Step 3: Identify blocks in the new function that /may/ lead to the target call,
  // those which may follow from it, and those which can be reached from the function entry
  // whilst circumventing the target function.

  addBlockAndPreds(TargetBB, mayReachTarget);
  addBlockAndSuccs(TargetBB, mayFollowTarget, true);

  {
    WNRFinder F(this);
    F.findWillNotReachBlocks(&NewF->getEntryBlock(), true);
  }

  // Step 4: insert PHI nodes wherever a def->use link will cross what will become a merge point
  // between the reaching-target and not-reaching-target paths: namely, where assumption tests
  // will merge with a not-reaching block, and where may-reach blocks branch into not-reaching blocks.

  insertMergePHIs(NewF);

  // Step 5: make clones of blocks that are needed in both the reaching-target and not-reaching-target
  // paths. The remap phase special-cases PHI nodes so that mayReach/willNotReach mergepoints
  // mention both possible predecessors.
  
  ValueToValueMapTy cloneMap;
  {
    Cloner C(cloneMap, this);
    C.cloneBBs(NewF);
    C.remapBBs();
  }

  // Step 6: Insert tests and corresponding branches (for which PHIs are now set).

  insertAssumptionTests(NewF, cloneMap);

  // Step 7: redirect mayReach and willNotReach branches that lead to mayFollow blocks to the 
  // corresponding clone, including removing PHI nodes regarding the incoming edges.

  redirectBranchesToMayFollow(NewF, cloneMap);

  // And at long last, plumb the new function in at the particular callsite demanded.
  
  targetStack[0]->setCalledFunction(NewF);
  return true;
  
}

static bool stringtol(std::string& s, long int& result) {

  if(s.empty())
    return false;
  
  char* sEnd;
  result = strtol(s.c_str(), &sEnd, 10);
  
  return !sEnd[0];

}

static Value* getInstOrArg(Function* F, std::string& bbName, std::string& instIdxStr, const char* msg) {

  long int instIdx;
  if(!stringtol(instIdxStr, instIdx)) 
    dieMessage(msg);

  if(bbName == "__args__") {
    
    if(instIdx >= (long int)F->arg_size())
      dieMessage(msg);

    Function::arg_iterator ArgIt = F->arg_begin();
    for(long int i = 0; i < instIdx; ++i)
      ++ArgIt;

    return ArgIt;

  }
  else {

    Function::iterator findit = std::find_if(F->begin(), F->end(), matchesName(bbName));
    if(findit == F->end())
      dieMessage(msg);
    BasicBlock* BB = findit;
    
    BasicBlock::iterator BBIt = BB->begin();
    for(long int i = 0; i < instIdx && BBIt != BB->end(); ++i)
      ++BBIt;
  
    if(BBIt == BB->end())
      dieMessage(msg);

    return BBIt;

  }

}

void CloneForSpecPass::parseArgs(Module& M) {

  for(cl::list<std::string>::iterator it = TargetStack.begin(), 
	itend = TargetStack.end(); it != itend; ++it) {

    std::string& thisCall = *it;

    std::string fName, bbName, instIdxStr;

    std::istringstream istr(thisCall);
    std::getline(istr, fName, ',');
    std::getline(istr, bbName, ',');
    std::getline(istr, instIdxStr, ',');

    if(fName.empty() || bbName.empty() || instIdxStr.empty())
      dieMessage("clone-target-stack must have form functionName,blockName,index");

    Function* F = M.getFunction(fName);
    if(!F)
      dieMessage("Bad function in clone-target-stack");

    CallInst* I = 
      dyn_cast<CallInst>(getInstOrArg(F, bbName, instIdxStr, "clone-target-stack: bad parameter"));
    if(!I)
      dieMessage("clone-target-stack: must specify a call instruction");
    
    targetStack.push_back(I);
    
  }

  // Format of IntAssumptions and StringAssumptions:
  // n,block,idx,val
  // n: index of a function in the TargetStack (implied by the CallInst). Cannot correspond to last function.
  // block: Basic Block name, or __args__ to make an assumption about an argument value.
  // idx: Instruction index in block, or argument index.
  // val: integer or string that that instruction must resolve to.

  for(cl::list<std::string>::iterator it = IntAssumptions.begin(),
	itend = IntAssumptions.end(); it != itend; ++it) {

    std::string& thisParam = *it;

    std::string fIndexStr, bbName, instIdx, valStr;

    std::istringstream istr(thisParam);
    std::getline(istr, fIndexStr, ',');
    std::getline(istr, bbName, ',');
    std::getline(istr, instIdx, ',');
    std::getline(istr, valStr, ',');

    if(fIndexStr.empty() || bbName.empty() || instIdx.empty() || valStr.empty())
      dieMessage("clone-assume-int: must have form findex,bbname,instorargindex,val");

    long int fIndex;
    if((!stringtol(fIndexStr, fIndex)) || fIndex < 0)
      dieMessage("clone-assume-int: first component not a positive integer");

    if(fIndex >= (long int)targetStack.size())
      dieMessage("clone-assume-int: function index out of range");

    Value* V = getInstOrArg(targetStack[fIndex]->getCalledFunction(), bbName, instIdx,
			    "clone-assume-int: bad format");

    if(!V)
      dieMessage("clone-assume-int: failed to get inst or arg");

    long int val;
    if(!stringtol(valStr, val))
      dieMessage("clone-assume-int: failed to parse int");
    
    Type* targetType = V->getType();
    if(!targetType->isIntegerTy())
      dieMessage("clone-assume-int: must target an integer value");

    Constant* valInt = ConstantInt::getSigned(V->getType(), (int64_t)val);
    intAssumptions[std::make_pair((uint32_t)fIndex, V)] = valInt;
    
  }

  for(cl::list<std::string>::iterator it = StringAssumptions.begin(),
	itend = StringAssumptions.end(); it != itend; ++it) {

    std::string& thisParam = *it;

    std::string fIndexStr, bbName, instIdx, valStr;

    std::istringstream istr(thisParam);
    std::getline(istr, fIndexStr, ',');
    std::getline(istr, bbName, ',');
    std::getline(istr, instIdx, ',');
    std::getline(istr, valStr, ',');

    if(fIndexStr.empty() || bbName.empty() || instIdx.empty() || valStr.empty())
      dieMessage("clone-assume-string: must have form findex,bbname,instorargindex,val");

    long int fIndex;
    if((!stringtol(fIndexStr, fIndex)) || fIndex < 0)
      dieMessage("clone-assume-string: first component not a positive integer");

    if(fIndex >= (long int)targetStack.size())
      dieMessage("clone-assume-string: function index out of range");

    Value* V = getInstOrArg(targetStack[fIndex]->getParent()->getParent(), bbName, instIdx,
			    "clone-assume-string: bad format");

    if(!V)
      dieMessage("clone-assume-string: failed to get inst or arg");

    Constant* val = ConstantDataArray::getString(M.getContext(), valStr);
    stringAssumptions[std::make_pair((uint32_t)fIndex, V)] = val;

  }
  
}
