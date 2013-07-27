
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"

using namespace llvm;

// Functions relating to conditional specialisation
// (that is, situations where the specialiser assumes some condition, specialises according to it,
//  and at commit time must synthesise duplicate successor blocks: specialised, and unmodified).

void IntegrationAttempt::checkTargetStack(ShadowInstruction* SI, InlineAttempt* IA) {

  InlineAttempt* MyRoot = getFunctionRoot();
  if(MyRoot->targetCallInfo && 
     SI->parent->invar->idx == MyRoot->targetCallInfo->targetCallBlock &&
     SI->invar->idx == MyRoot->targetCallInfo->targetCallInst &&
     MyRoot->targetCallInfo->targetStackDepth < pass->targetCallStack.size()) {

    uint32_t newDepth = MyRoot->targetCallInfo->targetStackDepth + 1;
    IA->setTargetCall(pass->targetCallStack[newDepth], newDepth);

  }

}

void InlineAttempt::addBlockAndSuccs(uint32_t idx, DenseSet<uint32_t>& Set, bool skipFirst) {

  if(!skipFirst) {
    if(!Set.insert(idx).second)
      return;
  }

  ShadowBBInvar* BBI = getBBInvar(idx);
  for(uint32_t i = 0, ilim = BBI->succIdxs.size(); i != ilim; ++i)
    addBlockAndSuccs(BBI->succIdxs[i], Set, false);

}

void InlineAttempt::markBlockAndSuccsFailed(uint32_t idx, uint32_t instIdx) {

  SmallDenseMap<uint32_t, uint32_t>::iterator it = blocksReachableOnFailure.find(idx);
  if(it != blocksReachableOnFailure.end() && it->second <= instIdx)
    return;

  blocksReachableOnFailure[idx] = instIdx;

  ShadowBBInvar* BBI = getBBInvar(idx);
  for(uint32_t i = 0, ilim = BBI->succIdxs.size(); i != ilim; ++i)
    markBlockAndSuccsFailed(BBI->succIdxs[i], 0);  

}

void InlineAttempt::addBlockAndPreds(uint32_t idx, DenseSet<uint32_t>& Set) {

  if(!Set.insert(idx).second)
    return;

  ShadowBBInvar* BBI = getBBInvar(idx);
  for(uint32_t i = 0, ilim = BBI->predIdxs.size(); i != ilim; ++i)
    addBlockAndPreds(BBI->predIdxs[i], Set);

}

void InlineAttempt::setTargetCall(std::pair<BasicBlock*, uint32_t>& arg, uint32_t stackIdx) {

  uint32_t blockIdx = findBlock(invarInfo, arg.first->getName());
  targetCallInfo = new IATargetInfo(blockIdx, arg.second, stackIdx);

  addBlockAndPreds(blockIdx, targetCallInfo->mayReachTarget);
  addBlockAndSuccs(blockIdx, targetCallInfo->mayFollowTarget, true); 

}

bool IntegrationAttempt::shouldIgnoreEdge(ShadowBBInvar* CurrBB, ShadowBBInvar* SuccBB) {

  InlineAttempt* MyRoot = getFunctionRoot();
  IATargetInfo* TI = MyRoot->targetCallInfo;

  if(!TI)
    return false;

  // This is the target block -> not ignored
  if(CurrBB->idx == TI->targetCallBlock)
    return false;

  // This block is pre-target, successor is not -> ignored
  if(TI->mayReachTarget.count(CurrBB->idx) && 
     !TI->mayReachTarget.count(SuccBB->idx)) {

    return true;

  }

  return false;

}


bool PeelIteration::tryGetPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result) {

  return false;

}

bool InlineAttempt::tryGetPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result) {

  if(!targetCallInfo)
    return false;

  ShadowInstruction* SI = V.getInst();
  ShadowArg* SA = V.getArg();
  if((!SI) && (!SA))
    return false;

  for(std::vector<PathCondition>::iterator it = pass->rootIntPathConditions.begin(),
	itend = pass->rootIntPathConditions.end(); it != itend; ++it) {

    /* fromStackIdx must equal instStackIdx for this kind of condition */

    if(it->instStackIdx == targetCallInfo->targetStackDepth) {
      
      bool match = false;

      if(SI && 
	 it->instBB == SI->parent->invar->BB &&
	 it->instIdx == SI->invar->idx) {

	if(DT->dominates(it->fromBB, UserBlock->invar->BB))
	  match = true;

      }
      else if(SA &&
	      it->instBB == (BasicBlock*)ULONG_MAX &&
	      it->instIdx == SA->invar->A->getArgNo()) {

	match = true;

      }

      if(match) {

	// Make sure a failed version of the from-block and its successors is created:
	uint32_t fromBlockIdx = findBlock(UserBlock->IA->invarInfo, it->fromBB);
	markBlockAndSuccsFailed(fromBlockIdx, 0);

	Result.first = ValSetTypeScalar;
	Result.second.V = it->val;
	return true;
	
      }

    }

  }

  return false;

}

void PeelIteration::applyMemoryPathConditions(ShadowBB* BB) {
  
  return;

}

InlineAttempt* llvm::getIAWithTargetStackDepth(InlineAttempt* IA, uint32_t depth) {

  release_assert(IA->targetCallInfo);
  if(IA->targetCallInfo->targetStackDepth == depth)
    return IA;

  release_assert(depth < IA->targetCallInfo->targetStackDepth);
  IntegrationAttempt* par = IA->getUniqueParent();
  release_assert(par && "Can't share functions in the target stack!");
  return getIAWithTargetStackDepth(par->getFunctionRoot(), depth);

}

void InlineAttempt::applyPathCondition(PathCondition* it, PathConditionTypes condty, ShadowBB* BB) {

  if(it->fromStackIdx == targetCallInfo->targetStackDepth && it->fromBB == BB->invar->BB) {

    ImprovedValSetSingle writePtr;
    ShadowValue ptrSV;

    if(!it->instBB) {

      ShadowGV* GV = &(GlobalIHP->shadowGlobals[it->instIdx]);
      writePtr.set(ImprovedVal(ShadowValue(GV), 0), ValSetTypePB);

    }
    else if(it->instBB == (BasicBlock*)ULONG_MAX) {

      InlineAttempt* ptrIA = getIAWithTargetStackDepth(this, it->instStackIdx);
      ShadowArg* ptr = &ptrIA->argShadows[it->instIdx];
      ptrSV = ShadowValue(ptr);
      ImprovedValSetSingle* ptrIVS = dyn_cast<ImprovedValSetSingle>(ptr->i.PB);
      if(!ptrIVS)
	return;

      writePtr = *ptrIVS;

    }
    else {

      InlineAttempt* ptrIA = getIAWithTargetStackDepth(this, it->instStackIdx);

      uint32_t ptrBBIdx = findBlock(ptrIA->invarInfo, it->instBB->getName());
      ShadowBB* ptrBB = ptrIA->getBB(ptrBBIdx);
      if(!ptrBB)
	return;

      ShadowInstruction* ptr = &(ptrBB->insts[it->instIdx]);
      ptrSV = ShadowValue(ptr);
      ImprovedValSetSingle* ptrIVS = dyn_cast<ImprovedValSetSingle>(ptr->i.PB);
      if(!ptrIVS)
	return;

      writePtr = *ptrIVS;

    }

    for(uint32_t i = 0; i < writePtr.Values.size(); ++i) {

      if(writePtr.Values[i].Offset != LLONG_MAX)
	writePtr.Values[i].Offset += it->offset;

    }

    if(condty == PathConditionTypeString) {
      
      GlobalVariable* GV = cast<GlobalVariable>(it->val);
      ConstantDataArray* CDA = cast<ConstantDataArray>(GV->getInitializer());
      uint32_t Size = CDA->getNumElements();
      
      ShadowGV* SGV = &(pass->shadowGlobals[pass->getShadowGlobalIndex(GV)]);
      
      ImprovedValSetSingle copyFromPointer;
      copyFromPointer.set(ImprovedVal(SGV, 0), ValSetTypePB);
      
      // Attribute the effect of the write to first instruction in block:
      executeCopyInst(ptrSV.isInval() ? 0 : &ptrSV, writePtr, copyFromPointer, Size, &(BB->insts[0]));

    }
    else {
      
      // IntMem condition
      
      ImprovedValSetSingle writeVal;
      getImprovedValSetSingle(ShadowValue(it->val), writeVal);

      // Attribute the effect of the write to first instruction in block:
      executeWriteInst(0, writePtr, writeVal, GlobalAA->getTypeStoreSize(it->val->getType()), &(BB->insts[0]));

    }

    // Make sure a failed version of this block and its successors is created:
    markBlockAndSuccsFailed(BB->invar->idx, 0);

  }

}

void InlineAttempt::applyMemoryPathConditions(ShadowBB* BB) {

  if(!targetCallInfo)
    return;

  for(std::vector<PathCondition>::iterator it = pass->rootStringPathConditions.begin(),
	itend = pass->rootStringPathConditions.end(); it != itend; ++it) {

    applyPathCondition(&*it, PathConditionTypeString, BB);

  }

  for(std::vector<PathCondition>::iterator it = pass->rootIntmemPathConditions.begin(),
	itend = pass->rootIntmemPathConditions.end(); it != itend; ++it) {  

    applyPathCondition(&*it, PathConditionTypeIntmem, BB);

  }

  for(std::vector<PathFunc>::iterator it = pass->rootFuncPathConditions.begin(),
	itend = pass->rootFuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx == targetCallInfo->targetStackDepth && it->BB == BB->invar->BB) {

      // Insert a model call that notionally occurs before the block begins.
      // Notionally its callsite is the first instruction in BB; this is probably not a call
      // instruction, but since only no-arg functions are allowed it doesn't matter.

      if(!it->IA) {
	InlineAttempt* SymIA = new InlineAttempt(pass, *it->F, this->LI, &BB->insts[0], this->nesting_depth + 1, true);
	it->IA = SymIA;
      }

      it->IA->activeCaller = &BB->insts[0];
      it->IA->analyseNoArgs(false, false, stack_depth);

      doCallStoreMerge(BB, it->IA);

    }

  }

}

void InlineAttempt::getFailedReturnBlocks(SmallVector<BasicBlock*, 4>& rets) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    if(!isa<ReturnInst>(BBI->BB->getTerminator()))
      continue;

    rets.push_back(BBI->BB);

  }

}

bool InlineAttempt::hasFailedReturnPath() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    if(!isa<ReturnInst>(BBI->BB->getTerminator()))
      continue;

    if(blocksReachableOnFailure.count(i))
      return true;

  }

  return false;

}

// Save phase bits:

void InlineAttempt::initFailedBlockCommit() {

  failedBlocks.resize(nBBs);
  failedBlockMap = new ValueToValueMapTy();
  PHIForwards = new DenseMap<std::pair<Instruction*, Use*>, PHINode*>();
  DT = &pass->getAnalysis<DominatorTree>(F);

}

struct matchesFromIdx {

  BasicBlock* BB;
  uint32_t stackIdx;
  bool operator()(PathCondition& C) { return C.fromBB == BB && C.fromStackIdx == stackIdx; }
  matchesFromIdx(BasicBlock* _BB, uint32_t si) : BB(_BB), stackIdx(si) {}

};

static uint32_t countPathConditionsIn(BasicBlock* BB, uint32_t stackIdx, std::vector<PathCondition>& Conds) {

  matchesFromIdx Pred(BB, stackIdx);
  return std::count_if(Conds.begin(), Conds.end(), Pred);

}

uint32_t IntegrationHeuristicsPass::countPathConditionsForBlock(ShadowBB* BB) {

  IATargetInfo* Info = BB->IA->getFunctionRoot()->targetCallInfo;
  if(!Info)
    return 0;

  uint32_t stackIdx = Info->targetStackDepth;
  BasicBlock* B = BB->invar->BB;

  return countPathConditionsIn(B, stackIdx, rootIntPathConditions) +
    countPathConditionsIn(B, stackIdx, rootStringPathConditions) +
    countPathConditionsIn(B, stackIdx, rootIntmemPathConditions);

}

void InlineAttempt::emitPathConditionCheck(PathCondition& Cond, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<BasicBlock*, 1>::iterator& emitBlockIt) {

  if(stackIdx != Cond.fromStackIdx || BB->invar->BB != Cond.fromBB)
    return;

  BasicBlock* emitBlock = *(emitBlockIt++);

  Instruction* resultInst = 0;
  Value* testRoot;

  LLVMContext& LLC = BB->invar->BB->getContext();

  if(!Cond.instBB) {
   
    testRoot = pass->shadowGlobals[Cond.instIdx].G;
    
  }
  else {

    InlineAttempt* testCtx = getIAWithTargetStackDepth(this, Cond.instStackIdx);
    ShadowValue V;
    
    if(Cond.instBB == (BasicBlock*)ULONG_MAX)
      V = ShadowValue(&testCtx->argShadows[Cond.instIdx]);
    else {
      uint32_t blockIdx = findBlock(testCtx->invarInfo, Cond.instBB);
      V = ShadowValue(&testCtx->getBB(blockIdx)->insts[Cond.instIdx]);
    }

    testRoot = getCommittedValue(V);

  }

  switch(Ty) {

  case PathConditionTypeIntmem:
  case PathConditionTypeString:

    if(Cond.offset) {

      Type* Int8Ptr = Type::getInt8PtrTy(LLC);
      if(testRoot->getType() != Int8Ptr)
	testRoot = new BitCastInst(testRoot, Int8Ptr, "", emitBlock);

      Value* offConst = ConstantInt::get(Type::getInt64Ty(LLC), Cond.offset);
      testRoot = GetElementPtrInst::Create(testRoot, ArrayRef<Value*>(&offConst, 1), "", emitBlock);

    }

  default:
    break;

  }

  switch(Ty) {

  case PathConditionTypeIntmem:

    {
      Type* PtrTy = PointerType::getUnqual(Cond.val->getType());
      if(PtrTy != testRoot->getType())
	testRoot = new BitCastInst(testRoot, PtrTy, "", emitBlock);
      testRoot = new LoadInst(testRoot, "", false, emitBlock);
    }
    
    // FALL THROUGH TO:

  case PathConditionTypeInt:

    if(testRoot->getType() != Cond.val->getType())
      testRoot = new SExtInst(testRoot, Cond.val->getType(), "", emitBlock);

    resultInst = new ICmpInst(*emitBlock, CmpInst::ICMP_EQ, testRoot, Cond.val);
    break;

  case PathConditionTypeString:

    {

      Type* IntTy = Type::getInt32Ty(LLC);
      Type* CharPtr = Type::getInt8PtrTy(LLC);
      Type* StrcmpArgTys[2] = { CharPtr, CharPtr };
      FunctionType* StrcmpType = FunctionType::get(IntTy, ArrayRef<Type*>(StrcmpArgTys, 2), false);

      Constant* StrcmpFun = emitBlock->getParent()->getParent()->getFunction("strcmp");
      if(!StrcmpFun)
	StrcmpFun = emitBlock->getParent()->getParent()->getOrInsertFunction("strcmp", StrcmpType);
      
      if(testRoot->getType() != CharPtr)
	testRoot = new BitCastInst(testRoot, CharPtr, "", emitBlock);
	
      Value* StrcmpArgs[2] = { Cond.val, testRoot };
      CallInst* CmpCall = CallInst::Create(StrcmpFun, ArrayRef<Value*>(StrcmpArgs, 2), "assume_test", emitBlock);
      resultInst = new ICmpInst(*emitBlock, CmpInst::ICMP_EQ, CmpCall, Constant::getNullValue(CmpCall->getType()), "");

    }

  }

  // resultInst is a boolean indicating if the path condition matched.
  // Branch to the next specialised block on pass, or the first non-specialised block otherwise.

  BranchInst::Create(*emitBlockIt, failedBlocks[BB->invar->idx].front(), resultInst, emitBlock);

}

void InlineAttempt::emitPathConditionChecksIn(std::vector<PathCondition>& Conds, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<BasicBlock*, 1>::iterator& emitBlockIt) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it)
    emitPathConditionCheck(*it, Ty, BB, stackIdx, emitBlockIt);

}

SmallVector<BasicBlock*, 1>::iterator InlineAttempt::emitPathConditionChecks(ShadowBB* BB) {

  SmallVector<BasicBlock*, 1>::iterator it = BB->committedBlocks.begin();

  IATargetInfo* Info = BB->IA->getFunctionRoot()->targetCallInfo;
  if(!Info)
    return it;

  emitPathConditionChecksIn(pass->rootIntPathConditions, PathConditionTypeInt, BB, Info->targetStackDepth, it);
  emitPathConditionChecksIn(pass->rootStringPathConditions, PathConditionTypeString, BB, Info->targetStackDepth, it);
  emitPathConditionChecksIn(pass->rootIntmemPathConditions, PathConditionTypeIntmem, BB, Info->targetStackDepth, it);

  return it;
  
}

// Assumption here: block has a specialised companion.
BasicBlock::iterator InlineAttempt::emitFirstSubblockMergePHIs(uint32_t idx, SmallVector<BasicBlock*, 4>::iterator firstNonPCBlock) {

  ShadowBB* BB = getBB(idx);

  // This top unspecialised subblock is a spec/unspec merge point if (a) path condition checks
  // exist, or (b) there are spec predecessors that branch to unspec.
  if(firstNonPCBlock != BB->committedBlocks.begin() || isSimpleMergeBlock(idx)) {

    SmallVector<BasicBlock*, 4> unspecPreds;
    SmallVector<BasicBlock*, 4> specPreds;
     
    for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

      uint32_t pred = BB->invar->predIdxs[i];

      if(failedBlocks[pred].size())
	unspecPreds.push_back(failedBlocks[pred].back());

      if(isSpecToUnspecEdge(pred, idx))
	specPreds.push_back(getBB(pred)->committedBlocks.back());

    }

    for(SmallVector<BasicBlock*, 1>::iterator specit = BB->committedBlocks.begin(); 
	specit != firstNonPCBlock; ++specit)
      specPreds.push_back(*specit);

    return insertMergePHIs(idx, specPreds, unspecPreds, failedBlocks[idx].front(), 0);

  }
  else {

    return failedBlocks[idx].front()->begin();

  }
  
}

bool InlineAttempt::isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx) {

  if(targetCallInfo && !targetCallInfo->mayReachTarget.count(BBIdx)) {  

    if(targetCallInfo->mayReachTarget.count(predBlockIdx) && blocksReachableOnFailure.count(predBlockIdx)) {
      
      if(!edgeIsDead(getBBInvar(predBlockIdx), getBBInvar(BBIdx)))
	return true;
      
    }    

  }
  
  return false;

}

bool InlineAttempt::isSimpleMergeBlock(uint32_t i) {

  ShadowBBInvar* BBI = getBBInvar(i);
  for(uint32_t j = 0, jlim = BBI->predIdxs.size(); j != jlim; ++j) {
    
    uint32_t pred = BBI->predIdxs[j];
    if(isSpecToUnspecEdge(pred, i))
      return true;
    
  }

  return false;

}

Value* InlineAttempt::getLocalFailedValue(Value* V, Use* U) {

  Instruction* I = dyn_cast<Instruction>(V);
  if(!I)
    return V;

  DenseMap<std::pair<Instruction*, Use*>, PHINode*>::iterator it = PHIForwards->find(std::make_pair(I, U));
  if(it != PHIForwards->end())
    return it->second;

  release_assert(failedBlockMap->count(I));
  return (*failedBlockMap)[I];

}

BasicBlock::iterator InlineAttempt::insertMergePHIs(uint32_t BBIdx, SmallVector<BasicBlock*, 4>& specPreds, SmallVector<BasicBlock*, 4>& unspecPreds, BasicBlock* InsertBB, uint32_t BBOffset) {

  // This block will be a merge point: insert explicit PHI forwarding wherever we or a block we dominate
  // will use a value that we do not contain/dominate.
  // We (and blocks we dominate) can use any value in our dominator blocks.

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  BasicBlock* BB = BBI->BB;

  uint32_t BBPreds = specPreds.size() + unspecPreds.size();

  uint32_t nInserted = 0;

  DomTreeNode* Node = DT->getNode(BB);
  for(Node = Node->getIDom(); Node; Node = Node->getIDom()) {

    BasicBlock* ThisBB = Node->getBlock();
    uint32_t ThisBBIdx = findBlock(invarInfo, ThisBB);
    ShadowBB* ThisSBB = BBs[ThisBBIdx];

    // If there will only be one version of this block then we can use its values as usual as they will
    // continue to dominate even duplicated users. Its dominators are necessarily in the same situation.

    if(!ThisSBB)
      break;
    if(!blocksReachableOnFailure.count(ThisBBIdx))
      break;

    for(uint32_t instIdx = 0, instLim = ThisSBB->invar->insts.size(); instIdx != instLim; ++instIdx) {
      
      SmallVector<Use*, 8> replaceUses;
      ShadowInstruction* SI = &ThisSBB->insts[instIdx];
      Instruction* I = SI->invar->I;

      for(Instruction::use_iterator UI = I->use_begin(), UE = I->use_end(); UI != UE; ++UI) {

	Instruction* UseInst = cast<Instruction>(*UI);
	BasicBlock* UseBB = UseInst->getParent();

	uint32_t InstOffset = std::distance(UseBB->begin(), BasicBlock::iterator(UseInst));

	bool doReplace = false;

	if(UseBB == BB) {
	  
	  if(InstOffset >= BBOffset && !isa<PHINode>(UseInst))
	    doReplace = true;

	}
	else if(DT->dominates(BB, UseBB))
	  doReplace = true;

	if(doReplace)
	  replaceUses.push_back(&UI.getUse());
	
      }
      
      if(replaceUses.size()) {
	
	// Build a forwarding PHI node merging the specialised and unspecialised versions of the
	// relevant instruction. 

	PHINode* NewNode = PHINode::Create(I->getType(), BBPreds, "clonemerge", InsertBB->begin());
	++nInserted;
	for(SmallVector<BasicBlock*, 4>::iterator it = specPreds.begin(), itend = specPreds.end(); it != itend; ++it) {

	  BasicBlock* PredBB = *it;
	  Value* Op = getValAsType(getCommittedValue(ShadowValue(SI)), NewNode->getType(), 
				   PredBB->getTerminator());
	  NewNode->addIncoming(Op, PredBB);
      
	}

	for(SmallVector<BasicBlock*, 4>::iterator it = unspecPreds.begin(), itend = unspecPreds.end(); it != itend; ++it) {

	  Value* Op = getLocalFailedValue(I, replaceUses.front());
	  NewNode->addIncoming(Op, *it);
	  
	}

	// Finally note that when the Instruction Use is committed, it should use
	// the new PHI instead of the expected value, and anyone attempting to PHI-gather
	// it further should use this relay node:

	for(SmallVector<Use*, 8>::iterator it = replaceUses.begin(), 
	      itend = replaceUses.end(); it != itend; ++it) {
	  std::pair<Instruction*, Use*> K = std::make_pair<Instruction*, Use*>(I, *it);
	  (*PHIForwards)[K] = NewNode;
	}
			     
      }

    }

  }

  BasicBlock::iterator RetBI(InsertBB->begin());
  std::advance(RetBI, nInserted);
  return RetBI;

}

BasicBlock::iterator InlineAttempt::insertSimpleMergePHIs(uint32_t BBIdx) {

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  SmallVector<BasicBlock*, 4> specPreds;
  SmallVector<BasicBlock*, 4> unspecPreds;

  for(uint32_t i = 0, ilim = BBI->predIdxs.size(); i != ilim; ++i) {
    
    uint32_t idx = BBI->predIdxs[i];
    if(!edgeIsDead(getBBInvar(idx), BBI)) {
      
      // A specialised block exists and reaches us! Gather the specialised value this way:
      ShadowBB* PredSBB = getBB(idx);
      specPreds.push_back(PredSBB->committedBlocks.back());

    }
    
    if(failedBlocks[i].size()) {
      
      // Consume the unspecialised value when accessed from an unspecialised block:
      unspecPreds.push_back(failedBlocks[i].back());
      
    }
    
  }

  return insertMergePHIs(BBIdx, specPreds, unspecPreds, failedBlocks[BBIdx].front(), 0);

}

BasicBlock::iterator InlineAttempt::insertPostCallPHIs(uint32_t OrigBBIdx, BasicBlock* InsertBB, uint32_t InsertBBOffset, ShadowInstruction* Call, BasicBlock* unspecPred) {

  SmallVector<BasicBlock*, 4> specPreds;
  SmallVector<BasicBlock*, 4> unspecPreds;

  unspecPreds.push_back(unspecPred);
  
  InlineAttempt* CallIA = inlineChildren[Call];
  CallIA->getFailedReturnBlocks(specPreds);
  
  return insertMergePHIs(OrigBBIdx, specPreds, unspecPreds, InsertBB, InsertBBOffset);

}

Value* InlineAttempt::getUnspecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, Use* U) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    // Pred is not an instruction. Use the same val whether consuming unspec or spec versions.
    return getSpecValue(blockIdx, instIdx, V);

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    if(failedBlocks[blockIdx].size())
      return getLocalFailedValue(V, U);
    else
      return getSpecValue(blockIdx, instIdx, V);

  }  

}

Value* InlineAttempt::getSpecValue(uint32_t blockIdx, uint32_t instIdx, Value* V) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    if(Argument* A = dyn_cast<Argument>(V))
      return argShadows[A->getArgNo()].committedVal;
    else
      return V;

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    ShadowBB* specBB = getBB(blockIdx);
    if(!specBB)
      return 0;
    else
      return getCommittedValue(ShadowValue(&specBB->insts[instIdx]));

  }  

}

BasicBlock::iterator InlineAttempt::commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx, SmallVector<BasicBlock*, 4>::iterator PCPredsBegin, SmallVector<BasicBlock*, 4>::iterator PCPredsEnd) {

  // Create PHI nodes for this unspecialised block, starting at BI.
  // Cases:
  // * If an incoming value is only defined in specialised code, 
  //     use it: it must dominate the sending block.
  // * If an incoming value is defined both ways then if this is a spec-to-unspec merge point 
  //     (i.e. this is an ignored block), merge both.
  // * Otherwise use just the unspec version.
  // * If this block has cross-edges at the top (due to path condition checks), 
  //     merge in the companion of this PHI node on each of those edges.

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  ShadowBB* SBB = getBB(BBIdx);
  uint32_t instIdx = 0;

  for(BasicBlock::iterator BE = BB->end(); BI != BE && isa<PHINode>(BI); ++BI, ++instIdx) {

    ShadowInstructionInvar* PNInfo = &BBI->insts[instIdx];
    PHINode* OrigPN = cast<PHINode>(PNInfo->I);
    PHINode* PN = cast<PHINode>(BI);

    SmallVector<std::pair<Value*, BasicBlock*>, 4> newPreds;

    for(uint32_t i = 0, ilim = PNInfo->operandBBs.size(); i != ilim; ++i) {

      uint32_t predBlockIdx = PNInfo->operandBBs[i];
      ShadowInstIdx predOp = PNInfo->operandIdxs[i];
      Value* predV = OrigPN->getIncomingValue(i);

      Value* unspecV = getUnspecValue(predOp.blockIdx, predOp.instIdx, predV, &OrigPN->getOperandUse(i));
      Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV);

      BasicBlock* specPred;
      if(!edgeIsDead(getBBInvar(predBlockIdx), getBBInvar(BBIdx)))
	specPred = getBB(predBlockIdx)->committedBlocks.back();
      else
	specPred = 0;

      BasicBlock* unspecPred;
      if(failedBlocks[predBlockIdx].size())
	unspecPred = failedBlocks[predBlockIdx].back();
      else
	unspecPred = 0;

      if(unspecPred) {

	bool isMerge = isSpecToUnspecEdge(predBlockIdx, BBIdx);

	if(isMerge) {
	  release_assert(specV && specPred);
	  newPreds.push_back(std::make_pair(specV, specPred));
	}

	release_assert(unspecV);
	newPreds.push_back(std::make_pair(unspecV, unspecPred));

      }
      else if(specPred) {

	release_assert(specV);
	newPreds.push_back(std::make_pair(specV, specPred));

      }

    }

    // If any edges from tests exist, consume the companion of this PHI node, which has already
    // selected an appropriate specialised value.

    Value* PCVal = 0;
    if(PCPredsBegin != PCPredsEnd) {

      release_assert(SBB);
      PCVal = getCommittedValue(ShadowValue(&SBB->insts[instIdx]));
	  
    }

    for(SmallVector<BasicBlock*, 4>::iterator PCIt = PCPredsBegin; PCIt != PCPredsEnd; ++PCIt)
      newPreds.push_back(std::make_pair(PCVal, *PCIt));

    // Clear node:
    for(uint32_t i = PN->getNumIncomingValues(); i > 0; --i)
      PN->removeIncomingValue(i - 1, false);

    // Populate node:
    for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator it = newPreds.begin(),
	  itend = newPreds.end(); it != itend; ++it) {

      PN->addIncoming(it->first, it->second);

    }

  }

  return BI;

}

void InlineAttempt::remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t idx, bool skipTerm) {

  // Map each instruction operand to the most local PHI translation of the target instruction,
  // or if that doesn't exist the specialised version.

  uint32_t instIdx = 0;
  for(BasicBlock::iterator it = BB->begin(); it != BI; ++it)
    ++instIdx;

  BasicBlock::iterator BE = BB->end();
  if(skipTerm)
    --BE;

  for(; BI != BE; ++BI, ++instIdx) {

    Instruction* I = BI;
    
    if(ReturnInst* RI = dyn_cast<ReturnInst>(BI)) {

      // Rewrite into a branch to and contribution to the failed return phi node.
      if(failedReturnPHI) {

	Use* U = &RI->getOperandUse(0);
	Value* Ret = getUnspecValue(idx, instIdx, *U, U);
	failedReturnPHI->addIncoming(Ret, BB);

      }

      RI->eraseFromParent();
      BranchInst::Create(failedReturnBlock, BB);
      // Bail out since we just ate the loop's controlling iterator
      return;

    }
    else {

      for(Instruction::op_iterator it = I->op_begin(), itend = I->op_end(); it != itend; ++it) {

	Use* U = it;
	Value* V = *U;

	Value* Repl;
	if(isa<BasicBlock>(V))
	  Repl = (*failedBlockMap)[V];
	else
	  Repl = getUnspecValue(idx, instIdx, V, U);

	U->set(Repl);

      }

    }

  }

}

BasicBlock::iterator InlineAttempt::commitSimpleFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx) {

  // Last two parameters: any old pair of identical iterators signifying no path condition checks here.
  return commitFailedPHIs(BB, BI, BBIdx, failedBlocks[BBIdx].begin(), failedBlocks[BBIdx].begin());

}

void InlineAttempt::commitSimpleFailedBlock(uint32_t i) {

  if(failedBlocks[i].empty())
    return;

  release_assert(failedBlocks[i].size() == 1 && "commitSimpleFailedBlock with a split block?");

  BasicBlock::iterator BI;
  BasicBlock* CommitBB = failedBlocks[i].front();

  bool isMerge = isSimpleMergeBlock(i);

  if(isMerge)
    BI = insertSimpleMergePHIs(i);
  else
    BI = CommitBB->begin();

  BI = commitFailedPHIs(CommitBB, BI, i, failedBlocks[i].begin(), failedBlocks[i].begin());
 
  remapFailedBlock(BI, CommitBB, i, false);

}

