
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
     MyRoot->targetCallInfo->targetStackDepth + 1 < pass->targetCallStack.size()) {

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

void PeelIteration::initFailedBlockCommit() {}

void InlineAttempt::initFailedBlockCommit() {

  failedBlocks.resize(nBBs);
  failedBlockMap = new ValueToValueMapTy();
  PHIForwards = new DenseMap<std::pair<Instruction*, Use*>, PHINode*>();

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

ShadowValue InlineAttempt::getPathConditionSV(PathCondition& Cond) {

  if(!Cond.instBB) {
   
    return ShadowValue(&pass->shadowGlobals[Cond.instIdx]);
    
  }
  else {

    InlineAttempt* testCtx = getIAWithTargetStackDepth(this, Cond.instStackIdx);
    
    if(Cond.instBB == (BasicBlock*)ULONG_MAX)
      return ShadowValue(&testCtx->argShadows[Cond.instIdx]);
    else {
      uint32_t blockIdx = findBlock(testCtx->invarInfo, Cond.instBB);
      return ShadowValue(&testCtx->getBB(blockIdx)->insts[Cond.instIdx]);
    }

  }

}

void InlineAttempt::emitPathConditionCheck(PathCondition& Cond, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<BasicBlock*, 1>::iterator& emitBlockIt) {

  if(stackIdx != Cond.fromStackIdx || BB->invar->BB != Cond.fromBB)
    return;

  BasicBlock* emitBlock = *(emitBlockIt++);

  Instruction* resultInst = 0;
  Value* testRoot = getCommittedValue(getPathConditionSV(Cond));

  LLVMContext& LLC = BB->invar->BB->getContext();
  Type* Int8Ptr = Type::getInt8PtrTy(LLC);

  switch(Ty) {

  case PathConditionTypeIntmem:
  case PathConditionTypeString:

    if(Cond.offset) {

      if(testRoot->getType() != Int8Ptr) {
	release_assert(CastInst::isCastable(testRoot->getType(), Int8Ptr));
	Instruction::CastOps Op = CastInst::getCastOpcode(testRoot, false, Int8Ptr, false);
	testRoot = CastInst::Create(Op, testRoot, Int8Ptr, "testcast", emitBlock);
      }

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
      Type* StrcmpArgTys[2] = { Int8Ptr, Int8Ptr };
      FunctionType* StrcmpType = FunctionType::get(IntTy, ArrayRef<Type*>(StrcmpArgTys, 2), false);

      Function* StrcmpFun = emitBlock->getParent()->getParent()->getFunction("strcmp");
      if(!StrcmpFun)
	StrcmpFun = cast<Function>(emitBlock->getParent()->getParent()->getOrInsertFunction("strcmp", StrcmpType));
      
      if(testRoot->getType() != Int8Ptr) {
	Instruction::CastOps Op = CastInst::getCastOpcode(testRoot, false, Int8Ptr, false);
	testRoot = CastInst::Create(Op, testRoot, Int8Ptr, "testcast", emitBlock);
      }
      
      Value* CondCast = ConstantExpr::getBitCast(Cond.val, Int8Ptr);
	
      Value* StrcmpArgs[2] = { CondCast, testRoot };
      CallInst* CmpCall = CallInst::Create(StrcmpFun, ArrayRef<Value*>(StrcmpArgs, 2), "assume_test", emitBlock);
      CmpCall->setCallingConv(StrcmpFun->getCallingConv());
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

SmallVector<BasicBlock*, 1>::iterator PeelIteration::emitPathConditionChecks(ShadowBB* BB) { 

  // No path conditions within loops at the moment.
  return BB->committedBlocks.begin();

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

BasicBlock::iterator InlineAttempt::emitFirstSubblockMergePHIs(uint32_t idx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondEnd) {

  ShadowBB* BB = getBB(idx);
  if(!BB)
    return failedBlocks[idx].front()->begin();

  // This top unspecialised subblock is a spec/unspec merge point if (a) path condition checks
  // exist, or (b) there are spec predecessors that branch to unspec.
  // This kind of merge necessarily does not involve branches out of loop context.
  if(pathCondBegin != pathCondEnd || isSimpleMergeBlock(idx)) {

    release_assert((!L) && "Path condition or spec/unspec merge in loop context?");

    SmallVector<BasicBlock*, 4> unspecPreds;
    SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> specPreds;
     
    for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

      uint32_t pred = BB->invar->predIdxs[i];

      if(failedBlocks[pred].size())
	unspecPreds.push_back(failedBlocks[pred].back().first);

      if(isSpecToUnspecEdge(pred, idx))
	specPreds.push_back(std::make_pair(getBB(pred)->committedBlocks.back().first, this));

    }

    for(SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator specit = pathCondBegin;
	specit != pathCondEnd; ++specit)
      specPreds.push_back(std::make_pair(specit->first, this));

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

  Value* Ret = tryGetLocalFailedValue(V, U);
  release_assert(Ret);
  return Ret;

}

Value* InlineAttempt::tryGetLocalFailedValue(Value* V, Use* U) {

  Instruction* I = dyn_cast<Instruction>(V);
  if(!I)
    return V;

  DenseMap<std::pair<Instruction*, Use*>, PHINode*>::iterator it = PHIForwards->find(std::make_pair(I, U));
  if(it != PHIForwards->end())
    return it->second;

  ValueToValueMapTy::iterator it2 = failedBlockMap->find(I);
  if(it2 == failedBlockMap->end())
    return 0;
  else
    return it2->second;

}

BasicBlock::iterator InlineAttempt::insertMergePHIs(uint32_t BBIdx, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& specPreds, SmallVector<BasicBlock*, 4>& unspecPreds, BasicBlock* InsertBB, uint32_t BBOffset) {

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
    ShadowBBInvar* ThisBBI = getBBInvar(ThisBBIdx);
    SmallDenseMap<uint32_t, uint32_t, 8>::iterator failIt = blocksReachableOnFailure.find(ThisBBIdx);

    // If there will only be one version of this block then we can use its values as usual as they will
    // continue to dominate even duplicated users. Its dominators are necessarily in the same situation.
    // If the definition comes from the same loop as the merge BB, or a parent loop, then we still
    // create a PHI to merge the different variants of the value.

    if((!ThisBBI->naturalScope) || !ThisBBI->naturalScope->contains(BBI->naturalScope)) {

      if(!getBB(ThisBBIdx))
	break;

      if(failIt == blocksReachableOnFailure.end())
	break;

    }

    for(uint32_t instIdx = 0, instLim = ThisSBB->invar->insts.size(); instIdx != instLim; ++instIdx) {
      
      SmallVector<Use*, 8> replaceUses;
      Instruction* I = ThisBBI->insts[instIdx].I;

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
	
	// Build a forwarding PHI node merging either several specialised variants of the instruction,
	// or unspecialised and specialised variants, or both. Note an unspecialised variant only
	// exists if instIdx >= failIt->second, but getUnspecValue takes care of that for us.

	PHINode* NewNode = PHINode::Create(I->getType(), BBPreds, "clonemerge", InsertBB->begin());
	++nInserted;
	for(SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>::iterator it = specPreds.begin(), itend = specPreds.end(); it != itend; ++it) {

	  BasicBlock* PredBB = it->first;
	  Value* Op = getValAsType(it->second->getSpecValue(ThisBBIdx, instIdx), NewNode->getType(), 
				   PredBB->getTerminator());
	  NewNode->addIncoming(Op, PredBB);
      
	}

	for(SmallVector<BasicBlock*, 4>::iterator it = unspecPreds.begin(), itend = unspecPreds.end(); it != itend; ++it) {

	  Value* Op = getUnspecValue(ThisBBIdx, instIdx, replaceUses.front());
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

  // This kind of merge happens when blocks are ignored because they aren't on the path to
  // the user's given goal stack. This cannot involve loop exiting branches.

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  SmallVector<BasicBlock*, 4> specPreds;
  SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> unspecPreds;

  for(uint32_t i = 0, ilim = BBI->predIdxs.size(); i != ilim; ++i) {
    
    uint32_t idx = BBI->predIdxs[i];
    if(!edgeIsDead(getBBInvar(idx), BBI)) {
      
      // A specialised block exists and reaches us! Gather the specialised value this way:
      ShadowBB* PredSBB = getBB(idx);
      specPreds.push_back(std::make_pair(PredSBB->committedBlocks.back(), this));

    }
    
    if(failedBlocks[i].size()) {
      
      // Consume the unspecialised value when accessed from an unspecialised block:
      unspecPreds.push_back(failedBlocks[i].back());
      
    }
    
  }

  return insertMergePHIs(BBIdx, specPreds, unspecPreds, failedBlocks[BBIdx].front(), 0);

}

uint32_t IntegrationAttempt::collectSpecIncomingEdges(uint32_t blockIdx, uint32_t instIdx, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& edges) {

  ShadowBBInvar* BBI = getBBInvar(blockIdx);
  if(BBI->naturalScope != L && ((!L) || L->contains(BBI->naturalScope))) {
    
    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {

      uint32_t count = 0;
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	count += LPA->Iterations[i]->collectSpecIncomingEdges(blockIdx, instIdx, edges);
      return count;

    }

  }

  ShadowBB* BB = getBB(*BBI);
  if(!BB)
    return 0;

  bool added = false;

  ShadowInstruction* SI = &BB->insts[instIdx];
  InlineAttempt* IA;
  if((IA = getInlineAttempt(SI)) && IA->isEnabled() && IA->failedReturnBlock) {

    edges.push_back(std::make_pair(IA->failedReturnBlock, this));
    added = true;

  }
  else if(requiresRuntimeCheck(ShadowValue(SI))) {

    edges.push_back(std::make_pair(BB->getCommittedBlockAt(instIdx), this));
    added = true;

  }

  if(added && L)
    return 1;
  else
    return 0;

}

BasicBlock::iterator InlineAttempt::insertSubBlockPHIs(uint32_t OrigBBIdx, BasicBlock* InsertBB, uint32_t InsertBBOffset, BasicBlock* unspecPred) {

  SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> specPreds;
  SmallVector<BasicBlock*, 4> unspecPreds;

  uint32_t nLoopPreds = collectSpecIncomingEdges(OrigBBIdx, InsertBBOffset - 1, specPreds);

  // No need for PHI insertion if we don't actually merge anything.
  if(nLoopPreds == 0 && !unspecPred)
    return InsertBB->begin();
  
  if(unspecPred)
    unspecPreds.push_back(unspecPred);

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

    Value* Ret = tryGetLocalFailedValue(V, U);
    if(!Ret)
      Ret = getSpecValue(blockIdx, instIdx, V);
    return Ret;

  }  

}

Value* IntegrationAttempt::getSpecValue(uint32_t blockIdx, uint32_t instIdx, Value* V) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    if(Argument* A = dyn_cast<Argument>(V))
      return getFunctionRoot()->argShadows[A->getArgNo()].committedVal;
    else
      return V;

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    ShadowInstruction* specI = getInst(blockIdx, instIdx);
    if(!specI)
      return 0;
    else
      return getCommittedValue(ShadowValue(specI));

  }  

}

BasicBlock::iterator InlineAttempt::commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx, SmallVector<std::pair<BasicBlock*, uint32_t>, 4>::iterator PCPredsBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 4>::iterator PCPredsEnd) {

  // Create PHI nodes for this unspecialised block, starting at BI.
  // Cases:
  // * If an incoming value is only defined in specialised code, 
  //     use it: it must dominate the sending block.
  // * If an incoming value is defined both ways then if this is a spec-to-unspec merge point 
  //     (i.e. this is an ignored block), merge both.
  // * Otherwise use just the unspec version.
  // * If this block has cross-edges at the top (due to path condition checks), 
  //     merge in the companion of this PHI node on each of those edges.

  // Note that if we don't have a companion BB then no augmentation is necessary: we are only
  // called this way regarding blocks accessible from within a loop, whose headers are not merge points.

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  ShadowBB* SBB = getBB(BBIdx);
  if(!SBB)
    return BI;

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
      if(isSpecToUnspecEdge(predBlockIdx, BBIdx))
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

void InlineAttempt::remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t idx, uint32_t instIdx, bool skipTerm) {

  // Map each instruction operand to the most local PHI translation of the target instruction,
  // or if that doesn't exist the specialised version.

  BasicBlock::iterator BE = BB->end();
  if(skipTerm)
    --BE;

  ShadowBBInvar* BBI = getBBInvar(idx);

  for(; BI != BE; ++BI, ++instIdx) {

    ShadowInstructionInvar& SII = BBI->insts[instIdx];
    Instruction* I = BI;
    
    ReturnInst* RI = dyn_cast<ReturnInst>(BI);
    if(RI && !isRootMainCall()) {

      // Rewrite into a branch to and contribution to the failed return phi node.
      if(failedReturnPHI) {

	Use* U = &RI->getOperandUse(0);
	Value* Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, *U, U);
	failedReturnPHI->addIncoming(Ret, BB);

      }

      RI->eraseFromParent();
      BranchInst::Create(failedReturnBlock, BB);
      // Bail out since we just ate the loop's controlling iterator
      return;

    }
    else {

      uint32_t opIdx = 0;
      for(Instruction::op_iterator it = I->op_begin(), itend = I->op_end(); it != itend; ++it, ++opIdx) {

	Use* U = it;
	Value* V = *U;

	ShadowInstIdx& op = SII.operandIdxs[opIdx];

	Value* Repl;
	if(isa<BasicBlock>(V))
	  Repl = (*failedBlockMap)[V];
	else
	  Repl = getUnspecValue(op.blockIdx, op.instIdx, V, U);

	U->set(Repl);

      }

    }

  }

}

void PeelIteration::commitSimpleFailedBlock(uint32_t i) { }

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

  BasicBlock::iterator PostPHIBI = commitFailedPHIs(CommitBB, BI, i, failedBlocks[i].begin(), failedBlocks[i].begin());
 
  remapFailedBlock(PostPHIBI, CommitBB, i, std::distance(BI, PostPHIBI), false);

}

void IntegrationAttempt::getSplitInsts(ShadowBBInvar* BBI, bool* splitInsts) {

  if(BBI->naturalScope != L && ((!L) || L->contains(BBI->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) && 
       LPA->isTerminated() && 
       LPA->isEnabled()) {

      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->getSplitInsts(BBI, splitInsts);

      return;

    }

  }

  ShadowBB* BB = getBB(*BBI);
  if(BB) {

    for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

      ShadowInstruction* SI = &BB->insts[i];
      InlineAttempt* IA;
      if((IA = getInlineAttempt(SI)) && IA->isEnabled() && IA->hasFailedReturnPath())
	splitInsts[i] = true;
      else if(requiresRuntimeCheck(ShadowValue(SI))) {

	// Check exit PHIs as a block:
	if(i + 1 != ilim && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[i+1]))
	  continue;

	splitInsts[i] = true;

      }

    }

  }

}

static BasicBlock* CloneBasicBlockFrom(const BasicBlock* BB,
				       ValueToValueMapTy& VMap,
				       const Twine &NameSuffix, 
				       Function* F,
				       uint32_t startIdx) {

  BasicBlock *NewBB = BasicBlock::Create(BB->getContext(), "", F);
  if (BB->hasName()) NewBB->setName(BB->getName()+NameSuffix);

  // Loop over all instructions, and copy them over.
  BasicBlock::const_iterator II = BB->begin();
  std::advance(II, startIdx);

  for (BasicBlock::const_iterator IE = BB->end(); II != IE; ++II) {
    Instruction *NewInst = II->clone();
    if (II->hasName())
      NewInst->setName(II->getName()+NameSuffix);
    NewBB->getInstList().push_back(NewInst);
    VMap[II] = NewInst;                // Add instruction map to value.
    
  }
  
  return NewBB;

}

void PeelIteration::createFailedBlock(uint32_t idx) {}

void InlineAttempt::createFailedBlock(uint32_t idx) {

  SmallDenseMap<uint32_t, uint32_t, 8>::iterator it = blocksReachableOnFailure.find(i);
  if(it == blocksReachableOnFailure.end())
    return;

  uint32_t createFailedBlockFrom = it->second;

  ShadowBBInvar* BBI = getBBInvar(idx);
  BasicBlock* NewBB = CloneBasicBlockFrom(BBI->BB, *failedBlockMap, "", CF, createFailedBlockFrom);
  std::string newName;
  {
    raw_string_ostream RSO(newName);
    RSO << getCommittedBlockPrefix() << BBI->BB->getName() << " (failed)";
  }

  NewBB->setName(newName);
  failedBlocks[i].push_back(std::make_pair(NewBB, createFailedBlockFrom));
  (*failedBlockMap)[BBI->BB] = NewBB;

  bool splitInsts[BBI->insts.size()];
  getSplitInsts(BBI, splitInsts);

  uint32_t instsSinceLastSplit = 0;
  for(uint32_t i = 0, ilim = BBI->insts.size(); i != ilim; ++i) {

    if(splitInsts[i]) {

      // No need to split (first sub-block?)
      if(i + 1 == createFailedBlockFrom)
	continue;

      BasicBlock* toSplit = failedBlocks[i].back().first;
      uint32_t instsToSplit = std::min((i+1) - createFailedBlockFrom, instsSinceLastSplit + 1);
      BasicBlock::iterator splitIterator = toSplit->begin();
      std::advance(splitIterator, instsToSplit);
      BasicBlock* splitBlock = 
	toSplit->splitBasicBlock(splitIterator, ".checksplit");
      failedBlocks[i].push_back(std::make_pair(splitBlock, i + 1));

      instsSinceLastSplit = 0;

    }
    else {
      
      ++instsSinceLastSplit;

    }

  }

}

void InlineAttempt::getSubBlockForInst(uint32_t blockIdx, uint32_t instIdx) {

  release_assert(failedBlocks.count(blockIdx) && "Failed block should exist");
  
  SmallVector<std::pair<BasicBlock*, uint32_t> >& splits = failedBlocks[blockIdx];
  SmallVector<std::pair<BasicBlock*, uint32_t> >::iterator it = splits.begin(), itend = splits.end();

  while(it->second < instIdx) {
    ++it;
    release_assert(it != itend);
  }

  return it->first;    
  
}

void IntegrationAttempt::collectSpecPreds(ShadowBBInvar* predBlock, uint32_t predIdx, ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds) {

  if(L != predBlock->naturalScope && ((!L) || L->contains(predBlock->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, predBlock->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->collectSpecPreds(predBlock, instBlock, instIdx, preds);

      return;

    }

  }

  ShadowBB* InstBB = getBB(*instBlock);
  ShadowInstruction* SI = &InstBB->insts[instIdx];

  ShadowBB* PredBB = getBB(*predBlock);
  if(!PredBB)
    return;

  BasicBlock* pred = PredBB->getCommittedBlockAt(predIdx);
  Value* committedVal = getCommittedValue(ShadowValue(&InstBB->insts[instIdx]));

  preds.push_back(std::make_pair(committedVal, pred));

}

void IntegrationAttempt::collectCallFailingEdges(ShadowBBInvar* predBlock, uint32_t predIdx, ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds) {
  
  if(L != predBlock->naturalScope && ((!L) || L->contains(predBlock->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, predBlock->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->collectCallFailingEdges(predBlock, instBlock, instIdx, preds);

      return;

    }

  }

  ShadowBB* InstBB = getBB(*instBlock);
  ShadowInstruction* SI = &InstBB->insts[instIdx];

  InlineAttempt* IA;
  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->failedReturnPHI)
      preds.push_back(IA->failedReturnPHI, CallIA->failedReturnBlock);

  }
  else {
    
    if(runtimeCheckRequired(SI)) {

      ShadowBB* PredBB = getBB(*predBlock);
      BasicBlock* pred = PredBB->getCommittedBlockAt(predIdx);
      Value* committedVal = getCommittedValue(ShadowValue(&InstBB->insts[instIdx]));
      preds.push_back(committedVal, pred);

    }

  }

}

void PeelIteration::populateFailedBlock(uint32_t idx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondEnd) { }

void InlineAttempt::populateFailedBlock(uint32_t idx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondEnd) {
  
  if(failedBlocks[idx].empty())
    return;

  ShadowBBInvar* BBI = getBBInvar(idx);

  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it, endit, lastit;
  it = failedBlocks[idx].begin(); endit = failedBlocks[idx].end(); lastit = endit;
  --lastit;

  if(it->second == 0) {

    // Possible predecessors: failing path conditions from a specialised partner,
    // specialised blocks that branch direct to unspecialised code, and an unspecialised predecessor.
    // These inserted / augmented PHIs cannot draw from loop iterations above us,
    // as loop iterations only make mid-block breaks due to failing tests.
    BasicBlock::iterator BI = emitFirstSubblockMergePHIs(idx, pathCondBegin, pathCondEnd);
    BasicBlock::iterator PostPHIBI = commitFailedPHIs(it->first, BI, idx, pathCondBegin, pathCondEnd);

    remapFailedBlock(PostPHIBI, it->first, idx, std::distance(BI, PostPHIBI), it != lastit);

    ++it;

  }

  for(; it != lastit; ++it) {

    release_assert(it->first != 0);

    // PHI node checks are done as a group; all others are tested one at a time.
    // Find the bounds of the group.

    uint32_t failedInstLim = it->first;
    uint32_t firstFailedInst = failedInstLim - 1;
    
    uint32_t insertedPHIs = 0;

    while(firstFailedInst != 0 && 
	  isa<PHINode>(BBI->insts[firstFailedInst]) && 
	  isa<PHINode>(BBI->insts[firstFailedInst - 1]))
      --firstFailedInst;

    // For each instruction tested here insert a PHI gathering the values from failed blocks
    // and from an unspecialised version if it exists.

    for(uint32_t failedInst = firstFailedInst; failedInst != failedInstLim; ++failedInst) {

      Instruction* failedI = BBI->insts[failedInst].I;

      SmallVector<std::pair<Value*, BasicBlock*>, 4> specPreds;
      if(isa<CallInst>(failedI)) {
	if(!failedI->getType()->isVoidTy())
	  collectCallFailingEdges(BBI, failedInst, BBI, failedInst, specPreds);
      }
      else
	collectSpecPreds(BBI, failedInst, BBI, failedInst, specPreds);

      if(specPreds.size()) {

	++insertedPHIs;

	PHINode* NewPN =  makePHI(failedI->getType(), "spec-unspec-merge", it->first);
	for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator it = specPreds.begin(),
	      itend = specPreds.end(); it != itend; ++it)
	  NewPN->addIncoming(it->first, it->second);

	if(it != failedBlocks[idx].begin()) {

	  // There is an unspecialised predecessor to this subblock. Merge the unspecialised pred.
	  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator predIt = it;
	  --predIt;

	  NewPN->addIncoming(getUnspecValue(idx, failedInst, failedI, &failedI->use_begin().getUse()), *predIt);

	}

	(*LocalRoot->failedBlockMap)[failedI] = NewPN;

      }

    }

    BasicBlock* unspecPred;
    if(it == failedBlocks[idx].begin())
      unspecPred = 0;
    else {
      SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator previt = it;
      --previt;
      unspecPred = previt->first;
    }

    BasicBlock::iterator BI = insertSubBlockPHIs(idx, it->first, it->second, unspecPred);
    
    // Skip past previously introduced PHI nodes to the normal instructions
    std::advance(BI, insertedPHIs);

    // Remap the normal instructions
    remapFailedBlock(BI, *it->first, idx, it->second, it != lastit);

  }
  
}

Value* IntegrationAttempt::emitCompareCheck(Value* realInst, ImprovedValSetSingle* IVS) {

  release_assert(isa<Instruction>(realInst) && "Checked instruction must be residualised");
  release_assert(IVS && IVS->Values.size() != 0 && "Must have an IVS for PHI check (multis not implemented)");

  Value* thisCheck = 0;
  for(uint32_t j = 0, jlim = IVS->Values.size(); j != jlim; ++j) {

    Value* thisVal = trySynthVal(SI, IVS->SetType, IVS->Values[j], emitBB);
    Value* newCheck;
    if(thisVal->getType()->isFloatingPointTy())
      newCheck = new FCmpInst(*emitBB, CmpInst::FCMP_OEQ, realInst, thisCheck, "check");
    else
      newCheck = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, realInst, thisCheck, "check");

    if(thisCheck)
      thisCheck = BinaryOperator::CreateOr(newCheck, thisCheck, "", emitBB);
    else
      thisCheck = newCheck;

  }

  return thisCheck;

}

Value* IntegrationAttempt::emitAsExpectedCheck(ShadowInstruction* SI, BasicBlock* emitBB) {

  Value* realInst = getCommittedValue(ShadowValue(SI));
  ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI->i.PB);

  return emitCompareCheck(realInst, IVS);

}

SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator
IntegrationAttempt::emitExitPHIChecks(SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitIt, ShadowBB* BB) {

  BasicBlock* emitBB = (emitIt++)->first;
  Value* prevCheck = 0;

  uint32_t i;
  for(i = 0, ilim = BB->invar->insts.size(); i != ilim && inst_is<PHINode>(&BB->insts[i]); ++i) {
    
    ShadowInstruction* SI = &BB->insts[i];

    Value* thisCheck = emitAsExpectedCheck(SI, emitBB);

    if(prevCheck)
      prevCheck = BinaryOperator::CreateAnd(thisCheck, prevCheck, "", emitBB);
    else
      prevCheck = thisCheck;

  }

  BasicBlock* successTarget = *emitIt;
  // i is the index of the first non-PHI at this point.
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, i);

  BranchInst::Create(successTarget, failTarget, emitBB); 

  return emitIt;

}

void IntegrationAttempt::emitMemcpyCheck(ShadowInstruction* SI, BasicBlock* emitBB) {

  release_assert(SI->memcpyValues && SI->memcpyValues.size() && "memcpyValues not set for checked copy?");

  Value* prevCheck = 0;
  Value* writtenPtr = getCommittedValue(SI->getOperand(0));

  Type* CharPtr = Type::getInt8PtrTy(SI->invar->I->getContext());
  Type* I64 = Type::getInt64Ty(SI->invar->I->getContext());

  if(writtenPtr->getType() != CharPtr)
    writtenPtr = new BitCastInst(writtenPtr, CharPtr, "", emitBB);

  uint64_t ptrOffset = cast<ImprovedValSetSingle>(SI->i.PB)->Values[0].Offset;

  for(SmallVector<IVSRange, 4>::iterator it = SI->memcpyValues->begin(), 
	itend = SI->memcpyValues->end(); it != itend; ++it) {

    if(it->second.Values.size() == 0)
      continue;

    int64_t ThisOffset = it->first.first - ptrOffset;
    release_assert(ThisOffset >= 0);
    
    Value* OffsetCI = ConstantInt::get(I64, (uint64_t)ThisOffset);
    Value* ElPtr = GetElementPtrInst::Create(writtenPtr, ArrayRef<Value*>(&OffsetCI, 1), "", emitBB);

    Type* TargetType = PointerType::getUnqual(it->second.Values[0].V.getType());
    if(!TargetType->isInt8Ty())
      ElPtr = new BitCastInst(ElPtr, TargetType, "", emitBB);

    Value* Loaded = new LoadInst(ElPtr, "", emitBB);

    Value* thisCheck = emitCompareCheck(Loaded, IVS->second, emitBB);
    if(!prevCheck)
      prevCheck = thisCheck;
    else
      prevCheck = BinaryOperator::CreateAnd(prevCheck, thisCheck, "", emitBB);

  }

  return prevCheck;

}

SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator
IntegrationAttempt::emitOrdinaryInstCheck(SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitIt, ShadowInstruction* SI) {

  BasicBlock* emitBB = (emitIt++)->first;
  Value* Check;

  if(inst_is<MemTransferInst>(SI))
    Check = emitMemcpyCheck(SI, emitBB);
  else
    Check = emitAsExpectedCheck(SI, emitBB);
    
  BasicBlock* successTarget = *emitIt;
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(SI->parent->invar->idx, SI->invar->idx + 1);

  BranchInst::Create(successTarget, failTarget, Check, emitBB);

  return emitIt;

}
