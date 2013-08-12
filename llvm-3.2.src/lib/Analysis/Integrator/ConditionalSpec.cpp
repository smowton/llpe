
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"

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

void IntegrationAttempt::initFailedBlockCommit() {}

void InlineAttempt::initFailedBlockCommit() {

  failedBlocks.resize(nBBs);
  failedBlockMap = new ValueToValueMapTy();
  PHIForwards = new DenseMap<std::pair<Instruction*, Use*>, PHINode*>();
  ForwardingPHIs = new DenseSet<PHINode*>();

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

void InlineAttempt::emitPathConditionCheck(PathCondition& Cond, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator& emitBlockIt) {

  if(stackIdx != Cond.fromStackIdx || BB->invar->BB != Cond.fromBB)
    return;

  BasicBlock* emitBlock = (emitBlockIt++)->first;

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

  BranchInst::Create(emitBlockIt->first, failedBlocks[BB->invar->idx].front().first, resultInst, emitBlock);

}

void InlineAttempt::emitPathConditionChecksIn(std::vector<PathCondition>& Conds, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator& emitBlockIt) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it)
    emitPathConditionCheck(*it, Ty, BB, stackIdx, emitBlockIt);

}

SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator IntegrationAttempt::emitPathConditionChecks(ShadowBB* BB) { 

  // No path conditions within loops at the moment.
  return BB->committedBlocks.begin();

}

SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator InlineAttempt::emitPathConditionChecks(ShadowBB* BB) {

  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it = BB->committedBlocks.begin();

  IATargetInfo* Info = BB->IA->getFunctionRoot()->targetCallInfo;
  if(!Info)
    return it;

  emitPathConditionChecksIn(pass->rootIntPathConditions, PathConditionTypeInt, BB, Info->targetStackDepth, it);
  emitPathConditionChecksIn(pass->rootStringPathConditions, PathConditionTypeString, BB, Info->targetStackDepth, it);
  emitPathConditionChecksIn(pass->rootIntmemPathConditions, PathConditionTypeIntmem, BB, Info->targetStackDepth, it);

  return it;
  
}

BasicBlock::iterator InlineAttempt::skipMergePHIs(BasicBlock::iterator it) {

  PHINode* PN;
  while((PN = dyn_cast<PHINode>(it)) && ForwardingPHIs->count(PN))
    ++it;

  return it;

}

bool InlineAttempt::isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx) {

  if(targetCallInfo && !targetCallInfo->mayReachTarget.count(BBIdx)) {  

    if(predBlockIdx != targetCallInfo->targetCallBlock && targetCallInfo->mayReachTarget.count(predBlockIdx) && blocksReachableOnFailure.count(predBlockIdx)) {
      
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
  bool fallThrough = false;

  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->failedReturnBlock)
      edges.push_back(std::make_pair(IA->failedReturnBlock, this));
    else 
      fallThrough = true;
    added = true;

  }

  if(fallThrough || requiresRuntimeCheck(ShadowValue(SI))) {

    edges.push_back(std::make_pair(BB->getCommittedBlockAt(instIdx), this));
    added = true;
    
  }

  if(added && L)
    return 1;
  else
    return 0;

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

BasicBlock::iterator InlineAttempt::commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator PCPredsBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator PCPredsEnd) {

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

  uint32_t instIdx = 0;

  for(BasicBlock::iterator BE = BB->end(); BI != BE && isa<PHINode>(BI); ++BI, ++instIdx) {

    ShadowInstructionInvar* PNInfo = &BBI->insts[instIdx];
    PHINode* OrigPN = cast<PHINode>(PNInfo->I);
    PHINode* PN = cast<PHINode>(BI);

    createForwardingPHIs(*PNInfo, PN);

    SmallVector<std::pair<Value*, BasicBlock*>, 4> newPreds;

    for(uint32_t i = 0, ilim = PNInfo->operandBBs.size(); i != ilim; ++i) {

      uint32_t predBlockIdx = PNInfo->operandBBs[i];
      ShadowInstIdx predOp = PNInfo->operandIdxs[i];
      Value* predV = OrigPN->getIncomingValue(i);

      Value* unspecV = getUnspecValue(predOp.blockIdx, predOp.instIdx, predV, &OrigPN->getOperandUse(i));
      Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV);

      BasicBlock* specPred;
      if(isSpecToUnspecEdge(predBlockIdx, BBIdx))
	specPred = getBB(predBlockIdx)->committedBlocks.back().first;
      else
	specPred = 0;

      BasicBlock* unspecPred;
      if(failedBlocks[predBlockIdx].size())
	unspecPred = failedBlocks[predBlockIdx].back().first;
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

    for(SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator PCIt = PCPredsBegin; 
	PCIt != PCPredsEnd; ++PCIt)
      newPreds.push_back(std::make_pair(PCVal, PCIt->first));

    // Clear node:
    for(uint32_t i = PN->getNumIncomingValues(); i > 0; --i)
      PN->removeIncomingValue(i - 1, false);

    // Populate node:
    for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator it = newPreds.begin(),
	  itend = newPreds.end(); it != itend; ++it) {

      release_assert(it->first);
      PN->addIncoming(it->first, it->second);

    }

  }

  return BI;

}

void InlineAttempt::markBBAndPreds(ShadowBBInvar* UseBBI, uint32_t instIdx, std::vector<std::pair<Instruction*, uint32_t> >& predBlocks, ShadowBBInvar* LimitBBI) {

  if(instIdx == ((uint32_t)-1))
    instIdx = UseBBI->insts.size();
  
  if(UseBBI == LimitBBI) {
    if(predBlocks[0].second < instIdx)
      predBlocks[0].second = instIdx;
    return;
  }

  release_assert(UseBBI->idx > LimitBBI->idx);
  uint32_t relIdx = UseBBI->idx - LimitBBI->idx;
  if(relIdx >= predBlocks.size())
    predBlocks.resize(relIdx + 1, std::make_pair<Instruction*, uint32_t>(0, 0));

  if(predBlocks[relIdx].first) {
    if(predBlocks[relIdx].second < instIdx)
      predBlocks[relIdx].second = instIdx;
    return;
  }
  
  predBlocks[relIdx] = std::make_pair((Instruction*)ULONG_MAX, instIdx);

  for(uint32_t i = 0, ilim = UseBBI->predIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* PredBBI = getBBInvar(UseBBI->predIdxs[i]);
    markBBAndPreds(PredBBI, (uint32_t)-1, predBlocks, LimitBBI);

  }

}

void InlineAttempt::remapBlockUsers(ShadowInstructionInvar& SI, BasicBlock* BB, PHINode* Replacement) {

  Instruction* I = SI.I;

  for(Instruction::use_iterator UI = I->use_begin(), UE = I->use_end(); UI != UE; ++UI) {

    Instruction* UseInst = cast<Instruction>(*UI);
    if(UseInst->getParent()->getParent() != &F) {

      // Spurious user due to block cloning
      continue;

    }

    // If the user maps to a cloned instruction in block BB...
    if(cast<Instruction>((*failedBlockMap)[UseInst])->getParent() == BB) {

      std::pair<Instruction*, Use*> K = std::make_pair(SI.I, &UI.getUse());
      (*PHIForwards)[K] = Replacement;

    }

  }

}

static PHINode* insertMergePHI(ShadowInstructionInvar& SI, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& specPreds, SmallVector<std::pair<BasicBlock*, Instruction*>, 4>& unspecPreds, BasicBlock* InsertBB) {

  PHINode* NewNode = PHINode::Create(SI.I->getType(), 0, "clonemerge", InsertBB->begin());

  for(SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>::iterator it = specPreds.begin(), itend = specPreds.end(); it != itend; ++it) {

    BasicBlock* PredBB = it->first;
    Value* Op = getValAsType(it->second->getSpecValue(SI.parent->idx, SI.idx, SI.I), NewNode->getType(), 
			     PredBB->getTerminator());
    release_assert(Op);
    NewNode->addIncoming(Op, PredBB);
      
  }

  for(SmallVector<std::pair<BasicBlock*, Instruction*>, 4>::iterator it = unspecPreds.begin(), itend = unspecPreds.end(); it != itend; ++it) {

    NewNode->addIncoming(it->second, it->first);
	  
  }

  return NewNode;

}

void InlineAttempt::createForwardingPHIs(ShadowInstructionInvar& OrigSI, Instruction* NewI) {

  // OrigSI is an instruction in the function being specialised; NewI is its failed clone.
  // If the instruction needs PHI forwarding, add PHI nodes in each (cloned) block where this is necessary.
  // The specialised companion(s) of this instruction have been created already so getSpecValue works.

  // Note that NewI might be in a different block to failedBlockMap[OrigSI.I->Parent] due to forwarding
  // performed before now. failedBlockMap[OrigSI.I] has been updated to point to NewI however.
  // We should start merging from the block after wherever NewI is defined, and use NewI rather than anything 
  // directly derived from OrigSI when forwarding.

  std::vector<std::pair<Instruction*, uint32_t> > predBlocks(1, std::make_pair(NewI, OrigSI.idx));

  // 1. Find the predecessor blocks for each user, setting the vector cell for each (original program)
  // block that reaches a user to ULONG_MAX.

  for(uint32_t i = 0, ilim = OrigSI.userIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* UseBBI = getBBInvar(OrigSI.userIdxs[i].blockIdx);
    markBBAndPreds(UseBBI, OrigSI.userIdxs[i].instIdx, predBlocks, OrigSI.parent);

  }

  // 2. Proceed forwards through those blocks, inserting forwarding each time there is a merge from
  // specialised code and each time conflicting versions of the forwarded value are presented
  // by block predecessors.

  for(uint32_t i = 0, ilim = predBlocks.size(); i != ilim; ++i) {

    // Not needed here?
    if(!predBlocks[i].first)
      continue;

    uint32_t thisBlockIdx = (OrigSI.parent->idx + i);
    ShadowBBInvar* thisBBI = getBBInvar(thisBlockIdx);

    Instruction* thisBlockInst;
    bool instDefined = false;

    if(i != 0) {

      // Top of block: merge the value if the block is a spec-to-unspec
      // merge point (path conditions, etc) or if there are conflicting unspec
      // definitions or both.

      uint32_t nCondsHere;
      ShadowBB* thisBB = getBB(thisBlockIdx);
      if(thisBB)
	nCondsHere = pass->countPathConditionsForBlock(thisBB);
      else
	nCondsHere = 0;

      bool isSpecToUnspec = isSimpleMergeBlock(thisBlockIdx);

      bool shouldMergeHere = nCondsHere != 0 || isSpecToUnspec;
      if(!shouldMergeHere) {

	Instruction* UniqueIncoming = 0;
	for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	  uint32_t predRelIdx = thisBBI->predIdxs[j] - OrigSI.parent->idx;
	  release_assert(predRelIdx < predBlocks.size());
	  Instruction* predInst = predBlocks[predRelIdx].first;
	  release_assert(predInst);
	  if(!UniqueIncoming)
	    UniqueIncoming = predInst;
	  else if(UniqueIncoming != predInst) {
	    UniqueIncoming = 0;
	    break;
	  }

	}

	if(!UniqueIncoming)
	  shouldMergeHere = true;

      }

      BasicBlock* insertBlock = failedBlocks[thisBlockIdx].front().first;

      if(shouldMergeHere) {

	SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> specPreds;
	SmallVector<std::pair<BasicBlock*, Instruction*>, 4> unspecPreds;

	if(isSpecToUnspec) {

	  // Some specialised predecessors branch straight to unspec code.
	  for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	    uint32_t pred = thisBBI->predIdxs[j];

	    if(isSpecToUnspecEdge(pred, thisBlockIdx))
	      specPreds.push_back(std::make_pair(getBB(pred)->committedBlocks.back().first, this));

	  }

	}
	if(nCondsHere) {

	  // The first n specialised blocks are specialised predecessors.
	  for(uint32_t k = 0, klim = nCondsHere; k != klim; ++k)
	    specPreds.push_back(std::make_pair(thisBB->committedBlocks[k].first, this));

	}

	for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	  uint32_t pred = thisBBI->predIdxs[j];
	  uint32_t relidx = pred - OrigSI.parent->idx;
	  unspecPreds.push_back(std::make_pair(failedBlocks[pred].back().first, predBlocks[relidx].first));

	}

	// Further subdivisions of this block should use the new PHI
	thisBlockInst = insertMergePHI(OrigSI, specPreds, unspecPreds, insertBlock);
	ForwardingPHIs->insert(cast<PHINode>(thisBlockInst));
	
      }
      else {
	
	// Further subdivisions of this block should use the same value as our predecessors
	// The preds necessarily match so just use the first.
	thisBlockInst = predBlocks[thisBBI->predIdxs[0] - OrigSI.parent->idx].first;

      }

      // Map instruction users to the appropriate local forward:
      if(thisBlockInst != NewI)
	remapBlockUsers(OrigSI, insertBlock, cast<PHINode>(thisBlockInst));
      
    }
    else {

      // This is the subblock that defines NewI, or one of its preds; just use it.
      thisBlockInst = NewI;
      if(failedBlocks[thisBlockIdx].front().first == NewI->getParent())
	instDefined = true;

    }

    // Now apply a similar process to each subblock:

    SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it = failedBlocks[thisBlockIdx].begin(),
      itend = failedBlocks[thisBlockIdx].end();
    ++it;
    for(; it != itend; ++it) {

      // This is the head and instruction not defined yet?
      if(i == 0 && !instDefined) {

	if(it->first == NewI->getParent()) {
	  // Defined here
	  instDefined = true;
	  continue;
	}

      }

      // Not needed at this offset?
      if(it->second > predBlocks[i].second)
	break;

      // If a block break exists, then there must be some cause to merge.
      SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> specPreds;
      collectSpecIncomingEdges(thisBBI->idx, it->second - 1, specPreds);

      SmallVector<std::pair<BasicBlock*, Instruction*>, 4> unspecPreds;
      SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator previt = it;
      --previt;
      unspecPreds.push_back(std::make_pair(previt->first, thisBlockInst));

      thisBlockInst = insertMergePHI(OrigSI, specPreds, unspecPreds, it->first);
      ForwardingPHIs->insert(cast<PHINode>(thisBlockInst));

      remapBlockUsers(OrigSI, it->first, cast<PHINode>(thisBlockInst));

    }
    
    predBlocks[i].first = thisBlockInst;

  }

}

bool IntegrationAttempt::hasSpecialisedCompanion(ShadowBBInvar* BBI) {

  if(getBB(*BBI))
    return true;

  PeelAttempt* LPA;
  if(BBI->naturalScope != L && 
     ((!L) || L->contains(BBI->naturalScope)) && 
     (LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) && 
     LPA->isTerminated() && 
     LPA->isEnabled()) {

    for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
      if(LPA->Iterations[i]->hasSpecialisedCompanion(BBI))
	return true;

  }

  return false;

}

void InlineAttempt::remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t idx, uint32_t instIdx, bool skipTerm) {

  // Map each instruction operand to the most local PHI translation of the target instruction,
  // or if that doesn't exist the specialised version.

  // If this block is a non-final subblock (i.e. skipTerm is true) then skip creating
  // PHI forwards of the second-to-last instruction (i.e. the instruction before the terminator)
  // as that will be special-cased in populateFailedBlock at the start of the next subblock.

  BasicBlock::iterator BE = BB->end();
  Instruction* testedInst;
  if(skipTerm) {
    --BE;
    --BE;
    testedInst = BE;
    ++BE;
  }
  else
    testedInst = 0;

  ShadowBBInvar* BBI = getBBInvar(idx);

  bool anySpecialisedCompanions = hasSpecialisedCompanion(BBI);

  for(; BI != BE; ++BI, ++instIdx) {

    ShadowInstructionInvar& SII = BBI->insts[instIdx];
    Instruction* I = BI;
    
    ReturnInst* RI = dyn_cast<ReturnInst>(BI);
    if(RI && !isRootMainCall()) {

      if(failedReturnBlock) {

	// Rewrite into a branch to and contribution to the failed return phi node.
	if(failedReturnPHI) {

	  Use* U = &RI->getOperandUse(0);
	  Value* Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, *U, U);
	  release_assert(Ret);
	  failedReturnPHI->addIncoming(Ret, BB);

	}

	RI->eraseFromParent();
	BranchInst::Create(failedReturnBlock, BB);

      }
      else {

	// Out-of-line commit
	Value* Ret;
	Value* FailFlag = ConstantInt::getFalse(BB->getContext());
	
	if(F.getFunctionType()->getReturnType()->isVoidTy())
	  Ret = FailFlag;
	else {

	  Use* U = &RI->getOperandUse(0);
	  Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, *U, U);
	  StructType* retType = cast<StructType>(CommitF->getFunctionType()->getReturnType());
	  Type* normalRet = Ret->getType();
	  Constant* undefRet = UndefValue::get(normalRet);
	  Value* aggTemplate = ConstantStruct::get(retType, undefRet, FailFlag, NULL);
	  Ret = InsertValueInst::Create(aggTemplate, Ret, 0, "fail_ret", RI);

	}
	
	// Existing RI might have wrong operand count, so replace it.
	ReturnInst::Create(BB->getContext(), Ret, RI);
	RI->eraseFromParent();

      }

      // Bail out since we just ate the loop's controlling iterator
      return;

    }
    else {

      if(anySpecialisedCompanions && I != testedInst && !SII.I->getType()->isVoidTy())
	createForwardingPHIs(SII, I);

      uint32_t opIdx = 0;
      Instruction::op_iterator replit = I->op_begin();

      for(Instruction::op_iterator it = SII.I->op_begin(), itend = SII.I->op_end(); it != itend; ++it, ++opIdx, ++replit) {

	Use* U = it;
	Value* V = *U;

	ShadowInstIdx& op = SII.operandIdxs[opIdx];

	Value* Repl;
	if(isa<BasicBlock>(V))
	  Repl = (*failedBlockMap)[V];
	else
	  Repl = getUnspecValue(op.blockIdx, op.instIdx, V, U);

	((Use*)replit)->set(Repl);

      }

    }

  }

}

void IntegrationAttempt::commitSimpleFailedBlock(uint32_t i) { }

void InlineAttempt::commitSimpleFailedBlock(uint32_t i) {

  if(failedBlocks[i].empty())
    return;

  release_assert(failedBlocks[i].size() == 1 && "commitSimpleFailedBlock with a split block?");

  BasicBlock* CommitBB = failedBlocks[i].front().first;
  BasicBlock::iterator BI = skipMergePHIs(CommitBB->begin());
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

void IntegrationAttempt::createFailedBlock(uint32_t idx) {}

void InlineAttempt::createFailedBlock(uint32_t idx) {

  SmallDenseMap<uint32_t, uint32_t, 8>::iterator it = blocksReachableOnFailure.find(idx);
  if(it == blocksReachableOnFailure.end())
    return;

  uint32_t createFailedBlockFrom = it->second;

  ShadowBBInvar* BBI = getBBInvar(idx);
  BasicBlock* NewBB = CloneBasicBlockFrom(BBI->BB, *failedBlockMap, "", CommitF, createFailedBlockFrom);
  std::string newName;
  {
    raw_string_ostream RSO(newName);
    RSO << getCommittedBlockPrefix() << BBI->BB->getName() << " (failed)";
  }

  NewBB->setName(newName);
  failedBlocks[idx].push_back(std::make_pair(NewBB, createFailedBlockFrom));
  (*failedBlockMap)[BBI->BB] = NewBB;

  bool splitInsts[BBI->insts.size()];
  memset(splitInsts, 0, sizeof(bool) * BBI->insts.size());
  getSplitInsts(BBI, splitInsts);

  release_assert((!splitInsts[BBI->insts.size() - 1]) && "Can't split after terminator");

  uint32_t instsSinceLastSplit = 0;
  for(uint32_t i = 0, ilim = BBI->insts.size(); i != ilim; ++i) {

    if(splitInsts[i]) {

      // No need to split (first sub-block?)
      if(i + 1 == createFailedBlockFrom)
	continue;

      BasicBlock* toSplit = failedBlocks[idx].back().first;
      uint32_t instsToSplit = std::min((i+1) - createFailedBlockFrom, instsSinceLastSplit + 1);
      BasicBlock::iterator splitIterator = toSplit->begin();
      std::advance(splitIterator, instsToSplit);
      BasicBlock* splitBlock = 
	toSplit->splitBasicBlock(splitIterator, toSplit->getName() + ".checksplit");
      failedBlocks[idx].push_back(std::make_pair(splitBlock, i + 1));

      instsSinceLastSplit = 0;

    }
    else {
      
      ++instsSinceLastSplit;

    }

  }

}

BasicBlock* InlineAttempt::getSubBlockForInst(uint32_t blockIdx, uint32_t instIdx) {

  release_assert(failedBlocks[blockIdx].size() && "Failed block should exist");
  
  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>& splits = failedBlocks[blockIdx];
  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it = splits.begin(), itend = splits.end();

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
	LPA->Iterations[i]->collectSpecPreds(predBlock, predIdx, instBlock, instIdx, preds);

      return;

    }

  }

  ShadowBB* InstBB = getBB(*instBlock);
  ShadowInstruction* SI = &InstBB->insts[instIdx];

  ShadowBB* PredBB = getBB(*predBlock);
  if(!PredBB)
    return;

  BasicBlock* pred = PredBB->getCommittedBlockAt(predIdx);
  Value* committedVal = getCommittedValue(ShadowValue(SI));

  preds.push_back(std::make_pair(committedVal, pred));

}

void IntegrationAttempt::collectCallFailingEdges(ShadowBBInvar* predBlock, uint32_t predIdx, ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds) {
  
  if(L != predBlock->naturalScope && ((!L) || L->contains(predBlock->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, predBlock->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->collectCallFailingEdges(predBlock, predIdx, instBlock, instIdx, preds);

      return;

    }

  }

  ShadowBB* InstBB = getBB(*instBlock);
  if(!InstBB)
    return;

  ShadowInstruction* SI = &InstBB->insts[instIdx];

  InlineAttempt* IA;
  bool fallThrough = false;

  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->commitsOutOfLine())
      fallThrough = true;    
    else if(IA->failedReturnPHI)
      preds.push_back(std::make_pair(IA->failedReturnPHI, IA->failedReturnBlock));

  }
  if(fallThrough || requiresRuntimeCheck(SI)) {

    ShadowBB* PredBB = getBB(*predBlock);
    BasicBlock* pred = PredBB->getCommittedBlockAt(predIdx);
    Value* committedVal = getCommittedValue(ShadowValue(&InstBB->insts[instIdx]));
    preds.push_back(std::make_pair(committedVal, pred));
    
  }

}

void IntegrationAttempt::populateFailedBlock(uint32_t idx, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondBegin, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathCondEnd) { }

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
    BasicBlock::iterator BI = skipMergePHIs(it->first->begin());
    BasicBlock::iterator PostPHIBI = commitFailedPHIs(it->first, BI, idx, pathCondBegin, pathCondEnd);

    remapFailedBlock(PostPHIBI, it->first, idx, std::distance(BI, PostPHIBI), it != lastit);

    ++it;

  }

  for(; it != endit; ++it) {

    release_assert(it->second != 0);

    // PHI node checks are done as a group; all others are tested one at a time.
    // Find the bounds of the group.

    uint32_t failedInstLim = it->second;
    uint32_t firstFailedInst = failedInstLim - 1;
    
    uint32_t insertedPHIs = 0;

    while(firstFailedInst != 0 && 
	  isa<PHINode>(BBI->insts[firstFailedInst].I) && 
	  isa<PHINode>(BBI->insts[firstFailedInst - 1].I))
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
	for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator specit = specPreds.begin(),
	      specend = specPreds.end(); specit != specend; ++specit) {
	  release_assert(specit->first);
	  NewPN->addIncoming(specit->first, specit->second);
	}

	if(it != failedBlocks[idx].begin()) {

	  // There is an unspecialised predecessor to this subblock. Merge the unspecialised pred.
	  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator predIt = it;
	  --predIt;

	  Value* NewV = getUnspecValue(idx, failedInst, failedI, &failedI->use_begin().getUse());
	  release_assert(NewV);
	  NewPN->addIncoming(NewV, predIt->first);

	}

	(*failedBlockMap)[failedI] = NewPN;

	// Insert PHI forwarding of this merge where necessary:
	createForwardingPHIs(BBI->insts[failedInst], NewPN);

      }

    }

    BasicBlock::iterator BI = skipMergePHIs(it->first->begin());
    
    // Skip past previously introduced PHI nodes to the normal instructions
    std::advance(BI, insertedPHIs);

    // Remap the normal instructions
    remapFailedBlock(BI, it->first, idx, it->second, it != lastit);

  }
  
}

Value* IntegrationAttempt::emitCompareCheck(Value* realInst, ImprovedValSetSingle* IVS, BasicBlock* emitBB) {

  release_assert(isa<Instruction>(realInst) && "Checked instruction must be residualised");

  Value* thisCheck = 0;
  for(uint32_t j = 0, jlim = IVS->Values.size(); j != jlim; ++j) {

    Value* thisVal = trySynthVal(0, realInst->getType(), IVS->SetType, IVS->Values[j], emitBB);
    Value* newCheck;
    if(thisVal->getType()->isFloatingPointTy())
      newCheck = new FCmpInst(*emitBB, CmpInst::FCMP_OEQ, realInst, thisVal, "check");
    else
      newCheck = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, realInst, thisVal, "check");

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

  if(!IVS) {

    Type* I64 = Type::getInt64Ty(emitBB->getContext());
    Value* PrevCheck = 0;

    // Check each non-overdef element of the source inst.
    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(SI->i.PB);
    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

      if(it.val().isWhollyUnknown())
	continue;

      // Shift value to least significant position:
      Constant* ShiftAmt = ConstantInt::get(I64, it.start());
      Value* Shifted = BinaryOperator::CreateLShr(realInst, ShiftAmt, "", emitBB);
      
      // Truncate to size:
      Type* SubTy = Type::getIntNTy(emitBB->getContext(), (it.stop() - it.start()) * 8);
      Value* Truncated = new TruncInst(Shifted, SubTy, "", emitBB);

      Value* ThisCheck = emitCompareCheck(Truncated, &it.val(), emitBB);
      if(!PrevCheck)
	PrevCheck = ThisCheck;
      else
	PrevCheck = BinaryOperator::CreateAnd(PrevCheck, ThisCheck, "", emitBB);
      
    }

    return PrevCheck;

  }
  else {

    return emitCompareCheck(realInst, IVS, emitBB);

  }

}

SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator
IntegrationAttempt::emitExitPHIChecks(SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitIt, ShadowBB* BB) {

  BasicBlock* emitBB = (emitIt++)->first;
  Value* prevCheck = 0;

  uint32_t i, ilim;
  for(i = 0, ilim = BB->invar->insts.size(); i != ilim && inst_is<PHINode>(&BB->insts[i]); ++i) {
    
    ShadowInstruction* SI = &BB->insts[i];

    Value* thisCheck = emitAsExpectedCheck(SI, emitBB);

    if(prevCheck)
      prevCheck = BinaryOperator::CreateAnd(thisCheck, prevCheck, "", emitBB);
    else
      prevCheck = thisCheck;

  }

  BasicBlock* successTarget = emitIt->first;
  // i is the index of the first non-PHI at this point.
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, i);

  BranchInst::Create(successTarget, failTarget, emitBB); 

  return emitIt;

}

Value* IntegrationAttempt::emitMemcpyCheck(ShadowInstruction* SI, BasicBlock* emitBB) {

  release_assert(SI->memcpyValues && SI->memcpyValues->size() && "memcpyValues not set for checked copy?");

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
    if(ElPtr->getType() != TargetType)
      ElPtr = new BitCastInst(ElPtr, TargetType, "", emitBB);

    Value* Loaded = new LoadInst(ElPtr, "", emitBB);

    Value* thisCheck = emitCompareCheck(Loaded, &it->second, emitBB);
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
    
  BasicBlock* successTarget = emitIt->first;
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(SI->parent->invar->idx, SI->invar->idx + 1);

  BranchInst::Create(successTarget, failTarget, Check, emitBB);

  return emitIt;

}
