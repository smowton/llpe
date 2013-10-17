
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/MathExtras.h"

using namespace llvm;

extern cl::opt<bool> VerboseNames;

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

bool IntegrationAttempt::tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef) {

  if(invarInfo->pathConditions) {

    if(tryGetPathValueFrom(*invarInfo->pathConditions, UINT_MAX, V, UserBlock, Result, asDef))
      return true;

  }

  return false;

}

bool InlineAttempt::tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef) {

  if(targetCallInfo) {
   
    if(tryGetPathValueFrom(pass->pathConditions, targetCallInfo->targetStackDepth, V, UserBlock, Result, asDef))
      return true;

  }

  return IntegrationAttempt::tryGetPathValue2(V, UserBlock, Result, asDef);

}

bool IntegrationAttempt::tryGetPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result) {

  return tryGetPathValue2(V, UserBlock, Result, false);

}

bool IntegrationAttempt::tryGetAsDefPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result) {

  return tryGetPathValue2(V, UserBlock, Result, true);

}

bool IntegrationAttempt::tryGetPathValueFrom(PathConditions& PC, uint32_t myStackDepth, ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef) {

  ShadowInstruction* SI = V.getInst();
  ShadowArg* SA = V.getArg();
  if((!SI) && (!SA))
    return false;

  std::vector<PathCondition>& PCs = asDef ? PC.AsDefIntPathConditions : PC.IntPathConditions;

  for(std::vector<PathCondition>::iterator it = PCs.begin(), itend = PCs.end(); it != itend; ++it) {

    /* fromStackIdx must equal instStackIdx for this kind of condition */

    if(it->instStackIdx == myStackDepth) {
      
      bool match = false;

      if(SI && 
	 it->instBB == SI->parent->invar->BB &&
	 it->instIdx == SI->invar->idx) {

	if(getFunctionRoot()->DT->dominates(it->fromBB, UserBlock->invar->BB))
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
	getFunctionRoot()->markBlockAndSuccsFailed(fromBlockIdx, 0);

	Result.first = ValSetTypeScalar;
	Result.second.V = it->val;
	return true;
	
      }

    }

  }

  return false;

}

InlineAttempt* llvm::getIAWithTargetStackDepth(InlineAttempt* IA, uint32_t depth) {

  if(depth == UINT_MAX)
    return IA;

  release_assert(IA->targetCallInfo);
  if(IA->targetCallInfo->targetStackDepth == depth)
    return IA;

  release_assert(depth < IA->targetCallInfo->targetStackDepth);
  IntegrationAttempt* par = IA->getUniqueParent();
  release_assert(par && "Can't share functions in the target stack!");
  return getIAWithTargetStackDepth(par->getFunctionRoot(), depth);

}

ShadowValue IntegrationAttempt::getPathConditionOperand(uint32_t stackIdx, BasicBlock* BB, uint32_t instIdx) {

  if(!BB) {
    
    ShadowGV* GV = &(GlobalIHP->shadowGlobals[instIdx]);
    return ShadowValue(GV);
    
  }

  IntegrationAttempt* ptrIA;
  if(stackIdx == UINT_MAX)
    ptrIA = this;
  else
    ptrIA = getIAWithTargetStackDepth(getFunctionRoot(), stackIdx);
  
  if(BB == (BasicBlock*)ULONG_MAX) {

    ShadowArg* ptr = &ptrIA->getFunctionRoot()->argShadows[instIdx];
    return ShadowValue(ptr);

  }
  else {
    
    uint32_t ptrBBIdx = findBlock(ptrIA->invarInfo, BB->getName());
    return ShadowValue(ptrIA->getInst(ptrBBIdx, instIdx));

  }

}

void IntegrationAttempt::applyPathCondition(PathCondition* it, PathConditionTypes condty, ShadowBB* BB, uint32_t targetStackDepth) {

  // UINT_MAX signifies a path condition that applies to all instances of this function.

  if(it->fromStackIdx == targetStackDepth && it->fromBB == BB->invar->BB) {

    ShadowValue ptrSV = getPathConditionOperand(it->instStackIdx, it->instBB, it->instIdx);
    ImprovedValSetSingle writePtr;
    if(!getImprovedValSetSingle(ptrSV, writePtr))
      return;

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
      executeCopyInst(ptrSV.isGV() ? 0 : &ptrSV, writePtr, copyFromPointer, Size, &(BB->insts[0]));

    }
    else {
      
      // IntMem condition
      
      ImprovedValSetSingle writeVal;
      getImprovedValSetSingle(ShadowValue(it->val), writeVal);

      // Attribute the effect of the write to first instruction in block:
      executeWriteInst(0, writePtr, writeVal, GlobalAA->getTypeStoreSize(it->val->getType()), &(BB->insts[0]));

    }

    // Make sure a failed version of this block and its successors is created:
    getFunctionRoot()->markBlockAndSuccsFailed(BB->invar->idx, 0);

  }

}

void llvm::clearAsExpectedChecks(ShadowBB* BB) {

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i)
    BB->insts[i].needsRuntimeCheck = RUNTIME_CHECK_NONE;

}

void IntegrationAttempt::noteAsExpectedChecksFrom(ShadowBB* BB, std::vector<PathCondition>& PCs, uint32_t stackIdx) {

  for(std::vector<PathCondition>::iterator it = PCs.begin(), itend = PCs.end(); it != itend; ++it) {

    if(it->fromStackIdx == stackIdx && it->fromBB == BB->invar->BB) {

      release_assert(it->fromStackIdx == it->instStackIdx && it->fromBB == it->instBB);

      // This flag indicates the path condition should be checked on definition, rather than
      // at the top of the block as for conditions that don't always apply.
      BB->insts[it->instIdx].needsRuntimeCheck = RUNTIME_CHECK_AS_EXPECTED;
      
    }

  }

}

void IntegrationAttempt::noteAsExpectedChecks(ShadowBB* BB) {

  if(invarInfo->pathConditions)
    noteAsExpectedChecksFrom(BB, invarInfo->pathConditions->AsDefIntPathConditions, UINT_MAX);

}

void InlineAttempt::noteAsExpectedChecks(ShadowBB* BB) {

  if(targetCallInfo)
    noteAsExpectedChecksFrom(BB, pass->pathConditions.AsDefIntPathConditions, targetCallInfo->targetStackDepth);

  IntegrationAttempt::noteAsExpectedChecks(BB);

}

void IntegrationAttempt::applyMemoryPathConditions(ShadowBB* BB) {
  
  if(invarInfo->pathConditions)
    applyMemoryPathConditionsFrom(BB, *invarInfo->pathConditions, UINT_MAX);

}

void InlineAttempt::applyMemoryPathConditions(ShadowBB* BB) {

  if(targetCallInfo)
    applyMemoryPathConditionsFrom(BB, pass->pathConditions, targetCallInfo->targetStackDepth);

  IntegrationAttempt::applyMemoryPathConditions(BB);

}

void IntegrationAttempt::applyMemoryPathConditionsFrom(ShadowBB* BB, PathConditions& PC, uint32_t targetStackDepth) {

  for(std::vector<PathCondition>::iterator it = PC.StringPathConditions.begin(),
	itend = PC.StringPathConditions.end(); it != itend; ++it) {

    applyPathCondition(&*it, PathConditionTypeString, BB, targetStackDepth);

  }

  for(std::vector<PathCondition>::iterator it = PC.IntmemPathConditions.begin(),
	itend = PC.IntmemPathConditions.end(); it != itend; ++it) {  

    applyPathCondition(&*it, PathConditionTypeIntmem, BB, targetStackDepth);

  }

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(),
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx == targetStackDepth && it->BB == BB->invar->BB) {

      // Insert a model call that notionally occurs before the block begins.
      // Notionally its callsite is the first instruction in BB; this is probably not a call
      // instruction, but since its arguments are pushed in rather than pulled it doesn't matter.

      if(!it->IA) {
	InlineAttempt* SymIA = new InlineAttempt(pass, *it->F, this->LI, &BB->insts[0], this->nesting_depth + 1, true);
	it->IA = SymIA;
      }

      for(unsigned i = 0, ilim = it->args.size(); i != ilim; ++i) {

	PathFuncArg& A = it->args[i];

	ShadowArg* SArg = &(it->IA->argShadows[i]);
	ShadowValue Op = getPathConditionOperand(A.stackIdx, A.instBB, A.instIdx);
    
	release_assert((!SArg->i.PB) && "Path condition functions shouldn't be reentrant");

	copyImprovedVal(Op, SArg->i.PB);
	noteIndirectUse(ShadowValue(SArg), SArg->i.PB);

      }

      it->IA->activeCaller = &BB->insts[0];
      it->IA->analyseNoArgs(false, false, stack_depth);

      doCallStoreMerge(BB, it->IA);

      // Make sure a failed version of this block and its successors is created:
      getFunctionRoot()->markBlockAndSuccsFailed(BB->invar->idx, 0);

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

  // We won't need PHIForwards or ForwardingPHIs until the instruction commit phase;
  // they will remain 0-sized and unallocated until then.
  // failedBlockMap only needs to hold a little more than one entry per failed block here.
  // Add a fudge factor to (a) avoid resizes to 64 and (b) account for path condition splits.

  // If there aren't any failed blocks, we don't need any of these!
  if(blocksReachableOnFailure.empty()) {
    failedBlockMap = 0;
    PHIForwards = 0;
    ForwardingPHIs = 0;
    return; 
  }

  failedBlocks.resize(nBBs);
  failedBlockMap = new ValueToValueMapTy(NextPowerOf2((blocksReachableOnFailure.size() * 3) - 1));
  PHIForwards = new DenseMap<std::pair<Instruction*, BasicBlock*>, PHINode*>();
  ForwardingPHIs = new DenseSet<PHINode*>();

}

void IntegrationAttempt::finishFailedBlockCommit() {}

void InlineAttempt::finishFailedBlockCommit() {

  delete failedBlockMap; failedBlockMap = 0;
  delete PHIForwards; PHIForwards = 0;
  delete ForwardingPHIs; ForwardingPHIs = 0;

}

struct matchesFromIdx {

  BasicBlock* BB;
  uint32_t stackIdx;

  bool operator()(PathCondition& C) { 

    return C.fromBB == BB && C.fromStackIdx == stackIdx; 

  }

  matchesFromIdx(BasicBlock* _BB, uint32_t si) : BB(_BB), stackIdx(si) {}

};

static uint32_t countPathConditionsIn(BasicBlock* BB, uint32_t stackIdx, std::vector<PathCondition>& Conds) {

  matchesFromIdx Pred(BB, stackIdx);
  return std::count_if(Conds.begin(), Conds.end(), Pred);

}

static uint32_t countPathConditionsAtBlockStartIn(ShadowBBInvar* BB, uint32_t stackIdx, PathConditions& PCs) {

  BasicBlock* B = BB->BB;

  uint32_t nPCs = countPathConditionsIn(B, stackIdx, PCs.IntPathConditions) +
    countPathConditionsIn(B, stackIdx, PCs.StringPathConditions) +
    countPathConditionsIn(B, stackIdx, PCs.IntmemPathConditions);

  for(std::vector<PathFunc>::iterator it = PCs.FuncPathConditions.begin(),
	itend = PCs.FuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx == stackIdx && it->BB == BB->BB)
      ++nPCs;

  }
  
  return nPCs;
  
}

uint32_t IntegrationHeuristicsPass::countPathConditionsAtBlockStart(ShadowBBInvar* BB, IntegrationAttempt* IA) {

  // Returns the number of path conditions that will be checked /before the start of BB/.
  // This does not include conditions listed in AsDefIntPathConditions which are checked
  // as the instruction becomes defined (hence the name), in the midst of the block.

  uint32_t total = 0;
  if(IA->invarInfo->pathConditions)
    total = countPathConditionsAtBlockStartIn(BB, UINT_MAX, *IA->invarInfo->pathConditions);
  
  IATargetInfo* Info = IA->getFunctionRoot()->targetCallInfo;
  if(Info)
    total += countPathConditionsAtBlockStartIn(BB, Info->targetStackDepth, pathConditions);

  return total;

}

ShadowValue IntegrationAttempt::getPathConditionSV(uint32_t instStackIdx, BasicBlock* instBB, uint32_t instIdx) {

  if(!instBB) {
   
    return ShadowValue(&pass->shadowGlobals[instIdx]);
    
  }
  else {

    IntegrationAttempt* testCtx;
    if(instStackIdx == UINT_MAX) {
      testCtx = this;
    }
    else {
      testCtx = getIAWithTargetStackDepth(getFunctionRoot(), instStackIdx);
    }
    
    if(instBB == (BasicBlock*)ULONG_MAX)
      return ShadowValue(&testCtx->getFunctionRoot()->argShadows[instIdx]);
    else {
      uint32_t blockIdx = findBlock(testCtx->invarInfo, instBB);
      return ShadowValue(testCtx->getInst(blockIdx, instIdx));
    }

  }

}

ShadowValue IntegrationAttempt::getPathConditionSV(PathCondition& Cond) {

  return getPathConditionSV(Cond.instStackIdx, Cond.instBB, Cond.instIdx);

}

void IntegrationAttempt::emitPathConditionCheck(PathCondition& Cond, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt) {

  if((stackIdx != UINT_MAX && stackIdx != Cond.fromStackIdx) || BB->invar->BB != Cond.fromBB)
    return;

  CommittedBlock& emitCB = *(emitBlockIt++);
  BasicBlock* emitBlock = emitCB.specBlock;

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
	testRoot = CastInst::Create(Op, testRoot, Int8Ptr, VerboseNames ? "testcast" : "", emitBlock);
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
	testRoot = CastInst::Create(Op, testRoot, Int8Ptr, VerboseNames ? "testcast" : "", emitBlock);
      }
      
      Value* CondCast = ConstantExpr::getBitCast(Cond.val, Int8Ptr);
	
      Value* StrcmpArgs[2] = { CondCast, testRoot };
      CallInst* CmpCall = CallInst::Create(StrcmpFun, ArrayRef<Value*>(StrcmpArgs, 2), VerboseNames ? "assume_test" : "", emitBlock);
      CmpCall->setCallingConv(StrcmpFun->getCallingConv());
      resultInst = new ICmpInst(*emitBlock, CmpInst::ICMP_EQ, CmpCall, Constant::getNullValue(CmpCall->getType()), "");

      break;

    }

  case PathConditionTypeFptrmem:
    
    release_assert(0 && "Bad path condition type");
    llvm_unreachable();

  }

  // resultInst is a boolean indicating if the path condition matched.
  // Branch to the next specialised block on pass, or the first non-specialised block otherwise.

  // If breakBlock != specBlock then we should emit a diagnostic message that is printed when breaking
  // from specialised to unspecialised code this way.

  BasicBlock* failTarget = getFunctionRoot()->failedBlocks[BB->invar->idx].front().first;

  if(emitCB.specBlock != emitCB.breakBlock) {

    std::string msg;
    {
      raw_string_ostream RSO(msg);
      RSO << "Failed path condition ";
      printPathCondition(Cond, Ty, BB, RSO, /* HTML escaped = */ false);
      RSO << " in block " << BB->invar->BB->getName() << " / " << BB->IA->SeqNumber << "\n";
    }

    escapePercent(msg);
    emitRuntimePrint(emitCB.breakBlock, msg, 0);

    BranchInst::Create(failTarget, emitCB.breakBlock);
    failTarget = emitCB.breakBlock;
    
  }
  
  BranchInst::Create(emitBlockIt->specBlock, failTarget, resultInst, emitBlock);

}

void IntegrationAttempt::emitPathConditionChecksIn(std::vector<PathCondition>& Conds, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it)
    emitPathConditionCheck(*it, Ty, BB, stackIdx, emitBlockIt);

}

void IntegrationAttempt::emitPathConditionChecks2(ShadowBB* BB, PathConditions& PC, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt) {

  emitPathConditionChecksIn(PC.IntPathConditions, PathConditionTypeInt, BB, stackIdx, emitBlockIt);
  emitPathConditionChecksIn(PC.StringPathConditions, PathConditionTypeString, BB, stackIdx, emitBlockIt);
  emitPathConditionChecksIn(PC.IntmemPathConditions, PathConditionTypeIntmem, BB, stackIdx, emitBlockIt);

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(), 
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(stackIdx != it->stackIdx || BB->invar->BB != it->BB)
      continue;

    CommittedBlock& emitCB = *(emitBlockIt++);
    BasicBlock* emitBlock = emitCB.specBlock;

    Value* verifyArgs[it->args.size()];
    
    // Call the verify function at runtime with arguments corresponding to those which were
    // passed to the path function during specialisation.

    uint32_t i = 0;
    for(SmallVector<PathFuncArg, 1>::iterator argit = it->args.begin(),
	  argend = it->args.end(); argit != argend; ++argit, ++i) {

      verifyArgs[i] = getCommittedValue(getPathConditionSV(argit->stackIdx, argit->instBB, argit->instIdx));
      
    }

    Value* VCall = CallInst::Create(it->VerifyF, ArrayRef<Value*>(verifyArgs, it->args.size()), VerboseNames ? "verifycall" : "", emitBlock);

    // The verify function returns zero if we're okay to continue into specialised code.
    Value* VCond = new ICmpInst(*emitBlock, CmpInst::ICMP_EQ, VCall, Constant::getNullValue(VCall->getType()), VerboseNames ? "verifycheck" : "");

    BasicBlock* failTarget = getFunctionRoot()->failedBlocks[BB->invar->idx].front().first;

    if(emitCB.specBlock != emitCB.breakBlock) {

      std::string msg;
      {
	raw_string_ostream RSO(msg);
	RSO << "Failed path function " << it->VerifyF->getName() << " in block " << 
	  BB->invar->BB->getName() << " / " << BB->IA->SeqNumber << ". Return code: ";
      }

      escapePercent(msg);

      std::string pasted;
      {
	raw_string_ostream RSO(pasted);
	RSO << msg << "%d\n";
      }

      emitRuntimePrint(emitCB.breakBlock, pasted, VCall);

      BranchInst::Create(failTarget, emitCB.breakBlock);
      failTarget = emitCB.breakBlock;
    
    }
    
    // Branch to next check or to failed block.
    BranchInst::Create(emitBlockIt->specBlock, failTarget, VCond, emitBlock);

  }

}

SmallVector<CommittedBlock, 1>::iterator IntegrationAttempt::emitPathConditionChecks(ShadowBB* BB) {

  SmallVector<CommittedBlock, 1>::iterator it = BB->committedBlocks.begin();

  IATargetInfo* Info = BB->IA->getFunctionRoot()->targetCallInfo;
  if(Info) {

    uint32_t stackIdx = Info->targetStackDepth;
    emitPathConditionChecks2(BB, pass->pathConditions, stackIdx, it);

  }

  if(invarInfo->pathConditions)
    emitPathConditionChecks2(BB, *invarInfo->pathConditions, UINT_MAX, it);

  return it;
  
}

BasicBlock::iterator InlineAttempt::skipMergePHIs(BasicBlock::iterator it) {

  PHINode* PN;
  while((PN = dyn_cast<PHINode>(it)) && ForwardingPHIs->count(PN))
    ++it;

  return it;

}

bool IntegrationAttempt::hasLiveIgnoredEdges(ShadowBB* BB) {

  for(uint32_t i = 0, ilim = BB->invar->succIdxs.size(); i != ilim; ++i) {

    if(shouldIgnoreEdge(BB->invar, getBBInvar(BB->invar->succIdxs[i])) &&
       !edgeIsDead(BB->invar, getBBInvar(BB->invar->succIdxs[i])))
      return true;

  }

  return false;

}

bool InlineAttempt::isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx) {

  if(targetCallInfo && !targetCallInfo->mayReachTarget.count(BBIdx)) {  

    if(predBlockIdx != targetCallInfo->targetCallBlock && targetCallInfo->mayReachTarget.count(predBlockIdx)) {
      
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

Value* InlineAttempt::getLocalFailedValue(Value* V, BasicBlock* UseBlock) {

  Value* Ret = tryGetLocalFailedValue(V, UseBlock);
  release_assert(Ret);
  return Ret;

}

Value* InlineAttempt::tryGetLocalFailedValue(Value* V, BasicBlock* UseBlock) {

  Instruction* I = dyn_cast<Instruction>(V);
  if(!I)
    return V;

  ValueToValueMapTy::iterator it2 = failedBlockMap->find(I);
  if(it2 == failedBlockMap->end())
    return 0;

  Instruction* CloneI = cast<Instruction>(it2->second);

  DenseMap<std::pair<Instruction*, BasicBlock*>, PHINode*>::iterator it = 
    PHIForwards->find(std::make_pair(CloneI, UseBlock));
  if(it != PHIForwards->end())
    return it->second;

  return CloneI;

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

  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->failedReturnBlock) {
      edges.push_back(std::make_pair(IA->failedReturnBlock, this));
      added = true;
    }

  }

  // Does this IA break at this instruction?
  // It does if this instruction requires an as-expected check ("requiresRuntimeCheck"), 
  // OR if the NEXT instruction requires a special check.
  if((!added) && 
     (requiresRuntimeCheck(ShadowValue(SI), false) || 
      (BB->insts.size() > instIdx + 1 && BB->insts[instIdx + 1].needsRuntimeCheck == RUNTIME_CHECK_SPECIAL))) {

    edges.push_back(std::make_pair(BB->getCommittedBreakBlockAt(instIdx), this));
    added = true;
    
  }

  if(added && L)
    return 1;
  else
    return 0;

}

Value* InlineAttempt::getUnspecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, BasicBlock* UseBlock) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    // Pred is not an instruction. Use the same val whether consuming unspec or spec versions.
    return getSpecValue(blockIdx, instIdx, V);

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    Value* Ret = tryGetLocalFailedValue(V, UseBlock);
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
    if((!specI) || !specI->committedVal)
      return 0;
    else
      return getCommittedValue(ShadowValue(specI));

  }  

}

void IntegrationAttempt::gatherPathConditionEdges(uint32_t bbIdx, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>* preds, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* IAPreds) {

  ShadowBBInvar* BBI = getBBInvar(bbIdx);
  PeelAttempt* LPA;

  if(BBI->naturalScope != L && ((!L) || L->contains(BBI->naturalScope)) &&
     (LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) &&
     LPA->isTerminated() && LPA->isEnabled()) {

    for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
      LPA->Iterations[i]->gatherPathConditionEdges(bbIdx, instIdx, preds, IAPreds);

  }
  else {

    ShadowBB* BB = getBB(bbIdx);
    if(!BB)
      return;

    Value* PCVal;
    if(preds)
      PCVal = getCommittedValue(ShadowValue(&BB->insts[instIdx]));
    else
      PCVal = 0;

    for(uint32_t i = 0, ilim = pass->countPathConditionsAtBlockStart(BB->invar, this); i != ilim; ++i) {

      // Assert block starts at offset 0, as with all PC test blocks.
      release_assert(BB->committedBlocks[i].startIndex == 0);

      if(preds)
	preds->push_back(std::make_pair(PCVal, BB->committedBlocks[i].breakBlock));
      else if(IAPreds)
	IAPreds->push_back(std::make_pair(BB->committedBlocks[i].breakBlock, this));
      
    }

  }

}

BasicBlock::iterator InlineAttempt::commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx) {

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
  uint32_t instIdx = 0;

  // If BBI is a loop header, skip the latch predecessor for the time being and we'll come back to it
  // after the latch operand is committed.
  
  uint32_t ignorePred = UINT_MAX;

  if(BBI->naturalScope) {

    ShadowLoopInvar* LInfo = invarInfo->LInfo[BBI->naturalScope];
    if(LInfo->headerIdx == BBIdx)
      ignorePred = LInfo->latchIdx;

  }

  for(BasicBlock::iterator BE = BB->end(); BI != BE && isa<PHINode>(BI); ++BI, ++instIdx) {

    ShadowInstructionInvar* PNInfo = &BBI->insts[instIdx];
    PHINode* OrigPN = cast<PHINode>(PNInfo->I);
    PHINode* PN = cast<PHINode>(BI);

    createForwardingPHIs(*PNInfo, PN);

    SmallVector<std::pair<Value*, BasicBlock*>, 4> newPreds;

    for(uint32_t i = 0, ilim = PNInfo->operandBBs.size(); i != ilim; ++i) {

      uint32_t predBlockIdx = PNInfo->operandBBs[i];

      if(predBlockIdx == ignorePred)
	continue;

      ShadowInstIdx predOp = PNInfo->operandIdxs[i];
      Value* predV = OrigPN->getIncomingValue(i);

      Value* unspecV = getUnspecValue(predOp.blockIdx, predOp.instIdx, predV, failedBlocks[predBlockIdx].back().first);
      Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV);

      BasicBlock* specPred;
      if(isSpecToUnspecEdge(predBlockIdx, BBIdx))
	specPred = getBB(predBlockIdx)->committedBlocks.back().breakBlock;
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

    // Gather incoming path condition edges and values: these either come from this context
    // or from loop iterations above it.
    gatherPathConditionEdges(BBIdx, instIdx, &newPreds, 0);

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

static PHINode* insertMergePHI(ShadowInstructionInvar& SI, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& specPreds, SmallVector<std::pair<BasicBlock*, Instruction*>, 4>& unspecPreds, BasicBlock* InsertBB) {

  PHINode* NewNode = PHINode::Create(SI.I->getType(), 0, VerboseNames ? "clonemerge" : "", InsertBB->begin());
  
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
    // If the user is a PHI node then it effectively uses in the predecessor it draws from.
    ShadowInstructionInvar& UseSI = UseBBI->insts[OrigSI.userIdxs[i].instIdx];
    if(isa<PHINode>(UseSI.I)) {

      for(uint32_t j = 0, jlim = UseSI.operandIdxs.size(); j != jlim; ++j) {

	if(UseSI.operandIdxs[j].blockIdx == OrigSI.parent->idx && UseSI.operandIdxs[j].instIdx == OrigSI.idx) {

	  ShadowBBInvar* PredBBI = getBBInvar(UseSI.operandBBs[j]);
	  markBBAndPreds(PredBBI, -1 /* needed in whole block */, predBlocks, OrigSI.parent);

	}

      }

    }
    else {

      markBBAndPreds(UseBBI, OrigSI.userIdxs[i].instIdx, predBlocks, OrigSI.parent);

    }

  }

  // 2. Proceed forwards through those blocks, inserting forwarding each time there is a merge from
  // specialised code and each time conflicting versions of the forwarded value are presented
  // by block predecessors.

  // Keep track of the stack of loops we're inside: loops with break edges inside them create
  // new loop variants and their header phis must be created incomplete and finished on completion.
  // Start it off containing the definition loop, which will never be popped.
  
  SmallVector<std::pair<const Loop*, PHINode*>, 4> loopStack;
  loopStack.push_back(std::make_pair(OrigSI.parent->naturalScope, (PHINode*)0));

  for(uint32_t i = 0, ilim = predBlocks.size(); i != ilim; ++i) {

    // Not needed here?
    if(!predBlocks[i].first)
      continue;

    uint32_t thisBlockIdx = (OrigSI.parent->idx + i);
    ShadowBBInvar* thisBBI = getBBInvar(thisBlockIdx);

    Instruction* thisBlockInst;
    bool instDefined = false;

    // This is set when we're dealing with a header PHI,
    // and serves to prevent attempts to merge the latch->header value
    // before it is created.
    std::pair<BasicBlock*, Instruction*> headerPred;

    if(i != 0) {

      // Top of block: merge the value if the block is a spec-to-unspec
      // merge point (path conditions, etc) or if there are conflicting unspec
      // definitions or both.

      // If this is a loop header, check whether there are any break edges in the loop. If not,
      // we can simply set all such blocks to use the same definition as the preheader; if there are,
      // we must create an incomplete header phi and complete it after exiting.

      const Loop* currentLoop = loopStack.back().first;
      if(currentLoop != thisBBI->naturalScope) {

	if((!currentLoop) || currentLoop->contains(thisBBI->naturalScope)) {

	  // Entered a new loop.
	  ShadowLoopInvar* LInfo = invarInfo->LInfo[thisBBI->naturalScope];

	  // The entire loop should be in our scope of consideration:
	  release_assert(OrigSI.parent->idx <= LInfo->preheaderIdx);
	  release_assert(OrigSI.parent->idx + predBlocks.size() >= LInfo->latchIdx);

	  // Are there any breaks in the loop body? These can be due to instruction checks
	  // or path conditions but not can't-reach-target conditions.

	  bool loopHasBreaks = false;
	  for(uint32_t j = LInfo->headerIdx, jlim = LInfo->latchIdx + 1; j != jlim && !loopHasBreaks; ++j) {

	    // Block is broken into pieces due to a mid-block check?
	    if(failedBlocks[j].size() > 1)
	      loopHasBreaks = true;

	    // Will there be incoming edges from specialised code due to path conditions?
	    else if(pass->countPathConditionsAtBlockStart(thisBBI, this))
	      loopHasBreaks = true;

	  }

	  Instruction* PreheaderInst = predBlocks[LInfo->preheaderIdx - OrigSI.parent->idx].first;

	  if(!loopHasBreaks) {

	    // If not use the preheader value everywhere and skip the loop.

	    for(uint32_t j = LInfo->headerIdx, jlim = LInfo->latchIdx + 1; j != jlim && !loopHasBreaks; ++j) {

	      predBlocks[j - OrigSI.parent->idx].first = PreheaderInst;

	      // In this case there are no block splits:
	      if(PreheaderInst != NewI) {
		BasicBlock* thisFailedBlock = failedBlocks[j].front().first;
		(*PHIForwards)[std::make_pair(NewI, thisFailedBlock)] = cast<PHINode>(PreheaderInst);
	      }

	    }

	    i = LInfo->latchIdx - OrigSI.parent->idx;
	    continue;

	  }
	  else {

	    // Otherwise create a phi that doesn't merge the latch edge and complete it later.
	    headerPred = std::make_pair(failedBlocks[LInfo->preheaderIdx].back().first, PreheaderInst);
	    loopStack.push_back(std::make_pair(thisBBI->naturalScope, (PHINode*)0));

	    // Fall through to ordinary treatment of the first subblock, where headerPred being set
	    // will override the usual merge-from-unspecialised-predecessors logic.

	  }

	}
	else {

	  // Left one or more loops, complete the corresponding header PHIs.
	  // All predecessor kinds apart from the latch->header unspecialised edge
	  // are already accounted for.

	  while(thisBBI->naturalScope != loopStack.back().first) {

	    const Loop* exitLoop = loopStack.back().first;
	    PHINode* PN = loopStack.back().second;
	    loopStack.pop_back();
	    // Lowest level loop should never be popped.
	    release_assert(loopStack.size());

	    ShadowLoopInvar* LInfo = invarInfo->LInfo[exitLoop];

	    PN->addIncoming(predBlocks[LInfo->latchIdx - OrigSI.parent->idx].first, 
			    failedBlocks[LInfo->latchIdx].back().first);

	  }

	  // Now process the block as per usual.

	}

      }
      
      // Create a PHI merge at the top of this block if (a) there are unspec->spec edges
      // due to ignored blocks, (b) there are path condition breaks to top of block,
      // or (c) unspecialised predecessor blocks are using different versions of the 
      // instruction in question. Also always insert a merge at the loop header if we
      // get to here, as some disagreement is sure to arise between the preheader->header
      // and latch->header edges.

      BasicBlock* insertBlock = failedBlocks[thisBlockIdx].front().first;

      // Cases (a) and (b).

      uint32_t nCondsHere = pass->countPathConditionsAtBlockStart(thisBBI, this);
      bool isSpecToUnspec = isSimpleMergeBlock(thisBlockIdx);

      bool shouldMergeHere = nCondsHere != 0 || isSpecToUnspec || headerPred.first != 0;

      if(!shouldMergeHere) {

	// Case (c): do predecesors disagree about which version of the instruction they're using?

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

      if(shouldMergeHere) {

	SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> specPreds;
	SmallVector<std::pair<BasicBlock*, Instruction*>, 4> unspecPreds;

	if(isSpecToUnspec) {

	  // Some specialised predecessors branch straight to unspec code.
	  for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	    uint32_t pred = thisBBI->predIdxs[j];

	    if(isSpecToUnspecEdge(pred, thisBlockIdx))
	      specPreds.push_back(std::make_pair(getBB(pred)->committedBlocks.back().breakBlock, this));

	  }

	}
	if(nCondsHere) {

	  // Adds to specPreds for each loop iteration that can break here:
	  gatherPathConditionEdges(thisBlockIdx, 0, 0, &specPreds);

	}

	if(headerPred.first) {

	  unspecPreds.push_back(headerPred);

	}
	else {

	  for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	    uint32_t pred = thisBBI->predIdxs[j];
	    uint32_t relidx = pred - OrigSI.parent->idx;
	    unspecPreds.push_back(std::make_pair(failedBlocks[pred].back().first, predBlocks[relidx].first));

	  }

	}

	// Further subdivisions of this block should use the new PHI
	thisBlockInst = insertMergePHI(OrigSI, specPreds, unspecPreds, insertBlock);
	ForwardingPHIs->insert(cast<PHINode>(thisBlockInst));

	if(headerPred.first) {

	  loopStack.back().second = cast<PHINode>(thisBlockInst);

	}
	
      }
      else {
	
	// Further subdivisions of this block should use the same value as our predecessors
	// The preds necessarily match so just use the first.
	thisBlockInst = predBlocks[thisBBI->predIdxs[0] - OrigSI.parent->idx].first;

      }

      // Map instruction users to the appropriate local forward:
      if(thisBlockInst != NewI)
	(*PHIForwards)[std::make_pair(NewI, insertBlock)] = cast<PHINode>(thisBlockInst);
      
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
	}

	continue;

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

      (*PHIForwards)[std::make_pair(NewI, it->first)] = cast<PHINode>(thisBlockInst);

    }
    
    predBlocks[i].first = thisBlockInst;

  }

  // If there are loops that exit exactly as this value goes out of scope, finish their headers.

  while(OrigSI.parent->naturalScope != loopStack.back().first) {

    const Loop* exitLoop = loopStack.back().first;
    PHINode* PN = loopStack.back().second;
    loopStack.pop_back();
    // Lowest level loop should never be popped.
    release_assert(loopStack.size());

    ShadowLoopInvar* LInfo = invarInfo->LInfo[exitLoop];
    
    PN->addIncoming(predBlocks[LInfo->latchIdx - OrigSI.parent->idx].first, 
		    failedBlocks[LInfo->latchIdx].back().first);

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

void InlineAttempt::remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t idx, uint32_t instIdx, bool skipTestedInst, bool skipTerm) {

  // Map each instruction operand to the most local PHI translation of the target instruction,
  // or if that doesn't exist the specialised version.

  // If skipTestedInst is true then skip creating
  // PHI forwards of the second-to-last instruction (i.e. the instruction before the terminator)
  // as that will be special-cased in populateFailedBlock at the start of the next subblock.

  BasicBlock::iterator BE = BB->end();
  Instruction* testedInst;
  if(skipTerm) {
    --BE;
    if(skipTestedInst) {
      --BE;
      testedInst = BE;
      ++BE;
    }
    else
      testedInst = 0;
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
	  
	  ReturnInst* OrigRI = cast<ReturnInst>(SII.I);
	  Value* V = OrigRI->getOperand(0);
	  Value* Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, V, BB);
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

	  ReturnInst* OrigRI = cast<ReturnInst>(SII.I);
	  Value* V = OrigRI->getOperand(0);
	  Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, V, BB);
	  StructType* retType = cast<StructType>(CommitF->getFunctionType()->getReturnType());
	  Type* normalRet = Ret->getType();
	  Constant* undefRet = UndefValue::get(normalRet);
	  Value* aggTemplate = ConstantStruct::get(retType, undefRet, FailFlag, NULL);
	  Ret = InsertValueInst::Create(aggTemplate, Ret, 0, VerboseNames ? "fail_ret" : "", RI);

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
	  Repl = getUnspecValue(op.blockIdx, op.instIdx, V, BB);

	((Use*)replit)->set(Repl);

      }

    }

  }

}

void IntegrationAttempt::commitSimpleFailedBlock(uint32_t i) { }

void InlineAttempt::commitSimpleFailedBlock(uint32_t i) {

  if(failedBlocks.empty() || failedBlocks[i].empty())
    return;

  release_assert(failedBlocks[i].size() == 1 && "commitSimpleFailedBlock with a split block?");

  BasicBlock* CommitBB = failedBlocks[i].front().first;
  BasicBlock::iterator BI = skipMergePHIs(CommitBB->begin());
  BasicBlock::iterator PostPHIBI = commitFailedPHIs(CommitBB, BI, i);
 
  remapFailedBlock(PostPHIBI, CommitBB, i, std::distance(BI, PostPHIBI), false, false);

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
      else if(requiresRuntimeCheck(ShadowValue(SI), true)) {

	// Check exit PHIs as a block:
	if(i + 1 != ilim && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[i+1]))
	  continue;

	// Special checks require a split BEFORE the block:
	if(SI->needsRuntimeCheck == RUNTIME_CHECK_SPECIAL) {

	  if(i != 0)
	    splitInsts[i - 1] = true;

	}
	else {
	  
	  splitInsts[i] = true;

	}

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
  if (VerboseNames && BB->hasName()) NewBB->setName(BB->getName()+NameSuffix);

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

  if(VerboseNames) {

    std::string newName;
    {
      raw_string_ostream RSO(newName);
      RSO << getCommittedBlockPrefix() << BBI->BB->getName() << " (failed)";
    }

    NewBB->setName(newName);

  }

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

      Twine SplitName;
      if(VerboseNames)
	SplitName = toSplit->getName() + ".checksplit";
      else
	SplitName = "";

      BasicBlock* splitBlock = 
	toSplit->splitBasicBlock(splitIterator, SplitName);
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
  if(!InstBB)
    return;

  ShadowInstruction* SI = &InstBB->insts[instIdx];

  // If we're called from a context that has loop predecessors then the
  // value may only be checked on some iterations:
  if(!requiresRuntimeCheck(ShadowValue(SI), true))
    return;

  ShadowBB* PredBB = getBB(*predBlock);
  if(!PredBB)
    return;

  BasicBlock* pred = PredBB->getCommittedBreakBlockAt(predIdx);
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
  if(fallThrough || requiresRuntimeCheck(SI, true)) {

    ShadowBB* PredBB = getBB(*predBlock);
    BasicBlock* pred = PredBB->getCommittedBreakBlockAt(predIdx);
    Value* committedVal = getCommittedValue(ShadowValue(&InstBB->insts[instIdx]));
    preds.push_back(std::make_pair(committedVal, pred));
    
  }

}

void IntegrationAttempt::populateFailedHeaderPHIs(const Loop*) {}

void InlineAttempt::populateFailedHeaderPHIs(const Loop* PopulateL) {

  // Add the latch predecessor to each header phi.
  ShadowLoopInvar* LInfo = invarInfo->LInfo[PopulateL];

  if(failedBlocks.empty() || failedBlocks[LInfo->headerIdx].empty())
    return;

  ShadowBBInvar* headerBBI = getBBInvar(LInfo->headerIdx);
  BasicBlock* headerBlock = failedBlocks[LInfo->headerIdx].front().first;
  uint32_t instIdx = 0;
 
  for(BasicBlock::iterator BI = skipMergePHIs(headerBlock->begin()), BE = headerBlock->end();
      BI != BE && isa<PHINode>(BI); ++BI, ++instIdx) {
  
    PHINode* PN = cast<PHINode>(BI);
    ShadowInstructionInvar& PNInfo = headerBBI->insts[instIdx];
    PHINode* OrigPN = cast<PHINode>(PNInfo.I);

    for(uint32_t i = 0, ilim = PNInfo.operandBBs.size(); i != ilim; ++i) {

      if(PNInfo.operandBBs[i] == LInfo->latchIdx) {

	Value* origPredVal = OrigPN->getIncomingValue(i);
	ShadowInstIdx predOp = PNInfo.operandIdxs[i];

	Value* predVal = getUnspecValue(predOp.blockIdx, predOp.instIdx, 
					origPredVal, failedBlocks[LInfo->latchIdx].back().first);
	BasicBlock* predBlock = failedBlocks[LInfo->latchIdx].back().first;

	PN->addIncoming(predVal, predBlock);

	break;

      }

    }
    
  }

}

bool IntegrationAttempt::instSpecialTest(uint32_t blockIdx, uint32_t instIdx) {

  ShadowBBInvar* BBI = getBBInvar(blockIdx);
  
  if(L != BBI->naturalScope && ((!L) || L->contains(BBI->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	if(LPA->Iterations[i]->instSpecialTest(blockIdx, instIdx))
	  return true;

      return false;

    }

  }

  if(ShadowBB* BB = getBB(*BBI)) {

    if(BB->insts[instIdx].needsRuntimeCheck == RUNTIME_CHECK_SPECIAL)
      return true;

  }

  return false;

}

// Return true if the subblock 'it' ends because of an instruction-as-expected test.
bool IntegrationAttempt::subblockEndsWithSpecialTest(uint32_t idx,
						     SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it, 
						     SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator lastit) {

  if(it == lastit)
    return false;

  // I *think* it's inconceivable that the same instruction should terminate a subblock in different loop iterations
  // for different reasons... so simply return true if this block boundary exists in some iteration and it's
  // a special test.

  ++it;
  uint32_t instIdx = it->second - 1;

  return instSpecialTest(idx, instIdx);

}

void IntegrationAttempt::populateFailedBlock(uint32_t idx) { }

void InlineAttempt::populateFailedBlock(uint32_t idx) {
  
  if(failedBlocks.empty() || failedBlocks[idx].empty())
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
    BasicBlock::iterator PostPHIBI = commitFailedPHIs(it->first, BI, idx);

    bool endsWithSpecial = subblockEndsWithSpecialTest(idx, it, lastit);
    remapFailedBlock(PostPHIBI, it->first, idx, std::distance(BI, PostPHIBI), !endsWithSpecial, it != lastit);

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

	Twine PhiName;
	PHINode* NewPN =  makePHI(failedI->getType(), VerboseNames ? "spec-unspec-merge" : "", it->first);
	for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator specit = specPreds.begin(),
	      specend = specPreds.end(); specit != specend; ++specit) {
	  release_assert(specit->first);
	  NewPN->addIncoming(getValAsType(specit->first, failedI->getType(), specit->second->getTerminator()), 
			     specit->second);
	}

	if(it != failedBlocks[idx].begin()) {

	  // There is an unspecialised predecessor to this subblock. Merge the unspecialised pred.
	  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator predIt = it;
	  --predIt;

	  Value* NewV = getUnspecValue(idx, failedInst, failedI, it->first);
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
    bool endsWithSpecial = subblockEndsWithSpecialTest(idx, it, lastit);
    remapFailedBlock(BI, it->first, idx, it->second, !endsWithSpecial, it != lastit);

  }
  
}

Value* IntegrationAttempt::emitCompareCheck(Value* realInst, ImprovedValSetSingle* IVS, BasicBlock* emitBB) {

  release_assert(isa<Instruction>(realInst) && "Checked instruction must be residualised");

  Value* thisCheck = 0;
  for(uint32_t j = 0, jlim = IVS->Values.size(); j != jlim; ++j) {

    Value* newCheck;

    if(IVS->SetType == ValSetTypePB && 
       IVS->Values[j].Offset == LLONG_MAX && 
       IVS->Values[j].V.getAllocSize() != ULONG_MAX) {

      ImprovedVal BaseVal = IVS->Values[j];
      BaseVal.Offset = 0;
      ImprovedVal LimitVal = IVS->Values[j];
      LimitVal.Offset = IVS->Values[j].V.getAllocSize();

      Value* Base = trySynthVal(0, realInst->getType(), IVS->SetType, BaseVal, emitBB);
      release_assert(Base && "Couldn't synth base");
      Value* Limit = trySynthVal(0, realInst->getType(), IVS->SetType, LimitVal, emitBB);
      release_assert(Base && "Couldn't synth limit");
     
      Value* BaseCheck = new ICmpInst(*emitBB, CmpInst::ICMP_UGE, 
				      realInst, Base, VerboseNames ? "checkbase" : "");
      Value* LimitCheck = new ICmpInst(*emitBB, CmpInst::ICMP_ULT, 
				       realInst, Limit, VerboseNames ? "checklimit" : "");
      newCheck = BinaryOperator::CreateAnd(BaseCheck, LimitCheck, VerboseNames ? "qptrcheck" : "", emitBB);
      
    }
    else {

      Value* thisVal = trySynthVal(0, realInst->getType(), IVS->SetType, IVS->Values[j], emitBB);
      assert(thisVal && "Couldn't synthesise value for check?");

      if(thisVal->getType()->isFloatingPointTy())
	newCheck = new FCmpInst(*emitBB, CmpInst::FCMP_OEQ, realInst, thisVal, VerboseNames ? "check" : "");
      else
	newCheck = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, realInst, thisVal, VerboseNames ? "check" : "");

    }

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
      Constant* ShiftAmt = ConstantInt::get(I64, it.start() * 8);
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

SmallVector<CommittedBlock, 1>::iterator
IntegrationAttempt::emitExitPHIChecks(SmallVector<CommittedBlock, 1>::iterator emitIt, ShadowBB* BB) {

  CommittedBlock& emitCB = *(emitIt++);
  BasicBlock* emitBB = emitCB.specBlock;
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

  BasicBlock* successTarget = emitIt->specBlock;
  // i is the index of the first non-PHI at this point.
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, i);

  if(emitCB.specBlock != emitCB.breakBlock) {

    std::string msg;
    {
      raw_string_ostream RSO(msg);
      RSO << "Failed exit phi checks in block " << BB->invar->BB->getName() << " / " << BB->IA->SeqNumber << "\n";
    }
    
    escapePercent(msg);
    emitRuntimePrint(emitCB.breakBlock, msg, 0);

    BranchInst::Create(failTarget, emitCB.breakBlock);
    failTarget = emitCB.breakBlock;
    
  }

  BranchInst::Create(successTarget, failTarget, prevCheck, emitBB); 

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

SmallVector<CommittedBlock, 1>::iterator
IntegrationAttempt::emitOrdinaryInstCheck(SmallVector<CommittedBlock, 1>::iterator emitIt, ShadowInstruction* SI) {

  CommittedBlock& emitCB = *(emitIt++);
  BasicBlock* emitBB = emitCB.specBlock;
  Value* Check;

  if(inst_is<MemTransferInst>(SI))
    Check = emitMemcpyCheck(SI, emitBB);
  else
    Check = emitAsExpectedCheck(SI, emitBB);
    
  BasicBlock* successTarget = emitIt->specBlock;
  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(SI->parent->invar->idx, SI->invar->idx + 1);

  if(emitCB.specBlock != emitCB.breakBlock) {

    std::string msg;
    {
      raw_string_ostream RSO(msg);
      RSO << "Failed checking instruction " << itcache(SI) << " in " << SI->parent->invar->BB->getName() << " / " << SI->parent->IA->SeqNumber << "\n";
    }
    
    escapePercent(msg);
    emitRuntimePrint(emitCB.breakBlock, msg, 0);

    BranchInst::Create(failTarget, emitCB.breakBlock);
    failTarget = emitCB.breakBlock;
    
  }

  BranchInst::Create(successTarget, failTarget, Check, emitBB);

  return emitIt;

}

void llvm::escapePercent(std::string& msg) {

  // Replace % with %% throughout msg.
  
  size_t pos = 0;
  while(pos < msg.size()) {

    pos = msg.find("%", pos);
    if(pos == std::string::npos)
      break;

    msg.insert(pos, "%");
    pos += 2;

  }

}

void llvm::emitRuntimePrint(BasicBlock* emitBB, std::string& message, Value* param) {

  Type* CharPtr = Type::getInt8PtrTy(emitBB->getContext());
  Module* M = emitBB->getParent()->getParent();

  static Constant* Printf = 0;
  if(!Printf) {

    Printf = M->getFunction("printf");
    if(!Printf) {

      errs() << "Warning: couldn't find a printf function for debug printing, will need to link against libc\n";

      Type* Int32 = Type::getInt32Ty(emitBB->getContext());
      FunctionType* PrintfTy = FunctionType::get(Int32, ArrayRef<Type*>(CharPtr), /*vararg=*/true);

      Printf = M->getOrInsertFunction("printf", PrintfTy);
    
    }

  }
    
  uint32_t nParams = param ? 2 : 1;
  Value* args[nParams];

  Constant* messageArray = ConstantDataArray::getString(emitBB->getContext(), message, true);
  GlobalVariable* messageGlobal = new GlobalVariable(*(emitBB->getParent()->getParent()), 
						     messageArray->getType(), true,
						     GlobalValue::InternalLinkage, messageArray);
  Constant* castMessage = ConstantExpr::getBitCast(messageGlobal, CharPtr);

  
  args[0] = castMessage;
  if(param)
    args[1] = param;

  CallInst::Create(Printf, ArrayRef<Value*>(args, nParams), "", emitBB);
  
}
