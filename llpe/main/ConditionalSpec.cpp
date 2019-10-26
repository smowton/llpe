//===-- ConditionalSpec.cpp -----------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/MathExtras.h"

using namespace llvm;

extern cl::opt<bool> VerboseNames;

// Functions relating to conditional specialisation
// (that is, situations where the specialiser assumes some condition, specialises according to it,
//  and at commit time must synthesise duplicate successor blocks: specialised, and unmodified).

// If the user has specified a target callstack, check whether SI (with corresponding context
// IA) is part of it. 
void IntegrationAttempt::checkTargetStack(ShadowInstruction* SI, InlineAttempt* IA) {

  InlineAttempt* MyRoot = getFunctionRoot();
  if(MyRoot->targetCallInfo && 
     SI->parent->invar->idx == MyRoot->targetCallInfo->targetCallBlock &&
     SI->invar->idx == MyRoot->targetCallInfo->targetCallInst) {

    if(MyRoot->targetCallInfo->targetStackDepth + 1 < pass->targetCallStack.size()) {

      pass->targetCallStackIAs.push_back(IA);
      
      uint32_t newDepth = MyRoot->targetCallInfo->targetStackDepth + 1;
      IA->setTargetCall(pass->targetCallStack[newDepth], newDepth);

    }
    else {

      IA->isStackTop = true;

    }

  }

}

// Mark block with index 'idx' reachable on unspecialised paths, starting from instruction
// index 'instIdx'. This might be because the user explicitly nominated "do not specialise
// this path" or because a runtime check needs to branch here on failure.
void InlineAttempt::markBlockAndSuccsReachableUnspecialised(uint32_t idx, uint32_t instIdx) {

  release_assert(getBBInvar(idx)->insts.size() > instIdx);

  if(pass->omitChecks)
    return;

  if(!blocksReachableOnFailure)
    blocksReachableOnFailure = new SmallDenseMap<uint32_t, uint32_t, 8>();

  // At least this much of the block already marked reachable?
  SmallDenseMap<uint32_t, uint32_t>::iterator it = blocksReachableOnFailure->find(idx);
  if(it != blocksReachableOnFailure->end() && it->second <= instIdx)
    return;

  (*blocksReachableOnFailure)[idx] = instIdx;

  // Mark all successors reachable too.
  ShadowBBInvar* BBI = getBBInvar(idx);
  for(uint32_t i = 0, ilim = BBI->succIdxs.size(); i != ilim; ++i)
    markBlockAndSuccsReachableUnspecialised(BBI->succIdxs[i], 0);  

}

// Collect block indices that can reach block 'idx' (i.e. its transitive predecessors)
void InlineAttempt::addBlockAndPreds(uint32_t idx, DenseSet<uint32_t>& Set) {

  if(!Set.insert(idx).second)
    return;

  ShadowBBInvar* BBI = getBBInvar(idx);
  for(uint32_t i = 0, ilim = BBI->predIdxs.size(); i != ilim; ++i)
    addBlockAndPreds(BBI->predIdxs[i], Set);

}

// The user has nominated this particular call instruction (given as a basic block / instruction offset)
// as the only interesting call for specialisation. Enumerate blocks that can possibly reach it: we will
// use this set as a cheap test to identify blocks that we shouldn't bother specialising because they
// won't reach the target call.
void InlineAttempt::setTargetCall(std::pair<BasicBlock*, uint32_t>& arg, uint32_t stackIdx) {

  uint32_t blockIdx = findBlock(invarInfo, arg.first->getName());
  targetCallInfo = new IATargetInfo(blockIdx, arg.second, stackIdx);

  addBlockAndPreds(blockIdx, targetCallInfo->mayReachTarget);

}

// Is CurrBB -> SuccBB an invoke instruction's exceptional control flow edge?
bool IntegrationAttempt::isExceptionEdge(ShadowBBInvar* CurrBB, ShadowBBInvar* SuccBB) {

  if(isa<InvokeInst>(CurrBB->BB->getTerminator())) {
    
    if(CurrBB->succIdxs[1] == SuccBB->idx)
      return true;
    
  }

  return false;

}

// Has the user marked CurrBB -> SuccBB as a control flow edge we shouldn't specialise along?
// (i.e. in the final program it will branch to unspecialised code)
bool IntegrationAttempt::edgeBranchesToUnspecialisedCode(ShadowBBInvar* CurrBB, ShadowBBInvar* SuccBB) {

  // Never specialise code reachable from an invoke instruction throwing.
  if(isExceptionEdge(CurrBB, SuccBB))
    return true;

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

// This whole family of functions: check whether we have a specialisation assumption assigning a value to V (an instruction or argument) 
// *when used in UserBlock*. Some assumptions apply immediately when V is defined (i.e. at the start of the function for an argument,
// or immediately after the instruction executes), whilst for other values the assumption is only applied later (e.g. only assume an argument
// has a value on a particular code path); in this latter case we must check whether the user block is dominated by the assumption.
// 'asDef' specifies whether we're checking for an assumption that applies immediately or one that applies later. This functions only apply
// to path conditions affecting virtual registers: any path condition affecting memory as applied to the store as it takes effect.

// Check for an assumption given with respect to *all* instances of this function
bool IntegrationAttempt::tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef) {

  if(invarInfo->pathConditions) {

    if(tryGetPathValueFrom(*invarInfo->pathConditions, UINT_MAX, V, UserBlock, Result, asDef))
      return true;

  }

  return false;

}

// Check for an ssumption given with respect to a particular call stack, or if that fails, check for assumptions that
// apply to all instances of this function as above.
bool InlineAttempt::tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef) {

  if(targetCallInfo) {
   
    if(tryGetPathValueFrom(pass->pathConditions, targetCallInfo->targetStackDepth, V, UserBlock, Result, asDef))
      return true;

  }

  return IntegrationAttempt::tryGetPathValue2(V, UserBlock, Result, asDef);

}

// Specifically find an assumption value that is enforced after definition.
bool IntegrationAttempt::tryGetPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result) {

  return tryGetPathValue2(V, UserBlock, Result, false);

}

// Find an assumption value that is enforced upon definition.
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

    // fromStackIdx must equal instStackIdx for integer assertions.

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
	getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(fromBlockIdx, 0);

	Result.first = ValSetTypeScalar;
	Result.second.V = it->u.val;
	return true;
	
      }

    }

  }

  return false;

}

// If the user has given a target call stack, walk up the stack from IA to the given depth
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

// Apply the given assumption (path condition) if it applies from block BB. If the user gave a target call stack, apply it only at the appropriate
// depth; otherwise apply it to all instances of this function.
void IntegrationAttempt::applyPathCondition(PathCondition* it, PathConditionTypes condty, ShadowBB* BB, uint32_t targetStackDepth) {

  // UINT_MAX signifies a path condition that applies to all instances of this function.

  if(it->fromStackIdx == targetStackDepth && it->fromBB == BB->invar->BB) {

    ShadowValue ptrSV = getPathConditionSV(it->instStackIdx, it->instBB, it->instIdx);
    ImprovedValSetSingle writePtr;
    if(!getImprovedValSetSingle(ptrSV, writePtr))
      return;

    for(uint32_t i = 0; i < writePtr.Values.size(); ++i) {

      if(writePtr.Values[i].Offset != LLONG_MAX)
	writePtr.Values[i].Offset += it->offset;

    }

    if(condty == PathConditionTypeString) {
      
      GlobalVariable* GV = cast<GlobalVariable>(it->u.val);
      ConstantDataArray* CDA = cast<ConstantDataArray>(GV->getInitializer());
      uint32_t Size = CDA->getNumElements();
      
      ShadowGV* SGV = &(pass->shadowGlobals[pass->getShadowGlobalIndex(GV)]);
      
      ImprovedValSetSingle copyFromPointer;
      copyFromPointer.set(ImprovedVal(SGV, 0), ValSetTypePB);
      
      // Attribute the effect of the write to first instruction in block:
      executeCopyInst(ptrSV.isGV() ? 0 : &ptrSV, writePtr, copyFromPointer, Size, &(BB->insts[0]));

    }
    else if(condty == PathConditionTypeStream) {

      const char* fname = it->u.filename;
      FDStore* FDS = BB->getWritableFDStore();
      uint32_t newId = pass->fds.size();
      pass->fds.push_back(FDGlobalState(0, /* is a fifo */ true));
      /* Pseudo FD is born waiting for a representitive value */
      pass->fds.back().isCommitted = true; 
      if(FDS->fds.size() <= newId)
	FDS->fds.resize(newId + 1);
      FDS->fds[newId] = FDState(std::string(fname));

      ImprovedValSetSingle writeVal;
      writeVal.set(ImprovedVal(ShadowValue::getFdIdx(newId)), ValSetTypeFD);

      executeWriteInst(0, writePtr, writeVal, /* sizeof fd: */ 4, &(BB->insts[0]));
	
    }
    else {
      
      // IntMem condition
      
      ImprovedValSetSingle writeVal;
      getImprovedValSetSingle(ShadowValue(it->u.val), writeVal);

      // Attribute the effect of the write to first instruction in block:
      executeWriteInst(0, writePtr, writeVal, GlobalTD->getTypeStoreSize(it->u.val->getType()), &(BB->insts[0]));

    }

    // Make sure a failed version of this block and its successors is created (except for stream conditions, which are checked on reads)
    if(condty != PathConditionTypeStream)
      getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(BB->invar->idx, 0);

  }

}

void llvm::clearAsExpectedChecks(ShadowBB* BB) {

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i)
    BB->insts[i].needsRuntimeCheck = RUNTIME_CHECK_NONE;

}

// If an assumption is to be made about any value in this function, flag it for runtime check generation.
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

// Flag required runtime checks that apply to all instances of this function.
void IntegrationAttempt::noteAsExpectedChecks(ShadowBB* BB) {

  if(invarInfo->pathConditions)
    noteAsExpectedChecksFrom(BB, invarInfo->pathConditions->AsDefIntPathConditions, UINT_MAX);

}

// Flag required runtime checks relating a function in the target call stack, or to a function in general as above.
void InlineAttempt::noteAsExpectedChecks(ShadowBB* BB) {

  if(targetCallInfo)
    noteAsExpectedChecksFrom(BB, pass->pathConditions.AsDefIntPathConditions, targetCallInfo->targetStackDepth);

  IntegrationAttempt::noteAsExpectedChecks(BB);

}

// Apply all assumptions that are expressed as effects on (symbolic) memory, that apply from block BB.
void IntegrationAttempt::applyMemoryPathConditions(ShadowBB* BB, bool inLoopAnalyser, bool inAnyLoop) {
  
  if(invarInfo->pathConditions)
    applyMemoryPathConditionsFrom(BB, *invarInfo->pathConditions, UINT_MAX, inLoopAnalyser, inAnyLoop);

}

// Apply all assumptions that are expressed as effects on (symbolic) memory, that apply from block BB. Account
// for conditions that relate to a given target call stack, and then to this function in general.
void InlineAttempt::applyMemoryPathConditions(ShadowBB* BB, bool inLoopAnalyser, bool inAnyLoop) {

  if(targetCallInfo)
    applyMemoryPathConditionsFrom(BB, pass->pathConditions, targetCallInfo->targetStackDepth, inLoopAnalyser, inAnyLoop);

  IntegrationAttempt::applyMemoryPathConditions(BB, inLoopAnalyser, inAnyLoop);

}

void IntegrationAttempt::applyMemoryPathConditionsFrom(ShadowBB* BB, PathConditions& PC, uint32_t targetStackDepth, bool inLoopAnalyser, bool inAnyLoop) {

  for(std::vector<PathCondition>::iterator it = PC.StringPathConditions.begin(),
	itend = PC.StringPathConditions.end(); it != itend; ++it) {

    applyPathCondition(&*it, PathConditionTypeString, BB, targetStackDepth);

  }

  for(std::vector<PathCondition>::iterator it = PC.IntmemPathConditions.begin(),
	itend = PC.IntmemPathConditions.end(); it != itend; ++it) {  

    applyPathCondition(&*it, PathConditionTypeIntmem, BB, targetStackDepth);

  }

  for(std::vector<PathCondition>::iterator it = PC.StreamPathConditions.begin(),
	itend = PC.StreamPathConditions.end(); it != itend; ++it) {

    applyPathCondition(&*it, PathConditionTypeStream, BB, targetStackDepth);

  }

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(),
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx == targetStackDepth && it->BB == BB->invar->BB) {

      // Insert a model call that notionally occurs before the block begins.
      // Notionally its callsite is the first instruction in BB; this is probably not a call
      // instruction, but since its arguments are pushed in rather than pulled it doesn't matter.

      if(!it->IA) {
	InlineAttempt* SymIA = new InlineAttempt(pass, *it->F, &BB->insts[0], this->nesting_depth + 1, true);
	it->IA = SymIA;
      }

      for(unsigned i = 0, ilim = it->args.size(); i != ilim; ++i) {

	PathFuncArg& A = it->args[i];

	ShadowArg* SArg = &(it->IA->argShadows[i]);
	ShadowValue Op = getPathConditionSV(A.stackIdx, A.instBB, A.instIdx);

	// Can't use noteIndirectUse since that deals with allocations being used by synthetic
	// pointers and the similar case of FDs.
	if(Op.isInst() || Op.isArg()) {
	  std::vector<std::pair<ShadowValue, uint32_t> >& Users = GlobalIHP->indirectDIEUsers[Op];
	  // TODO: figure out what to register the dependency against
	  // when indirectDIEUsers stops being a simple set of used things.
	}
    
	release_assert((!SArg->i.PB) && "Path condition functions shouldn't be reentrant");

	copyImprovedVal(Op, SArg->i.PB);

      }

      it->IA->activeCaller = &BB->insts[0];
      it->IA->analyseNoArgs(inLoopAnalyser, inAnyLoop, stack_depth);

      // This is a bit of a hack -- the whole context is obviously ordained not to
      // be committed from the start and only exists for its side-effects -- but
      // path conditions are rare and it's simplest to treat it like we decided to disable
      // the context after the fact like the normal InlineAttempt analyse path.
      it->IA->markAllocationsAndFDsCommitted();
      it->IA->releaseCommittedChildren();

      doCallStoreMerge(BB, it->IA);

      if(!inLoopAnalyser) {

	  doTLCallMerge(BB, it->IA);

	  // Symbolic function has no effect on DSE: it doesn't register its stores for later
	  // elimination, and doesn't contribute to eliminating other stores either.

	  doDSECallMerge(BB, it->IA);
	  BB->dseStore->dropReference();
	  BB->dseStore = it->IA->backupDSEStore;
	  BB->dseStore->refCount++;

	  it->IA->releaseBackupStores();

      }
      
      // Make sure a failed version of this block and its successors is created:
      getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(BB->invar->idx, 0);

    }

  }

}

// Can this function return having bailed to unspecialised code due to a
// runtime check failure?
bool InlineAttempt::hasFailedReturnPath() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    if(!isa<ReturnInst>(BBI->BB->getTerminator()))
      continue;

    if(blocksReachableOnFailure && blocksReachableOnFailure->count(i))
      return true;

  }

  return false;

}

// Functions to generate unspecialised paths out of specialised code,
// and to generate runtime checks that branch into them.

// "Failed" throughout refers to blocks reachable upon runtime check failure, e.g. because
// the real situation did not match an assumption given by the user.

void IntegrationAttempt::initFailedBlockCommit() {}

void InlineAttempt::initFailedBlockCommit() {

  if(pass->omitChecks)
    release_assert(!blocksReachableOnFailure);

  // We won't need PHIForwards or ForwardingPHIs until the instruction commit phase;
  // they will remain 0-sized and unallocated until then.
  // failedBlockMap only needs to hold a little more than one entry per failed block here.
  // Add a fudge factor to (a) avoid resizes to 64 and (b) account for path condition splits.

  // If there aren't any failed blocks, we don't need any of these!
  if(!blocksReachableOnFailure) {
    failedBlockMap = 0;
    PHIForwards = 0;
    ForwardingPHIs = 0;
    return; 
  }

  failedBlocks.resize(nBBs);
  failedBlockMap = new ValueToValueMapTy(NextPowerOf2((blocksReachableOnFailure->size() * 3) - 1));
  PHIForwards = new DenseMap<std::pair<Instruction*, BasicBlock*>, PHINode*>();
  ForwardingPHIs = new DenseSet<PHINode*>();

}

void IntegrationAttempt::finishFailedBlockCommit() {}

void InlineAttempt::finishFailedBlockCommit() {

  delete failedBlockMap; failedBlockMap = 0;
  delete PHIForwards; PHIForwards = 0;
  delete ForwardingPHIs; ForwardingPHIs = 0;

}

// Helper for matching (BB, stackIdx) tuples
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

// Returns the number of path conditions that will be checked /before the start of BB/.
// This does not include conditions listed in AsDefIntPathConditions which are checked
// as the instruction becomes defined (hence the name), in the midst of the block.
uint32_t LLPEAnalysisPass::countPathConditionsAtBlockStart(ShadowBBInvar* BB, IntegrationAttempt* IA) {

  uint32_t total = 0;
  if(IA->invarInfo->pathConditions)
    total = countPathConditionsAtBlockStartIn(BB, UINT_MAX, *IA->invarInfo->pathConditions);
  
  IATargetInfo* Info = IA->getFunctionRoot()->targetCallInfo;
  if(Info)
    total += countPathConditionsAtBlockStartIn(BB, Info->targetStackDepth, pathConditions);

  return total;

}

// Fetch the result of the given instruction / block / stack depth. Some magic values:
// BB might be null indicating a global value, or ULONG_MAX indicating an argument.
// stackIdx might be UINT_MAX indicating we should search this context.
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

// Generate a check that verifies a user assumption, branching to unspecialised code if it fails.
// emitBlockIt points to the CommittedBlock where the test code should be emitted. We should move it
// to point at the next block as a side-effect.
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

      testRoot = GetElementPtrInst::Create(Int8Ptr, testRoot, ArrayRef<Value*>(&offConst, 1), "", emitBlock);

    }

  default:
    break;

  }

  switch(Ty) {

  case PathConditionTypeIntmem:

    {
      Type* PtrTy = PointerType::getUnqual(Cond.u.val->getType());
      if(PtrTy != testRoot->getType())
	testRoot = new BitCastInst(testRoot, PtrTy, "", emitBlock);
      testRoot = new LoadInst(testRoot, "", false, emitBlock);
    }
    
    // FALL THROUGH TO:

  case PathConditionTypeInt:

    if(testRoot->getType() != Cond.u.val->getType())
      testRoot = new SExtInst(testRoot, Cond.u.val->getType(), "", emitBlock);

    resultInst = emitCompositeCheck(testRoot, Cond.u.val, emitBlock);
    break;

  case PathConditionTypeString:

    {

      Type* IntTy = Type::getInt32Ty(LLC);
      Type* StrcmpArgTys[2] = { Int8Ptr, Int8Ptr };
      FunctionType* StrcmpType = FunctionType::get(IntTy, ArrayRef<Type*>(StrcmpArgTys, 2), false);

      Function* StrcmpFun = getGlobalModule()->getFunction("strcmp");
      if(!StrcmpFun)
	StrcmpFun = cast<Function>(getGlobalModule()->getOrInsertFunction("strcmp", StrcmpType).getCallee());
      
      if(testRoot->getType() != Int8Ptr) {
	Instruction::CastOps Op = CastInst::getCastOpcode(testRoot, false, Int8Ptr, false);
	testRoot = CastInst::Create(Op, testRoot, Int8Ptr, VerboseNames ? "testcast" : "", emitBlock);
      }
      
      Value* CondCast = ConstantExpr::getBitCast(Cond.u.val, Int8Ptr);
	
      Value* StrcmpArgs[2] = { CondCast, testRoot };
      CallInst* CmpCall = CallInst::Create(StrcmpFun, ArrayRef<Value*>(StrcmpArgs, 2), VerboseNames ? "assume_test" : "", emitBlock);
      CmpCall->setCallingConv(StrcmpFun->getCallingConv());
      resultInst = new ICmpInst(*emitBlock, CmpInst::ICMP_EQ, CmpCall, Constant::getNullValue(CmpCall->getType()), "");

      break;

    }

  default:
    
    release_assert(0 && "Bad path condition type");
    llvm_unreachable("Bad path condition type");

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
  
  release_assert(emitBlockIt->specBlock && failTarget && resultInst);
  BranchInst::Create(emitBlockIt->specBlock, failTarget, resultInst, emitBlock);

}

void IntegrationAttempt::emitPathConditionChecksIn(std::vector<PathCondition>& Conds, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it)
    emitPathConditionCheck(*it, Ty, BB, stackIdx, emitBlockIt);

}

// Emit all path condition checks that should take place at the start of block BB.
void IntegrationAttempt::emitPathConditionChecks2(ShadowBB* BB, PathConditions& PC, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt) {

  // Integer, string and integer-memory checks are all straightforward check-and-branch affairs.
  emitPathConditionChecksIn(PC.IntPathConditions, PathConditionTypeInt, BB, stackIdx, emitBlockIt);
  emitPathConditionChecksIn(PC.StringPathConditions, PathConditionTypeString, BB, stackIdx, emitBlockIt);
  emitPathConditionChecksIn(PC.IntmemPathConditions, PathConditionTypeIntmem, BB, stackIdx, emitBlockIt);

  // Function path conditions specify that we should insert a call to a verifier function,
  // then check its return value is as required.

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

      ShadowValue argVal = getPathConditionSV(argit->stackIdx, argit->instBB, argit->instIdx);
      verifyArgs[i] = getCommittedValue(argVal);

      if(!verifyArgs[i]) {

	// Path conditions can request args in other contexts if there is a target stack.
	// They might be legitimately not committed yet; rather than use the patch-refs
	// system again, just re-synthesise the instruction here.

	ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(argVal));
	release_assert(IVS);
	release_assert(IVS->Values.size() == 1);
	verifyArgs[i] = trySynthVal(0, it->VerifyF->getFunctionType()->getParamType(i), IVS->SetType, IVS->Values[0], emitBlock);

      }

      release_assert(verifyArgs[i]);
      
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
    release_assert(emitBlockIt->specBlock && failTarget && VCond);
    BranchInst::Create(emitBlockIt->specBlock, failTarget, VCond, emitBlock);

  }

}

// Emit all path condition checks that need to take place at the start of this BB.
// Return an iterator pointing into its committed (sub-)block list pointing at the block
// where specialised code should be emitted (the first X sub-blocks having been used to
// emit check instructions and consequent branches to unspecialised code)
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

// Skip over extra PHI nodes introduced at the top of an emitted unspecialised code block,
// to account for extra control-flow merges from specialised code.
BasicBlock::iterator InlineAttempt::skipMergePHIs(BasicBlock::iterator it) {

  PHINode* PN;
  while((PN = dyn_cast<PHINode>(it)) && ForwardingPHIs->count(PN))
    ++it;

  return it;

}

// Does this basic block branch direct to unspecialised code, e.g. because an ordinary edge routes
// away from the path the user is interested in specialising?
bool IntegrationAttempt::hasLiveIgnoredEdges(ShadowBB* BB) {

  if(pass->omitChecks)
    return false;

  ShadowBBInvar* SBBI = BB->invar;

  for(uint32_t i = 0, ilim = BB->invar->succIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* TBBI = getBBInvar(BB->invar->succIdxs[i]);

    if(edgeBranchesToUnspecialisedCode(SBBI, TBBI) && (!isExceptionEdge(SBBI, TBBI)) && !edgeIsDead(SBBI, TBBI))
      return true;

  }

  return false;

}

// If the user has given a target call (a particular call instruction within this function
// that is the only interesting target for specialisation), does the given edge branch away from it
// (i.e. onto a path that cannot each it?)
bool InlineAttempt::isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx) {

  if(targetCallInfo && !targetCallInfo->mayReachTarget.count(BBIdx)) {  

    if(predBlockIdx != targetCallInfo->targetCallBlock && targetCallInfo->mayReachTarget.count(predBlockIdx)) {
      
      if(!edgeIsDead(getBBInvar(predBlockIdx), getBBInvar(BBIdx)))
	return true;
      
    }    

  }

  return false;

}

// BB predBlockIdx ends with an invoke instruction. BBIdx is one of its successors. Gather a list of invoke
// instruction instances that might follow this edge, breaking from specialised to unspecialised code as they
// do so, due to an exception being thrown within the invoke instance or already having broken to unspec
// code within the invoke.
bool IntegrationAttempt::gatherInvokeBreaks(uint32_t predBlockIdx, uint32_t BBIdx, ShadowInstIdx predOp, 
					    Value* predV, SmallVector<std::pair<Value*, BasicBlock*>, 4>* newPreds, 
					    SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* newEdgeSources) {

  ShadowBBInvar* predBBI = getBBInvar(predBlockIdx);
  
  PeelAttempt* LPA;

  if(predBBI->naturalScope != L && 
     ((!L) || L->contains(predBBI->naturalScope)) &&
     (LPA = getPeelAttempt(immediateChildLoop(L, predBBI->naturalScope))) &&
     LPA->isEnabled() && LPA->isTerminated()) {

    // We will emit code for each loop instance individually. Find the corresponding instruction
    // for each instance.

    bool ret = false;

    for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
      ret |= LPA->Iterations[i]->gatherInvokeBreaks(predBlockIdx, BBIdx, predOp, predV, newPreds, newEdgeSources);

    return ret;

  }
  else {

    // Edge 0 is the ordinary continuation; it leads to unspecialised code (via a test) if the call can fail and is emitted OOL,
    // or via the call's failedReturnBlock if it is emitted inline.
    // Edge 1 is the exceptional continuation, and always leads to unspecialised code if it is live.

    if(edgeIsDead(predBBI, getBBInvar(BBIdx)))
      return false;

    ShadowBB* BB = getBB(predBlockIdx);
    BasicBlock* predBlock = 0;

    if(BBIdx == predBBI->succIdxs[0]) {

      InlineAttempt* IA;
      
      // Where the following code gets BB->committedBlocks.back().breakBlock, this will be the
      // breakBlock corresponding to the CommittedBlock *after* the invoke instruction itself.

      if((IA = getInlineAttempt(&BB->insts.back())) && IA->isEnabled()) {
	
	if(IA->hasFailedReturnPath()) {

	  // Enabled invoke context with a failed path?
	  if(IA->mustCommitOutOfLine())
	    predBlock = BB->committedBlocks.back().breakBlock;
	  else
	    predBlock = IA->failedReturnBlock;

	}
	
      }
      else if(requiresRuntimeCheck(ShadowValue(&BB->insts.back()), false)) {

	// Disabled invoke context with a checked return value?
	predBlock = BB->committedBlocks.back().breakBlock;

      }

    }
    else if(BBIdx == predBBI->succIdxs[1]) {

      // As this is the exception edge, it isn't legal to interpose a break block
      // between the edge leaving the invoke and the landingpad block. Thus this
      // must return the breakBlock of a CommittedBlock where .breakBlock == .specBlock.
      predBlock = BB->getCommittedBreakBlockAt(predBBI->insts.size() - 1);

    }

    if(predBlock) {

      if(newPreds) {
	Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV, predBlock->getTerminator());
	release_assert(specV);
	newPreds->push_back(std::make_pair(specV, predBlock));
      }
      else if(newEdgeSources) {
	newEdgeSources->push_back(std::make_pair(predBlock, this));
      }

    }
    
    return !!predBlock;
    
  }

}

// Can any invoke instruction at the end of block 'breakFrom' enter unspecialised code
// at 'breakTo'?
bool IntegrationAttempt::hasInvokeBreaks(uint32_t breakFrom, uint32_t breakTo) {

  if(!isa<InvokeInst>(getBBInvar(breakFrom)->BB->getTerminator()))
    return false;
  return gatherInvokeBreaks(breakFrom, breakTo, ShadowInstIdx(), 0, 0, 0);

}

// Find checks that precede the first specialised instruction in block BBIdx, which check against
// concurrent modifcation to a file whose contents we're using for specialisation.
// This will lead to code of the form if(fileHasChanged()) { unspecialisedCode } else { specialisedCode }
bool IntegrationAttempt::gatherTopOfBlockVFSChecks(uint32_t BBIdx, ShadowInstIdx predOp, Value* predV,
						   SmallVector<std::pair<Value*, BasicBlock*>, 4>* newPreds, 
						   SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* newEdgeSources) {

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  
  PeelAttempt* LPA;

  if(BBI->naturalScope != L && 
     ((!L) || L->contains(BBI->naturalScope)) &&
     (LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) &&
     LPA->isEnabled() && LPA->isTerminated()) {

    bool ret = false;

    for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
      ret |= LPA->Iterations[i]->gatherTopOfBlockVFSChecks(BBIdx, predOp, predV, newPreds, newEdgeSources);

    return ret;

  }
  else {

    ShadowBB* BB = getBB(BBIdx);
    if(!BB)
      return false;
    if(BB->insts[0].needsRuntimeCheck != RUNTIME_CHECK_READ_LLIOWD)
      return false;

    BasicBlock* predBlock = BB->getCommittedBreakBlockAt(0);

    if(newPreds) {
      Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV, predBlock->getTerminator());
      release_assert(specV);
      newPreds->push_back(std::make_pair(specV, predBlock));
    }
    else if(newEdgeSources) {
      newEdgeSources->push_back(std::make_pair(predBlock, this));
    }

    return true;
    
  }

}

bool IntegrationAttempt::hasTopOfBlockVFSChecks(uint32_t idx) {

  return gatherTopOfBlockVFSChecks(idx, ShadowInstIdx(), 0, 0, 0);

}

// Gather branches from specialised to unspecialised code at the end of block predBlockIdx and leading to
// unspecialised block BBIdx. These could be because the user is not interested in specialising BBIdx,
// or due to a break from an invoke instruction at the end of predBlock. These breaks are distinct from
// mid-block breaks resulting from introduced checks, in that they follow the existing CFG.
void InlineAttempt::gatherSpecToUnspecEdges(uint32_t predBlockIdx, uint32_t BBIdx, ShadowInstIdx predOp, 
					    Value* predV, SmallVector<std::pair<Value*, BasicBlock*>, 4>& newPreds) {

  if(isSpecToUnspecEdge(predBlockIdx, BBIdx)) {
    
    BasicBlock* specPred = getBB(predBlockIdx)->committedBlocks.back().breakBlock;
    Value* specV = getSpecValue(predOp.blockIdx, predOp.instIdx, predV, specPred->getTerminator());
    release_assert(specV);
    newPreds.push_back(std::make_pair(specV, specPred));
    
  }
  else if(isa<InvokeInst>(getBBInvar(predBlockIdx)->BB->getTerminator())) {

    gatherInvokeBreaks(predBlockIdx, BBIdx, predOp, predV, &newPreds, 0);

  }

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

// Find the version of V that is usable in unspecialised block UseBlock, which might involve
// extra PHI nodes inserted to account for specialised-to-unspecialised branches.
Value* InlineAttempt::getLocalFailedValue(Value* V, BasicBlock* UseBlock) {

  Value* Ret = tryGetLocalFailedValue(V, UseBlock);
  release_assert(Ret);
  return Ret;

}

// As above, but returns null if V is only computed in specialised code.
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

// Collect block instances that will branch from specialised to unspecialised code, mid-block blockIdx, between instIdx and its successor.
// This means we're performing a test *after* instruction instIdx has been computed (e.g. %x = load %p; %as_expected = $x eq 0)
// or because we need a test *before* the next instruction (e.g. checking for concurrent file modification before a read call)
// As with most of these gather-spec-to-unspec functions, we must account for peeled loop iterations. 
// Out-param 'edges' is not blanked. Return number of edges added.
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

  uint32_t oldEdgesSize = edges.size();

  ShadowInstruction* SI = &BB->insts[instIdx];
  InlineAttempt* IA;

  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->failedReturnBlock)
      edges.push_back(std::make_pair(IA->failedReturnBlock, this));
    else if(IA->commitsOutOfLine() && IA->hasFailedReturnPath())
      edges.push_back(std::make_pair(BB->getCommittedBreakBlockAt(instIdx), this));

  }

  // Does this context break at this instruction?
  // It does if this instruction requires an as-expected check ("requiresRuntimeCheck"), 
  // OR if the NEXT instruction requires a special check.
  if(edges.size() == oldEdgesSize) {

    if(requiresRuntimeCheck(ShadowValue(SI), false) || SI->needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP)
      edges.push_back(std::make_pair(BB->getCommittedBreakBlockAt(instIdx), this));

  }

  // Add for a failing VFS op even if we've already found other failing paths above:
  // it is possible for the NEXT instruction (i + 1) to have an LLIOWD check,
  // which backs up an instruction to repeat the VFS op, and for the CURRENT instruction (i)
  
  if(BB->insts.size() > instIdx + 1 && BB->insts[instIdx + 1].needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD)
    edges.push_back(std::make_pair(BB->getCommittedBreakBlockAt(instIdx + 1), this));

  if(edges.size() != oldEdgesSize && L)
    return 1;
  else
    return 0;

}

// V is a Value in the original (pre-specialisation) program; blockIdx / instIdx correspond to V. Get the version of V that should be
// used in UseBlock. If there is no unspecialised version of V, use the specialised version -- otherwise, we might directly use
// the unspecialised clone of V, or might use some Phi node that has been inserted to merge the unspecialised and specialised variants.
// If we need to insert e.g. type casts, insert them before InsertBefore, which is an Instruction in the emitted program.
Value* InlineAttempt::getUnspecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, BasicBlock* UseBlock, Instruction* InsertBefore) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    // Pred is not an instruction. Use the same val whether consuming unspec or spec versions.
    return getSpecValue(blockIdx, instIdx, V, InsertBefore);

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    Value* Ret = tryGetLocalFailedValue(V, UseBlock);
    if(!Ret)
      Ret = getSpecValue(blockIdx, instIdx, V, InsertBefore);
    return Ret;

  }  

}

// Get a specialised variant of V (an original-program Value). blockIdx / instIdx refer to the same
// original program location. If V / blockIdx / instIdx refers to a child loop of this context,
// we're talking about the last loop iteration (and since we insist on Loop-closed SSA form,
// we're necessarily doing this in the context of an exit PHI).
// Note this only makes sense because at present only loops with a single established iteration count will
// be emitted in peeled form.
Value* IntegrationAttempt::getSpecValueAnyType(uint32_t blockIdx, uint32_t instIdx, Value* V) {

  if(blockIdx == INVALID_BLOCK_IDX) {

    if(Argument* A = dyn_cast<Argument>(V))
      return getFunctionRoot()->getCommittedValue(&getFunctionRoot()->argShadows[A->getArgNo()]);
    else
      return V;

  }
  else {

    // Pred is an instruction. If only a specialised definition exists, use that on both spec
    // and unspec incoming paths.

    ShadowInstruction* specI = getInst(blockIdx, instIdx);
    if((!specI) || !specI->committedVal)
      return 0;
    else {

      // Rise if appropriate:
      ShadowBBInvar* BBI = getBBInvar(blockIdx);
      PeelAttempt* LPA;
      if(BBI->naturalScope != L && 
	 ((!L) || L->contains(BBI->naturalScope)) &&
	 (LPA = getPeelAttempt(immediateChildLoop(L, BBI->naturalScope))) &&
	 LPA->isTerminated() &&
	 LPA->isEnabled()) {

	return LPA->Iterations.back()->getSpecValueAnyType(blockIdx, instIdx, V);
	  
      }
      else {
     
	return getCommittedValue(ShadowValue(specI));

      }

    }

  }  

}

// As above, but additionally insert type conversions as required to match the orignal V.
Value* IntegrationAttempt::getSpecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, Instruction* InsertBefore) {

  Value* Ret = getSpecValueAnyType(blockIdx, instIdx, V);
  if(!Ret)
    return 0;

  if(Ret->getType() != V->getType()) {

    if(Instruction* I = dyn_cast<Instruction>(Ret)) {

      BasicBlock::iterator BI(I);
      ++BI;

      if(BI == I->getParent()->end()) {

	// Should only happen to a block that is currently being written.
	Ret = getValAsType(Ret, V->getType(), I->getParent());

      }
      else {

	Ret = getValAsType(Ret, V->getType(), &*BI);
	
      }

    }
    else {

      release_assert(isa<Constant>(Ret));
      Ret = getConstAsType(cast<Constant>(Ret), V->getType());

    }

  }

  return Ret;

}

// Gather specialised versions of bbIdx / instIdx, along with the predecessor blocks coming from specialised to unspecialised code due to top-of-block path condition tests.
// Either provide the values and blocks or the blocks and contexs, depending on the caller's requirements.
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

    Value* PCVal = 0;

    for(uint32_t i = 0, ilim = pass->countPathConditionsAtBlockStart(BB->invar, this); i != ilim; ++i) {

      // Assert block starts at offset 0, as with all PC test blocks.
      release_assert(BB->committedBlocks[i].startIndex == 0);

      if(preds) {
	if(!PCVal)
	  PCVal = getCommittedValue(ShadowValue(&BB->insts[instIdx]));	  
	preds->push_back(std::make_pair(PCVal, BB->committedBlocks[i].breakBlock));
      }
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
  //     (i.e. this is an ignored block, or has invoke predecessors that fail), merge both.
  // * Otherwise use just the unspec version.
  // * If this block has cross-edges at the top (due to path condition checks), 
  //     merge in the companion of this PHI node on each of those edges.
  //     Note this case does not apply to failing invokes, which branch to failed code
  //     BEFORE the specialised version of this block's phi nodes.

  // Note that if we don't have a companion BB then no augmentation is necessary: we are only
  // called this way regarding blocks accessible from within a loop, whose headers are not merge points.

  ShadowBBInvar* BBI = getBBInvar(BBIdx);
  uint32_t instIdx = 0;

  // If BBI is a loop header, skip the latch predecessor for the time being and we'll come back to it
  // after the latch operand is committed.
  
  uint32_t ignorePred = UINT_MAX;

  if(BBI->naturalScope) {

    const ShadowLoopInvar* LInfo = BBI->naturalScope;
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

      gatherSpecToUnspecEdges(predBlockIdx, BBIdx, predOp, predV, newPreds);

      if(failedBlocks[predBlockIdx].size()) {

	BasicBlock* unspecPred = failedBlocks[predBlockIdx].back().first;
	Value* unspecV = getUnspecValue(predOp.blockIdx, predOp.instIdx, predV, unspecPred, unspecPred->getTerminator());
	release_assert(unspecV);
	newPreds.push_back(std::make_pair(unspecV, unspecPred));

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

// Collect basic block indices that can reach UseBBI by setting predBlocks[bbIdx] to ((Instruction*)ULONG_MAX, instIdx) for each one (actual Instructions will be synthesised by our caller)
// The instIdx there indicates it is needed up to that instruction index, which can be relevant if blocks are split to introduce specialised-to-unspecialised
// edges. LimitBBI is the definition block. It terminates the search since it must dominate all users in the original program BB graph.
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

// Create a PHI node merging some specialised instances of SI and some unspecialised variants of it (given as emitted-program BB / Instruction)
// The specialised instance path might insert type conversions before the predecessor block's terminator.
static PHINode* insertMergePHI(ShadowInstructionInvar& SI, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& specPreds, SmallVector<std::pair<BasicBlock*, Instruction*>, 4>& unspecPreds, BasicBlock* InsertBB) {

  PHINode* NewNode = PHINode::Create(SI.I->getType(), 0, VerboseNames ? "clonemerge" : "", &*(InsertBB->begin()));
  
  for(SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>::iterator it = specPreds.begin(), itend = specPreds.end(); it != itend; ++it) {

    BasicBlock* PredBB = it->first;
    Value* Op = getValAsType(it->second->getSpecValue(SI.parent->idx, SI.idx, SI.I, PredBB->getTerminator()), 
			     NewNode->getType(), PredBB->getTerminator());
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
  
  SmallVector<std::pair<const ShadowLoopInvar*, PHINode*>, 4> loopStack;
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

      const ShadowLoopInvar* currentLoop = loopStack.back().first;
      if(currentLoop != thisBBI->naturalScope) {

	if((!currentLoop) || currentLoop->contains(thisBBI->naturalScope)) {

	  // Entered a new loop.
	  const ShadowLoopInvar* LInfo = thisBBI->naturalScope;

	  // The entire loop should be in our scope of consideration:
	  release_assert(OrigSI.parent->idx <= LInfo->preheaderIdx);
	  release_assert(OrigSI.parent->idx + predBlocks.size() >= LInfo->latchIdx);

	  // Are there any breaks in the loop body? These can be due to instruction checks
	  // or path conditions but not can't-reach-target conditions.

	  bool loopHasBreaks = false;
	  for(uint32_t j = LInfo->headerIdx, jlim = LInfo->latchIdx + 1; j != jlim && !loopHasBreaks; ++j) {

	    ShadowBBInvar* jbbi = getBBInvar(j);

	    // Block is broken into pieces due to a mid-block check?
	    if(failedBlocks[j].size() > 1)
	      loopHasBreaks = true;

	    // Will there be incoming edges from specialised code due to path conditions?
	    else if(pass->countPathConditionsAtBlockStart(jbbi, this))
	      loopHasBreaks = true;

	    // Do invoke instructions within the loop cause break edges on an existing block boundary?
	    else if(isa<InvokeInst>(jbbi->BB->getTerminator())) {

	      if(jbbi->naturalScope->contains(getBBInvar(jbbi->succIdxs[0])->naturalScope) &&
		 hasInvokeBreaks(jbbi->idx, jbbi->succIdxs[0]))
		loopHasBreaks = true;
	      else if(jbbi->naturalScope->contains(getBBInvar(jbbi->succIdxs[1])->naturalScope) &&
		      hasInvokeBreaks(jbbi->idx, jbbi->succIdxs[1]))
		loopHasBreaks = true;

	    }

	    else if(hasTopOfBlockVFSChecks(jbbi->idx))
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

	    const ShadowLoopInvar* exitLoop = loopStack.back().first;

	    PHINode* PN = loopStack.back().second;
	    loopStack.pop_back();
	    // Lowest level loop should never be popped.
	    release_assert(loopStack.size());

	    PN->addIncoming(predBlocks[exitLoop->latchIdx - OrigSI.parent->idx].first, 
			    failedBlocks[exitLoop->latchIdx].back().first);

	  }

	  // Now process the block as per usual.

	}

      }
      
      // Create a PHI merge at the top of this block if:
      // (a) there are unspec->spec edges due to ignored blocks, 
      // (b) there are path condition breaks to top of block,
      // (c) there are invoke instructions branching here on test failure or exception,
      // (d) there are checked VFS instructions at the top of the block,
      // or (e) unspecialised predecessor blocks are using different versions of the 
      // instruction in question. Also always insert a merge at the loop header if we
      // get to here, as some disagreement is sure to arise between the preheader->header
      // and latch->header edges.

      BasicBlock* insertBlock = failedBlocks[thisBlockIdx].front().first;

      // Cases (a) and (b).

      uint32_t nCondsHere = pass->countPathConditionsAtBlockStart(thisBBI, this);
      bool isSpecToUnspec = isSimpleMergeBlock(thisBlockIdx);

      bool shouldMergeHere = nCondsHere != 0 || isSpecToUnspec || headerPred.first != 0;

      // Case (d): failing VFS instructions exist that will target the start of this block.
      if((!shouldMergeHere) && hasTopOfBlockVFSChecks(thisBBI->idx))
	shouldMergeHere = true;

      if(!shouldMergeHere) {

	// Case (c): invoke breaks, either due to checked invoke instruction
	// or due to exceptional control flow that leads here.
      
	for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim && !shouldMergeHere; ++j) {

	  if(hasInvokeBreaks(thisBBI->predIdxs[j], thisBBI->idx))
	    shouldMergeHere = true;

	}

      }

      if(!shouldMergeHere) {

	// Case (e): do predecesors disagree about which version of the instruction they're using?

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

	// Some specialised predecessors branch straight to unspec code.
	for(uint32_t j = 0, jlim = thisBBI->predIdxs.size(); j != jlim; ++j) {

	  uint32_t pred = thisBBI->predIdxs[j];
	  ShadowBBInvar* predBBI = getBBInvar(pred);

	  if(isSpecToUnspec && isSpecToUnspecEdge(pred, thisBlockIdx))
	    specPreds.push_back(std::make_pair(getBB(pred)->committedBlocks.back().breakBlock, this));
	  
	  if(isa<InvokeInst>(predBBI->BB->getTerminator()))
	    gatherInvokeBreaks(predBBI->idx, thisBBI->idx, ShadowInstIdx(), 0, 0, &specPreds);

	}

	if(nCondsHere) {

	  // Adds to specPreds for each loop iteration that can break here:
	  gatherPathConditionEdges(thisBlockIdx, 0, 0, &specPreds);

	}

	gatherTopOfBlockVFSChecks(thisBBI->idx, ShadowInstIdx(), 0, 0, &specPreds);

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

    const ShadowLoopInvar* exitLoop = loopStack.back().first;
    PHINode* PN = loopStack.back().second;
    loopStack.pop_back();
    // Lowest level loop should never be popped.
    release_assert(loopStack.size());

    PN->addIncoming(predBlocks[exitLoop->latchIdx - OrigSI.parent->idx].first, 
		    failedBlocks[exitLoop->latchIdx].back().first);

  }

}

// Are there any specialised instances of BBI in this context or a child?
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

  // If skipTestedInst is true then skip creating PHI forwards of the second-to-last instruction 
  // (i.e. the instruction before the terminator) as that will be special-cased in populateFailedBlock 
  // at the start of the next subblock.

  BasicBlock::iterator BE = BB->end();
  Instruction* testedInst;
  if(skipTerm) {
    --BE;
    if(skipTestedInst) {
      --BE;
      testedInst = &*BE;
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
    Instruction* I = &*BI;
    
    ReturnInst* RI = dyn_cast<ReturnInst>(BI);
    if(RI && !isRootMainCall()) {

      if(failedReturnBlock) {

	// Rewrite into a branch to and contribution to the failed return phi node.
	if(failedReturnPHI) {
	  
	  ReturnInst* OrigRI = cast<ReturnInst>(SII.I);
	  Value* V = OrigRI->getOperand(0);
	  Value* Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, V, BB, RI);
	  release_assert(Ret);
	  failedReturnPHI->addIncoming(Ret, BB);

	}

	RI->eraseFromParent();
	BranchInst::Create(failedReturnBlock, BB);

      }
      else {

	// Out-of-line commit
	release_assert(CommitF);
	Value* Ret;
	Constant* FailFlag = ConstantInt::getFalse(BB->getContext());
	
	if(F.getFunctionType()->getReturnType()->isVoidTy())
	  Ret = FailFlag;
	else {

	  ReturnInst* OrigRI = cast<ReturnInst>(SII.I);
	  Value* V = OrigRI->getOperand(0);
	  Ret = getUnspecValue(SII.operandIdxs[0].blockIdx, SII.operandIdxs[0].instIdx, V, BB, RI);
	  StructType* retType = cast<StructType>(CommitF->getFunctionType()->getReturnType());
	  Type* normalRet = Ret->getType();
	  Constant* undefRet = UndefValue::get(normalRet);
	  Value* aggTemplate = ConstantStruct::get(retType, {undefRet, FailFlag});
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
	  Repl = getUnspecValue(op.blockIdx, op.instIdx, V, BB, I);

	release_assert(Repl);
	((Use*)replit)->set(Repl);

      }

      if(pass->verbosePCs && isa<LandingPadInst>(I)) {

	std::string msg;
	{
	  raw_string_ostream RSO(msg);
	  RSO << "Landed at landing pad inst in block " << BB->getName() << " / " << F.getName() << " / " << SeqNumber << "\n";
	}
	// Insert print before the next instruction:
	++BI;
	emitRuntimePrint(BB, msg, 0, &*BI);
	// Point iterator back at the new instruction:
	--BI;
    
      }

    }

  }

}

// Emit an unspecialised basic block that is known to have no specialised companions.
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

// Fill in bool-vector splitInsts to indicate where this block's specialised-to-unspecialised
// edges will be inserted due to introduced checks.
void IntegrationAttempt::getLocalSplitInsts(ShadowBB* BB, bool* splitInsts) {

  // Stop before the terminator because invoke instructions are treated specially
  // and other kinds of terminator cannot be split points.

  for(uint32_t i = 0, ilim = BB->insts.size() - 1; i != ilim; ++i) {

    ShadowInstruction* SI = &BB->insts[i];
    InlineAttempt* IA;
    if((IA = getInlineAttempt(SI)) && IA->isEnabled() && IA->hasFailedReturnPath())
      splitInsts[i] = true;
    else if(requiresRuntimeCheck(ShadowValue(SI), true)) {

      // Check exit PHIs as a block:
      if(i + 1 != ilim && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[i+1]))
	continue;

      // Special checks require a split BEFORE the instruction:
      if(SI->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD) {

	if(i != 0)
	  splitInsts[i - 1] = true;

      }
      else {
	  
	splitInsts[i] = true;

      }

    }

  }

}

bool IntegrationAttempt::hasSplitInsts(ShadowBB* BB) {

  bool splits[BB->insts.size()];
  memset(splits, 0, sizeof(bool) * BB->insts.size());
  getLocalSplitInsts(BB, splits);

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i)
    if(splits[i])
      return true;

  return false;

}

// Find split points for this context or any child.
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
  if(BB)
    getLocalSplitInsts(BB, splitInsts);

}

// Straightforward basic block cloning, optionally taking a suffix of the block rather than the whole thing.
BasicBlock* IntegrationAttempt::CloneBasicBlockFrom(const BasicBlock* BB,
						    ValueToValueMapTy& VMap,
						    const Twine &NameSuffix, 
						    Function* F,
						    uint32_t startIdx) {

  BasicBlock *NewBB = createBasicBlock(BB->getContext(), "", F, false, /* isfailedblock= */ true);
  if (VerboseNames && BB->hasName()) NewBB->setName(BB->getName()+NameSuffix);

  // Loop over all instructions, and copy them over.
  BasicBlock::const_iterator II = BB->begin();
  std::advance(II, startIdx);

  for (BasicBlock::const_iterator IE = BB->end(); II != IE; ++II) {
    Instruction *NewInst = II->clone();
    if (II->hasName())
      NewInst->setName(II->getName()+NameSuffix);
    NewBB->getInstList().push_back(NewInst);
    VMap[&*II] = NewInst;
    
  }
  
  return NewBB;

}

// If we need any unspecialised variant of BB idx, clone it from the original program code and split it into subblocks
// as required by any specialised-to-unspecialised mid-block edges. Don't actually introduce subblock PHI nodes
// or adjust the top-of-block PHI yet.
void IntegrationAttempt::createFailedBlock(uint32_t idx) {}

void InlineAttempt::createFailedBlock(uint32_t idx) {

  if(!blocksReachableOnFailure)
    return;

  SmallDenseMap<uint32_t, uint32_t, 8>::iterator it = blocksReachableOnFailure->find(idx);
  if(it == blocksReachableOnFailure->end())
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

      std::string SplitName;
      if(VerboseNames)
	SplitName = (toSplit->getName() + ".checksplit").str();

      BasicBlock* splitBlock = 
	toSplit->splitBasicBlock(splitIterator, SplitName);
      failedBlocks[idx].push_back(std::make_pair(splitBlock, i + 1));

      if(!CommitF)
	CommitFailedBlocks.push_back(splitBlock);

      instsSinceLastSplit = 0;

    }
    else {
      
      ++instsSinceLastSplit;

    }

  }

}

// Find the emitted-program BasicBlock containing the unspecialised variant of blockIdx / instIdx.
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

// Gather specialised variants of instBlock / instIdx, along with the predecessor block on the path from specialised to unspecialised code.
void IntegrationAttempt::collectSpecPreds(ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds) {

  if(L != instBlock->naturalScope && ((!L) || L->contains(instBlock->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, instBlock->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->collectSpecPreds(instBlock, instIdx, preds);

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

  BasicBlock* pred = InstBB->getCommittedBreakBlockAt(instIdx);
  Value* committedVal = getCommittedValue(ShadowValue(SI));

  preds.push_back(std::make_pair(committedVal, pred));

}

// Gather block / value instances of a call, representing the case that the call has internally bailed to unspecialised code and so we
// must do the same.
void IntegrationAttempt::collectCallFailingEdges(ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds) {
  
  if(L != instBlock->naturalScope && ((!L) || L->contains(instBlock->naturalScope))) {

    PeelAttempt* LPA;
    if((LPA = getPeelAttempt(immediateChildLoop(L, instBlock->naturalScope))) &&
       LPA->isTerminated() && LPA->isEnabled()) {
      
      for(uint32_t i = 0, ilim = LPA->Iterations.size(); i != ilim; ++i)
	LPA->Iterations[i]->collectCallFailingEdges(instBlock, instIdx, preds);

      return;

    }

  }

  ShadowBB* InstBB = getBB(*instBlock);
  if(!InstBB)
    return;

  ShadowInstruction* SI = &InstBB->insts[instIdx];

  InlineAttempt* IA;
  bool fallThrough = false;

  // Two possible variants: the call commits inline, in which case a special failure-return
  // block will have been created if it can fail internally, or it commits out-of-line
  // and a post-return test will be synthesised to check if it failed.
  if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

    if(IA->commitsOutOfLine() && IA->hasFailedReturnPath())
      fallThrough = true;    
    else if(IA->failedReturnPHI)
      preds.push_back(std::make_pair(IA->failedReturnPHI, IA->failedReturnBlock));

  }
  if(fallThrough || requiresRuntimeCheck(SI, true)) {

    BasicBlock* pred = InstBB->getCommittedBreakBlockAt(instIdx);
    Value* committedVal = getCommittedValue(ShadowValue(&InstBB->insts[instIdx]));
    preds.push_back(std::make_pair(committedVal, pred));
    
  }

}

// Adjust loop header PHI nodes to account for specialised-to-unspecialised edges.
void IntegrationAttempt::populateFailedHeaderPHIs(const ShadowLoopInvar*) {}

void InlineAttempt::populateFailedHeaderPHIs(const ShadowLoopInvar* PopulateL) {

  // Add the latch predecessor to each header phi.
  if(failedBlocks.empty() || failedBlocks[PopulateL->headerIdx].empty())
    return;

  ShadowBBInvar* headerBBI = getBBInvar(PopulateL->headerIdx);
  BasicBlock* headerBlock = failedBlocks[PopulateL->headerIdx].front().first;
  uint32_t instIdx = 0;
 
  for(BasicBlock::iterator BI = skipMergePHIs(headerBlock->begin()), BE = headerBlock->end();
      BI != BE && isa<PHINode>(BI); ++BI, ++instIdx) {
  
    PHINode* PN = cast<PHINode>(BI);
    ShadowInstructionInvar& PNInfo = headerBBI->insts[instIdx];
    PHINode* OrigPN = cast<PHINode>(PNInfo.I);

    for(uint32_t i = 0, ilim = PNInfo.operandBBs.size(); i != ilim; ++i) {

      if(PNInfo.operandBBs[i] == PopulateL->latchIdx) {

	Value* origPredVal = OrigPN->getIncomingValue(i);
	ShadowInstIdx predOp = PNInfo.operandIdxs[i];
	BasicBlock* predBlock = failedBlocks[PopulateL->latchIdx].back().first;
	
	Value* predVal = getUnspecValue(predOp.blockIdx, predOp.instIdx, 
					origPredVal, predBlock, predBlock->getTerminator());

	PN->addIncoming(predVal, predBlock);

	break;

      }

    }
    
  }

}

// Does a test need to be inserted *before* any instance of blockIdx / instIdx?
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

    if(BB->insts[instIdx].needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD)
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
  uint32_t instIdx = it->second;

  return instSpecialTest(idx, instIdx);

}

// Fix the cloned, unspecialised version of block 'idx'. On entry the instructions are straightforward
// clones of the original program block; we need to introduce PHI nodes to account for spec-to-unspec edges.
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
    // failing invoke instructions from a specialised predecessor,
    // specialised blocks that branch direct to unspecialised code, and an unspecialised predecessor.

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

      // Splits at this point cannot be caused by invoke instructions, because they are
      // always terminators and this split is not at the top of the block.

      if(isa<CallInst>(failedI)) {
	if(!failedI->getType()->isVoidTy())
	  collectCallFailingEdges(BBI, failedInst, specPreds);
      }
      else
	collectSpecPreds(BBI, failedInst, specPreds);

      // In the rare circumstance where there is a VFS instruction immediately after a checked
      // call or load, the edges can converge at this failed block because the VFS failing edge
      // branches to a repeat of the VFS instruction. In this case we must add variants of the
      // same failedInst for the VFS failing edge.
      
      // This is only necessary if some specpreds have been found already for the load or call
      // that is the primary motivation for this merge point: otherwise no PHI will be created
      // and the edge form a converging VFS check is irrelevant.
      
      // TODO: improve this ugly hack. I don't use the same algorithm as insertMergePHI
      // purely because call instructions need different treatment, with this path consuming
      // failedReturnPHI instead of their successful return values.

      if(specPreds.size()) {

	SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4> incomingEdges;
	collectSpecIncomingEdges(idx, it->second - 1, incomingEdges);

	for(SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>::iterator it = incomingEdges.begin(),
	      itend = incomingEdges.end(); it != itend; ++it) {

	  bool blockAlreadyDone = false;
	  for(SmallVector<std::pair<Value*, BasicBlock*>, 4>::iterator findit = specPreds.begin(),
		finditend = specPreds.end(); findit != finditend && !blockAlreadyDone; ++findit)
	    if(findit->second == it->first)
	      blockAlreadyDone = true;

	  if(!blockAlreadyDone) {

	    Value* newVal = it->second->getSpecValue(/*blockIdx =*/idx, failedInst, failedI, it->first->getTerminator());
	    specPreds.push_back(std::make_pair(newVal, it->first));

	  }

	}

      }
      
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

	  Value* NewV = getUnspecValue(idx, failedInst, failedI, it->first, predIt->first->getTerminator());
	  release_assert(NewV);
	  NewPN->addIncoming(NewV, predIt->first);

	}

	release_assert(NewPN);
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

// Synthesise a check that composite value realInst == CV.
Instruction* IntegrationAttempt::emitCompositeCheck(Value* realInst, Value* CV, BasicBlock* emitBB) {

  Type* VTy = CV->getType();

  if(VTy->isFloatingPointTy())
    return new FCmpInst(*emitBB, CmpInst::FCMP_OEQ, realInst, CV, VerboseNames ? "check" : "");
  else if(VTy->isIntegerTy() || VTy->isPointerTy() || VTy->isVectorTy())
    return new ICmpInst(*emitBB, CmpInst::ICMP_EQ, realInst, CV, VerboseNames ? "check" : "");
  else if(VTy->isArrayTy() || VTy->isStructTy()) {
    // Fall through
  }
  else {

    release_assert(0 && "Can't compare value of given type");

  }
  
  // Really I'd like to do memcmp to compare two aggregates, but they're value types
  // and may not have addresses. In practice this path is only entered to deal with comparison
  // against struct or array literals from the source program though, so unconditionally unrolling
  // memcmp into value type compares is probably OK.

  release_assert(isa<Constant>(CV));
  release_assert(realInst->getType() == CV->getType());

  CompositeType* CT = cast<CompositeType>(CV->getType());
  unsigned numElements;
  if(StructType* ST = dyn_cast<StructType>(CT))
    numElements = ST->getNumElements();
  else
    numElements = cast<ArrayType>(CT)->getNumElements();

  Instruction* ret = 0;

  for(uint32_t i = 0, ilim = numElements; i != ilim; ++i) {

    Instruction* Op1 = ExtractValueInst::Create(realInst, ArrayRef<unsigned>(&i, 1), "", emitBB);
    Constant* CVC = cast<Constant>(CV);
    Constant* Op2;
    if(isa<ConstantAggregateZero>(CVC))
      Op2 = Constant::getNullValue(Op1->getType());
    else
      Op2 = cast<Constant>(CVC->getOperand(i));
    
    Instruction* thisTest = emitCompositeCheck(Op1, Op2, emitBB);
    if(ret)
      ret = BinaryOperator::CreateAnd(thisTest, ret, "", emitBB);
    else
      ret = thisTest;

  }
  
  release_assert(ret);
  return ret;

}

// Synth a check that realInst == IVS, or if IVS is looser than a constant value, realInst satisfies IVS.
Value* IntegrationAttempt::emitCompareCheck(Value* realInst, const ImprovedValSetSingle* IVS, BasicBlock* emitBB) {

  release_assert(isa<Instruction>(realInst) && "Checked instruction must be residualised");

  Value* thisCheck = 0;
  // If IVS is a set, synthesise a big-or check.
  for(uint32_t j = 0, jlim = IVS->Values.size(); j != jlim; ++j) {

    Value* newCheck;

    // If all we know is a pointer is *somewhere* within a particular object, check if it falls within
    // its bounds. (TOCHECK: what about temporarily OOB pointers?)
    if(IVS->SetType == ValSetTypePB && 
       IVS->Values[j].Offset == LLONG_MAX && 
       IVS->Values[j].V.getAllocSize(this) != ULONG_MAX) {

      ImprovedVal BaseVal = IVS->Values[j];
      BaseVal.Offset = 0;
      ImprovedVal LimitVal = IVS->Values[j];
      LimitVal.Offset = IVS->Values[j].V.getAllocSize(this);

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
      release_assert(thisVal && "Couldn't synthesise value for check?");

      newCheck = emitCompositeCheck(realInst, thisVal, emitBB);

    }

    if(thisCheck)
      thisCheck = BinaryOperator::CreateOr(newCheck, thisCheck, "", emitBB);
    else
      thisCheck = newCheck;

  }
  
  release_assert(thisCheck && "Check synthesis failed?");

  return thisCheck;

}

// Emit a check that the actual value of SI matches what we established about it during specialisation.
Value* IntegrationAttempt::emitAsExpectedCheck(ShadowInstruction* SI, BasicBlock* emitBB) {

  Value* realInst = getCommittedValue(ShadowValue(SI));
  ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI->i.PB);

  if(!IVS) {

    // The expected value is a list-of-extents (ImprovedValSetMulti). Since we're checking a scalar, this
    // typically means a vector-of-pointers or something like a file-descriptor-plus-flags in an int64.

    Type* I64 = Type::getInt64Ty(emitBB->getContext());
    Value* PrevCheck = 0;

    // Ptrtoint if necessary (usually this indicates a union type).
    if(!realInst->getType()->isIntegerTy()) {

      release_assert(realInst->getType()->isPointerTy());
      realInst = new PtrToIntInst(realInst, I64, "", emitBB);
	
    }

    // Check each non-overdef element of the source inst.
    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(SI->i.PB);
    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

      const ImprovedValSetSingle& thisIVS = it.value();

      // Overdef doesn't assert anything about the value...
      if(thisIVS.isWhollyUnknown())
	continue;
      
      // ...and neither does undef.
      if(thisIVS.Values.size() == 1 && thisIVS.SetType == ValSetTypeScalar &&
	 thisIVS.Values[0].V.isVal() && isa<UndefValue>(thisIVS.Values[0].V.getVal()))
	continue;

      // Shift value to least significant position:
      Constant* ShiftAmt = ConstantInt::get(I64, it.start() * 8);
      Value* Shifted = BinaryOperator::CreateLShr(realInst, ShiftAmt, "", emitBB);
      
      // Truncate to size:
      Type* SubTy = Type::getIntNTy(emitBB->getContext(), (it.stop() - it.start()) * 8);
      Value* Truncated = new TruncInst(Shifted, SubTy, "", emitBB);

      Value* ThisCheck = emitCompareCheck(Truncated, &thisIVS, emitBB);
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

// Check that loop exit PHIs are as expected. We check them as a block rather than introduce a block
// split after each one. Emit checks into emitIt; return pointer to the next CommittedBlock.
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

  release_assert(successTarget && failTarget && prevCheck);
  BranchInst::Create(successTarget, failTarget, prevCheck, emitBB); 

  return emitIt;

}

// SI is a memcpy or memmove instruction which we established during specialisation would copy a particular vector
// of values. Check it actually did so at runtime.
Value* IntegrationAttempt::emitMemcpyCheck(ShadowInstruction* SI, BasicBlock* emitBB) {

  release_assert(GlobalIHP->memcpyValues.count(SI) && GlobalIHP->memcpyValues[SI].size() && "memcpyValues not set for checked copy?");

  Value* prevCheck = 0;
  Value* writtenPtr = getCommittedValue(SI->getOperand(0));

  Type* CharPtr = Type::getInt8PtrTy(SI->invar->I->getContext());
  Type* I64 = Type::getInt64Ty(SI->invar->I->getContext());

  if(writtenPtr->getType() != CharPtr)
    writtenPtr = new BitCastInst(writtenPtr, CharPtr, "", emitBB);

  uint64_t ptrOffset = cast<ImprovedValSetSingle>(SI->i.PB)->Values[0].Offset;

  SmallVector<IVSRange, 4>& Vals = GlobalIHP->memcpyValues[SI];

  for(SmallVector<IVSRange, 4>::iterator it = Vals.begin(), itend = Vals.end(); it != itend; ++it) {

    if(it->second.Values.size() == 0)
      continue;

    int64_t ThisOffset = it->first.first - ptrOffset;
    release_assert(ThisOffset >= 0);
    
    Value* OffsetCI = ConstantInt::get(I64, (uint64_t)ThisOffset);
    Value* ElPtr = GetElementPtrInst::Create(CharPtr, writtenPtr, ArrayRef<Value*>(&OffsetCI, 1), "", emitBB);

    Type* TargetType = PointerType::getUnqual(getValueType(it->second.Values[0].V));
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

// Emit a check that SI behaved as expected at runtime. If it's an invoke instruction that means choosing between
// the block's specialised and unspecialised non-exceptional successors (the throws case has already been taken
// care of by introducing an invoke -> check_block, unspec_landingpad_block structure before calling this.
// For normal (non-terminator) instructions this introduces a mid-(original program)-block spec-to-unspec edge.
SmallVector<CommittedBlock, 1>::iterator
IntegrationAttempt::emitOrdinaryInstCheck(SmallVector<CommittedBlock, 1>::iterator emitIt, ShadowInstruction* SI) {

  CommittedBlock& emitCB = *(emitIt++);
  BasicBlock* emitBB = emitCB.specBlock;
  Value* Check;

  if(inst_is<MemTransferInst>(SI))
    Check = emitMemcpyCheck(SI, emitBB);
  else
    Check = emitAsExpectedCheck(SI, emitBB);
    
  BasicBlock* successTarget; 
  BasicBlock* failTarget;

  if(inst_is<InvokeInst>(SI)) {

    // emititer already bumped above.
    bool markUnreachable = false;
    successTarget = getSuccessorBB(SI->parent, SI->parent->invar->succIdxs[0], markUnreachable);
    if(markUnreachable) {
      successTarget = createBasicBlock(emitBB->getContext(), 
				       VerboseNames ? "invoke-check-unreachable" : "", 
				       emitBB->getParent(), false, true);
      new UnreachableInst(emitBB->getContext(), successTarget);
    }

    failTarget = getFunctionRoot()->getSubBlockForInst(SI->parent->invar->succIdxs[0], 0);

  }
  else {

    successTarget = emitIt->specBlock;
    failTarget = getFunctionRoot()->getSubBlockForInst(SI->parent->invar->idx, SI->invar->idx + 1);

  }

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

  release_assert(successTarget && failTarget && Check);
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

// Emit a 'printf' call for debugging when specialisations are entered and exited.
void llvm::emitRuntimePrint(BasicBlock* emitBB, std::string& message, Value* param, Instruction* insertBefore) {

  Type* CharPtr = Type::getInt8PtrTy(emitBB->getContext());
  Module* M = getGlobalModule();

  static Constant* Printf = 0;
  if(!Printf) {

    Printf = M->getFunction("printf");
    if(!Printf) {

      errs() << "Warning: couldn't find a printf function for debug printing, will need to link against libc\n";

      Type* Int32 = Type::getInt32Ty(emitBB->getContext());
      FunctionType* PrintfTy = FunctionType::get(Int32, ArrayRef<Type*>(CharPtr), /*vararg=*/true);

      Printf = cast<Function>(M->getOrInsertFunction("printf", PrintfTy).getCallee());
    
    }

  }
    
  uint32_t nParams = param ? 2 : 1;
  Value* args[nParams];

  Constant* messageArray = ConstantDataArray::getString(emitBB->getContext(), message, true);
  GlobalVariable* messageGlobal = new GlobalVariable(*M, messageArray->getType(), true,
						     GlobalValue::InternalLinkage, messageArray);
  Constant* castMessage = ConstantExpr::getBitCast(messageGlobal, CharPtr);

  
  args[0] = castMessage;
  if(param)
    args[1] = param;

  if(insertBefore)
    CallInst::Create(Printf, ArrayRef<Value*>(args, nParams), "", insertBefore);
  else
    CallInst::Create(Printf, ArrayRef<Value*>(args, nParams), "", emitBB);
  
}
