
#include "llvm/Analysis/HypotheticalConstantFolder.h"

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
  DominatorTree* DT = &pass->getAnalysis<DominatorTree>(F);
  targetCallInfo = new IATargetInfo(blockIdx, arg.second, stackIdx, DT);

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

	if(targetCallInfo->DT->dominates(it->fromBB, UserBlock->invar->BB))
	  match = true;

      }
      else if(SA &&
	      it->instBB == (BasicBlock*)ULONG_MAX &&
	      it->instIdx == SA->invar->A->getArgNo()) {

	match = true;

      }

      if(match) {

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
