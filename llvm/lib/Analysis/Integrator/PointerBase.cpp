// Implementation of an SCCP-like solver to discover the base object pointers refer to.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Function.h"
#include "llvm/Constants.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/Debug.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Analysis/MemoryBuiltins.h"

using namespace llvm;

/*
static double time_diff(struct timespec& start, struct timespec& end) {

  timespec temp;
  if ((end.tv_nsec-start.tv_nsec)<0) {
    temp.tv_sec = end.tv_sec-start.tv_sec-1;
    temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
  } else {
    temp.tv_sec = end.tv_sec-start.tv_sec;
    temp.tv_nsec = end.tv_nsec-start.tv_nsec;
  }

  return (temp.tv_sec) + (((double)temp.tv_nsec) / 1000000000.0);

}
*/

void InlineAttempt::queueUpdateCall(LoopPBAnalyser* LPBA) {

  if(parent)
    queueUpdatePB(ShadowValue(CI), LPBA);

}

// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(ShadowValue V, LoopPBAnalyser* LPBA) {

  ImmutableArray<ShadowInstIdx>* Users;
  if(ShadowInstruction* SI = V.getInst()) {
    Users = &(SI->invar->userIdxs);
  }
  else {
    ShadowArgument* SA = V.getArg();
    Users = &(SI->invar->userIdxs);
  }

  for(uint32_t i = 0; i < Users->size(); ++i) {

    ShadowInstIdx& SII = (*Users)[i];
    if(SII.blockIdx != INVALID_BLOCK_IDX && SII.instIdx != INVALID_INST_IDX) {

      ShadowInstructionInvar* UserI = getInstInvar(SII.blockIdx, SII.instIdx);
      queueUserUpdatePB(UserI, LPBA);

    }

  }

}

 void IntegrationAttempt::queueUserUpdatePB(ShadowInstructionInvar* UserI, LoopPBAnalyser* LPBA) {

  const Loop* MyL = L;
  
  if(inst_is<ReturnInst>(UserI)) {
	
    getFunctionRoot()->queueUpdateCall(LPBA);
	
  }

  const Loop* UserL = UserI->scope;

  if((!L) || (UserL && L->contains(UserL))) {
	  
    queueUsersUpdatePBRising(UserI, LPBA);
	
  }
  else {
	
    queueUsersUpdatePBFalling(UserI, LPBA);

  }
  
}

void IntegrationAttempt::queueUpdatePB(ShadowValue V, LoopPBAnalyser* LPBA) {
  
  LPBA->queueIfConsidered(V);

}

void IntegrationAttempt::queueUsersUpdatePBFalling(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  if(I->scope == L) {

    ShadowInst* SI = getInst(I);
    if(!SI)
      return;

    if((!inst_is<CallInst>(SI)) && hasResolvedPB(SI)) {

      // No point investigating instructions whose concrete values are already known.
      return;

    }

    if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	unsigned i = 0;
	Function* F = IA->getFunction();
	for(uint32_t i = 0; i < F->arg_size(); ++i) {
	  
	  if(I->I == CI->getArgOperand(i))
	    queueUpdatePB(IA->argShadows[i], LPBA);

	}

      }

    }
    else if(inst_is<StoreInst>(SI)) {

      for(SmallVector<ShadowInstruction*, 1>::iterator it = SI->i.PBIndirectUsers.begin(), it2 = SI->i.PBIndirectUsers.end(); it != it2; ++it) {

	queueUpdatePB(*it, LPBA);

      }

    }
    else {

      queueUpdatePB(SI, LPBA);

    }

  }
  else {
    if(parent)
      parent->queueUsersUpdatePBFalling(I, LPBA);
  }

}

void PeelAttempt::queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUsersUpdatePBRising(I, LPBA);

}

void IntegrationAttempt::queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  const Loop* MyL = L;
  const Loop* NextL = I->scope == MyL ? I->scope : immediateChildLoop(MyL, I->scope);
  bool investigateHere = true;

  if(TargetLI->scope != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(NextL)) {
      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	investigateHere = false;
      PA->queueUsersUpdatePBRising(I, LPBA);
    }

  }

  if(investigateHere)
    queueUsersUpdatePBFalling(I, LPBA);

}

bool IntegrationAttempt::shouldCheckPB(ShadowValue V) {

  bool verbose = false;

  if(verbose)
    errs() << "shouldCheckPB " << itcache(V) << "\n";

  if(contextIsDead) {
    if(verbose)
      errs() << "Ctx dead\n";
    return false;
  }

  PointerBase PB;
  if(getPB(V, PB)) {

    if((!PB.Overdef) && PB.Values.size() == 1) {

      // Is this PB as good as it can get already?
      if(Type != ValSetTypePB || PB.Values[0].Offset != LLONG_MAX)
	return false;

    }

  }

  const Loop* MyL = getLoopContext();
  const Loop* VL = V.getScope();
				     
  if(MyL != VL) {

    // Check if there's a terminated loop above us which would cause this query
    // to malfunction (we'd jump into the last iteration without transiting
    // an exit edge; to fix?)

    // Extend this to all values: if there's a terminated loop we can just identify its value
    // per iteration as usual.

    if(MyL && !MyL->contains(VL)) {
      if(verbose)
	errs() << "Not within context loop\n";
      return false;
    }

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(MyL, VL))) {

      if(PA->Iterations.back()->iterStatus == IterationStatusFinal) {
	if(verbose)
	  errs() << "Under a terminated loop\n";
	return false;
      }

    }

  }

  if(verbose)
    errs() << "Will check\n";
  return true;

}

void IntegrationAttempt::queuePBUpdateIfUnresolved(ShadowValue V, LoopPBAnalyser* LPBA) {

  if(shouldCheckPB(V)) {
    
    LPBA->addVal(V);
    //errs() << "Queue " << itcache(make_vc(V, this)) << "\n";
    if(ShadowInstruction* SI = V.getInst()) {
      SI->i.PB = PointerBase();
    }
    else {
      ShadowArg* SA = V.getArg();
      SA->i.PB = PointerBase();
    }

  }
  else {

    LPDEBUG("Shouldn't check " << itcache(V) << "\n");

  }

}

void InlineAttempt::queueCheckAllArgs(LoopPBAnalyser* LPBA) {

  for(uint32_t i = 0; i < F.arg_size(); ++i)
    queuePBUpdateIfUnresolved(ShadowValue(argShadows[i]));

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCsInScope(const Loop* CheckL, LoopPBAnalyser* LPBA) {

  if((!L) && !CheckL) {

    queueCheckAllArgs();

  }

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    const Loop* BBL = BB->invar->naturalScope;

    if((!CheckL) || (BBL && CheckL->contains(BBL))) {

      for(uint32_t j = 0; j < BB->insts.size(); ++j)
	queuePBUpdateIfUnresolved(ShadowValue(BB->insts[j]), LPBA);

    }

  }

}

void IntegrationAttempt::queueUpdatePBWholeLoop(const Loop* L, LoopPBAnalyser* LPBA) {

  //errs() << "QUEUE WHOLE LOOP " << (L ? L->getHeader()->getName() : F.getName()) << "\n";

  //bool verbose = false;

  queuePBUpdateAllUnresolvedVCsInScope(L, LPBA);

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if((!L) || L->contains(it->first->getParent()))
      it->second->queueUpdatePBWholeLoop(0, LPBA);

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(L->contains(it->first) && it->second->Iterations.back()->iterStatus == IterationStatusFinal) {
      for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
	it->second->Iterations[i]->queueUpdatePBWholeLoop(it->first, LPBA);
    }

  }

}

// Currently unused:
/*
static bool isBetterThanOrEqual(PointerBase& NewPB, PointerBase& OldPB) {

  if(OldPB.Overdef)
    return true;

  if(NewPB.Overdef)
    return false;

  return NewPB.Values.size() <= OldPB.Values.size();

}
*/

void LoopPBAnalyser::runPointerBaseSolver(bool finalise, std::vector<ShadowValue>* modifiedVals) {

  //DenseMap<ShadowValue, int> considerCount;

  SmallVector<ShadowValue, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;

  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ShadowValue, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());

    for(SmallVector<ShadowValue, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      assert(inLoopVCs.count(*it));

      if(it->second->updateBasePointer(*it, finalise, this, CacheThresholdBB, CacheThresholdIA)) {
	if(modifiedVCs) {
	  modifiedVCs->push_back(*it);
	}
      }

      //++(considerCount[*it]);

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

  /*
  std::vector<std::pair<int, ValCtx> > sortCounts;

  for(DenseMap<ValCtx, int>::iterator it = considerCount.begin(), it2 = considerCount.end(); it != it2; ++it) {

    sortCounts.push_back(std::make_pair(it->second, it->first));

  }

  std::sort(sortCounts.begin(), sortCounts.end());

  for(std::vector<std::pair<int, ValCtx> >::iterator it = sortCounts.begin(), it2 = sortCounts.end(); it != it2; ++it) {

    errs() << it->first << ": " << sortCounts[0].second.second->itcache(it->second) << "\n";

  }
  */

}

void LoopPBAnalyser::run() {

  std::vector<ShadowValue> updatedVals;
  runPointerBaseSolver(false, &updatedVals);

  std::sort(updatedVals.begin(), updatedVals.end());
  std::vector<ShadowValue>::iterator startit, endit;
  endit = std::unique(updatedVals.begin(), updatedVals.end());

  for(startit = updatedVals.begin(); startit != endit; ++startit) {
	
    queueUpdatePB(*startit);

  }

  runPointerBaseSolver(true, 0);

  for(startit = updatedVals.begin(); startit != endit; ++startit) {

    startit->second->tryPromoteSingleValuedPB(*startit);
    
  }

}

void IntegrationAttempt::analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  // L is an immediate child of this context.

  LoopPBAnalyser LPBA(CacheThresholdBB, CacheThresholdIA);

  // Step 1: queue VCs falling within this loop.

  queueUpdatePBWholeLoop(L, &LPBA);

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.
  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  LPBA.run();

}

bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}

bool llvm::basesAlias(ShadowValue V1, ShadowValue V2) {

  if(VC1.first == VC2.first) {

    if((!VC1.second) || (!VC2.second))
      return true;

    if(VC1.second->ctxContains(VC2.second) || VC2.second->ctxContains(VC1.second))
      return true;

  }

  return false;

}
