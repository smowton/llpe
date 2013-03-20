// Implement a solver that finds fixed point solutions for instruction resolution when those instructions
// have cycles in their def-use graph, i.e. are part of a loop.
// The instruction evaluation logic is in HCF; this part concerns maintaining a queue of pending instructions
// and determining which instructions to recheck when an instruction is updated.

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
    ShadowArg* SA = V.getArg();
    Users = &(SA->invar->userIdxs);
  }

  for(uint32_t i = 0; i < Users->size(); ++i) {

    ShadowInstIdx& SII = (*Users)[i];
    if(SII.blockIdx != INVALID_BLOCK_IDX && SII.instIdx != INVALID_INSTRUCTION_IDX) {

      ShadowInstructionInvar* UserI = getInstInvar(SII.blockIdx, SII.instIdx);
      queueUserUpdatePB(UserI, V, LPBA);

    }

  }

}

void IntegrationAttempt::queueUserUpdatePB(ShadowInstructionInvar* UserI, ShadowValue UsedV, LoopPBAnalyser* LPBA) {

  if(inst_is<ReturnInst>(UserI)) {
	
    getFunctionRoot()->queueUpdateCall(LPBA);
	
  }

  const Loop* UserL = UserI->scope;

  if((!L) || (UserL && L->contains(UserL))) {
	  
    queueUserUpdatePBRising(UserI, UsedV, LPBA);
	
  }
  else {
	
    queueUserUpdatePBFalling(UserI, UsedV, LPBA);

  }
  
}

void IntegrationAttempt::queueUpdatePB(ShadowValue V, LoopPBAnalyser* LPBA) {
  
  LPBA->queueIfConsidered(V);

}

void IntegrationAttempt::queueUserUpdatePBLocal(ShadowInstructionInvar* I, ShadowValue UsedV, LoopPBAnalyser* LPBA) {

  ShadowInstruction* SI = getInst(I);
  if(!SI)
    return;

  if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {

    if(InlineAttempt* IA = getInlineAttempt(CI)) {

      Function* F = &(IA->getFunction());
      for(uint32_t i = 0; i < F->arg_size(); ++i) {
	  
	if(UsedV.getBareVal() == CI->getArgOperand(i))
	  queueUpdatePB(ShadowValue(&(IA->argShadows[i])), LPBA);

      }

    }

  }
  else if(inst_is<StoreInst>(SI)) {

    for(SmallVector<ShadowInstruction*, 1>::iterator it = SI->indirectUsers.begin(), it2 = SI->indirectUsers.end(); it != it2; ++it) {
      
      //errs() << "QUEUE LOAD " << itcache(*it) << "\n";
      queueUpdatePB(*it, LPBA);

    }

  }
  else {

    queueUpdatePB(SI, LPBA);

  }

}

void IntegrationAttempt::queueUserUpdatePBFalling(ShadowInstructionInvar* I, ShadowValue UsedV, LoopPBAnalyser* LPBA) {

  if(I->scope == L) {

    queueUserUpdatePBLocal(I, UsedV, LPBA);

  }
  else {
    if(parent)
      parent->queueUserUpdatePBFalling(I, UsedV, LPBA);
  }

}

void PeelAttempt::queueUserUpdatePBRising(ShadowInstructionInvar* I, ShadowValue UsedV, LoopPBAnalyser* LPBA) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUserUpdatePBRising(I, UsedV, LPBA);

}

void IntegrationAttempt::queueUserUpdatePBRising(ShadowInstructionInvar* I, ShadowValue UsedV, LoopPBAnalyser* LPBA) {

  const Loop* MyL = L;
  const Loop* NextL = I->scope == MyL ? I->scope : immediateChildLoop(MyL, I->scope);
  bool investigateHere = true;

  if(I->scope != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(NextL)) {
      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	investigateHere = false;
      PA->queueUserUpdatePBRising(I, UsedV, LPBA);
    }

  }

  if(investigateHere)
    queueUserUpdatePBLocal(I, UsedV, LPBA);

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
  if(getPointerBase(V, PB)) {

    if((!PB.Overdef) && PB.Values.size() == 1) {

      // Is this PB as good as it can get already?
      if(PB.Type != ValSetTypePB || PB.Values[0].Offset != LLONG_MAX)
	return false;

    }

  }

  const Loop* MyL = L;
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
    queuePBUpdateIfUnresolved(ShadowValue(&(argShadows[i])), LPBA);

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCsInScope(const Loop* CheckL, LoopPBAnalyser* LPBA) {

  if((!L) && !CheckL) {

    getFunctionRoot()->queueCheckAllArgs(LPBA);

  }

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    const Loop* BBL = BB->invar->naturalScope;

    if((!CheckL) || (BBL && CheckL->contains(BBL))) {

      for(uint32_t j = 0; j < BB->insts.size(); ++j)
	queuePBUpdateIfUnresolved(ShadowValue(&(BB->insts[j])), LPBA);

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
  bool verbose = false;

  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ShadowValue, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());

    for(SmallVector<ShadowValue, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      assert(inLoopVCs.count(*it));

      if(verbose) {
	PointerBase NewPB;
	getPointerBase(*it, NewPB);
	errs() << "OLD ";
	it->getCtx()->printPB(errs(), NewPB);
	errs() << "\n";
	errs() << "TE " << it->getCtx()->itcache(*it) << " "  << finalise  << "\n";
      }

      if(it->getCtx()->tryEvaluate(*it, finalise, this, CacheThresholdBB, CacheThresholdIA)) {
	if(modifiedVals) {
	  modifiedVals->push_back(*it);
	}
      }

      if(verbose) {
	PointerBase NewPB;
	getPointerBase(*it, NewPB);
	errs() << "NEW ";
	it->getCtx()->printPB(errs(), NewPB);
	errs() << "\n";
      }

      //++(considerCount[*it]);

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

  /*
  std::vector<std::pair<int, ShadowValue> > sortCounts;

  for(DenseMap<ShadowValue, int>::iterator it = considerCount.begin(), it2 = considerCount.end(); it != it2; ++it) {

    sortCounts.push_back(std::make_pair(it->second, it->first));

  }

  std::sort(sortCounts.begin(), sortCounts.end());

  for(std::vector<std::pair<int, ShadowValue> >::iterator it = sortCounts.begin(), it2 = sortCounts.end(); it != it2; ++it) {

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

  // Remove any indirectUsers data, which will only be useful again if this loop is reanalysed
  // in the context of an outer loop.

  for(DenseSet<ShadowValue>::iterator it = inLoopVCs.begin(), it2 = inLoopVCs.end(); it != it2; ++it) {

    if(ShadowInstruction* SI = it->getInst())
      SI->indirectUsers.clear();

  }

}

void IntegrationAttempt::analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  //errs() << "Start solver for " << getShortHeader() << " / " << L->getHeader() << "\n";

  struct timespec start;
  clock_gettime(CLOCK_REALTIME, &start);
  
  // L is an immediate child of this context.

  bool makeTemporaryCachepoint = (CacheThresholdBB != L->getLoopPreheader() || CacheThresholdIA != this);
  bool cacheWasEmpty = LFPBCache.size() == 0;

  // If we don't already have a cachepoint available at the preheader, make a temporary one:
  LoopPBAnalyser LPBA(L->getLoopPreheader(), this, makeTemporaryCachepoint);

  // Step 1: queue VCs falling within this loop.

  queueUpdatePBWholeLoop(L, &LPBA);

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.
  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  LPBA.run();

  struct timespec end;
  clock_gettime(CLOCK_REALTIME, &end);

  if(time_diff(start, end) > 1) {
    errs() << "Solver for " <<  getShortHeader() << " / " << L->getHeader()->getName() << " took " << time_diff(start, end) << "s\n";
  }

  // If the cachepoint was temporary, nuke any entries that are newly created.
  if(makeTemporaryCachepoint) {

    if(cacheWasEmpty)
      LFPBCache.clear();
    else {

      for(DenseMap<LFCacheKey, PointerBase>::iterator it = LFPBCache.begin(), it2 = LFPBCache.end(); it != it2; ++it) {
	
	if(it->first.first.first.first == L->getLoopPreheader())
	  LFPBCache.erase(it);

      }

    }

  }

}

bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}
