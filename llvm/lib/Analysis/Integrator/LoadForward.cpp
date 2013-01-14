
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

class LoadForwardWalker : public BackwardIAWalker {

  Value* LoadedPtr;
  uint64_t LoadSize;
  IntegrationAttempt* SourceCtx;
  AliasAnalysis* AA;
  TargetData* TD;

public:

  SmallVector<ValCtx, 4> StoreInsts;
  DenseSet<IntegrationAttempt*> WalkCtxs;

  LoadForwardWalker(LoadInst* LI, Value* Ptr, uint64_t Size, IntegrationAttempt* IA, AliasAnalysis* _AA, TargetData* _TD) 
    : BackwardIAWalker(LI, IA, true), LoadedPtr(Ptr), LoadSize(Size), SourceCtx(IA), AA(_AA), TD(_TD) { }
  virtual WalkInstructionResult walkInstruction(Instruction*, IntegrationAttempt*, void*);
  virtual bool shouldEnterCall(CallInst*, IntegrationAttempt*);
  virtual bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*);

};

WalkInstructionResult LoadForwardWalker::walkInstruction(Instruction* I, IntegrationAttempt* IA, void*) {

  Value* Ptr;
  uint64_t PtrSize;

  WalkCtxs.insert(IA);

  if (StoreInst *SI = dyn_cast<StoreInst>(I)) {

    Ptr = SI->getPointerOperand();
    PtrSize = AA->getTypeStoreSize(SI->getOperand(0)->getType());

    // Fall through

  }
  else if (isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I))) {
    
    if(make_vc(LoadedPtr->getUnderlyingObject(), IA) == make_vc(LoadedPtr, SourceCtx))
      return WIRStopThisPath;
    else
      return WIRContinue;

  }
  else if(MemIntrinsic* MI = dyn_cast<MemIntrinsic>(I)) {

    Ptr = MI->getDest();
    ConstantInt* CI = dyn_cast_or_null<ConstantInt>(IA->getConstReplacement(MI->getLength()));
    PtrSize = CI ? CI->getLimitedValue() : AliasAnalysis::UnknownSize;

    // Fall through

  }
  else {

    return WIRContinue;

  }

  if(AA->aliasHypothetical(make_vc(LoadedPtr, SourceCtx), LoadSize, make_vc(Ptr, IA), PtrSize, true)
     != AliasAnalysis::MustAlias) {
    return WIRContinue;
  }
  else {
    StoreInsts.push_back(make_vc(I, IA));
    return WIRStopThisPath;
  }

}

bool LoadForwardWalker::shouldEnterCall(CallInst* CI, IntegrationAttempt* IA) {

  switch(AA->getModRefInfo(CI, LoadedPtr, LoadSize, SourceCtx, IA, true)) {

  case AliasAnalysis::NoModRef:
  case AliasAnalysis::Ref:
    return false;
  default:
    return true;
  }

}

bool LoadForwardWalker::blockedByUnexpandedCall(CallInst* CI, IntegrationAttempt* IA) {

  return false;

}

void IntegrationAttempt::testLoadWalk(LoadInst* LI) {

  LoadForwardWalker Walker(LI, LI->getPointerOperand(), AA->getTypeStoreSize(LI->getOperand(0)->getType()),
			   this, AA, TD);

  Walker.walk();
  errs() << "Walked " << Walker.WalkCtxs.size() << "\n";
  /*  for(DenseSet<IntegrationAttempt*>::iterator it = Walker.WalkCtxs.begin(), it2 = Walker.WalkCtxs.end(); it != it2; ++it) {

    errs() << (*it)->getShortHeader() << "\n";

  }

  for(SmallVector<ValCtx, 4>::iterator it = Walker.StoreInsts.begin(), it2 = Walker.StoreInsts.end(); it != it2; ++it) {

    errs() << "Stopped at " << itcache(*it) << "\n";

  }
  */

}
