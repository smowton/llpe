
#define DEBUG_TYPE "raiseopencalls"
#include "llvm/Pass.h"
#include "llvm/Instructions.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"

#include <fcntl.h>

using namespace llvm;

namespace {
  class RaiseOpenCalls : public ModulePass {

    DenseSet<uint64_t> identifiersSeen;
    uint64_t nextFreeID;

  public:
    static char ID; // Pass identification, replacement for typeid
    explicit RaiseOpenCalls() : ModulePass(ID), nextFreeID(0) { }

    virtual bool runOnModule(Module &M);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
    }
  };

}

char RaiseOpenCalls::ID = 0;
INITIALIZE_PASS(RaiseOpenCalls, "raiseopencalls",
                "Raise open calls into uniquely-identified openat intrinsics", false, false);

ModulePass *llvm::createRaiseOpenCallsPass() {
  return new RaiseOpenCalls();
}

bool RaiseOpenCalls::runOnModule(Module &M) {
  bool Changed = false;

  LLVMContext& Context = M.getContext();
  IRBuilder<> Builder(Context);
  const Type* Int64 = IntegerType::get(Context, 64);

  if (Function *OpenAt = M.getFunction("llvm.openat")) {

    for(Function::use_iterator FI = OpenAt->use_begin(), FE = OpenAt->use_end(); FI != FE; ++FI) {
      CallInst* CI = cast<CallInst>(*FI);
      uint64_t UID = cast<ConstantInt>(CI->getArgOperand(3))->getLimitedValue();
      if(identifiersSeen.count(UID)) {
	DEBUG(dbgs() << "Duplicate identifer " << UID << "\n");
	UID = nextFreeID;
	CI->setArgOperand(3, ConstantInt::get(Int64, UID, false));
	Changed = true;
      }
      identifiersSeen.insert(UID);
      if(UID >= nextFreeID)
	nextFreeID = UID + 1;
    }

  }

  if(Function *SysOpen = M.getFunction("open")) {
    const FunctionType *FT = SysOpen->getFunctionType();
    if (FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
        FT->getParamType(0)->isPointerTy() &&
        FT->getParamType(1)->isIntegerTy(32) &&
	FT->isVarArg()) {

      for(Function::use_iterator FI = SysOpen->use_begin(), FE = SysOpen->use_end(); FI != FE;) {

	CallInst* CI = cast<CallInst>(*(FI++));
	ConstantInt* ModeValue;
	if((ModeValue = dyn_cast<ConstantInt>(CI->getArgOperand(1)))) {
	  int RawMode = (int)ModeValue->getLimitedValue();
	  if(RawMode & O_RDWR || RawMode & O_WRONLY)
	    continue;
	}
	else
	  continue;
	
	Builder.SetInsertPoint(CI->getParent(), CI);
	DEBUG(dbgs() << "Numbering new openat " << nextFreeID << "\n");
	Value* NewCall = EmitOpenAt(CI->getArgOperand(0), CI->getArgOperand(1), ConstantInt::get(Int64, 0), ConstantInt::get(Int64, nextFreeID++), Builder);
	CI->replaceAllUsesWith(NewCall);
	CI->eraseFromParent();
	Changed = true;

      }

    }

  }

  return Changed;
}
