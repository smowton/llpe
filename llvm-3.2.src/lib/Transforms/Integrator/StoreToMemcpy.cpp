// A simple utility pass that replaces long trains of Store instructions to consecutive addresses with a memcpy from a constant global.

#define DEBUG_TYPE "delink"

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Value.h"
#include "llvm/Operator.h"
#include "llvm/Instructions.h"
#include "llvm/DerivedTypes.h"
#include "llvm/DataLayout.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"

using namespace llvm;

namespace {

  class StoreToMemcpyPass : public ModulePass {
  public:

    static char ID;
    StoreToMemcpyPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);
    void runOnFunction(Function* F);
    void runOnBasicBlock(BasicBlock* BB);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DataLayout>();
    };

  };

}

static DataLayout* DL;

char StoreToMemcpyPass::ID = 0;
static RegisterPass<StoreToMemcpyPass> X("storetomemcpy", "Convert store chains to memcpy instructions",
					 false /* CFG only? */,
					 false /* Is analysis? */);

namespace llvm {

  Pass* createStoreToMemcpyPass() { return new StoreToMemcpyPass(); }

}

static Value* getUnderlyingBaseAndOffset(Value* Ptr, int64_t& Offset) {

  Operator* O = dyn_cast<Operator>(Ptr);
  if(!O)
    return Ptr;

  if(O->getOpcode() == Instruction::BitCast)
    return getUnderlyingBaseAndOffset(O->getOperand(0), Offset);

  if(GEPOperator* GEP = dyn_cast<GEPOperator>(O)) {

    for(uint32_t i = 1, ilim = O->getNumOperands(); i != ilim; ++i) {

      if(!isa<ConstantInt>(GEP->getOperand(i)))
	return Ptr;

    }
  
    // Bump base by amount indexed by GEP:
    gep_type_iterator GTI = gep_type_begin(GEP);
    for (uint32_t i = 1, ilim = O->getNumOperands(); i != ilim; ++i, ++GTI) {

      int64_t ThisOff = cast<ConstantInt>(O->getOperand(i))->getSExtValue();

      if (!ThisOff) continue;
      // Handle a struct and array indices which add their offset to the pointer.
      if (StructType *STy = dyn_cast<StructType>(*GTI)) {
	Offset += DL->getStructLayout(STy)->getElementOffset(ThisOff);
      } else {
	uint64_t Size = DL->getTypeAllocSize(GTI.getIndexedType());
	Offset += ((int64_t)ThisOff) * Size;
      }

    }

    return getUnderlyingBaseAndOffset(GEP->getOperand(0), Offset);

  }

  return Ptr;

}

static bool debugmts = false;

static void replaceStores(BasicBlock::iterator itstart, BasicBlock::iterator itend) {

  Value* TargetPtr = 0;
  std::vector<StoreInst*> Deletes;
  std::vector<Type*> Types;
  std::vector<Constant*> Copy;
  uint64_t CpySize = 0;
  Type* UniqueType = 0;

  BasicBlock* BB = itstart->getParent();
  Module* M = BB->getParent()->getParent();
  
  for(BasicBlock::iterator it = itstart; it != itend; ++it) {

    if(!isa<StoreInst>(it))
      continue;
    Constant* newVal = cast<Constant>(cast<StoreInst>(it)->getValueOperand());
    CpySize += DL->getTypeStoreSize(newVal->getType());
    Deletes.push_back(cast<StoreInst>(it));
    Types.push_back(newVal->getType());
    if(UniqueType && Types.back() != UniqueType)
      UniqueType = 0;
    Copy.push_back(newVal);

    if(it == itstart) {
      TargetPtr = cast<StoreInst>(it)->getPointerOperand();
      UniqueType = Types.back();
    }
    
  }

  Type* GType;
  Constant* CS;
  if(UniqueType) {
    
    GType = ArrayType::get(UniqueType, Types.size());
    CS = ConstantArray::get(cast<ArrayType>(GType), Copy);

  }
  else {
    
    GType = StructType::get(BB->getContext(), Types, /*isPacked=*/true);
    CS = ConstantStruct::get(cast<StructType>(GType), Copy);

  }

  Type* BytePtr = Type::getInt8PtrTy(BB->getContext());
  
  if(TargetPtr->getType() != BytePtr) {
    
    if(Constant* C = dyn_cast<Constant>(TargetPtr)) {

      TargetPtr = ConstantExpr::getBitCast(C, BytePtr);

    }
    else {

      TargetPtr = new BitCastInst(TargetPtr, BytePtr, "", itend);

    }

  }

  GlobalVariable* GCS = new GlobalVariable(*M, GType, true, GlobalValue::InternalLinkage, CS);
  Constant* GCSPtr = ConstantExpr::getBitCast(GCS, BytePtr);
  
  Type* Int64Ty = Type::getInt64Ty(BB->getContext());
  Constant* MemcpySize = ConstantInt::get(Int64Ty, CpySize);

  Type *Tys[3] = {BytePtr, BytePtr, Int64Ty};
  Function *MemCpyFn = Intrinsic::getDeclaration(M, Intrinsic::memcpy, ArrayRef<Type*>(Tys, 3));

  Value *CallArgs[] = {
    TargetPtr, GCSPtr, MemcpySize,
    ConstantInt::get(Type::getInt32Ty(BB->getContext()), 1),
    ConstantInt::get(Type::getInt1Ty(BB->getContext()), 0)
  };

  // Remove store instructions first:
  for(std::vector<StoreInst*>::iterator it = Deletes.begin(), delitend = Deletes.end(); it != delitend; ++it) {
    if(debugmts)
      errs() << "Delete " << **it << "\n";
    (*it)->eraseFromParent();
  }

  Instruction* NewCI = CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", itend);
  if(debugmts)
    errs() << "Replace with " << *NewCI << "\n---\n";
  
}

#define REPLACE_THRESHOLD 256

void StoreToMemcpyPass::runOnBasicBlock(BasicBlock* BB) {

  // Look for blocks of stores seperated only by non-memory instructions (likely calculating pointers)
  // that operate on a common base. If they're storing constants, replace with with a big memcpy.

  BasicBlock::iterator firstStore = BB->end();
  Value* CommonBase = 0;
  int64_t NextOffset = 0;
  int64_t FirstOffset = 0;

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

    Instruction* I = BI;
    if(!I->mayReadOrWriteMemory())
      continue;

    if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

      Value* StorePtr = SI->getPointerOperand();
      int64_t Offset = 0;
      Value* StoreBase = getUnderlyingBaseAndOffset(StorePtr, Offset);

      if(CommonBase && 
	 ((!isa<Constant>(SI->getValueOperand())) || 
	  (CommonBase != StoreBase) || 
	  (NextOffset != Offset))) {

	if((NextOffset - FirstOffset) >= REPLACE_THRESHOLD)
	  replaceStores(firstStore, BI);
	CommonBase = 0;
	
      }

      if(!CommonBase) {
	CommonBase = StoreBase;
	firstStore = BI;
	NextOffset = Offset;
	FirstOffset = Offset;
      }

      // Calculate next required store address:
      NextOffset += DL->getTypeStoreSize(SI->getValueOperand()->getType());

    }
    else {

      if((NextOffset - FirstOffset) >= REPLACE_THRESHOLD)
	replaceStores(firstStore, BI);
      CommonBase = 0;
      NextOffset = 0;
      FirstOffset = 0;

    }

  }

}

void StoreToMemcpyPass::runOnFunction(Function* F) {

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI)
    runOnBasicBlock(FI);

}

bool StoreToMemcpyPass::runOnModule(Module& M) {

  DL = &getAnalysis<DataLayout>();

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
    runOnFunction(MI);

  return true;

}
