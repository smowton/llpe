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
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

namespace {

  class StoreToMemcpyPass : public ModulePass {
  public:

    static char ID;
    StoreToMemcpyPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);
    void runOnFunction(Function* F);
    void runOnBasicBlock(BasicBlock* BB);
    bool getWriteDetails(Instruction* I, Value*& Base, int64_t& Offset, int64_t& Size);

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

static void DeleteDeadInstruction(Instruction *I) {

  SmallVector<Instruction*, 32> NowDeadInsts;

  NowDeadInsts.push_back(I);

  do {
    Instruction *DeadInst = NowDeadInsts.pop_back_val();

    // This instruction is dead, zap it, in stages.

    for (unsigned op = 0, e = DeadInst->getNumOperands(); op != e; ++op) {
      Value *Op = DeadInst->getOperand(op);
      DeadInst->setOperand(op, 0);

      // If this operand just became dead, add it to the NowDeadInsts list.
      if (!Op->use_empty()) continue;

      if (Instruction *OpI = dyn_cast<Instruction>(Op)) {
        if (isInstructionTriviallyDead(OpI, 0))
          NowDeadInsts.push_back(OpI);
      }
      else if(Constant* C = dyn_cast<Constant>(Op)) {

	if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(GetUnderlyingObject(C))) {
	  
	  GV->removeDeadConstantUsers();
	  if(GV->use_empty() && GV->isDiscardableIfUnused())
	    GV->eraseFromParent();

	}

      }

    }
    
    DeadInst->eraseFromParent();

  } while (!NowDeadInsts.empty());

}

static void replaceStores(BasicBlock::iterator itstart, BasicBlock::iterator itend) {

  Value* TargetPtr = 0;
  std::vector<Instruction*> Deletes;
  std::vector<Type*> Types;
  std::vector<Constant*> Copy;
  uint64_t CpySize = 0;
  Type* UniqueType = 0;

  BasicBlock* BB = itstart->getParent();
  Module* M = BB->getParent()->getParent();
  
  for(BasicBlock::iterator it = itstart; it != itend; ++it) {

    if(isa<StoreInst>(it)) {

      Constant* newVal = cast<Constant>(cast<StoreInst>(it)->getValueOperand());
      CpySize += DL->getTypeStoreSize(newVal->getType());
      Deletes.push_back(it);
      Types.push_back(newVal->getType());
      if(UniqueType && Types.back() != UniqueType)
	UniqueType = 0;
      Copy.push_back(newVal);
      
      if(it == itstart) {
	TargetPtr = cast<StoreInst>(it)->getPointerOperand();
	UniqueType = Types.back();
      }

    }
    else if(isa<MemTransferInst>(it)) {

      MemTransferInst* MTI = cast<MemTransferInst>(it);

      int64_t Ign;
      GlobalVariable* SourceGV = cast<GlobalVariable>(getUnderlyingBaseAndOffset(MTI->getRawSource(), Ign));

      ConstantStruct* SourceC = cast<ConstantStruct>(SourceGV->getInitializer());
      for(uint32_t i = 0, ilim = SourceC->getNumOperands(); i != ilim; ++i) {

	Constant* newVal = cast<Constant>(SourceC->getOperand(i));
	Types.push_back(newVal->getType());
	if(UniqueType && Types.back() != UniqueType)
	  UniqueType = 0;
	Copy.push_back(newVal);
      
	if(it == itstart) {
	  TargetPtr = MTI->getDest();
	  UniqueType = Types.back();
	}

      }

      Deletes.push_back(it);
      CpySize += cast<ConstantInt>(MTI->getLength())->getLimitedValue();

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

  Instruction* NewCI = CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", itend);
  if(debugmts)
    errs() << "Replace with " << *NewCI << "\n---\n";

  // Remove afterwards, or else the target pointer may be destroyed.
  for(std::vector<Instruction*>::iterator it = Deletes.begin(), delitend = Deletes.end(); it != delitend; ++it) {
    if(debugmts)
      errs() << "Delete " << **it << "\n";
    DeleteDeadInstruction(*it);
  }

}

#define REPLACE_THRESHOLD 256

bool StoreToMemcpyPass::getWriteDetails(Instruction* I, Value*& Base, int64_t& Offset, int64_t& Size) {

  if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

    if(!isa<Constant>(SI->getValueOperand()))
      return false;
    
    Offset = 0;
    Base = getUnderlyingBaseAndOffset(SI->getPointerOperand(), Offset);
    Size = DL->getTypeStoreSize(SI->getValueOperand()->getType());
    
    return true;

  }
  else if(MemTransferInst* MTI = dyn_cast<MemTransferInst>(I)) {

    Value* FromPtr = MTI->getRawSource();
    int64_t FromOffset = 0;
    Value* FromBase = getUnderlyingBaseAndOffset(FromPtr, FromOffset);

    GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(FromBase);
    if(!GV)
      return false;

    if(FromOffset != 0)
      return false;

    if(!GV->isConstant())
      return false;

    ConstantStruct* CS = dyn_cast_or_null<ConstantStruct>(GV->getInitializer());
    if(!CS)
      return false;
	
    if(!cast<StructType>(CS->getType())->isPacked())
      return false;

    ConstantInt* LenC = dyn_cast<ConstantInt>(MTI->getLength());
    if(!LenC)
      return false;

    if(LenC->getLimitedValue() != DL->getTypeStoreSize(CS->getType()))
      return false;

    Offset = 0;
    Base = getUnderlyingBaseAndOffset(MTI->getDest(), Offset);
    Size = LenC->getLimitedValue();

    return true;

  }
  else {

    return false;

  }

}

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

    Value* ThisBase;
    int64_t ThisOffset;
    int64_t ThisSize;

    if(getWriteDetails(I, ThisBase, ThisOffset, ThisSize)) {

      if(CommonBase && 
	 ((CommonBase != ThisBase) || 
	  (NextOffset != ThisOffset))) {
	
	if((NextOffset - FirstOffset) >= REPLACE_THRESHOLD)
	  replaceStores(firstStore, BI);
	CommonBase = 0;
	
      }

      if(!CommonBase) {
	CommonBase = ThisBase;
	firstStore = BI;
	NextOffset = ThisOffset;
	FirstOffset = ThisOffset;
      }      
      
      NextOffset += ThisSize;

    }
    else {

      if((NextOffset - FirstOffset) >= REPLACE_THRESHOLD)
	replaceStores(firstStore, BI);
      CommonBase = 0;
      NextOffset = 0;
      FirstOffset = 0;

    }

  }

  // Emit last block if any
  if(CommonBase && (NextOffset - FirstOffset) >= REPLACE_THRESHOLD) {
    BasicBlock::iterator endit = BB->end();
    // Insert memcpy before the terminator!
    --endit;
    replaceStores(firstStore, endit);
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
