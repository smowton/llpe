// Some functions converted from Transforms/Scalar/GVN.cpp that try to deal with cases when loads are clobbered by writes which define them
// but do so in a more complicated way than just an equal-sized write to the same pointer. For example, a memcpy that covers the load
// or a load i8 that gets a sub-field of a store i64.
// I also handle forwarding from read() operations here, since it's a lot like a forward from a memcpy.

#include <llvm/Analysis/HypotheticalConstantFolder.h>

#include <llvm/Instructions.h>
#include <llvm/Type.h>
#include <llvm/IntrinsicInst.h>
#include <llvm/GlobalVariable.h>

#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/GetElementPtrTypeIterator.h>
#include <llvm/Support/raw_ostream.h>

#include <errno.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <alloca.h>
#include <unistd.h>

using namespace llvm;

// Given a defining instruction "definer" and a defined instruction "defined", each of which access an offset
// from a base at a given size, find the offset FROM THE DEFINER which should be accessed to satisfy
// the defined instruction, and the byte offsets of the defined which is satisfies.

// For example, suppose Defined acesses X + (0-3) and Definer accesses X + (1-2), then the answer will be:
// ReadOffset: 0 (start reading Definer's operand at offset 0)
// FirstDef: 1 (The read satisfies Defined's offset 1...
// FirstNotDef: 3 (to 2 (i.e. 3 is outside the range).

// Returns false if there is no overlap at all.

bool llvm::GetDefinedRange(ShadowValue DefinedBase, int64_t DefinedOffset, uint64_t DefinedSize,
			   ShadowValue DefinerBase, int64_t DefinerOffset, uint64_t DefinerSize,
			   uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset) {

  if (DefinerBase != DefinedBase)
    return false;

  // If the load and store don't overlap at all, the store doesn't provide
  // anything to the load.  In this case, they really don't alias at all, AA
  // must have gotten confused.
  // FIXME: Investigate cases where this bails out, e.g. rdar://7238614. Then
  // remove this check, as it is duplicated with what we have below.
  
  bool isAAFailure = false;
  if (DefinerOffset < DefinedOffset)
    isAAFailure = DefinerOffset+int64_t(DefinerSize) <= DefinedOffset;
  else
    isAAFailure = DefinedOffset+int64_t(DefinedSize) <= DefinerOffset;

  if (isAAFailure) {
#if 0
    dbgs() << "STORE LOAD DEP WITH COMMON BASE:\n"
    << "Base       = " << *DefinerBase << "\n"
    << "Store Ptr  = " << *WritePtr << "\n"
    << "Store Offs = " << DefinerOffset << "\n"
    << "Load Ptr   = " << *LoadPtr << "\n";
    abort();
#endif
    LPDEBUG("*** AA Failure ***\n");
    return false;
  }
  
  if(DefinerOffset > DefinedOffset) {
    
    FirstDef = (DefinerOffset - DefinedOffset);
    ReadOffset = 0;

  }
  else {

    FirstDef = 0;
    ReadOffset = DefinedOffset-DefinerOffset;

  }

  if (DefinerOffset+DefinerSize < DefinedOffset+DefinedSize) {
    FirstNotDef = DefinedSize - ((DefinedOffset+DefinedSize) - (DefinerOffset+DefinerSize));
  }
  else {
    FirstNotDef = DefinedSize;
  }

  return true;

}  

/// GetBaseWithConstantOffset - Analyze the specified pointer to see if it can
/// be expressed as a base pointer plus a constant offset.  Return the base and
/// offset to the caller.
ShadowValue llvm::GetBaseWithConstantOffset(Constant* Ptr, int64_t &Offset) {

  Operator *PtrOp = dyn_cast<Operator>(Ptr);
  
  // Just look through bitcasts.
  if (PtrOp && PtrOp->getOpcode() == Instruction::BitCast)
    return GetBaseWithConstantOffset(cast<Constant>(PtrOp->getOperand(0)), Offset);
  
  // If this is a GEP with constant indices, we can look through it.
  GEPOperator *GEP = dyn_cast_or_null<GEPOperator>(PtrOp);
  if(!GEP)
    return ShadowValue(Ptr);
  
  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
       ++I, ++GTI) {
    ConstantInt* OpC = cast<ConstantInt>(*I);
    if (OpC->isZero()) continue;
    
    // Handle a struct and array indices which add their offset to the pointer.
    if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
      Offset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
    } else {
      uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
      Offset += OpC->getSExtValue()*Size;
    }
  }
  
  // Re-sign extend from the pointer size if needed to get overflow edge cases
  // right.
  unsigned PtrSize = GlobalTD->getPointerSizeInBits();
  if (PtrSize < 64)
    Offset = (Offset << (64-PtrSize)) >> (64-PtrSize);
  
  return GetBaseWithConstantOffset(cast<Constant>(GEP->getPointerOperand()), Offset);

}

Constant* llvm::intFromBytes(const uint64_t* data, unsigned data_length, unsigned data_bits, LLVMContext& Context) {

  APInt AP(data_bits, data_length, data);
  return ConstantInt::get(Context, AP);

}

uint32_t llvm::getInitialBytesOnStack(Function& F) {

  uint32_t total = 0;

  for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) {

    // AFAIK the rules are: pointers and integer types take up 8 bytes.
    // FP types take up nothing.

    const Type* T = AI->getType();
    if(T->isPointerTy())
      total += 8;
    else if(T->isIntegerTy())
      total += 8;
    else if(T->isFloatingPointTy()) {

    }
    else {

      assert(0 && "Unhandled vararg argument type");

    }

  }

  return total;

}

uint32_t llvm::getInitialFPBytesOnStack(Function& F) {

  uint32_t total = 0;

  for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) {

    // FP types take up 16 bytes
    // Other types fill no space.

    const Type* T = AI->getType();
    if(T->isPointerTy())
      total += 0;
    else if(T->isIntegerTy())
      total += 0;
    else if(T->isFloatingPointTy()) {
      total += 16;
    }
    else {

      assert(0 && "Unhandled vararg argument type");

    }

  }

  return total;

}

int64_t llvm::getSpilledVarargAfter(ShadowInstruction* CI, int64_t OldArg) {

  Function* F = getCalledFunction(CI);
  assert(F && F->isVarArg());

  int32_t nonFPBytesLeft = 48;
  int32_t FPBytesLeft = 128;

  nonFPBytesLeft -= getInitialBytesOnStack(*F);
  FPBytesLeft -= getInitialFPBytesOnStack(*F);

  bool returnNext = (OldArg == ValCtx::not_va_arg);

  // For each vararg:
  unsigned nonFPArgs = 0;
  unsigned FPArgs = 0;
  for(unsigned i = F->getFunctionType()->getNumParams(); i < CI->getNumArgOperands(); ++i) {

    const Type* T = cast_inst<CallInst>(CI)->getArgOperand(i)->getType();
    if(T->isPointerTy() || T->isIntegerTy()) {

      if(nonFPBytesLeft <= 0) {
	if(returnNext)
	  return nonFPArgs;
	else if(OldArg == nonFPArgs)
	  returnNext = true;
      }
      nonFPBytesLeft -= 8;
      nonFPArgs++;

    }
    else if(T->isFloatingPointTy()) {
      
      if(FPBytesLeft <= 0) {
	if(returnNext)
	  return (FPArgs + ValCtx::first_fp_arg);
	else if(OldArg == FPArgs + ValCtx::first_fp_arg)
	  returnNext = true;
      }
      FPBytesLeft -= 16;
      FPArgs++;

    }
    else {

      assert(0 && "Unhandled vararg type");

    }

  }

  return ValCtx::not_va_arg;

}

int64_t InlineAttempt::getSpilledVarargAfter(int64_t arg) {

  return parent->getSpilledVarargAfter(CI, arg);
  
}

static int64_t getFirstSpilledVararg(IntegrationAttempt* IA) {

  InlineAttempt* BaseIA = IA->getFunctionRoot();
  return BaseIA->getSpilledVarargAfter(ValCtx::not_va_arg);

}

// Regrettably for now we must fold contexts that are tainted by varargs results because
// low-level understanding of DragonEgg's implementation of va_xxx gets broken when e.g.
// dead arguments are eliminated from emitted functions.
// This can go away when we forward port to an LLVM version that uses the va_arg instruction
// instead of having the frontend lower by itself!

bool llvm::isVarargsTainted() {

  return contextTaintedByVarargs;

}

void llvm::disableChildVarargsContexts() {

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->disableVarargsContexts();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    it->second->disableVarargsContexts();

  }

}

void InlineAttempt::disableVarargsContexts() {

  if(parent && isVarargsTainted()) {

    errs() << "*** DISABLE " << getShortHeader() << " due to varargs instructions\n";
    parent->disableInline(CI, false);

  }
  else {

    disableChildVarargsContexts();

  }

}

void PeelAttempt::disableVarargsContexts() {

  for(unsigned i = 0; i < Iterations.size(); ++i) {

    if(Iterations[i]->isVarargsTainted()) {

      errs() << "*** DISABLE " << getShortHeader() << " due to varargs instructions\n";     
      parent->disablePeel(L, false);
      return;

    }

  }

  // Else if no iteration contains varargs results:

  for(unsigned i = 0; i < Iterations.size(); ++i) {

    Iterations[i]->disableChildVarargsContexts();

  }  

}

  // The GVN code I swiped this from contained the comment:
  // "The address being loaded in this non-local block may not be the same as
  // "the pointer operand of the load if PHI translation occurs.  Make sure
  // "to consider the right address: use Address not LI->getPointerOperand()"

  // I think I can ignore that because my replacement logic will root both stores on the same underlying
  // object with constant integer offsets if we can analyse this at all.
  // That condition is required for the trickier cases (e.g. crossing call boundaries) in any case.

  // This is the original load instruction, but LI->getPointerOperand() is not necessarily
  // the basis of this load forwarding attempt, e.g. because we're making a sub-attempt after
  // passing through a memcpy.

bool llvm::getPVFromCopy(ShadowValue copySource, ShadowInstruction* copyInst, uint64_t ReadOffset, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t ReadSize, bool* validBytes, PartialVal& NewPV, std::string& error) {

  ConstantInt* OffsetCI = ConstantInt::get(Type::getInt64Ty(copySource->getContext()), ReadOffset);
  const Type* byteArrayType = Type::getInt8PtrTy(copySource->getContext());

  // Add 2 extra instructions calculating an offset from copyInst, which is the allocation
  // being read from: cast to i8* and offset by the right number of bytes.

  LPDEBUG("Attempting to forward a load based on memcpy/va_copy source parameter\n");

  Value* castInst;
  if(copySource->getType() == byteArrayType) {
    castInst = copySource;
  }
  else {
    castInst = new BitCastInst(copySource, byteArrayType, "", copyInst);
  }

  Instruction* gepInst = GetElementPtrInst::Create(castInst, OffsetCI, "", copyInst);

  // Requery starting at copyInst (the memcpy or va_copy).
  NewPV = tryForwardLoadTypeless(copyInst, make_vc(gepInst, this), FirstNotDef - FirstDef, validBytes ? &(validBytes[ReadOffset]): 0, error);

  gepInst->eraseFromParent();
  if(castInst != copySource)
    cast<Instruction>(castInst)->eraseFromParent();

  return (!NewPV.isEmpty());

}

bool getMemsetPV(ShadowInstruction* MSI, uint64_t nbytes, PartialVal& NewPV, std::string& error) {

  // memset(P, 'x', 1234) -> splat('x'), even if x is a variable, and
  // independently of what the offset is.
  ConstantInt *Val = dyn_cast_or_null<ConstantInt>(getConstReplacement(MSI->getCallArgOperand(1)));
  if(!Val) {

    LPDEBUG("Won't forward load from uncertain memset " << itcache(*MSI) << "\n");
    error = "UCMemSet";
    return false;

  }

  uint8_t ValI = (uint8_t)Val->getLimitedValue();
  NewPV = PartialVal::getByteArray(nbytes);

  uint8_t* buffer = (uint8_t*)NewPV.partialBuf;
  bool* validBuf = (bool*)NewPV.partialValidBuf;

  for(uint64_t i = 0; i < nbytes; ++i) {
    buffer[i] = ValI;
    validBuf[i] = true;
  }

  NewPV.loadFinished = true;

  return true;

}

bool llvm::getMemcpyPV(ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error) {

  // If it's a memcpy from a constant source, resolve here and now.
  // Otherwise issue a subquery to find out what happens to the source buffer before it's copied.

  // First of all check for an easy case: the memcpy is from a constant global.
  // Then we can just appropriately bracket the source constant and the outside
  // extract-element-from-aggregate code will pick it up.

  if(Constant* CpySrc = getConstReplacement(I->getCallArgOperand(1))) {

    int64_t Offset;
    Constant* CpyBase = GetBaseWithConstantOffset(CpySrc, Offset);
    if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(CpyBase)) {

      if(GV->isConstant()) {
      
	Constant* C = GV->getInitializer();
	NewPV = PartialVal::getPartial(C, ReadOffset + Offset);

      }

    }

  }

  return getPVFromCopy(I->getCallArgOperand(1), I, ReadOffset, FirstDef, FirstNotDef, LoadSize, validBytes, NewPV, error);

}

bool llvm::getVaStartPV(ShadowInstruction* CI, int64_t ReadOffset, PartialVal& NewPV, std::string& error) {

  int32_t initialOffset = getInitialBytesOnStack(F);
  int32_t initialFPOffset = 48 + getInitialFPBytesOnStack(F);

  if(ReadOffset == 0) {
	
    LPDEBUG("Load from va_start field 0: return non-vararg byte count\n");
    // Get number of non-vararg argument bytes passed on the stack on Dragonegg / x86_64:
    NewPV = PartialVal::getTotal(ShadowValue(ConstantInt::get(Type::getInt32Ty(CI->getContext()), initialOffset)));

  }
  else if(ReadOffset == 4) {

    LPDEBUG("Load from va_start field 0: return non-vararg byte count\n");
    // Get number of non-vararg FP argument bytes passed on the stack on Dragonegg / x86_64:	
    NewPV = PartialVal::getTotal(ShadowValue(ConstantInt::get(Type::getInt32Ty(CI->getContext()), initialFPOffset)));	

  }
  else if(ReadOffset == 8) {

    LPDEBUG("Load from va_start field 2: return va_arg ptr to first arg requiring field 2\n");
    // Pointer to first vararg, or first vararg after 48 bytes of real args.
    int64_t initialVararg = getFirstSpilledVararg(this);
    if(initialVararg == ValCtx::not_va_arg) {
      error = "VaArgFail";
      return false;
    }

    NewPV = PartialVal::getTotal(ShadowValue(CI, initialVararg));

  }
  else if(ReadOffset == 16) {

    LPDEBUG("Load from va_start field 3: return va_arg ptr to stack base represented as negative vararg\n");
    NewPV = PartialVal::getTotal(ShadowValue(CI, ValCtx::va_baseptr));

  }

  NewPV.isVarargTainted = true;
  return true;

}

bool llvm::getReallocPV(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error) {

  // Handling an alias against the result of a realloc, try investigating as an alias against the original
  // allocation, passed as arg0.
  return getPVFromCopy(CI->getCallArgOperand(0), CI, ReadOffset, FirstDef, FirstNotDef, LoadSize, validBytes, NewPV, error);

}

bool llvm::getVaCopyPV(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error) {

  return getPVFromCopy(CI->getCallArgOperand(1), CI, ReadOffset, FirstDef, FirstNotDef, LoadSize, validBytes, NewPV, error);

}

bool llvm::getReadPV(ShadowInstruction* SI, uint64_t nbytes, int64_t ReadOffset, PartialVal& NewPV, std::string& error) {

  // First determine whether the read targets the same buffer as the load, similar to memcpy analysis.
  CallInst* CI = cast_inst<CallInst>(SI);
  ReadFile* RF = SI->parent->IA->tryGetReadFile(CI);
  assert(RF);

  int fd = open(RF->openArg->Name.c_str(), O_RDONLY);
  if(fd == -1) {
    LPDEBUG("Failed to open " << RF->openArg->Name << "\n");
    error = "OpenErr";
    return false;
  }

  NewPV = PartialVal::getByteArray(nbytes);
  uint8_t* buffer = (uint8_t*)NewPV.partialBuf;

  unsigned bytes_read = 0;
  while(bytes_read < nbytes) {
    int this_read = pread(fd, ((char*)buffer) + bytes_read, nbytes - bytes_read, RF->incomingOffset + ReadOffset + bytes_read);
    if(this_read == 0)
      break;
    else if(this_read == -1 && errno != EINTR)
      break;
    bytes_read += this_read;
  }

  close(fd);

  if(bytes_read != nbytes) {
    LPDEBUG("Short read on " << RF->openArg->Name << ": could only read " << bytes_read << " bytes out of " << RF->readSize << " needed at offset " << RF->incomingOffset << "\n");
    error = "ShortRead";
    return false;
  }

  for(uint64_t i = 0; i < nbytes; ++i) {

    NewPV.partialValidBuf[i] = true;

  }

  NewPV.loadFinished = true;

  return true;

}

