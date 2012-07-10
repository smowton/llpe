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

using namespace llvm;

/// AnalyzeLoadFromClobberingWrite - This function is called when we have a
/// memdep query of a load that ends up being a clobbering memory write (store,
/// memset, memcpy, memmove).  This means that the write *may* provide bits used
/// by the load but we can't be sure because the pointers don't mustalias.
///
/// Check this case to see if there is anything more we can do before we give
/// up.  This returns -1 if we have to give up, or a byte number in the stored
/// value of the piece that feeds the load.
int IntegrationAttempt::AnalyzeLoadFromClobberingWrite(const Type *LoadTy, Value *LoadPtr,
						       Value *WritePtr, HCFParentCallbacks* WriteCtx,
						       uint64_t WriteSizeInBits) {
  // If the loaded or stored value is an first class array or struct, don't try
  // to transform them.  We need to be able to bitcast to integer.
  if (LoadTy->isStructTy() || LoadTy->isArrayTy())
    return -1;
  
  int64_t StoreOffset = 0, LoadOffset = 0;
  ValCtx StoreBase = GetBaseWithConstantOffset(WritePtr, WriteCtx, StoreOffset);
  ValCtx LoadBase = GetBaseWithConstantOffset(LoadPtr, this, LoadOffset);
  if (StoreBase != LoadBase)
    return -1;
  
  // If the load and store don't overlap at all, the store doesn't provide
  // anything to the load.  In this case, they really don't alias at all, AA
  // must have gotten confused.
  // FIXME: Investigate cases where this bails out, e.g. rdar://7238614. Then
  // remove this check, as it is duplicated with what we have below.
  uint64_t LoadSize = TD->getTypeSizeInBits(LoadTy);
  
  if ((WriteSizeInBits & 7) | (LoadSize & 7))
    return -1;
  uint64_t StoreSize = WriteSizeInBits >> 3;  // Convert to bytes.
  LoadSize >>= 3;
  
  
  bool isAAFailure = false;
  if (StoreOffset < LoadOffset)
    isAAFailure = StoreOffset+int64_t(StoreSize) <= LoadOffset;
  else
    isAAFailure = LoadOffset+int64_t(LoadSize) <= StoreOffset;

  if (isAAFailure) {
#if 0
    dbgs() << "STORE LOAD DEP WITH COMMON BASE:\n"
    << "Base       = " << *StoreBase << "\n"
    << "Store Ptr  = " << *WritePtr << "\n"
    << "Store Offs = " << StoreOffset << "\n"
    << "Load Ptr   = " << *LoadPtr << "\n";
    abort();
#endif
    return -1;
  }
  
  // If the Load isn't completely contained within the stored bits, we don't
  // have all the bits to feed it.  We could do something crazy in the future
  // (issue a smaller load then merge the bits in) but this seems unlikely to be
  // valuable.
  if (StoreOffset > LoadOffset ||
      StoreOffset+StoreSize < LoadOffset+LoadSize)
    return -1;
  
  // Okay, we can do this transformation.  Return the number of bytes into the
  // store that the load is.
  return LoadOffset-StoreOffset;
}  

/// AnalyzeLoadFromClobberingStore - This function is called when we have a
/// memdep query of a load that ends up being a clobbering store.
int IntegrationAttempt::AnalyzeLoadFromClobberingStore(const Type *LoadTy, Value *LoadPtr, StoreInst *DepSI, HCFParentCallbacks* DepSICtx) {
  // Cannot handle reading from store of first-class aggregate yet.
  if (DepSI->getOperand(0)->getType()->isStructTy() ||
      DepSI->getOperand(0)->getType()->isArrayTy())
    return -1;

  Value *StorePtr = DepSI->getPointerOperand();
  uint64_t StoreSize = TD->getTypeSizeInBits(DepSI->getOperand(0)->getType());
  return AnalyzeLoadFromClobberingWrite(LoadTy, LoadPtr, StorePtr, DepSICtx, StoreSize);
}

int IntegrationAttempt::AnalyzeLoadFromClobberingMemInst(const Type *LoadTy, Value *LoadPtr, MemIntrinsic *MI, HCFParentCallbacks* MICtx) {
  // If the mem operation is a non-constant size, we can't handle it.
  ConstantInt *SizeCst = dyn_cast_or_null<ConstantInt>(MICtx->getConstReplacement(MI->getLength()));
  if (SizeCst == 0) return -1;
  uint64_t MemSizeInBits = SizeCst->getZExtValue()*8;

  // If this is memset, we just need to see if the offset is valid in the size
  // of the memset..
  if (MI->getIntrinsicID() == Intrinsic::memset)
    return AnalyzeLoadFromClobberingWrite(LoadTy, LoadPtr, MI->getDest(), MICtx, MemSizeInBits);
  
  // If we have a memcpy/memmove, the only case we can handle is if this is a
  // copy from constant memory.  In that case, we can read directly from the
  // constant memory.
  MemTransferInst *MTI = cast<MemTransferInst>(MI);
  
  Constant *Src = getConstReplacement(MTI->getSource());
  if (Src == 0) return -1;
  
  GlobalVariable *GV = dyn_cast<GlobalVariable>(Src->getUnderlyingObject());
  if (GV == 0 || !GV->isConstant()) return -1;
  
  // See if the access is within the bounds of the transfer.
  int Offset = AnalyzeLoadFromClobberingWrite(LoadTy, LoadPtr,
                                              MI->getDest(), MICtx, MemSizeInBits);
  if (Offset == -1)
    return Offset;
  
  // Otherwise, see if we can constant fold a load from the constant with the
  // offset applied as appropriate.
  Src = ConstantExpr::getBitCast(Src,
                                 llvm::Type::getInt8PtrTy(Src->getContext()));
  Constant *OffsetCst = 
    ConstantInt::get(Type::getInt64Ty(Src->getContext()), (unsigned)Offset);
  Src = ConstantExpr::getGetElementPtr(Src, &OffsetCst, 1);
  Src = ConstantExpr::getBitCast(Src, PointerType::getUnqual(LoadTy));
  if (ConstantFoldLoadFromConstPtr(Src, TD))
    return Offset;
  return -1;
}
                                            
/// GetBaseWithConstantOffset - Analyze the specified pointer to see if it can
/// be expressed as a base pointer plus a constant offset.  Return the base and
/// offset to the caller.
ValCtx IntegrationAttempt::GetBaseWithConstantOffset(Value *Ptr, HCFParentCallbacks* PtrCtx, int64_t &Offset) {

  Operator *PtrOp = dyn_cast<Operator>(Ptr);
  if(PtrOp == 0) {
    return make_vc(Ptr, PtrCtx);
  }
  
  // Just look through bitcasts.
  if (PtrOp->getOpcode() == Instruction::BitCast)
    return GetBaseWithConstantOffset(PtrOp->getOperand(0), PtrCtx, Offset);
  
  // If this is a GEP with constant indices, we can look through it.
  GEPOperator *GEP = dyn_cast<GEPOperator>(PtrOp);
  if (GEP == 0) {
    ValCtx NewVC = PtrCtx->getReplacement(Ptr);
    if(NewVC == make_vc(Ptr, PtrCtx))
      return NewVC;
    else
      return GetBaseWithConstantOffset(NewVC.first, NewVC.second, Offset);
  }
  
  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
       ++I, ++GTI) {
    ConstantInt *OpC = dyn_cast_or_null<ConstantInt>(PtrCtx->getConstReplacement(*I));
    if(!OpC)
      return make_vc(Ptr, PtrCtx);
  }
  
  GTI = gep_type_begin(GEP);
  for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
       ++I, ++GTI) {
    ConstantInt *OpC = cast<ConstantInt>(PtrCtx->getConstReplacement(*I));
    if (OpC->isZero()) continue;
    
    // Handle a struct and array indices which add their offset to the pointer.
    if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
      Offset += TD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
    } else {
      uint64_t Size = TD->getTypeAllocSize(GTI.getIndexedType());
      Offset += OpC->getSExtValue()*Size;
    }
  }
  
  // Re-sign extend from the pointer size if needed to get overflow edge cases
  // right.
  unsigned PtrSize = TD->getPointerSizeInBits();
  if (PtrSize < 64)
    Offset = (Offset << (64-PtrSize)) >> (64-PtrSize);
  
  return GetBaseWithConstantOffset(GEP->getPointerOperand(), PtrCtx, Offset);

}

/// CanCoerceMustAliasedValueToLoad - Return true if
/// CoerceAvailableValueToLoadType will succeed.
bool IntegrationAttempt::CanCoerceMustAliasedValueToLoad(Value *StoredVal, const Type *LoadTy) {
  // If the loaded or stored value is an first class array or struct, don't try
  // to transform them.  We need to be able to bitcast to integer.
  if (LoadTy->isStructTy() || LoadTy->isArrayTy() ||
      StoredVal->getType()->isStructTy() ||
      StoredVal->getType()->isArrayTy())
    return false;
  
  // The store has to be at least as big as the load.
  if (TD->getTypeSizeInBits(StoredVal->getType()) <
      TD->getTypeSizeInBits(LoadTy))
    return false;
  
  return true;
}
  

/// CoerceAvailableValueToLoadType - If we saw a store of a value to memory, and
/// then a load from a must-aliased pointer of a different type, try to coerce
/// the stored value.  LoadedTy is the type of the load we want to replace.
///
/// If we can't do it, return null.
Constant* IntegrationAttempt::CoerceConstExprToLoadType(Constant *StoredVal, const Type *LoadedTy) {
  if (!CanCoerceMustAliasedValueToLoad(StoredVal, LoadedTy)) {
    LPDEBUG("Won't execute a load forwarding operation over aggregate types");
    return 0;
  }

  // We already know the stored type is an integer
  if (LoadedTy->isPointerTy()) {
    LPDEBUG("Won't execute a load which implicitly casts int to ptr");
    return 0;
  }
    
  const Type *StoredValTy = StoredVal->getType();
  
  uint64_t StoreSize = TD->getTypeStoreSizeInBits(StoredValTy);
  uint64_t LoadSize = TD->getTypeSizeInBits(LoadedTy);
  
  // If the store and reload are the same size, we can always reuse it.
  if (StoreSize == LoadSize) {
    if (StoredValTy != LoadedTy)
      return ConstantExpr::getBitCast(StoredVal, LoadedTy);
    else
      return StoredVal;
  }
  
  // If the loaded value is smaller than the available value, then we can
  // extract out a piece from it.  If the available value is too small, then we
  // can't do anything.
  assert(StoreSize >= LoadSize && "CanCoerceMustAliasedValueToLoad fail");
  
  // If this is a big-endian system, we need to shift the value down to the low
  // bits so that a truncate will work.
  if (TD->isBigEndian()) {
    Constant *Val = ConstantInt::get(StoredVal->getType(), StoreSize-LoadSize);
    StoredVal = ConstantExpr::getLShr(StoredVal, Val);
  }
  
  // Truncate the integer to the right size now.
  const Type *NewIntTy = IntegerType::get(StoredValTy->getContext(), LoadSize);
  StoredVal = ConstantExpr::getTrunc(StoredVal, NewIntTy);
  
  if (LoadedTy == NewIntTy)
    return StoredVal;
  
  // Otherwise, bitcast.
  return ConstantExpr::getBitCast(StoredVal, LoadedTy);
}

// Try to improve a load which got clobbered. Cope with cases where:
// * It's defined by a store that subsumes but is not identical to the load
// * It's defined by a memcpy in similar fashion
// * It's defined by a VFS read operation, similar to a memcpy
// Return the result of forwarding, or VCNull if none.
ValCtx IntegrationAttempt::tryResolveClobber(LoadInst *LI, ValCtx Clobber) {

  // The GVN code I swiped this from contained the comment:
  // "The address being loaded in this non-local block may not be the same as
  // "the pointer operand of the load if PHI translation occurs.  Make sure
  // "to consider the right address: use Address not LI->getPointerOperand()"

  // I think I can ignore that because my replacement logic will root both stores on the same underlying
  // object with constant integer offsets if we can analyse this at all.
  // That condition is required for the trickier cases (e.g. crossing call boundaries) in any case.
      
  // If the dependence is to a store that writes to a superset of the bits
  // read by the load, we can extract the bits we need for the load from the
  // stored value.
  if (StoreInst *DepSI = dyn_cast<StoreInst>(Clobber.first)) {
    int Offset = AnalyzeLoadFromClobberingStore(LI->getType(), LI->getPointerOperand(), DepSI, Clobber.second);
    if (Offset != -1) {

      LPDEBUG("Salvaged a clobbering store (load is defined by offset " << Offset << ")\n");

      // Only deal with integer types handled this way for now.
      Constant* StoreC = Clobber.second->getConstReplacement(DepSI->getValueOperand());
      if(!StoreC) {
	
	LPDEBUG("Can't resolve clobber of " << *LI << " by " << Clobber << " because the store's value is unknown");
	return VCNull;

      }

      LLVMContext &Ctx = StoreC->getType()->getContext();
  
      const Type* LoadTy = LI->getType();

      uint64_t StoreSize = (TD->getTypeSizeInBits(StoreC->getType()) + 7) / 8;
      uint64_t LoadSize = (TD->getTypeSizeInBits(LoadTy) + 7) / 8;
    
      if (!StoreC->getType()->isIntegerTy()) {
	LPDEBUG("Can't resolve clobber of " << *LI << " by " << Clobber << " because the store has a non-integer type");
	return VCNull;
      }
	  
      // Compute which bits of the stored value are being used by the load.
  
      // Shift the bits to the least significant depending on endianness.
      unsigned ShiftAmt;
      if (TD->isLittleEndian())
	ShiftAmt = Offset*8;
      else
	ShiftAmt = (StoreSize-LoadSize-Offset)*8;
  
      if (ShiftAmt)
	StoreC = ConstantExpr::getLShr(StoreC, ConstantInt::get(IntegerType::get(Ctx, 32), ShiftAmt));
  
      if (LoadSize != StoreSize)
	StoreC = ConstantExpr::getTrunc(StoreC, IntegerType::get(Ctx, LoadSize*8));
  
      StoreC = CoerceConstExprToLoadType(StoreC, LoadTy);
      if(StoreC)
	StoreC = ConstantFoldLoadFromConstPtr(StoreC, TD);

      return make_vc(StoreC, 0);

    }
    
    return VCNull;

  }

  // If the clobbering value is a memset/memcpy/memmove, see if we can
  // forward a value on from it.
  if (MemIntrinsic *DepMI = dyn_cast<MemIntrinsic>(Clobber.first)) {

    int Offset = AnalyzeLoadFromClobberingMemInst(LI->getType(), LI->getPointerOperand(), DepMI, Clobber.second);
    if (Offset != -1) {

      LPDEBUG("Salvaged a clobbering memory intrinsic (load is defined by offset " << Offset << ")\n");

      const Type* LoadTy = LI->getType();

      uint64_t LoadSize = (TD->getTypeSizeInBits(LoadTy) + 7) / 8;

      // For now this means we have a memset or memcpy from constant data. Just read it.
      if (MemSetInst *MSI = dyn_cast<MemSetInst>(Clobber.first)) {
	// memset(P, 'x', 1234) -> splat('x'), even if x is a variable, and
	// independently of what the offset is.
	Constant *Val = dyn_cast_or_null<ConstantInt>(getConstReplacement(MSI->getValue()));
	if(!Val) {

	  LPDEBUG("Won't forward load " << *LI << " from uncertain memset " << *DepMI << "\n");
	  return VCNull;

	}

	if (LoadSize != 1)
	  Val = ConstantExpr::getZExt(Val, IntegerType::get(LoadTy->getContext(), LoadSize*8));
    
	Constant *OneElt = Val;
    
	// Splat the value out to the right number of bits.
	for (unsigned NumBytesSet = 1; NumBytesSet != LoadSize; ) {
	  // If we can double the number of bytes set, do it.
	  if (NumBytesSet*2 <= LoadSize) {
	    Constant *ShVal = ConstantExpr::getShl(Val, ConstantInt::get(IntegerType::get(LoadTy->getContext(), 32), NumBytesSet*8));
	    Val = ConstantExpr::getOr(Val, ShVal);
	    NumBytesSet <<= 1;
	    continue;
	  }
      
	  // Otherwise insert one byte at a time.
	  Constant *ShVal = ConstantExpr::getShl(Val, ConstantInt::get(IntegerType::get(LoadTy->getContext(), 32), 1*8));
	  Val = ConstantExpr::getOr(OneElt, ShVal);
	  ++NumBytesSet;
	}
   
	Val = CoerceConstExprToLoadType(Val, LoadTy);
	return make_vc(Val, 0);
      }
 
      // Otherwise, this is a memcpy/memmove from a constant global.
      MemTransferInst *MTI = cast<MemTransferInst>(Clobber.first);
      Constant *Src = getConstReplacement(MTI->getSource());

      // See if we can constant fold a load from the constant with the offset applied as appropriate.
      Src = ConstantExpr::getBitCast(Src, llvm::Type::getInt8PtrTy(Src->getContext()));

      Constant *OffsetCst = 
	ConstantInt::get(Type::getInt64Ty(Src->getContext()), (unsigned)Offset);

      Src = ConstantExpr::getGetElementPtr(Src, &OffsetCst, 1);
      Src = ConstantExpr::getBitCast(Src, PointerType::getUnqual(LoadTy));
      Src = ConstantFoldLoadFromConstPtr(Src, TD);
      return make_vc(Src, 0);

    }

    return VCNull;

  }

  if(CallInst* CI = dyn_cast<CallInst>(Clobber.first)) {

    // First determine whether the read targets the same buffer as the load, similar to memcpy analysis.
    ReadFile* RF = Clobber.second->tryGetReadFile(CI);
    if(!RF) {
      LPDEBUG("Can't improve load " << *LI << " clobbered by " << *CI << ": call does not appear to be a read()\n");
      return VCNull;
    }

    int loadOffset = AnalyzeLoadFromClobberingWrite(LI->getType(), LI->getPointerOperand(), CI->getArgOperand(1), Clobber.second, RF->readSize * 8);
    if(loadOffset != -1) {

      const Type* loadTy = LI->getType();
      uint64_t loadSize = (TD->getTypeSizeInBits(loadTy) + 7) / 8;
      if(loadOffset + loadSize > RF->readSize) {

	LPDEBUG("Load " << *LI << " overruns the bounds of read " << *CI << "\n");
	return VCNull;

      }
      else {
	
	unsigned int read_buf_size = (loadSize + 7) / 8;
	uint64_t read_buf[(loadSize + 7) / 8];
	int fd = open(RF->openArg->Name.c_str(), O_RDONLY);
	if(fd == -1) {
	  LPDEBUG("Failed to open " << RF->openArg->Name << "\n");
	  return VCNull;
	}

	unsigned bytes_read = 0;
	while(bytes_read < loadSize) {
	  int this_read = pread(fd, ((char*)read_buf) + bytes_read, loadSize - bytes_read, RF->incomingOffset + loadOffset + bytes_read);
	  if(this_read == 0)
	    break;
	  else if(this_read == -1 && errno != EINTR)
	    break;
	  bytes_read += this_read;
	}

	close(fd);

	if(bytes_read != loadSize) {
	  LPDEBUG("Short read on " << RF->openArg->Name << ": could only read " << bytes_read << " bytes out of " << RF->readSize << " needed at offset " << RF->incomingOffset << "\n");
	  return VCNull;
	}

	APInt AP(TD->getTypeSizeInBits(loadTy), read_buf_size, (const uint64_t*)read_buf);
	return make_vc(ConstantInt::get(loadTy->getContext(), AP), 0);

      }

    }

  }

  return VCNull;

}

						   

  
