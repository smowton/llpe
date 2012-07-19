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

using namespace llvm;

/// AnalyzeLoadFromClobberingWrite - This function is called when we have a
/// memdep query of a load that ends up being a clobbering memory write (store,
/// memset, memcpy, memmove).  This means that the write *may* provide bits used
/// by the load but we can't be sure because the pointers don't mustalias.
///
/// Check this case to see if there is anything more we can do before we give
/// up.  This returns -1 if we have to give up, or a byte number in the stored
/// value of the piece that feeds the load.
int IntegrationAttempt::AnalyzeLoadFromClobberingWrite(LoadForwardAttempt& LFA,
						       Value *WritePtr, HCFParentCallbacks* WriteCtx,
						       uint64_t WriteSizeInBits, 
						       uint64_t* FirstDef, uint64_t* FirstNotDef) {
  const Type* LoadTy = LFA.getOriginalInst()->getType();

  // If the loaded or stored value is an first class array or struct, don't try
  // to transform them.  We need to be able to bitcast to integer.
  if (LoadTy->isStructTy() || LoadTy->isArrayTy())
    return -1;
  
  int64_t StoreOffset = 0;
  ValCtx StoreBase = GetBaseWithConstantOffset(WritePtr, WriteCtx, StoreOffset);

  return AnalyzeLoadFromClobberingWrite(LFA, StoreBase, StoreOffset, WriteSizeInBits, FirstDef, FirstNotDef);

}

int IntegrationAttempt::AnalyzeLoadFromClobberingWrite(LoadForwardAttempt& LFA,
						       ValCtx StoreBase,
						       int64_t StoreOffset,
						       uint64_t WriteSizeInBits,
						       uint64_t* FirstDef, uint64_t* FirstNotDef) {

  const Type* LoadTy = LFA.getTargetTy();

  if (LoadTy->isStructTy() || LoadTy->isArrayTy())
    return -1;

  int64_t LoadOffset = 0;

  if(!LFA.canBuildSymExpr()) {
    LPDEBUG("Can't build a symbolic expression regarding " << *(LFA.getOriginalInst()) << " so it isn't a known base plus constant offset\n");
    return -1;
  }
  ValCtx LoadBase = LFA.getBaseVC();
  LoadOffset = LFA.getSymExprOffset(); // Succeeds if canBuildSymExpr does
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
  
  bool insufficient = false;
  // If the Load isn't completely contained within the stored bits, we don't
  // have all the bits to feed it.
  if(StoreOffset > LoadOffset) {
    
    if(FirstDef)
      *FirstDef = (StoreOffset - LoadOffset);
    insufficient = true;

  }
  else {
    if(FirstDef)
      *FirstDef = 0;
  }

  if (StoreOffset+StoreSize < LoadOffset+LoadSize) {

    if(FirstNotDef)
      *FirstNotDef = LoadSize - ((LoadOffset+LoadSize) - (StoreOffset+StoreSize));
    insufficient = true;

  }
  else {
    if(FirstNotDef)
      *FirstNotDef = LoadSize;
  }

  if(insufficient)
    return -1;
  
  // Okay, we can do this transformation.  Return the number of bytes into the
  // store that the load is.
  return LoadOffset-StoreOffset;
}  

/// AnalyzeLoadFromClobberingStore - This function is called when we have a
/// memdep query of a load that ends up being a clobbering store.
int IntegrationAttempt::AnalyzeLoadFromClobberingStore(LoadForwardAttempt& LFA, StoreInst *DepSI, HCFParentCallbacks* DepSICtx, uint64_t* FirstDef, uint64_t* FirstNotDef) {
  // Cannot handle reading from store of first-class aggregate yet.
  if (DepSI->getOperand(0)->getType()->isStructTy() ||
      DepSI->getOperand(0)->getType()->isArrayTy())
    return -1;

  Value *StorePtr = DepSI->getPointerOperand();
  uint64_t StoreSize = TD->getTypeSizeInBits(DepSI->getOperand(0)->getType());
  return AnalyzeLoadFromClobberingWrite(LFA, StorePtr, DepSICtx, StoreSize, FirstDef, FirstNotDef);
}

int IntegrationAttempt::AnalyzeLoadFromClobberingMemInst(LoadForwardAttempt& LFA, MemIntrinsic *MI, HCFParentCallbacks* MICtx, uint64_t* FirstDef, uint64_t* FirstNotDef) {

  // If the mem operation is a non-constant size, we can't handle it.
  ConstantInt *SizeCst = dyn_cast_or_null<ConstantInt>(MICtx->getConstReplacement(MI->getLength()));
  if (SizeCst == 0) return -1;
  uint64_t MemSizeInBits = SizeCst->getZExtValue()*8;

  return AnalyzeLoadFromClobberingWrite(LFA, MI->getDest(), MICtx, MemSizeInBits, FirstDef, FirstNotDef);
  
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
      StoredVal->getType()->isArrayTy()) {
    LPDEBUG("Won't execute a load forwarding operation over aggregate types\n");
    return false;
  }
  
  // The store has to be at least as big as the load.
  if (TD->getTypeSizeInBits(StoredVal->getType()) <
      TD->getTypeSizeInBits(LoadTy)) {
    LPDEBUG("Won't forward a load from a smaller type\n");
    return false;
  }
  
  return true;
}
  

/// CoerceAvailableValueToLoadType - If we saw a store of a value to memory, and
/// then a load from a must-aliased pointer of a different type, try to coerce
/// the stored value.  LoadedTy is the type of the load we want to replace.
///
/// If we can't do it, return null.
Constant* IntegrationAttempt::CoerceConstExprToLoadType(Constant *StoredVal, const Type *LoadedTy) {
  if (!CanCoerceMustAliasedValueToLoad(StoredVal, LoadedTy)) {
    return 0;
  }

  const Type *StoredValTy = StoredVal->getType();
  
  if (LoadedTy->isPointerTy() != StoredValTy->isPointerTy()) {
    LPDEBUG("Won't execute a load which implicitly casts int to ptr or vice versa\n");
    return 0;
  }
    
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

Constant* IntegrationAttempt::offsetConstantInt(Constant* SourceC, int64_t Offset, const Type* targetTy) {

  LLVMContext &Ctx = SourceC->getType()->getContext();

  // Compute which bits of the stored value are being used by the load.
  uint64_t StoreSize = (TD->getTypeSizeInBits(SourceC->getType()) + 7) / 8;
  uint64_t LoadSize = (TD->getTypeSizeInBits(targetTy) + 7) / 8;
    
  // Shift the bits to the least significant depending on endianness.
  unsigned ShiftAmt;
  if (TD->isLittleEndian())
    ShiftAmt = Offset*8;
  else
    ShiftAmt = (StoreSize-LoadSize-Offset)*8;
  
  if (ShiftAmt)
    SourceC = ConstantExpr::getLShr(SourceC, ConstantInt::get(SourceC->getType(), ShiftAmt));
  
  if (LoadSize != StoreSize)
    SourceC = ConstantExpr::getTrunc(SourceC, IntegerType::get(Ctx, LoadSize*8));
  
  SourceC = CoerceConstExprToLoadType(SourceC, targetTy);
  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(SourceC)) {
    SourceC = ConstantFoldConstantExpression(CE, TD);
  }

  return SourceC;

}

Constant* IntegrationAttempt::intFromBytes(const uint64_t* data, unsigned data_length, unsigned data_bits, LLVMContext& Context) {

  APInt AP(data_bits, data_length, data);
  return ConstantInt::get(Context, AP);

}

ValCtx IntegrationAttempt::handleTotalDefn(LoadForwardAttempt& LFA, ValCtx StoreC) {

  return handleTotalDefn(LFA, cast<Constant>(StoreC.first));

}

ValCtx IntegrationAttempt::handleTotalDefn(LoadForwardAttempt& LFA, Constant* StoreC) {

  bool* bufValid = LFA.tryGetBufValid();

  if(!bufValid)
    return const_vc(StoreC);

  uint64_t LoadSize = TD->getTypeSizeInBits(LFA.getTargetTy()) / 8;

  // Pass VCNull since this will either fail outright or complete the load.
  return handlePartialDefnByConst(LFA, 0, LoadSize, StoreC, VCNull);

}

ValCtx IntegrationAttempt::handlePartialDefnByConst(LoadForwardAttempt& LFA, uint64_t FirstDef, uint64_t FirstNotDef, Constant* StoreC, ValCtx Defn) {

  uint64_t LoadSize = TD->getTypeSizeInBits(LFA.getTargetTy()) / 8;

  LPDEBUG("This store can satisfy bytes (" << FirstDef << "-" << FirstNotDef << "] of the source load\n");

  // Store defined some of the bytes we need! Grab those, and either reissue the load to keep
  // chasing after the other bytes, or perhaps complete an existing attempt of this kind.
  unsigned char* partialBuf = LFA.getPartialBuf(LoadSize);
  bool* bufValid = LFA.getBufValid(); // Same size as partialBuf

  uint64_t StoreSize = TD->getTypeSizeInBits(StoreC->getType()) / 8;
  uint64_t StartOffset = 0;
  if(FirstDef == 0)
    StartOffset = StoreSize - (FirstNotDef - FirstDef);

  unsigned char* tempBuf = (unsigned char*)alloca(FirstNotDef - FirstDef);

  if(!ReadDataFromGlobal(StoreC, StartOffset, tempBuf, FirstNotDef - FirstDef, *TD)) {
    LPDEBUG("ReadDataFromGlobal failed\n");
    return VCNull;
  }
  else {
    // Avoid rewriting bytes which have already been defined
    for(uint64_t i = 0; i < (FirstNotDef - FirstDef); ++i) {
      if(!bufValid[FirstDef + i])
	partialBuf[FirstDef + i] = tempBuf[i];
    }
    return handlePartialDefn(LFA, FirstDef, FirstNotDef, Defn);
  }

}

ValCtx IntegrationAttempt::handlePartialDefn(LoadForwardAttempt& LFA, uint64_t FirstDef, uint64_t FirstNotDef, ValCtx Defn) {

  LoadInst* LI = LFA.getOriginalInst();
  uint64_t LoadSize = TD->getTypeSizeInBits(LFA.getTargetTy()) / 8;

  unsigned char* partialBuf = LFA.getPartialBuf(LoadSize);
  bool* bufValid = LFA.getBufValid(); // Same size as partialBuf

  bool loadFinished = true;
  // Meaning of the predicate: stop at the boundary, or bail out if there's no more setting to do
  // and there's no hope we've finished.
  for(uint64_t i = 0; i < LoadSize && (loadFinished || i < FirstNotDef); ++i) {

    if(i >= FirstDef && i < FirstNotDef) {
      bufValid[i] = true;
    }
    else {
      if(!bufValid[i]) {
	loadFinished = false;
      }
    }

  }

  if(loadFinished) {
    ValCtx Ret = const_vc(intFromBytes((const uint64_t*)partialBuf, (LoadSize + 7) / 8, LoadSize * 8, LI->getContext()));
    LPDEBUG("This store completes the load (final value: " << Ret << ")\n");
    return Ret;
  }
  else {
    // Issue a subquery to try to get the other bytes! Reuse the same LFA, since it owns the partialBuf.
    // Start from right before the clobber, like with memcpy forwarding.
    LPDEBUG("This does not complete the load: requerying starting at " << Defn << "\n");
    return ((IntegrationAttempt*)Defn.second)->tryForwardLoad(LFA, cast<Instruction>(Defn.first));
  }

}

// Try to improve a load which got clobbered. Cope with cases where:
// * It's defined by a store that subsumes but is not identical to the load
// * It's defined by a memcpy in similar fashion
// * It's defined by a VFS read operation, similar to a memcpy
// Return the result of forwarding, or VCNull if none.
ValCtx IntegrationAttempt::tryResolveClobber(LoadForwardAttempt& LFA, ValCtx Clobber) {

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
  LoadInst* LI = LFA.getOriginalInst();
  const Type* LoadTy = LFA.getTargetTy();
  uint64_t LoadSize = (TD->getTypeSizeInBits(LoadTy) + 7) / 8;

  if((!this->parent) && F.getName() == "main") {

    if(Clobber.second == this) {

      BasicBlock& Entry = F.getEntryBlock();
      if(Entry.begin() == Clobber.first) {

	if(LFA.canBuildSymExpr()) {
	  
	  ValCtx PointerVC = LFA.getBaseVC();

	  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(PointerVC.first)) {
	    
	    if(GV->hasDefinitiveInitializer()) {

	      LPDEBUG("Load is clobbered by the first instruction in main(), using global initialiser " << *(GV->getInitializer()) << "\n");

	      Constant* GVC = GV->getInitializer();

	      // Use const_vc to describe the global variable because all GVs are constants
	      // (i.e. they're constant *pointers*)
	      int Offset = AnalyzeLoadFromClobberingWrite(LFA, const_vc(GV), 0, TD->getTypeSizeInBits(GVC->getType()));
	      if(Offset >= 0) {
		// Load fully defined by the stored value

		// First try to use existing code to catch a simple case:
		SmallVector<SymExpr*, 4>& Expr = *(LFA.getSymExpr());
		SymGEP* GEP;
		if(Expr.size() == 2 && (GEP = dyn_cast<SymGEP>(Expr[0]))) {

		  // Foundation of this CE doesn't actually matter
		  ConstantExpr* CE = cast<ConstantExpr>(ConstantExpr::getGetElementPtr(GV, &*(GEP->Offsets.begin()), GEP->Offsets.size()));
		  LPDEBUG("Trying to fold a load from " << *CE << " using CFLTGEPCE\n");
		  Constant* Result = ConstantFoldLoadThroughGEPConstantExpr(GVC, CE);
		  if(Result) {
		    LPDEBUG("GFLTGEPCE Success: got " << *Result << "\n");
		    return handleTotalDefn(LFA, Result);
		  }
		  else {
		    LPDEBUG("GFLTGEPCE Failed\n");
		  }

		}

	      }

	      if(Offset == 0) {
		
		GVC = CoerceConstExprToLoadType(GVC, LoadTy);
		return handleTotalDefn(LFA, GVC);
	      }
	      else if(Offset == -1) {
		return VCNull;
	      }
	      else {

		if(ConstantInt* GVCI = dyn_cast<ConstantInt>(GVC)) {
		 
		  Constant* adjC = offsetConstantInt(GVCI, Offset, LFA.getOriginalInst()->getType());
		  if(adjC)
		    LPDEBUG("Adjusted initializer to access offset " << Offset << ", got " << *adjC << "\n");
		  else
		    LPDEBUG("Failed to adjust initializer (tried offset " << Offset << ")\n");

		  return handleTotalDefn(LFA, adjC);

		}

	      }

	    }

	  }
	  else {

	  LPDEBUG("Load is clobbered by the first instruction in main(), but the pointer was not a global variable\n");

	  }
	  
	}

      }

    }
  
  }

  // If the dependence is to a store that writes to a superset of the bits
  // read by the load, we can extract the bits we need for the load from the
  // stored value.
  if (StoreInst *DepSI = dyn_cast<StoreInst>(Clobber.first)) {

    uint64_t FirstDef = 0, FirstNotDef = 0;

    // Only deal with integer types handled this way for now.
    Constant* StoreC = Clobber.second->getConstReplacement(DepSI->getValueOperand());
    if(!StoreC) {
	
      LPDEBUG("Can't resolve clobber of " << *LI << " by " << Clobber << " because the store's value is unknown");
      return VCNull;

    }

    int Offset = AnalyzeLoadFromClobberingStore(LFA, DepSI, Clobber.second, &FirstDef, &FirstNotDef);
    if (Offset != -1) {

      if (!StoreC->getType()->isIntegerTy()) {
	LPDEBUG("Can't resolve clobber of " << *LI << " by " << Clobber << " because the store has a non-integer type");
	return VCNull;
      }
	  
      StoreC = offsetConstantInt(StoreC, Offset, LoadTy);

      if(StoreC) {
	LPDEBUG("Salvaged a clobbering store (load is defined by offset " << Offset << ", resolved to " << *StoreC << ")\n");
      }

      return handleTotalDefn(LFA, StoreC);

    }
    else {

      if(FirstDef != FirstNotDef)
	return handlePartialDefnByConst(LFA, FirstDef, FirstNotDef, StoreC, Clobber);

    }
    
    return VCNull;

  }

  // If the clobbering value is a memset/memcpy/memmove, see if we can
  // forward a value on from it.
  if (MemIntrinsic *DepMI = dyn_cast<MemIntrinsic>(Clobber.first)) {

    uint64_t FirstDef = 0, FirstNotDef = 0;
    int Offset = AnalyzeLoadFromClobberingMemInst(LFA, DepMI, Clobber.second, &FirstDef, &FirstNotDef);
    unsigned char* targetBuf;
    bool* targetBufValid = LFA.tryGetBufValid();
    if(targetBufValid) {
      targetBuf = LFA.getPartialBuf(LoadSize);
    }
    else {
      targetBuf = (unsigned char*)alloca(((LoadSize + 7) / 8) * 8);
    }

    if (Offset != -1) {
      FirstDef = 0; 
      FirstNotDef = LoadSize;
    }
    else if(FirstDef == FirstNotDef) {
      return VCNull;
    }

    LPDEBUG("Salvaged a clobbering memory intrinsic (load is defined by offset " << Offset << ")\n");

    // For now this means we have a memset or memcpy from constant data. Just read it.
    if (MemSetInst *MSI = dyn_cast<MemSetInst>(Clobber.first)) {

      // memset(P, 'x', 1234) -> splat('x'), even if x is a variable, and
      // independently of what the offset is.
      ConstantInt *Val = dyn_cast_or_null<ConstantInt>(getConstReplacement(MSI->getValue()));
      if(!Val) {

	LPDEBUG("Won't forward load " << *LI << " from uncertain memset " << *DepMI << "\n");
	return VCNull;

      }

      uint8_t ValI = (uint8_t)Val->getLimitedValue();

      for(uint64_t i = FirstDef; i < FirstNotDef; ++i) {
	if((!targetBufValid) || (!targetBufValid[i]))
	  targetBuf[i] = ValI;
      }

      if(Offset >= 0) {
	// Completely defined
	Constant* C = intFromBytes((uint64_t*)targetBuf, (LoadSize + 7) / 8, LoadSize * 8, Val->getContext());
	return const_vc(CoerceConstExprToLoadType(C, LoadTy));
      }
      else {
	// Partially defined?
	return handlePartialDefn(LFA, FirstDef, FirstNotDef, Clobber);
      }

    }
 
    // Otherwise, this is a memcpy/memmove from a constant global. 
    // Construct an expression for an access against the source of the memcpy/move
    // and attempt to resolve that subquery.

    MemTransferInst *MTI = cast<MemTransferInst>(Clobber.first);

    bool isPartial;
    const Type* byteArrayType = Type::getInt8PtrTy(LI->getContext());
    const Type* subTargetType;

    if(Offset == -1) {
      // This memcpy/move is partially defining the load
      uint64_t MISize = (cast<ConstantInt>(Clobber.second->getConstReplacement(MTI->getLength())))->getLimitedValue();
      isPartial = true;
      if(FirstDef == 0) // Plus we know it's a partial -- the store runs off the beginning a little
	Offset = MISize - (FirstNotDef - FirstDef);
      else
	Offset = 0;
      subTargetType = Type::getIntNTy(MTI->getContext(), (FirstNotDef - FirstDef) * 8);
    }
    else {
      isPartial = false;
      subTargetType = LoadTy;
    }

    ConstantInt* OffsetCI = ConstantInt::get(Type::getInt32Ty(LI->getContext()), (unsigned)Offset);

    // First of all check for an easy case: the memcpy is from a constant.
    // Then we can just treat the memcpy as a GEP, augment the constant expression
    // and try to resolve it.

    if(Constant* MTISourceC = getConstReplacement(MTI->getSource())) {

      if(Offset > 0) {

	if(MTISourceC->getType() != byteArrayType) {

	  MTISourceC = ConstantExpr::getBitCast(MTISourceC, byteArrayType);
	  
	}

	Constant* OffsetCIC = OffsetCI;
	MTISourceC = ConstantExpr::getGetElementPtr(MTISourceC, &OffsetCIC, 1);

      }

      if(MTISourceC->getType() != subTargetType) {

	MTISourceC = ConstantExpr::getBitCast(MTISourceC, PointerType::get(subTargetType, 0));

      }

      LPDEBUG("Forwarding through memcpy yields a load from constant pointer! Will resolve " << *MTISourceC << "\n");

      Constant* Result = ConstantFoldLoadFromConstPtr(MTISourceC, TD);

      if(Result) {
	LPDEBUG("Resolved to " << *Result << "\n");
      }
      else {
	LPDEBUG("Resolution failed\n");
      }

      if(isPartial) {
	return handlePartialDefnByConst(LFA, FirstDef, FirstNotDef, Result, Clobber);
      }
      else {
	return handleTotalDefn(LFA, Result);
      }

    }

    // Found the LFA on the original load, so any failures get attributed to it.
    // Attempt to load a smaller type if necessary!
    LoadForwardAttempt SubLFA(LI, this, TD, subTargetType);

    // Generate our own symbolic expression rather than the one that naturally results from the load.
    // This will be used for realisations outside this scope, so it had better be rooted on an identified
    // object as per usual.
    if(!SubLFA.tryBuildSymExpr(MTI->getSource())) {

      LPDEBUG("Can't try harder to forward over a memcpy because the source address " << *(MTI->getSource()) << " is not fully resolved\n");
      return VCNull;

    }

    LPDEBUG("Attempting to forward a load based on memcpy source parameter\n");

    // Augment the symbolic expression to take the offset within the source into account
    SmallVector<SymExpr*, 4>* SymExpr = SubLFA.getSymExpr();

    if(MTI->getSource()->getType() != byteArrayType) {
      SymExpr->insert(SymExpr->begin(), new SymCast(byteArrayType));
    }

    // Pointer arithmetic: add Offset bytes
    SmallVector<Value*, 4> GEPOffsets;
    GEPOffsets.push_back(OffsetCI);
    SymExpr->insert(SymExpr->begin(), new SymGEP(GEPOffsets));

    // Cast back to Load type
    const Type* castTarget = PointerType::get(subTargetType, 0);
    if(castTarget != byteArrayType) {
      SymExpr->insert(SymExpr->begin(), new SymCast(castTarget));
    }

    // Adjust the offset-from-symbolic-expression-base if the memcpy does so:
    SubLFA.setSymExprOffset(SubLFA.getSymExprOffset() + Offset);

    // Realise the symbolic expression before the memcpy and query it.
    ValCtx MTIResult = ((IntegrationAttempt*)Clobber.second)->tryForwardLoad(SubLFA, MTI);

    if(MTIResult == VCNull) {
      LPDEBUG("Memcpy sub-forwarding attempt failed\n");
      return MTIResult;
    }
    else {
      LPDEBUG("Memcpy sub-fowarding yielded " << MTIResult << "\n");
    }

    if(isPartial) {
      if(Constant* C = dyn_cast<Constant>(MTIResult.first)) {
	return handlePartialDefnByConst(LFA, FirstDef, FirstNotDef, C, Clobber);
      }
      else {
	LPDEBUG("Memcpy sub-forwarding yielded a non-constant?!");
	return VCNull;
      }
    }
    else {
      return handleTotalDefn(LFA, MTIResult);
    }

  }

  if(CallInst* CI = dyn_cast<CallInst>(Clobber.first)) {

    // First determine whether the read targets the same buffer as the load, similar to memcpy analysis.
    ReadFile* RF = Clobber.second->tryGetReadFile(CI);
    if(!RF) {
      LPDEBUG("Can't improve load " << *LI << " clobbered by " << *CI << ": call does not appear to be a read()\n");
      return VCNull;
    }

    uint64_t FirstDef, FirstNotDef;
    int loadOffset = AnalyzeLoadFromClobberingWrite(LFA, CI->getArgOperand(1), Clobber.second, RF->readSize * 8, &FirstDef, &FirstNotDef);
    unsigned char* read_buf;
    unsigned int read_buf_size = ((LoadSize + 7) / 8) * 8;
    uint64_t thisReadSize;
    bool isPartial;
    if(loadOffset >= 0) {
      isPartial = false;
      read_buf = (unsigned char*)alloca(read_buf_size);
      thisReadSize = LoadSize;
    }
    else if(FirstDef != FirstNotDef) {
      isPartial = true;
      if(FirstDef == 0)
	loadOffset = RF->readSize - (FirstNotDef - FirstDef);
      else
	loadOffset = 0;
      read_buf = LFA.getPartialBuf(LoadSize) + FirstDef;
      thisReadSize = (FirstNotDef - FirstDef);
    }
    else {
      return VCNull;
    }

    int fd = open(RF->openArg->Name.c_str(), O_RDONLY);
    if(fd == -1) {
      LPDEBUG("Failed to open " << RF->openArg->Name << "\n");
      return VCNull;
    }

    unsigned bytes_read = 0;
    while(bytes_read < thisReadSize) {
      int this_read = pread(fd, ((char*)read_buf) + bytes_read, thisReadSize - bytes_read, RF->incomingOffset + loadOffset + bytes_read);
      if(this_read == 0)
	break;
      else if(this_read == -1 && errno != EINTR)
	break;
      bytes_read += this_read;
    }

    close(fd);

    if(bytes_read != LoadSize) {
      LPDEBUG("Short read on " << RF->openArg->Name << ": could only read " << bytes_read << " bytes out of " << RF->readSize << " needed at offset " << RF->incomingOffset << "\n");
      return VCNull;
    }

    if(!isPartial)
      return handleTotalDefn(LFA, intFromBytes((uint64_t*)read_buf, read_buf_size, TD->getTypeSizeInBits(LoadTy), LoadTy->getContext()));
    else
      return handlePartialDefn(LFA, FirstDef, FirstNotDef, Clobber);

  }

  return VCNull;

}

