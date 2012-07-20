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
bool IntegrationAttempt::AnalyzeLoadFromClobberingWrite(LoadForwardAttempt& LFA,
						       Value *WritePtr, HCFParentCallbacks* WriteCtx,
						       uint64_t WriteSizeInBits, 
						       uint64_t* FirstDef, uint64_t* FirstNotDef) {
  const Type* LoadTy = LFA.getOriginalInst()->getType();

  int64_t StoreOffset = 0;
  ValCtx StoreBase = GetBaseWithConstantOffset(WritePtr, WriteCtx, StoreOffset);

  return AnalyzeLoadFromClobberingWrite(LFA, StoreBase, StoreOffset, WriteSizeInBits, FirstDef, FirstNotDef);

}

// Given a write to ((char*)StoreBase) + StoreOffset of size WriteSizeInBits
// Find out which bits in the load LFA are defined, and by what offset within the write.
// Return true if this store contributes anything at all to the load.
bool IntegrationAttempt::AnalyzeLoadFromClobberingWrite(LoadForwardAttempt& LFA,
							ValCtx StoreBase,
							uint64_t StoreOffset,
							uint64_t WriteSizeInBits,
							/* Out params: */
							uint64_t& FirstDef, 
							uint64_t& FirstNotDef, 
							uint64_t& ReadOffset) {

  const Type* LoadTy = LFA.getTargetTy();

  if(!LFA.canBuildSymExpr()) {
    LPDEBUG("Can't build a symbolic expression regarding " << *(LFA.getOriginalInst()) << " so it isn't a known base plus constant offset\n");
    return false;
  }
  ValCtx LoadBase = LFA.getBaseVC();
  if (StoreBase != LoadBase) {
    LPDEBUG("Write to " << StoreBase << " and load from " << LoadBase << " do not share a base\n");
    return false;
  }

  LoadOffset = LFA.getSymExprOffset(); // Succeeds if canBuildSymExpr does
  
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
    LPDEBUG("*** AA Failure ***\n");
    return false;
  }
  
  if(StoreOffset > LoadOffset) {
    
    FirstDef = (StoreOffset - LoadOffset);
    ReadOffset = 0;

  }
  else {

    FirstDef = 0;
    ReadOffset = LoadOffset-StoreOffset;

  }

  if (StoreOffset+StoreSize < LoadOffset+LoadSize) {
    FirstNotDef = LoadSize - ((LoadOffset+LoadSize) - (StoreOffset+StoreSize));
  }
  else {
    FirstNotDef = LoadSize;
  }

  return true;

}  

/// AnalyzeLoadFromClobberingStore - This function is called when we have a
/// memdep query of a load that ends up being a clobbering store.
bool IntegrationAttempt::AnalyzeLoadFromClobberingStore(LoadForwardAttempt& LFA, StoreInst *DepSI, HCFParentCallbacks* DepSICtx, uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& LoadOffset) {
  // Cannot handle reading from store of first-class aggregate yet.
  if (DepSI->getOperand(0)->getType()->isStructTy() ||
      DepSI->getOperand(0)->getType()->isArrayTy())
    return -1;

  Value *StorePtr = DepSI->getPointerOperand();
  uint64_t StoreSize = TD->getTypeSizeInBits(DepSI->getOperand(0)->getType());
  return AnalyzeLoadFromClobberingWrite(LFA, StorePtr, DepSICtx, StoreSize, FirstDef, FirstNotDef, LoadOffset);
}

bool IntegrationAttempt::AnalyzeLoadFromClobberingMemInst(LoadForwardAttempt& LFA, MemIntrinsic *MI, HCFParentCallbacks* MICtx, uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& LoadOffset) {

  // If the mem operation is a non-constant size, we can't handle it.
  ConstantInt *SizeCst = dyn_cast_or_null<ConstantInt>(MICtx->getConstReplacement(MI->getLength()));
  if (SizeCst == 0) return false;
  uint64_t MemSizeInBits = SizeCst->getZExtValue()*8;

  return AnalyzeLoadFromClobberingWrite(LFA, MI->getDest(), MICtx, MemSizeInBits, FirstDef, FirstNotDef, LoadOffset);
  
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

Constant* intFromBytes(const uint64_t* data, unsigned data_length, unsigned data_bits, LLVMContext& Context) {

  APInt AP(data_bits, data_length, data);
  return ConstantInt::get(Context, AP);

}

// Try to improve a load which got clobbered. Cope with cases where:
// * It's defined by a store that subsumes but is not identical to the load
// * It's defined by a memcpy in similar fashion
// * It's defined by a VFS read operation, similar to a memcpy
// Return the result of forwarding, or VCNull if none.
PartialVal IntegrationAttempt::tryResolveClobber(LoadForwardAttempt& LFA, ValCtx Clobber) {

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
	      uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
	      uint64_t ReadOffset = (uint64_t)LFA.getSymExprOffset();
	      uint64_t FirstNotDef = std::min(GVCSize - ReadOffset, LoadSize);
	      return PartialVal::getPartial(0, FirstNotDef, GVC, ReadOffset);

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

    uint64_t FirstDef, FirstNotDef, ReadOffset;

    // Only deal with integer types handled this way for now.
    Constant* StoreC = Clobber.second->getConstReplacement(DepSI->getValueOperand());
    if(!StoreC) {
	
      LPDEBUG("Can't resolve clobber of " << *LI << " by " << Clobber << " because the store's value is not constant and the load is not exactly aligned\n");
      return PartialVal();

    }

    if(!AnalyzeLoadFromClobberingStore(LFA, DepSI, Clobber.second, FirstDef, FirstNotDef, ReadOffset))
      return PartialVal();

    return PartailVal::getPartial(FirstDef, FirstNotDef, StoreC, ReadOffset);

  }

  // If the clobbering value is a memset/memcpy/memmove, see if we can
  // forward a value on from it.
  if (MemIntrinsic *DepMI = dyn_cast<MemIntrinsic>(Clobber.first)) {

    uint64_t FirstDef, FirstNotDef, ReadOffset;

    if(!AnalyzeLoadFromClobberingMemInst(LFA, DepMI, Clobber.second, FirstDef, FirstNotDef, ReadOffset))
      return PartialVal();

    LPDEBUG("Salvaged a clobbering memory intrinsic (load (" << FirstDef << "-" << FirstNotDef << "] defined by " << (*DepMI) << " source + " << ReadOffset << "\n");

    // For now this means we have a memset or memcpy from constant data. Just read it.
    if (MemSetInst *MSI = dyn_cast<MemSetInst>(Clobber.first)) {

      // memset(P, 'x', 1234) -> splat('x'), even if x is a variable, and
      // independently of what the offset is.
      ConstantInt *Val = dyn_cast_or_null<ConstantInt>(getConstReplacement(MSI->getValue()));
      if(!Val) {

	LPDEBUG("Won't forward load " << *LI << " from uncertain memset " << *DepMI << "\n");
	return PartialVal();

      }

      uint8_t ValI = (uint8_t)Val->getLimitedValue();
      uint64_t nbytes = FirstNotDef - FirstDef;
      uint64_t nqwords = (nbytes + 7) / 8;
      uint64_t bufsize = nqwords * 8;
            
      uint8_t* buffer = (uint8_t*)alloca(bufsize);

      for(uint64_t i = 0; i < nbytes; ++i) {
	buffer[i] = ValI;
      }

      Constant* Result = intFromBytes((uint64_t*)buffer, nqwords, nbytes * 8, MSI->getContext());
      return PartialVal::getPartial(FirstDef, FirstNotDef, Result, 0);

    }
 
    // Otherwise this is a memcpy or memmove.
    // If it's a memcpy from a constant source, resolve here and now.
    // Otherwise issue a subquery to find out what happens to the source buffer before it's copied.

    MemTransferInst *MTI = cast<MemTransferInst>(Clobber.first);

    const Type* byteArrayType = Type::getInt8PtrTy(LI->getContext());
    const Type* subTargetType;

    uint64_t DefSize = FirstNonDef - FirstDef;

    if(DefSize != LoadSize) {
      // This memcpy/move is partially defining the load
      subTargetType = Type::getIntNTy(MTI->getContext(), DefSize * 8);
    }
    else {
      subTargetType = LoadTy;
    }

    ConstantInt* OffsetCI = ConstantInt::get(Type::getInt64Ty(LI->getContext()), ReadOffset);

    // First of all check for an easy case: the memcpy is from a constant.
    // Then we can just treat the memcpy as a GEP, augment the constant expression
    // and try to resolve it.

    if(Constant* MTISourceC = getConstReplacement(MTI->getSource())) {

      if(ReadOffset > 0) {

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
	return PartialVal::getPartial(FirstDef, FirstNotDef, Result, 0);
      }
      else {
	LPDEBUG("Resolution failed\n");
	return PartialVal();
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

    // Pointer arithmetic: add ReadOffset bytes
    SmallVector<Value*, 4> GEPOffsets;
    GEPOffsets.push_back(OffsetCI);
    SymExpr->insert(SymExpr->begin(), new SymGEP(GEPOffsets));

    // Cast back to Load type
    const Type* castTarget = PointerType::get(subTargetType, 0);
    if(castTarget != byteArrayType) {
      SymExpr->insert(SymExpr->begin(), new SymCast(castTarget));
    }

    // Adjust the offset-from-symbolic-expression-base
    // if we're only interested in an offset from the memop source:
    SubLFA.setSymExprOffset(SubLFA.getSymExprOffset() + ReadOffset);

    // Realise the symbolic expression before the memcpy and query it.
    ValCtx MTIResult = ((IntegrationAttempt*)Clobber.second)->tryForwardLoad(SubLFA, MTI);

    if(MTIResult == VCNull) {
      LPDEBUG("Memcpy sub-forwarding attempt failed\n");
      return PartialVal();
    }
    else if(FirstNotDef - FirstDef == LoadSize) {
      LPDEBUG("Memcpy sub-forwarding yielded " << MTIResult << " (using as whole result)\n");
      return PartialVal::getTotal(MTIResult);
    }
    else if(Constant* C = dyn_cast<Constant>(MTIResult.first)) {
      LPDEBUG("Memcpy sub-forwarding yielded " << MTIResult << " (using as partial)\n");
      return PartialVal::getPartial(FirstDef, FirstNotDef, C, 0);
    }
    else {
      LPDEBUG("Memcpy sub-forwarding yielded " << MTIResult << " but that kind of value cannot partially define a result\n");
      return PartialVal();
    }

  }

  if(CallInst* CI = dyn_cast<CallInst>(Clobber.first)) {

    // First determine whether the read targets the same buffer as the load, similar to memcpy analysis.
    ReadFile* RF = Clobber.second->tryGetReadFile(CI);
    if(!RF) {
      LPDEBUG("Can't improve load " << *LI << " clobbered by " << *CI << ": call does not appear to be a read()\n");
      return VCNull;
    }

    uint64_t FirstDef, FirstNotDef, loadOffset;
    if(!AnalyzeLoadFromClobberingWrite(LFA, CI->getArgOperand(1), Clobber.second, RF->readSize * 8, FirstDef, FirstNotDef, loadOffset))
      return false;

    uint64_t nbytes = FirstNotDef - FirstDef;
    uint64_t nqwords = (nbytes + 7) / 8;
    uint64_t bufsize = nqwords * 8;
    
    uint8_t* buffer = (uint8_t*)alloca(bufsize);
    uint64_t thisReadSize;

    int fd = open(RF->openArg->Name.c_str(), O_RDONLY);
    if(fd == -1) {
      LPDEBUG("Failed to open " << RF->openArg->Name << "\n");
      return VCNull;
    }

    unsigned bytes_read = 0;
    while(bytes_read < thisReadSize) {
      int this_read = pread(fd, ((char*)buffer) + bytes_read, thisReadSize - bytes_read, RF->incomingOffset + loadOffset + bytes_read);
      if(this_read == 0)
	break;
      else if(this_read == -1 && errno != EINTR)
	break;
      bytes_read += this_read;
    }

    close(fd);

    if(bytes_read != LoadSize) {
      LPDEBUG("Short read on " << RF->openArg->Name << ": could only read " << bytes_read << " bytes out of " << RF->readSize << " needed at offset " << RF->incomingOffset << "\n");
      return PartialVal();
    }

    Constant* Result = intFromBytes((uint64_t*)buffer, nqwords, nbytes * 8, MSI->getContext());
    return PartialVal::getPartial(FirstDef, FirstNotDef, Result, 0);

  }

  return PartialVal();

}

