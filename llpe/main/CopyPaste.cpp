//===-- CopyPaste.cpp -----------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPECopyPaste.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/DataLayout.h"

using namespace llvm;

// Functions copy-and-pasted from LLVM main source, marginally preferred to trying to patch the source to export from version to version.
// TODO persuade upstream to export these if possible.

// Only needed to support ReadDataFromGlobal

/// FoldBitCast - Constant fold bitcast, symbolically evaluating it with
/// DataLayout.  This always returns a non-null constant, but it may be a
/// ConstantExpr if unfoldable.
static Constant *FoldBitCast(Constant *C, Type *DestTy,
                             const DataLayout &TD) {
  // Catch the obvious splat cases.
  if (C->isNullValue() && !DestTy->isX86_MMXTy())
    return Constant::getNullValue(DestTy);
  if (C->isAllOnesValue() && !DestTy->isX86_MMXTy())
    return Constant::getAllOnesValue(DestTy);

  // Handle a vector->integer cast.
  if (IntegerType *IT = dyn_cast<IntegerType>(DestTy)) {
    ConstantDataVector *CDV = dyn_cast<ConstantDataVector>(C);
    if (CDV == 0)
      return ConstantExpr::getBitCast(C, DestTy);

    unsigned NumSrcElts = CDV->getType()->getNumElements();

    Type *SrcEltTy = CDV->getType()->getElementType();

    // If the vector is a vector of floating point, convert it to vector of int
    // to simplify things.
    if (SrcEltTy->isFloatingPointTy()) {
      unsigned FPWidth = SrcEltTy->getPrimitiveSizeInBits();
      Type *SrcIVTy =
        VectorType::get(IntegerType::get(C->getContext(), FPWidth), NumSrcElts);
      // Ask VMCore to do the conversion now that #elts line up.
      C = ConstantExpr::getBitCast(C, SrcIVTy);
      CDV = cast<ConstantDataVector>(C);
    }

    // Now that we know that the input value is a vector of integers, just shift
    // and insert them into our result.
    unsigned BitShift = TD.getTypeAllocSizeInBits(SrcEltTy);
    APInt Result(IT->getBitWidth(), 0);
    for (unsigned i = 0; i != NumSrcElts; ++i) {
      Result <<= BitShift;
      if (TD.isLittleEndian())
        Result |= CDV->getElementAsInteger(NumSrcElts-i-1);
      else
        Result |= CDV->getElementAsInteger(i);
    }

    return ConstantInt::get(IT, Result);
  }

  // The code below only handles casts to vectors currently.
  VectorType *DestVTy = dyn_cast<VectorType>(DestTy);
  if (DestVTy == 0)
    return ConstantExpr::getBitCast(C, DestTy);

  // If this is a scalar -> vector cast, convert the input into a <1 x scalar>
  // vector so the code below can handle it uniformly.
  if (isa<ConstantFP>(C) || isa<ConstantInt>(C)) {
    Constant *Ops = C; // don't take the address of C!
    return FoldBitCast(ConstantVector::get(Ops), DestTy, TD);
  }

  // If this is a bitcast from constant vector -> vector, fold it.
  if (!isa<ConstantDataVector>(C) && !isa<ConstantVector>(C))
    return ConstantExpr::getBitCast(C, DestTy);

  // If the element types match, VMCore can fold it.
  unsigned NumDstElt = DestVTy->getNumElements();
  unsigned NumSrcElt = C->getType()->getVectorNumElements();
  if (NumDstElt == NumSrcElt)
    return ConstantExpr::getBitCast(C, DestTy);

  Type *SrcEltTy = C->getType()->getVectorElementType();
  Type *DstEltTy = DestVTy->getElementType();

  // Otherwise, we're changing the number of elements in a vector, which
  // requires endianness information to do the right thing.  For example,
  //    bitcast (<2 x i64> <i64 0, i64 1> to <4 x i32>)
  // folds to (little endian):
  //    <4 x i32> <i32 0, i32 0, i32 1, i32 0>
  // and to (big endian):
  //    <4 x i32> <i32 0, i32 0, i32 0, i32 1>

  // First thing is first.  We only want to think about integer here, so if
  // we have something in FP form, recast it as integer.
  if (DstEltTy->isFloatingPointTy()) {
    // Fold to an vector of integers with same size as our FP type.
    unsigned FPWidth = DstEltTy->getPrimitiveSizeInBits();
    Type *DestIVTy =
      VectorType::get(IntegerType::get(C->getContext(), FPWidth), NumDstElt);
    // Recursively handle this integer conversion, if possible.
    C = FoldBitCast(C, DestIVTy, TD);

    // Finally, VMCore can handle this now that #elts line up.
    return ConstantExpr::getBitCast(C, DestTy);
  }

  // Okay, we know the destination is integer, if the input is FP, convert
  // it to integer first.
  if (SrcEltTy->isFloatingPointTy()) {
    unsigned FPWidth = SrcEltTy->getPrimitiveSizeInBits();
    Type *SrcIVTy =
      VectorType::get(IntegerType::get(C->getContext(), FPWidth), NumSrcElt);
    // Ask VMCore to do the conversion now that #elts line up.
    C = ConstantExpr::getBitCast(C, SrcIVTy);
    // If VMCore wasn't able to fold it, bail out.
    if (!isa<ConstantVector>(C) &&  // FIXME: Remove ConstantVector.
        !isa<ConstantDataVector>(C))
      return C;
  }

  // Now we know that the input and output vectors are both integer vectors
  // of the same size, and that their #elements is not the same.  Do the
  // conversion here, which depends on whether the input or output has
  // more elements.
  bool isLittleEndian = TD.isLittleEndian();

  SmallVector<Constant*, 32> Result;
  if (NumDstElt < NumSrcElt) {
    // Handle: bitcast (<4 x i32> <i32 0, i32 1, i32 2, i32 3> to <2 x i64>)
    Constant *Zero = Constant::getNullValue(DstEltTy);
    unsigned Ratio = NumSrcElt/NumDstElt;
    unsigned SrcBitSize = SrcEltTy->getPrimitiveSizeInBits();
    unsigned SrcElt = 0;
    for (unsigned i = 0; i != NumDstElt; ++i) {
      // Build each element of the result.
      Constant *Elt = Zero;
      unsigned ShiftAmt = isLittleEndian ? 0 : SrcBitSize*(Ratio-1);
      for (unsigned j = 0; j != Ratio; ++j) {
        Constant *Src =dyn_cast<ConstantInt>(C->getAggregateElement(SrcElt++));
        if (!Src)  // Reject constantexpr elements.
          return ConstantExpr::getBitCast(C, DestTy);

        // Zero extend the element to the right size.
        Src = ConstantExpr::getZExt(Src, Elt->getType());

        // Shift it to the right place, depending on endianness.
        Src = ConstantExpr::getShl(Src,
                                   ConstantInt::get(Src->getType(), ShiftAmt));
        ShiftAmt += isLittleEndian ? SrcBitSize : -SrcBitSize;

        // Mix it in.
        Elt = ConstantExpr::getOr(Elt, Src);
      }
      Result.push_back(Elt);
    }
    return ConstantVector::get(Result);
  }

  // Handle: bitcast (<2 x i64> <i64 0, i64 1> to <4 x i32>)
  unsigned Ratio = NumDstElt/NumSrcElt;
  unsigned DstBitSize = DstEltTy->getPrimitiveSizeInBits();

  // Loop over each source value, expanding into multiple results.
  for (unsigned i = 0; i != NumSrcElt; ++i) {
    Constant *Src = dyn_cast<ConstantInt>(C->getAggregateElement(i));
    if (!Src)  // Reject constantexpr elements.
      return ConstantExpr::getBitCast(C, DestTy);

    unsigned ShiftAmt = isLittleEndian ? 0 : DstBitSize*(Ratio-1);
    for (unsigned j = 0; j != Ratio; ++j) {
      // Shift the piece of the value into the right place, depending on
      // endianness.
      Constant *Elt = ConstantExpr::getLShr(Src,
                                  ConstantInt::get(Src->getType(), ShiftAmt));
      ShiftAmt += isLittleEndian ? DstBitSize : -DstBitSize;

      // Truncate and remember this piece.
      Result.push_back(ConstantExpr::getTrunc(Elt, DstEltTy));
    }
  }

  return ConstantVector::get(Result);
}

/// ReadDataFromGlobal - Recursive helper to read bits out of global.  C is the
/// constant being copied out of. ByteOffset is an offset into C.  CurPtr is the
/// pointer to copy results into and BytesLeft is the number of bytes left in
/// the CurPtr buffer.  TD is the target data.
/// Taken from llvm-3.2 lib/Analysis/ConstantFolding.cpp
bool llvm::XXXReadDataFromGlobal(Constant *C, uint64_t ByteOffset,
				 unsigned char *CurPtr, unsigned BytesLeft,
				 const DataLayout &TD) {
  assert(ByteOffset <= TD.getTypeAllocSize(C->getType()) &&
         "Out of range access");

  // If this element is zero or undefined, we can just return since *CurPtr is
  // zero initialized.
  if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C))
    return true;

  if (ConstantInt *CI = dyn_cast<ConstantInt>(C)) {
    if (CI->getBitWidth() > 64 ||
        (CI->getBitWidth() & 7) != 0)
      return false;

    uint64_t Val = CI->getZExtValue();
    unsigned IntBytes = unsigned(CI->getBitWidth()/8);

    for (unsigned i = 0; i != BytesLeft && ByteOffset != IntBytes; ++i) {
      int n = ByteOffset;
      if (!TD.isLittleEndian())
        n = IntBytes - n - 1;
      CurPtr[i] = (unsigned char)(Val >> (n * 8));
      ++ByteOffset;
    }
    return true;
  }

  if (ConstantFP *CFP = dyn_cast<ConstantFP>(C)) {
    if (CFP->getType()->isDoubleTy()) {
      C = FoldBitCast(C, Type::getInt64Ty(C->getContext()), TD);
      return XXXReadDataFromGlobal(C, ByteOffset, CurPtr, BytesLeft, TD);
    }
    if (CFP->getType()->isFloatTy()){
      C = FoldBitCast(C, Type::getInt32Ty(C->getContext()), TD);
      return XXXReadDataFromGlobal(C, ByteOffset, CurPtr, BytesLeft, TD);
    }
    return false;
  }

  if (ConstantStruct *CS = dyn_cast<ConstantStruct>(C)) {
    const StructLayout *SL = TD.getStructLayout(CS->getType());
    unsigned Index = SL->getElementContainingOffset(ByteOffset);
    uint64_t CurEltOffset = SL->getElementOffset(Index);
    ByteOffset -= CurEltOffset;

    while (1) {
      // If the element access is to the element itself and not to tail padding,
      // read the bytes from the element.
      uint64_t EltSize = TD.getTypeAllocSize(CS->getOperand(Index)->getType());

      if (ByteOffset < EltSize &&
          !XXXReadDataFromGlobal(CS->getOperand(Index), ByteOffset, CurPtr,
                              BytesLeft, TD))
        return false;

      ++Index;

      // Check to see if we read from the last struct element, if so we're done.
      if (Index == CS->getType()->getNumElements())
        return true;

      // If we read all of the bytes we needed from this element we're done.
      uint64_t NextEltOffset = SL->getElementOffset(Index);

      if (BytesLeft <= NextEltOffset-CurEltOffset-ByteOffset)
        return true;

      // Move to the next element of the struct.
      CurPtr += NextEltOffset-CurEltOffset-ByteOffset;
      BytesLeft -= NextEltOffset-CurEltOffset-ByteOffset;
      ByteOffset = 0;
      CurEltOffset = NextEltOffset;
    }
    // not reached.
  }

  if (isa<ConstantArray>(C) || isa<ConstantVector>(C) ||
      isa<ConstantDataSequential>(C)) {
    Type *EltTy = cast<SequentialType>(C->getType())->getElementType();
    uint64_t EltSize = TD.getTypeAllocSize(EltTy);
    uint64_t Index = ByteOffset / EltSize;
    uint64_t Offset = ByteOffset - Index * EltSize;
    uint64_t NumElts;
    if (ArrayType *AT = dyn_cast<ArrayType>(C->getType()))
      NumElts = AT->getNumElements();
    else
      NumElts = cast<VectorType>(C->getType())->getNumElements();

    for (; Index != NumElts; ++Index) {
      if (!XXXReadDataFromGlobal(C->getAggregateElement(Index), Offset, CurPtr,
                              BytesLeft, TD))
        return false;

      uint64_t BytesWritten = EltSize - Offset;
      assert(BytesWritten <= EltSize && "Not indexing into this element?");
      if (BytesWritten >= BytesLeft)
        return true;

      Offset = 0;
      BytesLeft -= BytesWritten;
      CurPtr += BytesWritten;
    }
    return true;
  }

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
    if (CE->getOpcode() == Instruction::IntToPtr &&
        CE->getOperand(0)->getType() == TD.getIntPtrType(CE->getContext()))
      return XXXReadDataFromGlobal(CE->getOperand(0), ByteOffset, CurPtr,
                                BytesLeft, TD);
  }

  // Otherwise, unknown initializer type.
  return false;
}

// Pinched from Transforms/InstCombine/InstructionCombining.cpp

Type* llvm::XXXFindElementAtOffset(Type *Ty, int64_t Offset,
				   SmallVectorImpl<Value*> &NewIndices,
				   const DataLayout* TD) {
  if (!TD) return 0;
  if (!Ty->isSized()) return 0;

  // Start with the index over the outer type.  Note that the type size
  // might be zero (even if the offset isn't zero) if the indexed type
  // is something like [0 x {int, int}]
  Type *IntPtrTy = TD->getIntPtrType(Ty->getContext());
  int64_t FirstIdx = 0;
  if (int64_t TySize = TD->getTypeAllocSize(Ty)) {
    FirstIdx = Offset/TySize;
    Offset -= FirstIdx*TySize;

    // Handle hosts where % returns negative instead of values [0..TySize).
    if (Offset < 0) {
      --FirstIdx;
      Offset += TySize;
      assert(Offset >= 0);
    }
    assert((uint64_t)Offset < (uint64_t)TySize && "Out of range offset");
  }

  NewIndices.push_back(ConstantInt::get(IntPtrTy, FirstIdx));

  // Index into the types.  If we fail, set OrigBase to null.
  while (Offset) {
    // Indexing into tail padding between struct/array elements.
    if (uint64_t(Offset*8) >= TD->getTypeSizeInBits(Ty))
      return 0;

    if (StructType *STy = dyn_cast<StructType>(Ty)) {
      const StructLayout *SL = TD->getStructLayout(STy);
      assert(Offset < (int64_t)SL->getSizeInBytes() &&
             "Offset must stay within the indexed type");

      unsigned Elt = SL->getElementContainingOffset(Offset);
      NewIndices.push_back(ConstantInt::get(Type::getInt32Ty(Ty->getContext()),
                                            Elt));

      Offset -= SL->getElementOffset(Elt);
      Ty = STy->getElementType(Elt);
    } else if (ArrayType *AT = dyn_cast<ArrayType>(Ty)) {
      uint64_t EltSize = TD->getTypeAllocSize(AT->getElementType());
      assert(EltSize && "Cannot index into a zero-sized array");
      NewIndices.push_back(ConstantInt::get(IntPtrTy,Offset/EltSize));
      Offset %= EltSize;
      Ty = AT->getElementType();
    } else {
      // Otherwise, we can't index into the middle of this atomic type, bail.
      return 0;
    }
  }

  return Ty;

}
