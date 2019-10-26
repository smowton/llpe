//===-- BytewiseReinterpret.cpp -------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// This file contains logic relating to use of PartialVal to do bytewise reinterpretation
// from one or more source values.

#define DEBUG_TYPE "BytewiseReinterpret"

#include "llvm/Analysis/LLPE.h"
#include "llvm/Analysis/LLPECopyPaste.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

//// Implement guts of PartialVal:

// This represents partial results when bytewise re-interpreting data.
// The internal byte array is represented as a uint64_t array because
// this is what the LLVM core reinterpreting function requires.

PartialVal::PartialVal(uint64_t nbytes) : partialBufBytes(nbytes), loadFinished(false) {

  uint64_t nqwords = (nbytes + 7) / 8;
  partialBuf = new uint64_t[nqwords];

  partialValidBuf = new bool[nbytes];
  for(uint64_t i = 0; i < nbytes; ++i)
    partialValidBuf[i] = false;

}

PartialVal& PartialVal::operator=(const PartialVal& Other) {

  if(partialBuf) {
    delete[] partialBuf;
    partialBuf = 0;
  }
  if(partialValidBuf) {
    delete[] partialValidBuf;
    partialValidBuf = 0;
  }

  partialBuf = new uint64_t[(Other.partialBufBytes + 7) / 8];
  memcpy(partialBuf, Other.partialBuf, Other.partialBufBytes);

  partialValidBuf = new bool[Other.partialBufBytes];
  memcpy(partialValidBuf, Other.partialValidBuf, Other.partialBufBytes);

  partialBufBytes = Other.partialBufBytes;
  loadFinished = Other.loadFinished;

  return *this;

}

PartialVal::PartialVal(const PartialVal& Other) {

  partialBuf = 0;
  partialValidBuf = 0;
  (*this) = Other;

}

PartialVal::~PartialVal() {

  if(partialBuf) {
    delete[] partialBuf;
  }
  if(partialValidBuf) {
    delete[] partialValidBuf;
  }

}

bool PartialVal::isComplete() {

  return loadFinished;

}

// Copy bytes in from the given buffer, targeting the range (FirstDef-FirstNotDef], marking each valid.
void PartialVal::combineWith(uint8_t* Other, uint64_t FirstDef, uint64_t FirstNotDef) {

  assert(FirstDef < partialBufBytes);
  assert(FirstNotDef <= partialBufBytes);

  // Avoid rewriting bytes which have already been defined
  for(uint64_t i = 0; i < (FirstNotDef - FirstDef); ++i) {
    if(partialValidBuf[FirstDef + i]) {
      continue;
    }
    else {
      ((unsigned char*)partialBuf)[FirstDef + i] = Other[i]; 
    }
  }

  loadFinished = true;
  // Meaning of the predicate: stop at the boundary, or bail out if there's no more setting to do
  // and there's no hope we've finished.
  for(uint64_t i = 0; i < partialBufBytes && (loadFinished || i < FirstNotDef); ++i) {

    if(i >= FirstDef && i < FirstNotDef) {
      partialValidBuf[i] = true;
    }
    else {
      if(!partialValidBuf[i]) {
	loadFinished = false;
      }
    }

  }

}

void PartialVal::combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef) {

  combineWith((uint8_t*)Other.partialBuf, FirstDef, FirstNotDef);

}

bool PartialVal::combineWith(Constant* C, uint64_t ReadOffset, uint64_t FirstDef, uint64_t FirstNotDef, std::string* error) {

  uint8_t* tempBuf = (unsigned char*)alloca(FirstNotDef - FirstDef);
  // XXXReadDataFromGlobal assumes a zero-initialised buffer!
  memset(tempBuf, 0, FirstNotDef - FirstDef);

  if(!XXXReadDataFromGlobal(C, ReadOffset, tempBuf, FirstNotDef - FirstDef, *GlobalTD)) {
    LLVM_DEBUG(dbgs() << "XXXReadDataFromGlobal failed; perhaps the source " << *(C) << " can't be bitcast?\n");
    if(error)
      *error = "RDFG";
    return false;
  }

  combineWith(tempBuf, FirstDef, FirstNotDef);
  return true;

}

// Build a Constant from filled PartialVal PV. 
Constant* llvm::PVToConst(PartialVal& PV, uint64_t Size, LLVMContext& Ctx) {

  if(Size <= 8) {
    Type* targetType = Type::getIntNTy(Ctx, Size * 8);
    return constFromBytes((unsigned char*)PV.partialBuf, targetType, GlobalTD);
  }
  else
    return ConstantDataArray::get(Ctx, ArrayRef<uint8_t>((uint8_t*)PV.partialBuf, Size));

}

bool llvm::addIVToPartialVal(const ImprovedVal& IV, ValSetType SetType, uint64_t IVOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error) {

  release_assert(PV && "Must allocate PV before calling addIVToPartialVal");

  // And also if the value that would be merged is not constant-typed:
  if(SetType != ValSetTypeScalar && SetType != ValSetTypeScalarSplat)
    return false;


  Constant* DefC = getSingleConstant(IV.V);
  if(SetType == ValSetTypeScalar) {

    return PV->combineWith(DefC, IVOffset, PVOffset, PVOffset + Size, error);
    
  }
  else {

    // Splat of i8:
    uint8_t SplatVal = (uint8_t)(cast<ConstantInt>(DefC)->getLimitedValue());
    PartialVal NewPV(Size);
    
    uint8_t* buffer = (uint8_t*)NewPV.partialBuf;
    bool* validBuf = (bool*)NewPV.partialValidBuf;
    
    for(uint64_t i = 0; i < Size; ++i) {
      buffer[i] = SplatVal;
      validBuf[i] = true;
    }

    PV->combineWith(NewPV, PVOffset, PVOffset + Size);
    return true;
    
  }

}

bool llvm::addIVSToPartialVal(const ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error) {

  // For now we forbid building from bytes when an input is set-typed:
  if(IVS.isWhollyUnknown() || IVS.Values.size() != 1)
    return false;
  
  return addIVToPartialVal(IVS.Values[0], IVS.SetType, IVSOffset, PVOffset, Size, PV, error);

}

