//===- PartialLoadForward.cpp ---------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// Some functions converted from Transforms/Scalar/GVN.cpp that try to deal with cases when loads are clobbered by writes which define them
// but do so in a more complicated way than just an equal-sized write to the same pointer. For example, a memcpy that covers the load
// or a load i8 that gets a sub-field of a store i64.
// I also handle forwarding from read() operations here, since it's a lot like a forward from a memcpy.

#define DEBUG_TYPE "PartialLoadForward"

#include <llvm/Analysis/LLPE.h>

#include <llvm/IR/Instructions.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/GlobalVariable.h>

#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/IR/CallSite.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
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
    LLVM_DEBUG(dbgs() << "*** AA Failure ***\n");
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

// Flatten a bytestream (given as a uint64_t array for compatability with APInt) into a ConstantInt.
Constant* llvm::intFromBytes(const uint64_t* data, unsigned data_length, unsigned data_bits, LLVMContext& Context) {

  APInt AP(data_bits, data_length, data);
  return ConstantInt::get(Context, AP);

}

// Find out the index of the idx'th non-floating-point argument to this function.
// This is needed because varargs calling convention splits the integer-typed and FP-typed
// varargs.
int64_t InlineAttempt::NonFPArgIdxToArgIdx(int64_t idx) {

  // All callers must have the same operand count, so Callers[0] is ok.
  for(unsigned i = F.getFunctionType()->getNumParams(); i < Callers[0]->getNumArgOperands(); ++i) {

    ImmutableCallSite ICS(Callers[0]->invar->I);

    Type* T = ICS.getArgument(i)->getType();
    if(T->isPointerTy() || T->isIntegerTy()) {

      if(idx == 0)
	return ImprovedVal::first_any_arg + (i - F.getFunctionType()->getNumParams());
      else
	--idx;

    }
    else if(T->isFloatingPointTy()) {

      continue;

    }
    else {

      release_assert(0 && "Unhandled vararg type");

    }

  }

  return ImprovedVal::not_va_arg;

}

// Find the idx'th floating-point argument similar to above.
int64_t InlineAttempt::FPArgIdxToArgIdx(int64_t idx) {
  
  for(unsigned i = F.getFunctionType()->getNumParams(); i < Callers[0]->getNumArgOperands(); ++i) {

    ImmutableCallSite ICS(Callers[0]->invar->I);

    Type* T = ICS.getArgument(i)->getType();
    if(T->isPointerTy() || T->isIntegerTy()) {

      continue;

    }
    else if(T->isFloatingPointTy()) {

      if(idx == 0)
	return ImprovedVal::first_any_arg + (i - F.getFunctionType()->getNumParams());
      else
	--idx;

    }
    else {

      release_assert(0 && "Unhandled vararg type");

    }

  }

  return ImprovedVal::not_va_arg;

}
