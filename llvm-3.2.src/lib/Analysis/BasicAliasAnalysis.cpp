//===- BasicAliasAnalysis.cpp - Stateless Alias Analysis Impl -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the default implementation of the Alias Analysis interface
// that simply implements a few identities (two different globals cannot alias,
// etc), but otherwise does no analysis.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Constants.h"
#include "llvm/DataLayout.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalAlias.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Operator.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"

#include <algorithm>
using namespace llvm;

//===----------------------------------------------------------------------===//
// Useful predicates
//===----------------------------------------------------------------------===//

/// isNonEscapingLocalObject - Return true if the pointer is to a function-local
/// object that never escapes from the function.
static bool isNonEscapingLocalObject(const Value *V, bool PHISelectCaptures = false) {
  // If this is a local allocation, check to see if it escapes.
  if (isa<AllocaInst>(V) || isNoAliasCall(V))
    // Set StoreCaptures to True so that we can assume in our callers that the
    // pointer is not the result of a load instruction. Currently
    // PointerMayBeCaptured doesn't have any special analysis for the
    // StoreCaptures=false case; if it did, our callers could be refined to be
    // more precise.
    return !PointerMayBeCaptured(V, false, /*StoreCaptures=*/true, PHISelectCaptures);

  // If this is an argument that corresponds to a byval or noalias argument,
  // then it has not escaped before entering the function.  Check if it escapes
  // inside the function.
  if (const Argument *A = dyn_cast<Argument>(V))
    if (A->hasByValAttr() || A->hasNoAliasAttr()) {
      // Note even if the argument is marked nocapture we still need to check
      // for copies made inside the function. The nocapture attribute only
      // specifies that there are no copies made that outlive the function.
      return !PointerMayBeCaptured(V, false, /*StoreCaptures=*/true, PHISelectCaptures);
    }
  return false;
}

static bool pointerNeverUsedIndirectly(const Value* V) {

  return isNonEscapingLocalObject(V, true);

}

/// isEscapeSource - Return true if the pointer is one which would have
/// been considered an escape by isNonEscapingLocalObject.
static bool isEscapeSource(const Value *V) {
  if (isa<CallInst>(V) || isa<InvokeInst>(V) || isa<Argument>(V))
    return true;

  // The load case works because isNonEscapingLocalObject considers all
  // stores to be escapes (it passes true for the StoreCaptures argument
  // to PointerMayBeCaptured).
  if (isa<LoadInst>(V))
    return true;

  return false;
}

static bool isIndirectUser(const Value* V) {

  return isEscapeSource(V) || isa<PHINode>(V) || isa<SelectInst>(V);

}

/// getObjectSize - Return the size of the object specified by V, or
/// UnknownSize if unknown.
static uint64_t getObjectSize(const Value *V, const DataLayout &TD,
                              const TargetLibraryInfo &TLI,
                              bool RoundToAlign = false) {
  uint64_t Size;
  if (getObjectSize(V, Size, &TD, &TLI, RoundToAlign))
    return Size;
  return AliasAnalysis::UnknownSize;
}

/// isObjectSmallerThan - Return true if we can prove that the object specified
/// by V is smaller than Size.
static bool isObjectSmallerThan(const Value *V, uint64_t Size,
				const DataLayout& TD,
				const TargetLibraryInfo& TLI) {

  // This function needs to use the aligned object size because we allow
  // reads a bit past the end given sufficient alignment.
  uint64_t ObjectSize = getObjectSize(V, TD, TLI, /*RoundToAlign*/true);
  return ObjectSize != AliasAnalysis::UnknownSize && ObjectSize < Size;

}

/// isObjectSize - Return true if we can prove that the object specified
/// by V has size Size.
static bool isObjectSize(const Value *V, uint64_t Size,
                         const DataLayout &TD, const TargetLibraryInfo &TLI) {
  uint64_t ObjectSize = getObjectSize(V, TD, TLI);
  return ObjectSize != AliasAnalysis::UnknownSize && ObjectSize == Size;
}

//===----------------------------------------------------------------------===//
// GetElementPtr Instruction Decomposition and Analysis
//===----------------------------------------------------------------------===//

namespace {
  enum ExtensionKind {
    EK_NotExtended,
    EK_SignExt,
    EK_ZeroExt
  };
  
  struct VariableGEPIndex {
    ShadowValue VC;
    ExtensionKind Extension;
    int64_t Scale;

    bool operator==(const VariableGEPIndex &Other) const {
      return VC == Other.VC && Extension == Other.Extension &&
        Scale == Other.Scale;
    }

    bool operator!=(const VariableGEPIndex &Other) const {
      return !operator==(Other);
    }

  };
}

/// GetIndexDifference - Dest and Src are the variable indices from two
/// decomposed GetElementPtr instructions GEP1 and GEP2 which have common base
/// pointers.  Subtract the GEP2 indices from GEP1 to find the symbolic
/// difference between the two pointers. 
static void GetIndexDifference(SmallVectorImpl<VariableGEPIndex> &Dest,
                               const SmallVectorImpl<VariableGEPIndex> &Src) {
  if (Src.empty()) return;

  for (unsigned i = 0, e = Src.size(); i != e; ++i) {
    const ShadowValue VC = Src[i].VC;
    ExtensionKind Extension = Src[i].Extension;
    int64_t Scale = Src[i].Scale;
    
    // Find VC in Dest.  This is N^2, but pointer indices almost never have more
    // than a few variable indexes.
    for (unsigned j = 0, e = Dest.size(); j != e; ++j) {
      if (Dest[j].VC != VC || Dest[j].Extension != Extension) continue;
      
      // If we found it, subtract off Scale VC's from the entry in Dest.  If it
      // goes to zero, remove the entry.
      if (Dest[j].Scale != Scale)
        Dest[j].Scale -= Scale;
      else
        Dest.erase(Dest.begin()+j);
      Scale = 0;
      break;
    }
    
    // If we didn't consume this entry, add it to the end of the Dest list.
    if (Scale) {
      VariableGEPIndex Entry = { VC, Extension, -Scale };
      Dest.push_back(Entry);
    }
  }
}

//===----------------------------------------------------------------------===//
// BasicAliasAnalysis Pass
//===----------------------------------------------------------------------===//

#ifndef NDEBUG
static const Function *getParent(const Value *V) {
  if (const Instruction *inst = dyn_cast<Instruction>(V))
    return inst->getParent()->getParent();

  if (const Argument *arg = dyn_cast<Argument>(V))
    return arg->getParent();

  return NULL;
}

static bool notDifferentParent(const Value *O1, const Value *O2) {

  const Function *F1 = getParent(O1);
  const Function *F2 = getParent(O2);

  return !F1 || !F2 || F1 == F2;
}
#endif

namespace {

  /// BasicAliasAnalysis - This is the primary alias analysis implementation.
  struct BasicAliasAnalysis : public ImmutablePass, public AliasAnalysis {
    static char ID; // Class identification, replacement for typeinfo
    BasicAliasAnalysis() : ImmutablePass(ID) {
      initializeBasicAliasAnalysisPass(*PassRegistry::getPassRegistry());
    }

    virtual void initializePass() {
      InitializeAliasAnalysis(this);
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<AliasAnalysis>();
      AU.addRequired<TargetLibraryInfo>();
    }

    virtual AliasResult alias(const Location &LocA,
			      const Location &LocB) {

      return aliasHypothetical(ShadowValue(const_cast<Value*>(LocA.Ptr)), LocA.Size, LocA.TBAATag, ShadowValue(const_cast<Value*>(LocB.Ptr)), LocB.Size, LocB.TBAATag, true);

    }

    virtual AliasResult aliasHypothetical(ShadowValue V1, uint64_t V1Size, const MDNode* V1TBAAInfo,
					  ShadowValue V2, uint64_t V2Size, const MDNode* V2TBAAInfo,
					  bool usePBKnowledge) {

      // I think I can ignore the not-different assertion!
      assert(AliasCache.empty() && "AliasCache must be cleared after use!");
      AliasResult Alias = aliasCheck(V1, V1Size, V1TBAAInfo, V2, V2Size, V2TBAAInfo);
      AliasCache.shrink_and_clear();
      return Alias;

    }

    virtual ModRefResult getCSModRefInfo(ShadowValue CS, ShadowValue P, uint64_t Size, const MDNode* PTBAAInfo,
					 bool usePBKnowledge = true, int64_t POffset = 0, IntAAProxy* AACB = 0);

    virtual ModRefResult get2CSModRefInfo(ShadowValue CS1, ShadowValue CS2, bool usePBKnowledge = true) {
      // The AliasAnalysis base class has some smarts, lets use them.
      return AliasAnalysis::get2CSModRefInfo(CS1, CS2, usePBKnowledge);
    }

    /// pointsToConstantMemory - Chase pointers until we find a (constant
    /// global) or not.
    virtual bool pointsToConstantMemory(const Location &Loc, bool OrLocal);

    /// getModRefBehavior - Return the behavior when calling the given
    /// call site.
    virtual ModRefBehavior getModRefBehavior(ImmutableCallSite CS);

    /// getModRefBehavior - Return the behavior when calling the given function.
    /// For use when the call site is not known.
    virtual ModRefBehavior getModRefBehavior(const Function *F);

    /// getAdjustedAnalysisPointer - This method is used when a pass implements
    /// an analysis interface through multiple inheritance.  If needed, it
    /// should override this to adjust the this pointer as needed for the
    /// specified pass info.
    virtual void *getAdjustedAnalysisPointer(const void *ID) {
      if (ID == &AliasAnalysis::ID)
        return (AliasAnalysis*)this;
      return this;
    }
    
  private:
    // AliasCache - Track alias queries to guard against recursion.
    typedef std::pair<Location, Location> LocPair;
    typedef SmallDenseMap<LocPair, AliasResult, 8> AliasCacheTy;
    AliasCacheTy AliasCache;
    SmallPtrSet<const Value*, 16> Visited;

    // aliasGEP - Provide a bunch of ad-hoc rules to disambiguate a GEP
    // instruction against another.
    AliasResult aliasGEP(ShadowValue V1, uint64_t V1Size,
			 const MDNode *V1TBAAInfo,
                         ShadowValue V2, uint64_t V2Size,
			 const MDNode *V2TBAAInfo,
                         ShadowValue UnderlyingV1, ShadowValue UnderlyingV2);

    // aliasPHI - Provide a bunch of ad-hoc rules to disambiguate a PHI
    // instruction against another.
    AliasResult aliasPHI(ShadowValue PN, uint64_t PNSize,
			 const MDNode *PNTBAAInfo,
                         ShadowValue V2, uint64_t V2Size,
			 const MDNode *V2TBAAInfo);

    /// aliasSelect - Disambiguate a Select instruction against another value.
    AliasResult aliasSelect(ShadowValue SI, uint64_t SISize,
			    const MDNode *SITBAAInfo,
                            ShadowValue V2, uint64_t V2Size,
			    const MDNode *V2TBAAInfo);

    AliasResult aliasCheck(ShadowValue V1, uint64_t V1Size,
			   const MDNode *V1TBAATag,
                           ShadowValue V2, uint64_t V2Size,
			   const MDNode *V2TBAATag);

    const ShadowValue DecomposeGEPExpression(const ShadowValue V, int64_t &BaseOffs,
					SmallVectorImpl<VariableGEPIndex> &VarIndices,
					const DataLayout *TD);

    bool GEPHasAllZeroIndices(ShadowValue GEPOp);

    ShadowValue getFirstOffset(ShadowValue);
		  
    // idOnly means that we won't walk through GEP instructions that offset the pointer.
    ShadowValue getUnderlyingObject(ShadowValue VIn, bool& isOffset, bool idOnly = false);


    ShadowValue GetLinearExpression(ShadowValue, APInt &Scale, APInt &Offset,
				    ExtensionKind &Extension,
				    const DataLayout &TD, unsigned Depth);

  };
}  // End of anonymous namespace

// Register this pass...
char BasicAliasAnalysis::ID = 0;
INITIALIZE_AG_PASS_BEGIN(BasicAliasAnalysis, AliasAnalysis, "basicaa",
			 "Basic Alias Analysis (stateless AA impl)",
			 false, true, false);
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfo)
INITIALIZE_AG_PASS_END(BasicAliasAnalysis, AliasAnalysis, "basicaa",
		       "Basic Alias Analysis (stateless AA impl)",
		       false, true, false)

ImmutablePass *llvm::createBasicAliasAnalysisPass() {
  return new BasicAliasAnalysis();
}

bool BasicAliasAnalysis::GEPHasAllZeroIndices(ShadowValue GEPOp) {
  const GEPOperator* GEP = cast_val<GEPOperator>(GEPOp);
  for (unsigned i = 1, e = GEP->getNumOperands(); i != e; ++i) {
    Constant* C = getConstReplacement(getValOperand(GEPOp, i));
    if (ConstantInt *CI = dyn_cast_or_null<ConstantInt>(C)) {
      if (!CI->isZero()) return false;
    } 
    else {
      return false;
    }
  }
  return true;
}

/// GetLinearExpression - Analyze the specified value as a linear expression:
/// "A*V + B", where A and B are constant integers.  Return the scale and offset
/// values as APInts and return V as a Value*, and return whether we looked
/// through any sign or zero extends.  The incoming Value is known to have
/// IntegerType and it may already be sign or zero extended.
///
/// Note that this looks through extends, so the high bits may not be
/// represented in the result.
ShadowValue BasicAliasAnalysis::GetLinearExpression(ShadowValue V, APInt &Scale, APInt &Offset,
						    ExtensionKind &Extension,
						    const DataLayout &TD, unsigned Depth) {
  assert(V->getType()->isIntegerTy() && "Not an integer value");

  // Limit our recursion depth.
  if (Depth == 6) {
    Scale = 1;
    Offset = 0;
    return V;
  }
  
  if (BinaryOperator* BOp = dyn_cast_val<BinaryOperator>(V)) {
    ShadowValue VC = getValOperand(V, 1);
    if (ConstantInt *RHSC = dyn_cast_or_null<ConstantInt>(getConstReplacement(VC))) {
      switch (BOp->getOpcode()) {
      default: break;
      case Instruction::Or:
        // X|C == X+C if all the bits in C are unset in X.  Otherwise we can't
        // analyze it.
        if (!MaskedValueIsZero(getValOperand(V, 0).getBareVal(), RHSC->getValue(), &TD))
          break;
        // FALL THROUGH.
      case Instruction::Add:
        V = GetLinearExpression(getValOperand(V, 0), Scale, Offset, Extension,
                                TD, Depth+1);
        Offset += RHSC->getValue();
        return V;
      case Instruction::Mul:
        V = GetLinearExpression(getValOperand(V, 0), Scale, Offset, Extension,
                                TD, Depth+1);
        Offset *= RHSC->getValue();
        Scale *= RHSC->getValue();
        return V;
      case Instruction::Shl:
        V = GetLinearExpression(getValOperand(V, 0), Scale, Offset, Extension,
                                TD, Depth+1);
        Offset <<= RHSC->getValue().getLimitedValue();
        Scale <<= RHSC->getValue().getLimitedValue();
        return V;
      }
    }
  }
  
  // Since GEP indices are sign extended anyway, we don't care about the high
  // bits of a sign or zero extended value - just scales and offsets.  The
  // extensions have to be consistent though.
  if ((val_is<SExtInst>(V) && Extension != EK_ZeroExt) ||
      (val_is<ZExtInst>(V) && Extension != EK_SignExt)) {
    ShadowValue CastOp = getValOperand(V, 0);
    unsigned OldWidth = Scale.getBitWidth();
    unsigned SmallWidth = CastOp.getType()->getPrimitiveSizeInBits();
    Scale = Scale.trunc(SmallWidth);
    Offset = Offset.trunc(SmallWidth);
    Extension = val_is<SExtInst>(V) ? EK_SignExt : EK_ZeroExt;

    ShadowValue Result = GetLinearExpression(CastOp, Scale, Offset, Extension,
					     TD, Depth+1);
    Scale = Scale.zext(OldWidth);
    Offset = Offset.zext(OldWidth);
    
    return Result;
  }
  
  Scale = 1;
  Offset = 0;
  return V;
}

/// DecomposeGEPExpression - If V is a symbolic pointer expression, decompose it
/// into a base pointer with a constant offset and a number of scaled symbolic
/// offsets.
///
/// The scaled symbolic offsets (represented by pairs of a Value* and a scale in
/// the VarIndices vector) are Value*'s that are known to be scaled by the
/// specified amount, but which may have other unrepresented high bits. As such,
/// the gep cannot necessarily be reconstructed from its decomposed form.
///
/// When DataLayout is around, this function is capable of analyzing everything
/// that getUnderlyingObject() can look through.  When not, it just looks
/// through pointer casts.
///
const ShadowValue BasicAliasAnalysis::DecomposeGEPExpression(ShadowValue FirstV, int64_t &BaseOffs,
							     SmallVectorImpl<VariableGEPIndex> &VarIndices,
							     const DataLayout *TD) {
  // Limit recursion depth to limit compile time in crazy cases.
  unsigned MaxLookup = 10;
  
  ShadowValue V = FirstV;
  BaseOffs = 0;
  do {
    // See if this is a bitcast or GEP.
    const Operator *Op = dyn_cast_val<Operator>(V);
    if (Op == 0) {
      // The only non-operator case we can handle are GlobalAliases.
      if (GlobalAlias *GA = dyn_cast_val<GlobalAlias>(V)) {
        if (!GA->mayBeOverridden()) {
          V = ShadowValue(GA->getAliasee());
          continue;
        }
      }
    }
    else if (Op->getOpcode() == Instruction::BitCast) {
      V = getValOperand(V, 0);
      continue;
    }
    
    const GEPOperator *GEPOp = dyn_cast_or_null<GEPOperator>(Op);
    if (GEPOp == 0) {
      // TODO here: the real LLVM 3.2 uses SimplifyInstruction, find out if this is useful for
      // ShadowValues and if so use it.
      return V;
    }
    
    // Don't attempt to analyze GEPs over unsized objects.
    if (!cast<PointerType>(GEPOp->getOperand(0)->getType())
        ->getElementType()->isSized())
      return V;
    
    // If we are lacking DataLayout information, we can't compute the offets of
    // elements computed by GEPs.  However, we can handle bitcast equivalent
    // GEPs.
    if (TD == 0) {
      if (!GEPHasAllZeroIndices(V))
        return V;
      V = getValOperand(V, 0);
      continue;
    }
    
    // Walk the indices of the GEP, accumulating them into BaseOff/VarIndices.
    gep_type_iterator GTI = gep_type_begin(GEPOp);
    for(unsigned i = 0; i < GEPOp->getNumOperands() - 1; ++i) {
      ShadowValue Index = tryGetConstReplacement(getValOperand(V, i+1));
      
      // Compute the (potentially symbolic) offset in bytes for this index.
      if (StructType *STy = dyn_cast<StructType>(*GTI++)) {
        // For a struct, add the member offset.
        unsigned FieldNo = cast_val<ConstantInt>(Index)->getZExtValue();
        if (FieldNo == 0) continue;
        
        BaseOffs += TD->getStructLayout(STy)->getElementOffset(FieldNo);
        continue;
      }

      // For an array/pointer, add the element offset, explicitly scaled.

      if (ConstantInt* CIdx = dyn_cast_val<ConstantInt>(Index)) {
        if (CIdx->isZero()) continue;
        BaseOffs += TD->getTypeAllocSize(*GTI)*CIdx->getSExtValue();
        continue;
      }
      
      uint64_t Scale = TD->getTypeAllocSize(*GTI);
      ExtensionKind Extension = EK_NotExtended;
      
      // If the integer type is smaller than the pointer size, it is implicitly
      // sign extended to pointer size.
      unsigned Width = cast<IntegerType>(Index.getType())->getBitWidth();
      if (TD->getPointerSizeInBits() > Width)
        Extension = EK_SignExt;
      
      // Use GetLinearExpression to decompose the index into a C1*V+C2 form.
      APInt IndexScale(Width, 0), IndexOffset(Width, 0);
      Index = GetLinearExpression(Index, IndexScale, IndexOffset, Extension, *TD, 0);
      
      // The GEP index scale ("Scale") scales C1*V+C2, yielding (C1*V+C2)*Scale.
      // This gives us an aggregate computation of (C1*Scale)*V + C2*Scale.
      BaseOffs += IndexOffset.getSExtValue()*Scale;
      Scale *= IndexScale.getSExtValue();
      
      
      // If we already had an occurrence of this index variable, merge this
      // scale into it.  For example, we want to handle:
      //   A[x][x] -> x*16 + x*4 -> x*20
      // This also ensures that 'x' only appears in the index list once.
      for (unsigned i = 0, e = VarIndices.size(); i != e; ++i) {
        if (VarIndices[i].VC == Index &&
            VarIndices[i].Extension == Extension) {
          Scale += VarIndices[i].Scale;
          VarIndices.erase(VarIndices.begin()+i);
          break;
        }
      }
      
      // Make sure that we have a scale that makes sense for this target's
      // pointer size.
      if (unsigned ShiftBits = 64-TD->getPointerSizeInBits()) {
        Scale <<= ShiftBits;
        Scale = (int64_t)Scale >> ShiftBits;
      }
      
      if (Scale) {
        VariableGEPIndex Entry = {Index, Extension, static_cast<int64_t>(Scale)};
        VarIndices.push_back(Entry);
      }
    }
    
    // Analyze the base pointer next.
    V = getValOperand(V, 0);
  } while (--MaxLookup);
  
  // If the chain of expressions is too deep, just return early.
  return V;
}

/// pointsToConstantMemory - Returns whether the given pointer value
/// points to memory that is local to the function, with global constants being
/// considered local to all functions.
bool
BasicAliasAnalysis::pointsToConstantMemory(const Location &Loc, bool OrLocal) {
  assert(Visited.empty() && "Visited must be cleared after use!");

  unsigned MaxLookup = 8;
  SmallVector<const Value *, 16> Worklist;
  Worklist.push_back(Loc.Ptr);
  do {
    const Value *V = GetUnderlyingObject(Worklist.pop_back_val(), TD);
    if (!Visited.insert(V)) {
      Visited.clear();
      return AliasAnalysis::pointsToConstantMemory(Loc, OrLocal);
    }

    // An alloca instruction defines local memory.
    if (OrLocal && isa<AllocaInst>(V))
      continue;

    // A global constant counts as local memory for our purposes.
    if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V)) {
      // Note: this doesn't require GV to be "ODR" because it isn't legal for a

      // global to be marked constant in some modules and non-constant in
      // others.  GV may even be a declaration, not a definition.
      if (!GV->isConstant()) {
        Visited.clear();
        return AliasAnalysis::pointsToConstantMemory(Loc, OrLocal);
      }
      continue;
    }

    // If both select values point to local memory, then so does the select.
    if (const SelectInst *SI = dyn_cast<SelectInst>(V)) {
      Worklist.push_back(SI->getTrueValue());
      Worklist.push_back(SI->getFalseValue());
      continue;
    }

    // If all values incoming to a phi node point to local memory, then so does
    // the phi.
    if (const PHINode *PN = dyn_cast<PHINode>(V)) {
      // Don't bother inspecting phi nodes with many operands.
      if (PN->getNumIncomingValues() > MaxLookup) {
        Visited.clear();
        return AliasAnalysis::pointsToConstantMemory(Loc, OrLocal);
      }
      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
        Worklist.push_back(PN->getIncomingValue(i));
      continue;
    }

    // Otherwise be conservative.
    Visited.clear();
    return AliasAnalysis::pointsToConstantMemory(Loc, OrLocal);

  } while (!Worklist.empty() && --MaxLookup);

  Visited.clear();
  return Worklist.empty();

}

/// getModRefBehavior - Return the behavior when calling the given call site.
AliasAnalysis::ModRefBehavior
BasicAliasAnalysis::getModRefBehavior(ImmutableCallSite CS) {
  if (CS.doesNotAccessMemory())
    // Can't do better than this.
    return DoesNotAccessMemory;

  ModRefBehavior Min = UnknownModRefBehavior;

  // If the callsite knows it only reads memory, don't return worse
  // than that.
  if (CS.onlyReadsMemory())
    Min = OnlyReadsMemory;

  // The AliasAnalysis base class has some smarts, lets use them.
  return ModRefBehavior(AliasAnalysis::getModRefBehavior(CS) & Min);
}

/// getModRefBehavior - Return the behavior when calling the given function.
/// For use when the call site is not known.
AliasAnalysis::ModRefBehavior
BasicAliasAnalysis::getModRefBehavior(const Function *F) {
  // If the function declares it doesn't access memory, we can't do better.
  if (F->doesNotAccessMemory())
    return DoesNotAccessMemory;
  
  // For intrinsics, we can check the table.
  if (unsigned iid = F->getIntrinsicID()) {
#define GET_INTRINSIC_MODREF_BEHAVIOR
#include "llvm/Intrinsics.gen"
#undef GET_INTRINSIC_MODREF_BEHAVIOR
  }
  
  ModRefBehavior Min = UnknownModRefBehavior;

  // If the function declares it only reads memory, go with that.
  if (F->onlyReadsMemory())
    Min = OnlyReadsMemory;

  // Otherwise be conservative.
  return ModRefBehavior(AliasAnalysis::getModRefBehavior(F) & Min);
}

/// getModRefInfo - Check to see if the specified callsite can clobber the
/// specified memory object.  Since we only look at local properties of this
/// function, we really can't say much about this query.  We do, however, use
/// simple "address taken" analysis on local objects.
AliasAnalysis::ModRefResult
BasicAliasAnalysis::getCSModRefInfo(ShadowValue CSV, ShadowValue P, uint64_t Size, const MDNode* PTBAAInfo, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {
  assert((notDifferentParent(CSV.getBareVal(), P.getBareVal()) || (CSV.getCtx() && P.getCtx())) &&
         "AliasAnalysis query involving multiple functions!");

  // Either both values have a context or neither one does.
  assert(!!CSV.getCtx() == !!P.getCtx());

  ImmutableCallSite CS(CSV.getBareVal());
  ShadowValue PUO;

  if(POffset == LLONG_MAX) {

    if(P.getCtx())
      getBaseAndOffset(P, PUO, POffset);
    else {
      bool ignored;
      PUO = getUnderlyingObject(P, ignored);
    }

  }
  else {

    PUO = P;

  }
  
  if(PUO.getCtx() == CSV.getCtx()) {

    Value* Object = PUO.getBareVal();
    
    // If this is a tail call and P points to a stack location, we know that
    // the tail call cannot access or modify the local stack.
    // We cannot exclude byval arguments here; these belong to the caller of
    // the current function not to the current function, and a tail callee
    // may reference them.
    if (isa<AllocaInst>(Object))
      if (const CallInst *CI = dyn_cast_val<CallInst>(CSV))
	if (CI->isTailCall())
	  return NoModRef;
  
    // If the pointer is to a locally allocated object that does not escape,
    // then the call can not mod/ref the pointer unless the call takes the pointer
    // as an argument, and itself doesn't capture it.
    if (!isa<Constant>(Object) && CSV.getBareVal() != Object &&
	isNonEscapingLocalObject(Object)) {
      bool PassedAsArg = false;
      unsigned ArgNo = 0;
      for (ImmutableCallSite::arg_iterator CI = CS.arg_begin(), CE = CS.arg_end();
	   CI != CE; ++CI, ++ArgNo) {
	// Only look at the no-capture or byval pointer arguments. If this
	// pointer were passed to arguments that were neither of these, then it
	// couldn't be no-capture.

	if (!(*CI)->getType()->isPointerTy() ||
	    (!CS.doesNotCapture(ArgNo) && !CS.isByValArgument(ArgNo)))
	  continue;
      
	// If  this is a no-capture pointer argument, see if we can tell that it
	// is impossible to alias the pointer we're checking.  If not, we have to
	// assume that the call could touch the pointer, even though it doesn't
	// escape.
	
	// TODO: Get actual arg TBAAInfo somehow (check Location constructor)
	if (!isNoAlias(P, UnknownSize, PTBAAInfo, getValOperand(CSV, ArgNo), UnknownSize, /* TBAA=*/0, usePBKnowledge, POffset, AACB)) {
	  PassedAsArg = true;
	  break;
	}
      }
    
      if (!PassedAsArg)
	return NoModRef;
    }

  }

  const TargetLibraryInfo &TLI = getAnalysis<TargetLibraryInfo>();
  ModRefResult Min = ModRef;

  // Finally, handle specific knowledge of intrinsics.
  const IntrinsicInst *II = dyn_cast_val<IntrinsicInst>(CSV);
  if (II != 0) {
    switch (II->getIntrinsicID()) {
    default: break;
    case Intrinsic::memcpy:
    case Intrinsic::memmove: {
      uint64_t Len = UnknownSize;
      if (ConstantInt *LenCI = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CSV, 2))))
        Len = LenCI->getZExtValue();
      ShadowValue Dest = getValArgOperand(CSV, 0);
      ShadowValue Src = getValArgOperand(CSV, 1);
      if (isNoAlias(P, Size, PTBAAInfo, Dest, Len, 0, usePBKnowledge, POffset, AACB)) {
        if (isNoAlias(P, Size, PTBAAInfo, Src, Len, 0, usePBKnowledge, POffset, AACB))
          return NoModRef;
	// If it can't overlap the dest, then worst case it reads the loc.
	Min = Ref;
      } else if (isNoAlias(P, Size, PTBAAInfo, Src, Len, 0, usePBKnowledge, POffset, AACB)) {
	// If it can't overlap the source, then worst case it mutates the loc.
	Min = Mod;
      }
      break;
    }
    case Intrinsic::memset:
      // Since memset is 'accesses arguments' only, the AliasAnalysis base class
      // will handle it for the variable length case.
      if (ConstantInt *LenCI = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CSV, 2)))) {
        uint64_t Len = LenCI->getZExtValue();
        ShadowValue Dest = getValArgOperand(CSV, 0);
        if (isNoAlias(P, Size, PTBAAInfo, Dest, Len, 0, usePBKnowledge, POffset, AACB))
          return NoModRef;
      }
      // We know that memset doesn't load anything.
      Min = Mod;
      break;
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
    case Intrinsic::invariant_start: {
      uint64_t PtrSize =
        (cast_val<ConstantInt>(getValArgOperand(CSV, 0)))->getZExtValue();
      if (isNoAlias(P, Size, PTBAAInfo, getValArgOperand(CSV, 1), PtrSize, II->getMetadata(LLVMContext::MD_tbaa), usePBKnowledge, POffset, AACB))
        return NoModRef;
      break;
    }
    case Intrinsic::invariant_end: {
      uint64_t PtrSize =
        cast_val<ConstantInt>(getValArgOperand(CSV, 1))->getZExtValue();
      if (isNoAlias(P, Size, PTBAAInfo, getValArgOperand(CSV, 2), PtrSize, II->getMetadata(LLVMContext::MD_tbaa), usePBKnowledge, POffset, AACB))
        return NoModRef;
      break;
    }
    case Intrinsic::arm_neon_vld1: {
      // LLVM's vld1 and vst1 intrinsics currently only support a single
      // vector register.
      uint64_t PtrSize =
        TD ? TD->getTypeStoreSize(II->getType()) : UnknownSize;
      if (isNoAlias(P, Size, PTBAAInfo, getValArgOperand(CSV, 0), PtrSize, II->getMetadata(LLVMContext::MD_tbaa), usePBKnowledge, POffset, AACB))
	return NoModRef;
      break;
    }
    case Intrinsic::arm_neon_vst1: {
      uint64_t PtrSize =
        TD ? TD->getTypeStoreSize(II->getArgOperand(1)->getType()) : UnknownSize;
      if (isNoAlias(P, Size, PTBAAInfo, getValArgOperand(CSV, 0), PtrSize, II->getMetadata(LLVMContext::MD_tbaa), usePBKnowledge, POffset, AACB))
        return NoModRef;
      break;
    }
    }

  } // End if-is-intrinsic

  // We can bound the aliasing properties of memset_pattern16 just as we can
  // for memcpy/memset.  This is particularly important because the 
  // LoopIdiomRecognizer likes to turn loops into calls to memset_pattern16
  // whenever possible.
  else if (TLI.has(LibFunc::memset_pattern16) &&
           CS.getCalledFunction() &&
           CS.getCalledFunction()->getName() == "memset_pattern16") {
    const Function *MS = CS.getCalledFunction();
    FunctionType *MemsetType = MS->getFunctionType();
    if (!MemsetType->isVarArg() && MemsetType->getNumParams() == 3 &&
        isa<PointerType>(MemsetType->getParamType(0)) &&
        isa<PointerType>(MemsetType->getParamType(1)) &&
        isa<IntegerType>(MemsetType->getParamType(2))) {
      uint64_t Len = UnknownSize;
      if (const ConstantInt *LenCI = dyn_cast<ConstantInt>(getConstReplacement(getValArgOperand(CSV, 2))))
        Len = LenCI->getZExtValue();
      ShadowValue Dest = getValArgOperand(CSV, 0);
      ShadowValue Src = getValArgOperand(CSV, 1);
      // If it can't overlap the source dest, then it doesn't modref the loc.
      if (isNoAlias(P, Size, PTBAAInfo, Dest, Len, 0, usePBKnowledge, POffset, AACB)) {
        // Always reads 16 bytes of the source.
        if (isNoAlias(P, Size, PTBAAInfo, Src, 16, 0, usePBKnowledge, POffset, AACB))
          return NoModRef;
	// If it can't overlap the dest, then worst case it reads the loc.
	Min = Ref;
	// Always reads 16 bytes of the source.
      } else if (isNoAlias(P, Size, PTBAAInfo, Src, 16, 0, usePBKnowledge, POffset, AACB)) {
        // If it can't overlap the source, then worst case it mutates the loc.
        Min = Mod;
      }
    }
  }
  
  // The AliasAnalysis base class has some smarts, lets use them.
  return ModRefResult(AliasAnalysis::getCSModRefInfo(CSV, P, Size, PTBAAInfo, usePBKnowledge, POffset, AACB) & Min);
}

static bool areVarIndicesEqual(SmallVector<VariableGEPIndex, 4> &Indices1,
                               SmallVector<VariableGEPIndex, 4> &Indices2) {
  unsigned Size1 = Indices1.size();
  unsigned Size2 = Indices2.size();

  if (Size1 != Size2)
    return false;

  for (unsigned I = 0; I != Size1; ++I)
    if (Indices1[I] != Indices2[I])
      return false;

  return true;
}

/// aliasGEP - Provide a bunch of ad-hoc rules to disambiguate a GEP instruction
/// against another pointer.  We know that V1 is a GEP, but we don't know
/// anything about V2.  UnderlyingV1 is GEP1->getUnderlyingObject(),
/// UnderlyingV2 is the same for V2.
///
AliasAnalysis::AliasResult
BasicAliasAnalysis::aliasGEP(ShadowValue V1, uint64_t V1Size,
			     const MDNode *V1TBAAInfo,
                             ShadowValue V2, uint64_t V2Size,
			     const MDNode *V2TBAAInfo,
                             ShadowValue UnderlyingV1,
                             ShadowValue UnderlyingV2) {
  
  int64_t GEP1BaseOffset;
  SmallVector<VariableGEPIndex, 4> GEP1VariableIndices;

  // If we have two gep instructions with must-alias or not-alias'ing base
  // pointers, figure out if the indexes to the GEP tell us anything about the
  // derived pointer.
  if (val_is<GEPOperator>(V2)) {

    // Check for geps of non-aliasing underlying pointers where the offsets are
    // identical.
    if (V1Size == V2Size) {
      // Do the base pointers alias assuming type and size.
      AliasResult PreciseBaseAlias = aliasCheck(UnderlyingV1, V1Size,
                                                V1TBAAInfo, UnderlyingV2,
                                                V2Size, V2TBAAInfo);
      if (PreciseBaseAlias == NoAlias) {
        // See if the computed offset from the common pointer tells us about the
        // relation of the resulting pointer.
        int64_t GEP2BaseOffset;
        SmallVector<VariableGEPIndex, 4> GEP2VariableIndices;
        ShadowValue GEP2BasePtr =
          DecomposeGEPExpression(V2, GEP2BaseOffset, GEP2VariableIndices, TD);
        ShadowValue GEP1BasePtr =
          DecomposeGEPExpression(V1, GEP1BaseOffset, GEP1VariableIndices, TD);
        // DecomposeGEPExpression and GetUnderlyingObject should return the
        // same result except when DecomposeGEPExpression has no DataLayout.
        if (GEP1BasePtr != UnderlyingV1 || GEP2BasePtr != UnderlyingV2) {
          assert(TD == 0 &&
             "DecomposeGEPExpression and GetUnderlyingObject disagree!");
          return MayAlias;
        }
        // Same offsets.
        if (GEP1BaseOffset == GEP2BaseOffset &&
            areVarIndicesEqual(GEP1VariableIndices, GEP2VariableIndices))
          return NoAlias;
        GEP1VariableIndices.clear();
      }
    }
    
    // Do the base pointers alias?
    AliasResult BaseAlias = aliasCheck(UnderlyingV1, UnknownSize, 0,
                                       UnderlyingV2, UnknownSize, 0);
    
    // If we get a No or May, then return it immediately, no amount of analysis
    // will improve this situation.
    if (BaseAlias != MustAlias) return BaseAlias;
    
    // Otherwise, we have a MustAlias.  Since the base pointers alias each other
    // exactly, see if the computed offset from the common pointer tells us
    // about the relation of the resulting pointer.
    const ShadowValue GEP1BasePtr =
      DecomposeGEPExpression(V1, GEP1BaseOffset, GEP1VariableIndices, TD);
    
    int64_t GEP2BaseOffset;
    SmallVector<VariableGEPIndex, 4> GEP2VariableIndices;
    const ShadowValue GEP2BasePtr =
      DecomposeGEPExpression(V2, GEP2BaseOffset, GEP2VariableIndices, TD);
    
    // DecomposeGEPExpression and GetUnderlyingObject should return the
    // same result except when DecomposeGEPExpression has no DataLayout.
    if (GEP1BasePtr != UnderlyingV1 || GEP2BasePtr != UnderlyingV2) {
      assert(TD == 0 &&
             "DecomposeGEPExpression and getUnderlyingObject disagree!");
      return MayAlias;
    }
    
    // Subtract the GEP2 pointer from the GEP1 pointer to find out their
    // symbolic difference.
    GEP1BaseOffset -= GEP2BaseOffset;
    GetIndexDifference(GEP1VariableIndices, GEP2VariableIndices);
    
  } else {
    // Check to see if these two pointers are related by the getelementptr
    // instruction.  If one pointer is a GEP with a non-zero index of the other
    // pointer, we know they cannot alias.

    // If both accesses are unknown size, we can't do anything useful here.
    if (V1Size == UnknownSize && V2Size == UnknownSize)
      return MayAlias;

    AliasResult R = aliasCheck(UnderlyingV1, UnknownSize, 0,
			       V2, V2Size, V2TBAAInfo);
    if (R != MustAlias)
      // If V2 may alias GEP base pointer, conservatively returns MayAlias.
      // If V2 is known not to alias GEP base pointer, then the two values
      // cannot alias per GEP semantics: "A pointer value formed from a
      // getelementptr instruction is associated with the addresses associated
      // with the first operand of the getelementptr".
      return R;

    const ShadowValue GEP1BasePtr =
      DecomposeGEPExpression(V1, GEP1BaseOffset, GEP1VariableIndices, TD);
    
    // DecomposeGEPExpression and GetUnderlyingObject should return the
    // same result except when DecomposeGEPExpression has no DataLayout.
    if (GEP1BasePtr != UnderlyingV1) {
      assert(TD == 0 &&
             "DecomposeGEPExpression and getUnderlyingObject disagree!");
      return MayAlias;
    }
  }
  
  // In the two GEP Case, if there is no difference in the offsets of the
  // computed pointers, the resultant pointers are a must alias.  This
  // hapens when we have two lexically identical GEP's (for example).
  //
  // In the other case, if we have getelementptr <ptr>, 0, 0, 0, 0, ... and V2
  // must aliases the GEP, the end result is a must alias also.
  if (GEP1BaseOffset == 0 && GEP1VariableIndices.empty())
    return MustAlias;

  // If there is a constant difference between the pointers, but the difference
  // is less than the size of the associated memory object, then we know
  // that the objects are partially overlapping.  If the difference is
  // greater, we know they do not overlap.
  if (GEP1BaseOffset != 0 && GEP1VariableIndices.empty()) {
    if (GEP1BaseOffset >= 0) {
      if (V2Size != UnknownSize) {
        if ((uint64_t)GEP1BaseOffset < V2Size)
          return PartialAlias;
        return NoAlias;
      }
    } else {
      if (V1Size != UnknownSize) {
        if (-(uint64_t)GEP1BaseOffset < V1Size)
          return PartialAlias;
        return NoAlias;
      }
    }
  }

  // Try to distinguish something like &A[i][1] against &A[42][0].
  // Grab the least significant bit set in any of the scales.
  if (!GEP1VariableIndices.empty()) {
    uint64_t Modulo = 0;
    for (unsigned i = 0, e = GEP1VariableIndices.size(); i != e; ++i)
      Modulo |= (uint64_t)GEP1VariableIndices[i].Scale;
    Modulo = Modulo ^ (Modulo & (Modulo - 1));

    // We can compute the difference between the two addresses
    // mod Modulo. Check whether that difference guarantees that the
    // two locations do not alias.
    uint64_t ModOffset = (uint64_t)GEP1BaseOffset & (Modulo - 1);
    if (V1Size != UnknownSize && V2Size != UnknownSize &&
        ModOffset >= V2Size && V1Size <= Modulo - ModOffset)
      return NoAlias;
  }
  
  // Statically, we can see that the base objects are the same, but the
  // pointers have dynamic offsets which we can't resolve. And none of our
  // little tricks above worked.
  //
  // TODO: Returning PartialAlias instead of MayAlias is a mild hack; the
  // practical effect of this is protecting TBAA in the case of dynamic
  // indices into arrays of unions or malloc'd memory.
  return PartialAlias;

}

static AliasAnalysis::AliasResult
MergeAliasResults(AliasAnalysis::AliasResult A, AliasAnalysis::AliasResult B) {
  // If the results agree, take it.
  if (A == B)
    return A;
  // A mix of PartialAlias and MustAlias is PartialAlias.
  if ((A == AliasAnalysis::PartialAlias && B == AliasAnalysis::MustAlias) ||
      (B == AliasAnalysis::PartialAlias && A == AliasAnalysis::MustAlias))
    return AliasAnalysis::PartialAlias;
  // Otherwise, we don't know anything.
  return AliasAnalysis::MayAlias;
}

/// aliasSelect - Provide a bunch of ad-hoc rules to disambiguate a Select
/// instruction against another.
AliasAnalysis::AliasResult
BasicAliasAnalysis::aliasSelect(ShadowValue V1, uint64_t SISize,
				const MDNode *SITBAAInfo,
                                ShadowValue V2, uint64_t V2Size,
				const MDNode *V2TBAAInfo) {
  
  if(ShadowInstruction* SI = V1.getInst()) {
    ConstantInt* SICond = cast_or_null<ConstantInt>(getConstReplacement(SI->getOperand(0)));
    if(SICond) {
      if(!SICond->isZero()) 
	return aliasCheck(getValOperand(V1, 1), SISize, SITBAAInfo, V2, V2Size, V2TBAAInfo);
      else
	return aliasCheck(getValOperand(V1, 2), SISize, SITBAAInfo, V2, V2Size, V2TBAAInfo);
    }
  }

  // If the values are Selects with the same condition, we can do a more precise
  // check: just check for aliases between the values on corresponding arms.
  if (val_is<SelectInst>(V2)) {
    if (getValOperand(V1, 0) == getValOperand(V2, 0)) {
      AliasResult Alias = aliasCheck(getValOperand(V1, 1), SISize, SITBAAInfo, 
				     getValOperand(V2, 1), V2Size, V2TBAAInfo);
      if (Alias == MayAlias)
        return MayAlias;
      AliasResult ThisAlias = aliasCheck(getValOperand(V1, 2), SISize, SITBAAInfo, 
					 getValOperand(V2, 2), V2Size, V2TBAAInfo);
      return MergeAliasResults(ThisAlias, Alias);
    }
  }

  // If both arms of the Select node NoAlias or MustAlias V2, then returns
  // NoAlias / MustAlias. Otherwise, returns MayAlias.
  AliasResult Alias =
    aliasCheck(V2, V2Size, V2TBAAInfo, getValOperand(V1, 1), SISize, SITBAAInfo);
  if (Alias == MayAlias)
    return MayAlias;

  AliasResult ThisAlias =
    aliasCheck(V2, V2Size, V2TBAAInfo, getValOperand(V1, 2), SISize, SITBAAInfo);
  return MergeAliasResults(ThisAlias, Alias);

}

// aliasPHI - Provide a bunch of ad-hoc rules to disambiguate a PHI instruction
// against another.
AliasAnalysis::AliasResult
BasicAliasAnalysis::aliasPHI(ShadowValue V1, uint64_t PNSize, const MDNode *PNTBAAInfo,
                             ShadowValue V2, uint64_t V2Size, const MDNode *V2TBAAInfo) {
  
  PHINode* PN = cast_val<PHINode>(V1);

  // If we're checking a header PHI, check the general case of the header rather than that
  // from this particular iteration of a loop. This is necessary so that e.g. iteration 2 doesn't
  // use the iteration 1 header input and conclude that the latch input is dead (in fact it's not
  // yet created).

  if(ShadowInstruction* SI = V1.getInst()) {
    if(SI->parent->IA->L && 
       SI->parent->IA->L == SI->parent->invar->naturalScope && 
       SI->parent->invar->naturalScope->getHeader() == SI->parent->invar->BB) {

      V1 = SI->parent->IA->getUniqueParent()->getInst(SI->invar);

    }
  }

  if(ShadowInstruction* SI = V2.getInst()) {
    if(inst_is<PHINode>(SI)) {
      if(SI->parent->IA->L && 
	 SI->parent->IA->L == SI->parent->invar->naturalScope && 
	 SI->parent->invar->naturalScope->getHeader() == SI->parent->invar->BB) {

	V2 = SI->parent->IA->getUniqueParent()->getInst(SI->invar);

      }
    }
  }

  // If the values are PHIs in the same block, we can do a more precise
  // as well as efficient check: just check for aliases between the values
  // on corresponding edges.

  const BasicBlock* PNParent = PN->getParent();

  if (const PHINode *PN2 = dyn_cast_val<PHINode>(V2))
    if (PN2->getParent() == PNParent && V1.getCtx() == V2.getCtx()) {

      // TOCHECK: Is discarding context ok here? I think it is because getValOperand
      // can't walk up the context tree and so introduce ambiguity and this map only
      // exists for the lifetime of one alias query.
      LocPair Locs(Location(PN, PNSize, PNTBAAInfo),
                   Location(PN2, V2Size, V2TBAAInfo));
      if (PN > V2)
        std::swap(Locs.first, Locs.second);

      bool AliasValid = false;
      AliasAnalysis::AliasResult Alias = MayAlias;
      bool ArePhisAssumedNoAlias = false;
      AliasResult OrigAliasResult = NoAlias;

      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
	
	AliasResult ThisAlias = MayAlias;

	if(ShadowInstruction* SI = V1.getInst()) {

	  ShadowBBInvar* PHIBB = SI->parent->invar;
	  uint32_t blockIdx = SI->invar->operandBBs[i];
	  ShadowBBInvar* PredBB = SI->parent->IA->getBBInvar(blockIdx);

	  if(SI->parent->IA->edgeIsDead(PredBB, PHIBB))
	    continue;
	  ShadowInstruction* SI2 = V2.getInst();

	  bool found = false;
  
	  for(uint32_t j = 0; j < PN2->getNumIncomingValues() && !found; ++j) {
	    
	    if(SI2->invar->operandBBs[j] == blockIdx) {
	      ThisAlias = aliasCheck(SI->getOperand(i), PNSize, PNTBAAInfo, SI2->getOperand(j), V2Size, V2TBAAInfo);
	      assert((!found) && "PHI predecessor named more than once?");
	      found = true;
	    }

	  }

	  assert(found && "Corresponding PHI predecessor not found?");

	}
	else {
	  ThisAlias =
	    aliasCheck(ShadowValue(PN->getIncomingValue(i)), PNSize, PNTBAAInfo,
		       ShadowValue(PN2->getIncomingValueForBlock(PN->getIncomingBlock(i))), V2Size, V2TBAAInfo);
	}

	if(!AliasValid) {

	  AliasValid = true;
	  Alias = ThisAlias;
	  if(ThisAlias == MayAlias)
	    return MayAlias;
	  
	  // If the first source of the PHI nodes NoAlias and the other inputs are
	  // the PHI node itself through some amount of recursion this does not add
	  // any new information so just return NoAlias.
	  // bb:
	  //    ptr = ptr2 + 1
	  // loop:
	  //    ptr_phi = phi [bb, ptr], [loop, ptr_plus_one]
	  //    ptr2_phi = phi [bb, ptr2], [loop, ptr2_plus_one]
	  //    ...
	  //    ptr_plus_one = gep ptr_phi, 1
	  //    ptr2_plus_one = gep ptr2_phi, 1
	  // We assume for the recursion that the the phis (ptr_phi, ptr2_phi) do
	  // not alias each other.
	  if (Alias == NoAlias) {
	    // Pretend the phis do not alias.
	    assert(AliasCache.count(Locs) &&
		   "There must exist an entry for the phi node");
	    OrigAliasResult = AliasCache[Locs];
	    AliasCache[Locs] = NoAlias;
	    ArePhisAssumedNoAlias = true;
	  }

	}
        else {
	  Alias = MergeAliasResults(ThisAlias, Alias);
	  if (Alias == MayAlias)
	    break;
	}

      }

      // Reset if speculation failed.
      if (ArePhisAssumedNoAlias && Alias != NoAlias)
        AliasCache[Locs] = OrigAliasResult;

      return Alias;

    }

  SmallVector<ShadowValue, 4> V1Srcs;
  for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
    
    // Get incoming value for predecessor i:
    ShadowValue PV1 = getValOperand(V1, i);

    if(PV1.isInval()) // Operand comes from a dead block
      continue;
    if (val_is<PHINode>(PV1))
      // If any of the source itself is a PHI, return MayAlias conservatively
      // to avoid compile time explosion. The worst possible case is if both
      // sides are PHI nodes. In which case, this is O(m x n) time where 'm'
      // and 'n' are the number of PHI sources.
      return MayAlias;
    if (std::find(V1Srcs.begin(), V1Srcs.end(), PV1) == V1Srcs.end())
      V1Srcs.push_back(PV1);
  }

  AliasResult Alias = aliasCheck(V2, V2Size, V2TBAAInfo, V1Srcs[0], PNSize, PNTBAAInfo);
  // Early exit if the check of the first PHI source against V2 is MayAlias.
  // Other results are not possible.
  if (Alias == MayAlias)
    return MayAlias;

  // If all sources of the PHI node NoAlias or MustAlias V2, then returns
  // NoAlias / MustAlias. Otherwise, returns MayAlias.
  for (unsigned i = 1, e = V1Srcs.size(); i != e; ++i) {
    ShadowValue V = V1Srcs[i];

    AliasResult ThisAlias = aliasCheck(V2, V2Size, V2TBAAInfo,
                                       V, PNSize, PNTBAAInfo);
    Alias = MergeAliasResults(ThisAlias, Alias);
    if (Alias == MayAlias)
      break;
  }
  
  return Alias;
}

// A cowardly duplication of Value::getUnderlyingObject, to avoid potentially screwups
// in modifying Value, which is used throughout LLVM.
ShadowValue BasicAliasAnalysis::getUnderlyingObject(ShadowValue VIn, bool& isOffset, bool idOnly) {
  
  unsigned MaxLookup = 10;
  if (!VIn.getType()->isPointerTy())
    return VIn;

  if(!VIn.isVal()) {
    
    ShadowValue VBase;
    int64_t VOffset;
    if(getBaseAndOffset(VIn, VBase, VOffset)) {

      isOffset = (VOffset != 0);
      return VBase;

    }

  }
  
  ShadowValue V = VIn;
  for (unsigned Count = 0; MaxLookup == 0 || Count < MaxLookup; ++Count) {

    if(ShadowInstruction* SI = V.getInst()) {

      if(inst_is<GetElementPtrInst>(SI)) {

	// This check turns out to be important: otherwise we might conclude that we need to 
	// check the aliasGEP path but then strip the all-zero GEP using Value::stripPointerCasts()
	// which regards such pointless GEPs as casts.
	// Then we end up with two non-GEP, non-PHI, non-Select instructions and fall through to MayAlias.
	// In summary: if we're going to conclude that two things Must-Alias due to referring 
	// to the same object without an offset, we must do so NOW.
	if(!GEPHasAllZeroIndices(V)) {
	  isOffset = true;
	  if(idOnly)
	    return V;
	}

	V = SI->getOperand(0);

      }
      else if(SI->invar->I->getOpcode() == Instruction::BitCast) {

	V = SI->getOperand(0);

      }
      else {
	
	return V;

      }

    }
    else if(Value* V2 = V.getVal()) {

      V2 = V2->stripPointerCasts();
      if(ConstantExpr* CE = dyn_cast<ConstantExpr>(V2)) {

	if(CE->getOpcode() == Instruction::GetElementPtr) {

	  if(!GEPHasAllZeroIndices(ShadowValue(CE))) {
	    isOffset = true;
	    if(idOnly)
	      return V2;
	  }

	  V = ShadowValue(CE->getOperand(0));

	}
	else {

	  return V2;

	}

      }
      else {

	return V2;

      }

    }
    else {

      return V;

    }

  }

  return V;  

}

// aliasCheck - Provide a bunch of ad-hoc rules to disambiguate in common cases,
// such as array references.
//
AliasAnalysis::AliasResult
BasicAliasAnalysis::aliasCheck(ShadowValue V1, uint64_t V1Size,
			       const MDNode *V1TBAAInfo,
                               ShadowValue V2, uint64_t V2Size,
			       const MDNode *V2TBAAInfo) {
  // If either of the memory references is empty, it doesn't matter what the
  // pointer values are.
  if (V1Size == 0 || V2Size == 0)
    return NoAlias;

  if (!V1.getType()->isPointerTy() || !V2.getType()->isPointerTy())
    return NoAlias;  // Scalars cannot alias each other

  // Figure out what objects these things are pointing to if we can.
  bool UO1Offset = false, UO2Offset = false;
  ShadowValue UO1 = getUnderlyingObject(V1, UO1Offset);
  Value* O1 = UO1.getBareVal();
  ShadowValue UO2 = getUnderlyingObject(V2, UO2Offset);
  Value* O2 = UO2.getBareVal();

  // Are we checking for alias of the same value?
  if (UO1 == UO2 && (!UO1Offset) && (!UO2Offset)) return MustAlias;

  // Otherwise either the pointers are based off potentially different objects,
  // or else they're potentially different derived pointers off the same base.

  // Strip off any casts and other identity operations if they exist.
  V1 = V1.stripPointerCasts();
  V2 = V2.stripPointerCasts();

  // Null values in the default address space don't point to any object, so they
  // don't alias any other pointer.
  if (const ConstantPointerNull *CPN = dyn_cast_or_null<ConstantPointerNull>(UO1.getVal()))
    if (CPN->getType()->getAddressSpace() == 0)
      return NoAlias;
  if (const ConstantPointerNull *CPN = dyn_cast_or_null<ConstantPointerNull>(UO2.getVal()))
    if (CPN->getType()->getAddressSpace() == 0)
      return NoAlias;

  if (UO1 != UO2) {
    // If V1/V2 point to two different objects we know that we have no alias.
    if (UO1.isIDObject() && UO2.isIDObject())
      return NoAlias;

    // Constant pointers can't alias with non-const isIdentifiedObject objects.
    if ((val_is<Constant>(UO1) && UO2.isIDObject() && !val_is<Constant>(UO2)) ||
        (val_is<Constant>(UO2) && UO1.isIDObject() && !val_is<Constant>(UO1)))
      return NoAlias;

    // Arguments can't alias with local allocations or noalias calls
    // in the same function.
    if (((val_is<Argument>(UO1) && (val_is<AllocaInst>(UO2) || isNoAliasCall(O2))) ||
         (val_is<Argument>(UO2) && (val_is<AllocaInst>(UO1) || isNoAliasCall(O1))))
	&& (UO1.getCtx() == UO2.getCtx()))
      return NoAlias;
    
    // Most objects can't alias null.
    if ((val_is<ConstantPointerNull>(UO2) && isKnownNonNull(O1)) ||
        (val_is<ConstantPointerNull>(UO1) && isKnownNonNull(O2)))
      return NoAlias;
    
    // If one pointer is the result of a call/invoke or load and the other is a
    // non-escaping local object within the same function, then we know the
    // object couldn't escape to a point where the call could return it.
    //
    // Note that if the pointers are in different functions, there are a
    // variety of complications. A call with a nocapture argument may still
    // temporary store the nocapture argument's value in a temporary memory
    // location if that memory location doesn't escape. Or it may pass a
    // nocapture value to other functions as long as they don't capture it.
    if(UO1.getCtx() == UO2.getCtx()) {

      if (isEscapeSource(O1) && isNonEscapingLocalObject(O2))
	return NoAlias;
      if (isIndirectUser(O1) && pointerNeverUsedIndirectly(O2))
	return NoAlias;

      if (isEscapeSource(O2) && isNonEscapingLocalObject(O1))
	return NoAlias;
      if (isIndirectUser(O2) && pointerNeverUsedIndirectly(O1))
	return NoAlias;

    }
  }

  // If the size of one access is larger than the entire object on the other
  // side, then we know such behavior is undefined and can assume no alias.
  if (TD)
    if ((V1Size != UnknownSize && isObjectSmallerThan(O2, V1Size, *TD, *TLI)) ||
        (V2Size != UnknownSize && isObjectSmallerThan(O1, V2Size, *TD, *TLI)))
      return NoAlias;

  // Check the cache before climbing up use-def chains. This also terminates
  // otherwise infinitely recursive queries.
  LocPair Locs(Location(V1.getBareVal(), V1Size, V1TBAAInfo),
               Location(V2.getBareVal(), V2Size, V2TBAAInfo));
  if (V1 > V2)
    std::swap(Locs.first, Locs.second);
  std::pair<AliasCacheTy::iterator, bool> Pair =
    AliasCache.insert(std::make_pair(Locs, MayAlias));
  if (!Pair.second)
    return Pair.first->second;
 
  // FIXME: This isn't aggressively handling alias(GEP, PHI) for example: if the
  // GEP can't simplify, we don't even look at the PHI cases.
  if (!val_is<GEPOperator>(V1) && val_is<GEPOperator>(V2)) {
    std::swap(V1, V2);
    std::swap(V1Size, V2Size);
    std::swap(UO1, UO2);
    std::swap(V1TBAAInfo, V2TBAAInfo);
  }
  if (val_is<GEPOperator>(V1)) {
    AliasResult Result = aliasGEP(V1, V1Size, V1TBAAInfo, V2, V2Size, V2TBAAInfo, UO1, UO2);
    if (Result != MayAlias) return AliasCache[Locs] = Result;
  }
  if (val_is<PHINode>(V2) && !val_is<PHINode>(V1)) {
    std::swap(V1, V2);
    std::swap(V1Size, V2Size);
    std::swap(V1TBAAInfo, V2TBAAInfo);
  }
  if (val_is<PHINode>(V1)) {
     AliasResult Result = aliasPHI(V1, V1Size, V1TBAAInfo, V2, V2Size, V2TBAAInfo);
     if (Result != MayAlias) return AliasCache[Locs] = Result;
  }

  if (val_is<SelectInst>(V2) && !val_is<SelectInst>(V1)) {
    std::swap(V1, V2);
    std::swap(V1Size, V2Size);
    std::swap(V1TBAAInfo, V2TBAAInfo);
  }
  if (val_is<SelectInst>(V1)) {
    AliasResult Result = aliasSelect(V1, V1Size, V1TBAAInfo, V2, V2Size, V2TBAAInfo);
    if (Result != MayAlias) return AliasCache[Locs] = Result;
  }
  
  // If both pointers are pointing into the same object and one of them
  // accesses is accessing the entire object, then the accesses must
  // overlap in some way.
  if (TD && O1 == O2)
    if ((V1Size != UnknownSize && isObjectSize(O1, V1Size, *TD, *TLI)) ||
        (V2Size != UnknownSize && isObjectSize(O2, V2Size, *TD, *TLI)))
      return AliasCache[Locs] = PartialAlias;
  
  AliasResult Result = AliasAnalysis::alias(Location(V1.getBareVal(), V1Size, V1TBAAInfo),
					    Location(V2.getBareVal(), V2Size, V2TBAAInfo));
  return AliasCache[Locs] = Result;

}

