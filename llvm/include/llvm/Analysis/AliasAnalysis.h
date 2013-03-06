//===- llvm/Analysis/AliasAnalysis.h - Alias Analysis Interface -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the generic AliasAnalysis interface, which is used as the
// common interface used by all clients of alias analysis information, and
// implemented by all alias analysis implementations.  Mod/Ref information is
// also captured by this interface.
//
// Implementations of this interface must implement the various virtual methods,
// which automatically provides functionality for the entire suite of client
// APIs.
//
// This API represents memory as a (Pointer, Size) pair.  The Pointer component
// specifies the base memory address of the region, the Size specifies how large
// of an area is being queried, or UnknownSize if the size is not known.
// Pointers that point to two completely different objects in memory never
// alias, regardless of the value of the Size component.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_ALIAS_ANALYSIS_H
#define LLVM_ANALYSIS_ALIAS_ANALYSIS_H

#include "llvm/Support/CallSite.h"
#include "llvm/System/IncludeFile.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include <vector>

namespace llvm {

class LoadInst;
class StoreInst;
class VAArgInst;
class TargetData;
class Pass;
class AnalysisUsage;
class IntegrationAttempt;

class AliasAnalysis {
protected:
  const TargetData *TD;

private:
  AliasAnalysis *AA;       // Previous Alias Analysis to chain to.

protected:
  /// InitializeAliasAnalysis - Subclasses must call this method to initialize
  /// the AliasAnalysis interface before any other methods are called.  This is
  /// typically called by the run* methods of these subclasses.  This may be
  /// called multiple times.
  ///
  void InitializeAliasAnalysis(Pass *P);

  /// getAnalysisUsage - All alias analysis implementations should invoke this
  /// directly (using AliasAnalysis::getAnalysisUsage(AU)).
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

public:
  static char ID; // Class identification, replacement for typeinfo
  AliasAnalysis() : TD(0), AA(0) {}
  virtual ~AliasAnalysis();  // We want to be subclassed

  /// UnknownSize - This is a special value which can be used with the
  /// size arguments in alias queries to indicate that the caller does not
  /// know the sizes of the potential memory references.
  static unsigned const UnknownSize = ~0u;

  /// getTargetData - Return a pointer to the current TargetData object, or
  /// null if no TargetData object is available.
  ///
  const TargetData *getTargetData() const { return TD; }

  /// getTypeStoreSize - Return the TargetData store size for the given type,
  /// if known, or a conservative value otherwise.
  ///
  unsigned getTypeStoreSize(const Type *Ty);

  //===--------------------------------------------------------------------===//
  /// Alias Queries...
  ///

  /// Alias analysis result - Either we know for sure that it does not alias, we
  /// know for sure it must alias, or we don't know anything: The two pointers
  /// _might_ alias.  This enum is designed so you can do things like:
  ///     if (AA.alias(P1, P2)) { ... }
  /// to check to see if two pointers might alias.
  ///
  /// See docs/AliasAnalysis.html for more information on the specific meanings
  /// of these values.
  ///
  enum AliasResult { NoAlias = 0, MayAlias = 1, MustAlias = 2 };

  // A version of alias that assumes instructions have been replaced by constants
  // as specified.
  virtual AliasResult aliasHypothetical(const Value *V1, unsigned V1Size,
					const Value *V2, unsigned V2Size,
					IntegrationAttempt*, bool usePBKnowledge = true);

  virtual AliasResult aliasHypothetical(ShadowValue V1, unsigned V1Size,
					ShadowValue V2, unsigned V2Size, bool usePBKnowledge = true);

  /// alias - The main low level interface to the alias analysis implementation.
  /// Returns a Result indicating whether the two pointers are aliased to each
  /// other.  This is the interface that must be implemented by specific alias
  /// analysis implementations.
  ///
  virtual AliasResult alias(const Value *V1, unsigned V1Size,
                            const Value *V2, unsigned V2Size);

  /// alias - A convenience wrapper for the case where the sizes are unknown.
  AliasResult alias(const Value *V1, const Value *V2) {
    return alias(V1, UnknownSize, V2, UnknownSize);
  }

  /// isNoAlias - A trivial helper function to check to see if the specified
  /// pointers are no-alias.
  bool isNoAlias(ShadowValue V1, unsigned V1Size, ShadowValue V2, unsigned V2Size, bool usePBKnowledge = true) {
    return aliasHypothetical(V1, V1Size, V2, V2Size, usePBKnowledge) == NoAlias;
  }

  bool isNoAlias(const Value* V1, unsigned V1Size, const Value* V2, unsigned V2Size) {
    return isNoAlias(ShadowValue(const_cast<Value*>(V1)), V1Size, ShadowValue(const_cast<Value*>(V2)), V2Size);
  }

  /// pointsToConstantMemory - If the specified pointer is known to point into
  /// constant global memory, return true.  This allows disambiguation of store
  /// instructions from constant pointers.
  ///
  virtual bool pointsToConstantMemory(const Value *P);

  //===--------------------------------------------------------------------===//
  /// Simple mod/ref information...
  ///

  /// ModRefResult - Represent the result of a mod/ref query.  Mod and Ref are
  /// bits which may be or'd together.
  ///
  enum ModRefResult { NoModRef = 0, Ref = 1, Mod = 2, ModRef = 3 };


  /// ModRefBehavior - Summary of how a function affects memory in the program.
  /// Loads from constant globals are not considered memory accesses for this
  /// interface.  Also, functions may freely modify stack space local to their
  /// invocation without having to report it through these interfaces.
  enum ModRefBehavior {
    // DoesNotAccessMemory - This function does not perform any non-local loads
    // or stores to memory.
    //
    // This property corresponds to the GCC 'const' attribute.
    DoesNotAccessMemory,

    // AccessesArguments - This function accesses function arguments in well
    // known (possibly volatile) ways, but does not access any other memory.
    AccessesArguments,

    // AccessesArgumentsAndGlobals - This function has accesses function
    // arguments and global variables well known (possibly volatile) ways, but
    // does not access any other memory.
    AccessesArgumentsAndGlobals,

    // OnlyReadsMemory - This function does not perform any non-local stores or
    // volatile loads, but may read from any memory location.
    //
    // This property corresponds to the GCC 'pure' attribute.
    OnlyReadsMemory,

    // UnknownModRefBehavior - This indicates that the function could not be
    // classified into one of the behaviors above.
    UnknownModRefBehavior
  };

  /// getModRefBehavior - Return the behavior when calling the given call site.
  virtual ModRefBehavior getModRefBehavior(ImmutableCallSite CS);

  /// getModRefBehavior - Return the behavior when calling the given function.
  /// For use when the call site is not known.
  virtual ModRefBehavior getModRefBehavior(const Function *F);

  /// getIntrinsicModRefBehavior - Return the modref behavior of the intrinsic
  /// with the given id.  Most clients won't need this, because the regular
  /// getModRefBehavior incorporates this information.
  static ModRefBehavior getIntrinsicModRefBehavior(unsigned iid);

  /// doesNotAccessMemory - If the specified call is known to never read or
  /// write memory, return true.  If the call only reads from known-constant
  /// memory, it is also legal to return true.  Calls that unwind the stack
  /// are legal for this predicate.
  ///
  /// Many optimizations (such as CSE and LICM) can be performed on such calls
  /// without worrying about aliasing properties, and many calls have this
  /// property (e.g. calls to 'sin' and 'cos').
  ///
  /// This property corresponds to the GCC 'const' attribute.
  ///
  bool doesNotAccessMemory(ImmutableCallSite CS) {
    return getModRefBehavior(CS) == DoesNotAccessMemory;
  }

  /// doesNotAccessMemory - If the specified function is known to never read or
  /// write memory, return true.  For use when the call site is not known.
  ///
  bool doesNotAccessMemory(const Function *F) {
    return getModRefBehavior(F) == DoesNotAccessMemory;
  }

  /// onlyReadsMemory - If the specified call is known to only read from
  /// non-volatile memory (or not access memory at all), return true.  Calls
  /// that unwind the stack are legal for this predicate.
  ///
  /// This property allows many common optimizations to be performed in the
  /// absence of interfering store instructions, such as CSE of strlen calls.
  ///
  /// This property corresponds to the GCC 'pure' attribute.
  ///
  bool onlyReadsMemory(ImmutableCallSite CS) {
    ModRefBehavior MRB = getModRefBehavior(CS);
    return MRB == DoesNotAccessMemory || MRB == OnlyReadsMemory;
  }

  /// onlyReadsMemory - If the specified function is known to only read from
  /// non-volatile memory (or not access memory at all), return true.  For use
  /// when the call site is not known.
  ///
  bool onlyReadsMemory(const Function *F) {
    ModRefBehavior MRB = getModRefBehavior(F);
    return MRB == DoesNotAccessMemory || MRB == OnlyReadsMemory;
  }


  /// getModRefInfo - Return information about whether or not an instruction may
  /// read or write memory specified by the pointer operand.  An instruction
  /// that doesn't read or write memory may be trivially LICM'd for example.

  /// getModRefInfo (for call sites) - Return whether information about whether
  /// a particular call site modifies or reads the memory specified by the
  /// pointer.
  ///
  virtual ModRefResult getCSModRefInfo(ShadowValue CS, ShadowValue P, unsigned Size, bool usePBKnowledge = true);

  ModRefResult getModRefInfo(ImmutableCallSite CS,
			     const Value *P, unsigned Size, 
			     bool usePBKnowledge = true) {

    return getCSModRefInfo(ShadowValue(const_cast<Instruction*>(CS.getInstruction())), ShadowValue(const_cast<Value*>(P)), Size, usePBKnowledge);

  }

  virtual ModRefResult get2CSModRefInfo(ShadowValue CS1, ShadowValue CS2, bool usePBKnowledge = true);

  /// getModRefInfo - Return information about whether two call sites may refer
  /// to the same set of memory locations.  See 
  ///   http://llvm.org/docs/AliasAnalysis.html#ModRefInfo
  /// for details.
  ModRefResult getModRefInfo(ImmutableCallSite CS1, ImmutableCallSite CS2, 
			     bool usePBKnowledge = true) {

    return get2CSModRefInfo(ShadowValue(const_cast<Instruction*>(CS1.getInstruction())), ShadowValue(const_cast<Instruction*>(CS2.getInstruction())), usePBKnowledge);

  }

public:
  /// Convenience functions...
  ModRefResult getLoadModRefInfo(ShadowValue L, ShadowValue P, unsigned Size, bool usePBKnowledge = true);
  ModRefResult getStoreModRefInfo(ShadowValue S, ShadowValue P, unsigned Size, bool usePBKnowledge = true);
  ModRefResult getVAModRefInfo(ShadowValue I, ShadowValue P, unsigned Size, bool usePBKnowledge = true);
  ModRefResult getCallModRefInfo(ShadowValue C, ShadowValue P, unsigned Size, bool usePBKnowledge = true) {
    return getCSModRefInfo(C, P, Size, usePBKnowledge);
  }
  ModRefResult getInvokeModRefInfo(ShadowValue I, ShadowValue P, unsigned Size, bool usePBKnowledge = true) {
    return getCSModRefInfo(I, P, Size, usePBKnowledge);
  }
  ModRefResult getSVModRefInfo(ShadowValue IV, ShadowValue P, unsigned Size, bool usePBKnowledge = true) {
    Instruction* I = IV.isInst() ? IV.getInst()->invar->I : cast<Instruction>(IV.getVal());
    switch (I->getOpcode()) {
    case Instruction::VAArg:  return getVAModRefInfo(IV, P, Size, usePBKnowledge);
    case Instruction::Load:   return getLoadModRefInfo(IV, P, Size, usePBKnowledge);
    case Instruction::Store:  return getStoreModRefInfo(IV, P, Size, usePBKnowledge);
    case Instruction::Call:   return getCallModRefInfo(IV, P, Size, usePBKnowledge);
    case Instruction::Invoke: return getInvokeModRefInfo(IV, P, Size, usePBKnowledge);
    default:                  return NoModRef;
    }
  }
  ModRefResult getModRefInfo(Instruction* I, const Value* P, unsigned Size) {
    return getSVModRefInfo(ShadowValue(I), ShadowValue(const_cast<Value*>(P)), Size, false);
  }

  //===--------------------------------------------------------------------===//
  /// Higher level methods for querying mod/ref information.
  ///

  /// canBasicBlockModify - Return true if it is possible for execution of the
  /// specified basic block to modify the value pointed to by Ptr.
  ///
  bool canBasicBlockModify(const BasicBlock &BB, const Value *P, unsigned Size);

  /// canInstructionRangeModify - Return true if it is possible for the
  /// execution of the specified instructions to modify the value pointed to by
  /// Ptr.  The instructions to consider are all of the instructions in the
  /// range of [I1,I2] INCLUSIVE.  I1 and I2 must be in the same basic block.
  ///
  bool canInstructionRangeModify(const Instruction &I1, const Instruction &I2,
                                 const Value *Ptr, unsigned Size);

  //===--------------------------------------------------------------------===//
  /// Methods that clients should call when they transform the program to allow
  /// alias analyses to update their internal data structures.  Note that these
  /// methods may be called on any instruction, regardless of whether or not
  /// they have pointer-analysis implications.
  ///

  /// deleteValue - This method should be called whenever an LLVM Value is
  /// deleted from the program, for example when an instruction is found to be
  /// redundant and is eliminated.
  ///
  virtual void deleteValue(Value *V);

  /// copyValue - This method should be used whenever a preexisting value in the
  /// program is copied or cloned, introducing a new value.  Note that analysis
  /// implementations should tolerate clients that use this method to introduce
  /// the same value multiple times: if the analysis already knows about a
  /// value, it should ignore the request.
  ///
  virtual void copyValue(Value *From, Value *To);

  /// replaceWithNewValue - This method is the obvious combination of the two
  /// above, and it provided as a helper to simplify client code.
  ///
  void replaceWithNewValue(Value *Old, Value *New) {
    copyValue(Old, New);
    deleteValue(Old);
  }
};

/// isNoAliasCall - Return true if this pointer is returned by a noalias
/// function.
bool isNoAliasCall(const Value *V);

/// isIdentifiedObject - Return true if this pointer refers to a distinct and
/// identifiable object.  This returns true for:
///    Global Variables and Functions (but not Global Aliases)
///    Allocas and Mallocs
///    ByVal and NoAlias Arguments
///    NoAlias returns
///
bool isIdentifiedObject(const Value *V);

} // End llvm namespace

// Because of the way .a files work, we must force the BasicAA implementation to
// be pulled in if the AliasAnalysis header is included.  Otherwise we run
// the risk of AliasAnalysis being used, but the default implementation not
// being linked into the tool that uses it.
FORCE_DEFINING_FILE_TO_BE_LINKED(AliasAnalysis)
FORCE_DEFINING_FILE_TO_BE_LINKED(BasicAliasAnalysis)

#endif
