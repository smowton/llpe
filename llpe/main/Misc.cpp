//===-- Misc.cpp ----------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// This file has really just accrued lots of unrelated families of functions,
// hence its current name. TODO: decide how to split these up in a sensible way.

#define DEBUG_TYPE "llpe-misc"

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/ConstantFolding.h"

using namespace llvm;

// A context's parent is usually unique, except when function instance sharing is enabled.

IntegrationAttempt* InlineAttempt::getUniqueParent() {

  return uniqueParent;

}

IntegrationAttempt* PeelIteration::getUniqueParent() {

  return parent;

}

Module& IntegrationAttempt::getModule() {

  return *(F.getParent());

}

// Find live return values from this function.
void InlineAttempt::getLiveReturnVals(SmallVector<ShadowValue, 4>& Vals) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(ShadowBB* BB = BBs[i]) {

      ShadowInstruction* TI = &(BB->insts.back());

      // The localStore check determines whether this block was
      // abandoned due to e.g. a call that cannot return.

      if(inst_is<ReturnInst>(TI) && BB->localStore)
	Vals.push_back(TI->getOperand(0));

    }

  }

}

// Visit live return blocks from this function.
void InlineAttempt::visitLiveReturnBlocks(ShadowBBVisitor& V) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(ShadowBB* BB = BBs[i]) {

      ShadowInstruction* TI = &(BB->insts.back());
      if(inst_is<ReturnInst>(TI))
	V.visit(BB, 0, false);

    }

  }

}

bool InlineAttempt::isRootMainCall() {

  return this == pass->getRoot();

}

// Fetch vararg idx if possible.
void InlineAttempt::getVarArg(int64_t idx, ImprovedValSet*& Result) {

  release_assert(idx >= ImprovedVal::first_any_arg && idx < ImprovedVal::max_arg);
  uint32_t argIdx = idx - ImprovedVal::first_any_arg;

  // Skip past the normal args:
  argIdx += F.arg_size();

  if(argIdx < argShadows.size())
     copyImprovedVal(ShadowValue(&argShadows[argIdx]), Result);
  else {
    
    LPDEBUG("Vararg index " << idx << ": out of bounds\n");
    Result = newOverdefIVS();

  }

}

void PeelIteration::getVarArg(int64_t idx, ImprovedValSet*& Result) {

  parent->getVarArg(idx, Result);

}

// Write debugging descriptions of specialisation contexts:
void PeelIteration::describe(raw_ostream& Stream) const {
  
  Stream << "(Loop " << getLName() << "/" << iterationCount << "/" << SeqNumber << ")";

}


void InlineAttempt::describe(raw_ostream& Stream) const {

  Stream << "(" << F.getName() << "/" << SeqNumber << ")";

}

void PeelIteration::describeBrief(raw_ostream& Stream) const {

  Stream << iterationCount;

}

void InlineAttempt::describeBrief(raw_ostream& Stream) const {

  Stream << F.getName();

}

// GDB callable:
void IntegrationAttempt::dump() const {

  describe(outs());

}

// Write descriptive headers for DOT / GUI consumption.
void InlineAttempt::printHeader(raw_ostream& OS) const {
  
  OS << (Callers.empty() ? "Root " : "") << "Function " << F.getName();
  if(isPathCondition)
    OS << " pathcond at " << Callers[0]->parent->invar->BB->getName();
  else if((!Callers.empty()) && F.getFunctionType()->getReturnType()->isVoidTy())
    OS << " at " << itcache(Callers[0], true);
  OS << " / " << SeqNumber;

}

void PeelIteration::printHeader(raw_ostream& OS) const {

  OS << "Loop " << getLName() << " iteration " << iterationCount;
  OS << " / " << SeqNumber;

}

void PeelAttempt::printHeader(raw_ostream& OS) const {
  
  OS << "Loop " << getLName();
  OS << " / " << SeqNumber;

}

std::string IntegrationAttempt::getFunctionName() {

  return F.getName();

}

// Write a full dump of this context and its children:
void PeelAttempt::print(raw_ostream& OS) const {

  OS << nestingIndent() << "Loop " << getLName() << (Iterations.back()->iterStatus == IterationStatusFinal ? "(terminated)" : "(not terminated)") << "\n";

  for(std::vector<PeelIteration*>::const_iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->print(OS);

  }

}

void IntegrationAttempt::print(raw_ostream& OS) const {

  OS << nestingIndent();
  printHeader(OS);
  OS << ": improved " << improvedInstructions << "/" << improvableInstructions << "\n";

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {
    it->second->print(OS);
  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    it->second->print(OS);
  }

}

void LLPEAnalysisPass::print(raw_ostream &OS, const Module* M) const {
  RootIA->print(OS);
}

std::string IntegrationAttempt::nestingIndent() const {
  return ind(nesting_depth * 2);
}

std::string PeelAttempt::nestingIndent() const {
  return ind(nesting_depth * 2);
}

// Debug functions:

void IntegrationAttempt::dumpMemoryUsage(int indent) {

  errs() << ind(indent);
  describeBrief(errs());

  for(IAIterator II = child_calls_begin(this), IE = child_calls_end(this); II != IE; II++) {
    II->second->dumpMemoryUsage(indent+2);
  } 
  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    PI->second->dumpMemoryUsage(indent+1);
  }

}

void PeelAttempt::dumpMemoryUsage(int indent) {

  errs() << ind(indent) << "Loop " << getLName() << " (" << Iterations.size() << " iterations)\n";
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->dumpMemoryUsage(indent+1);

}

// Brief descriptions for DOT / debug.

std::string InlineAttempt::getShortHeader() {
 
  if(isCommitted())
    return pass->shortHeaders[this];
 
  std::string ret;
  raw_string_ostream ROS(ret);
  printHeader(ROS);
  ROS.flush();
  return ret;

}

std::string PeelIteration::getShortHeader() {

  std::string ret;
  raw_string_ostream ROS(ret);
  ROS << "Iteration " << iterationCount;
  ROS.flush();
  return ret;

}

std::string PeelAttempt::getShortHeader() {

  std::string ret;
  raw_string_ostream ROS(ret);
  printHeader(ROS);
  ROS.flush();
  return ret;

}

// Build a constant from a byte array.
Constant* llvm::constFromBytes(unsigned char* Bytes, Type* Ty, const DataLayout* TD) {

  if(Ty->isVectorTy() || Ty->isFloatingPointTy() || Ty->isIntegerTy()) {

    uint64_t TyBits = TD->getTypeSizeInBits(Ty);
    uint64_t TySize = TyBits / 8;
    Constant* IntResult = intFromBytes((const uint64_t*)Bytes, (TySize + 7) / 8, TyBits, Ty->getContext());
      
    if(Ty->isIntegerTy()) {
      assert(Ty == IntResult->getType());
      return IntResult;
    }
    else {
      assert(TD->getTypeSizeInBits(IntResult->getType()) == TD->getTypeSizeInBits(Ty));
      // We know the target type does not contain non-null pointers

      Constant* Result = ConstantExpr::getBitCast(IntResult, Ty); // The bitcast might eval here
      if(ConstantExpr* CE = dyn_cast_or_null<ConstantExpr>(Result))
	Result = ConstantFoldConstant(CE, *TD);
      if(!Result) {
	LLVM_DEBUG(dbgs() << "Failed to fold casting " << *(IntResult) << " to " << *(Ty) << "\n");
	return 0;
      }
      else {
	return Result;
      }
    }
	
  }
  else if(Ty->isPointerTy()) {

    uint64_t PtrSize = TD->getTypeStoreSize(Ty);
    for(unsigned i = 0; i < PtrSize; ++i) {
      
      // Only null pointers can be synth'd from bytes
      if(Bytes[i])
	return 0;

    }

    return Constant::getNullValue(Ty);

  }
  else if(ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    if(ECount == 0) {
      LLVM_DEBUG(dbgs() << "Can't produce a constant array of 0 length\n");
      return 0;
    }

    // I *think* arrays are always dense, i.e. it's for the child type to specify padding.
    Type* EType = ATy->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;
    std::vector<Constant*> Elems;
    Elems.reserve(ECount);

    uint64_t Offset = 0;
    for(uint64_t i = 0; i < ECount; ++i, Offset += ESize) {

      Constant* NextE = constFromBytes(&(Bytes[Offset]), EType, TD);
      if(!NextE)
	return 0;
      Elems.push_back(NextE);

    }

    return ConstantArray::get(ATy, Elems);
    
  }
  else if(StructType* STy = dyn_cast<StructType>(Ty)) {

    const StructLayout* SL = TD->getStructLayout(STy);
    if(!SL) {
      LLVM_DEBUG(dbgs() << "Couldn't get struct layout for type " << *STy << "\n");
      return 0;
    }
    
    uint64_t ECount = STy->getNumElements();
    std::vector<Constant*> Elems;
    Elems.reserve(ECount);

    uint64_t EIdx = 0;
    for(StructType::element_iterator EI = STy->element_begin(), EE = STy->element_end(); EI != EE; ++EI, ++EIdx) {

      Type* EType = *EI;
      uint64_t EOffset = SL->getElementOffset(EIdx);
      Constant* NextE = constFromBytes(&(Bytes[EOffset]), EType, TD);
      if(!NextE)
	return 0;
      Elems.push_back(NextE);

    }

    return ConstantStruct::get(STy, Elems);

  }
  else {

    LLVM_DEBUG(dbgs() << "Can't build a constant containing unhandled type " << (*Ty) << "\n");
    return 0;

  }

}

Module* llvm::getGlobalModule() {

  return GlobalIHP->RootIA->F.getParent();

}

std::string PeelAttempt::getLName() const {
  return Iterations[0]->getLName();
}

std::string PeelIteration::getLName() const {
  return getBBInvar(L->headerIdx)->BB->getName();
}

bool llvm::IHPSaveDOTFiles = true;
