//===-- GlobalDCERanges.cpp - DCE unreachable internal functions ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This transform is designed to eliminate unreachable internal globals from the
// program.  It uses an aggressive algorithm, searching out globals that are
// known to be alive.  After it finds all of the globals which are needed, it
// deletes whatever is left over.  This allows it to delete recursive chunks of
// the program which are unreachable.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "globaldceranges"
#include "llvm/Transforms/IPO.h"
#include "llvm/Constants.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/Operator.h"
#include "llvm/Instructions.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/DataLayout.h"
using namespace llvm;

STATISTIC(NumAliases  , "Number of global aliases removed");
STATISTIC(NumFunctions, "Number of functions removed");
STATISTIC(NumVariables, "Number of global variables removed");

namespace {
  struct GlobalDCERanges : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    GlobalDCERanges() : ModulePass(ID), DL(0) {
      initializeGlobalDCERangesPass(*PassRegistry::getPassRegistry());
    }

    // run - Do the GlobalDCERanges pass on the specified module, optionally updating
    // the specified callgraph to reflect the changes.
    //
    bool runOnModule(Module &M);

  private:

    DataLayout* DL;

    DenseMap<GlobalValue*, std::vector<bool> > AliveGlobals;

    /// GlobalIsNeeded - mark the specific global value as needed, and
    /// recursively mark anything that it uses as also needed.
    void GlobalIsNeeded(Value* User, GlobalValue *GV, uint64_t Offset = 0, uint64_t Size = ULONG_MAX);
    void MarkUsedGlobalsAsNeeded(Value* User, Constant *C, uint64_t Offset = 0, uint64_t Size = ULONG_MAX, bool Traverse = false);
    void InstructionIsNeeded(Value* User, Instruction* I);
    void MarkValueAsNeeded(Value* User, Value* Used, uint64_t Offset, uint64_t Size, bool Traverse);
    uint64_t getGEPOffset(GEPOperator*);
    Constant* buildPartialInitializer(Constant* Old, uint64_t Offset, std::vector<bool>& Needed);
    bool AddUsedBytes(GlobalValue* G, uint64_t Offset, uint64_t Size);

    bool RemoveUnusedGlobalValue(GlobalValue &GV);
  };
}

char GlobalDCERanges::ID = 0;
INITIALIZE_PASS(GlobalDCERanges, "globaldceranges",
                "Dead Global Elimination (super)", false, false)

ModulePass *llvm::createGlobalDCERangesPass() { return new GlobalDCERanges(); }

Constant* GlobalDCERanges::buildPartialInitializer(Constant* Old, uint64_t Offset, std::vector<bool>& Needed) {

  // Return a version of Old that has nulled pointers if Needed doesn't indicate they are necessary.
  // Offset is our current working offset within Needed.

  // Is this bit completely unnecessary?
  bool needed = false;
  
  uint64_t OldSize = DL->getTypeStoreSize(Old->getType());
  for(uint64_t i = Offset, ilim = Offset + OldSize; i != ilim && !needed; ++i) {

    if(Needed[Offset])
      needed = true;

  }

  if(!needed)
    return Constant::getNullValue(Old->getType());

  // If it's a structured type, try to eliminate sub-elements...

  if(ConstantArray* CA = dyn_cast<ConstantArray>(Old)) {

    Type* EType = CA->getType()->getElementType();
    uint64_t ESize = (DL->getTypeSizeInBits(EType) + 7) / 8;

    std::vector<Constant*> Results;
    for(uint64_t i = 0, ilim = CA->getNumOperands(), ElOff = Offset; i != ilim; ++i, ElOff += ESize)
      Results.push_back(buildPartialInitializer(CA->getOperand(i), ElOff, Needed));

    return ConstantArray::get(cast<ArrayType>(CA->getType()), Results);

  }
  else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(Old)) {

    const StructLayout* SL = DL->getStructLayout(cast<StructType>(CS->getType()));
    if(!SL)
      return CS;

    StructType* STy = cast<StructType>(Old->getType());

    std::vector<Constant*> Elements;
    for(uint64_t i = 0, ilim = CS->getNumOperands(); i != ilim; ++i)
      Elements.push_back(buildPartialInitializer(CS->getOperand(i), Offset + DL->getStructLayout(STy)->getElementOffset(i), Needed));

    return ConstantStruct::get(STy, Elements);
    
  }

  // Otherwise just return it as-is.
  return Old;

}

bool GlobalDCERanges::runOnModule(Module &M) {

  bool Changed = false;
  DL = getAnalysisIfAvailable<DataLayout>();
  
  // Loop over the module, adding globals which are obviously necessary.
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Functions with external linkage are needed if they have a body
    if (!I->isDiscardableIfUnused() &&
        !I->isDeclaration() && !I->hasAvailableExternallyLinkage())
      GlobalIsNeeded(0, I);
  }

  for (Module::global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Externally visible & appending globals are needed, if they have an
    // initializer.
    if (!I->isDiscardableIfUnused() &&
        !I->isDeclaration() && !I->hasAvailableExternallyLinkage())
      GlobalIsNeeded(0, I);
  }

  for (Module::alias_iterator I = M.alias_begin(), E = M.alias_end();
       I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Externally visible aliases are needed.
    if (!I->isDiscardableIfUnused())
      GlobalIsNeeded(0, I);
  }

  // Now that all globals which are needed are in the AliveGlobals set, we loop
  // through the program, deleting those which are not alive.
  //

  // The first pass is to drop initializers of global variables which are dead.
  std::vector<GlobalVariable*> DeadGlobalVars;   // Keep track of dead globals
  for (Module::global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I) {

    DenseMap<GlobalValue*, std::vector<bool> >::iterator it = AliveGlobals.find(I);
    if(it == AliveGlobals.end()) {
      DeadGlobalVars.push_back(I);         // Keep track of dead globals
      I->setInitializer(0);
    }
    else if(it->second.size()) {

      if(I->hasInitializer()) {

	Constant* newInit = buildPartialInitializer(I->getInitializer(), 0, it->second);
	errs() << "Replacing initialiser for " << (*I) << "\n";
	errs() << "Old: " << (*I->getInitializer()) << "\n";
	errs() << "New: " << (*newInit) << "\n";
	I->setInitializer(newInit);

      }

    }

  }
  

  // The second pass drops the bodies of functions which are dead...
  std::vector<Function*> DeadFunctions;
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!AliveGlobals.count(I)) {
      DeadFunctions.push_back(I);         // Keep track of dead globals
      if (!I->isDeclaration())
        I->deleteBody();
    }

  // The third pass drops targets of aliases which are dead...
  std::vector<GlobalAlias*> DeadAliases;
  for (Module::alias_iterator I = M.alias_begin(), E = M.alias_end(); I != E;
       ++I)
    if (!AliveGlobals.count(I)) {
      DeadAliases.push_back(I);
      I->setAliasee(0);
    }

  if (!DeadFunctions.empty()) {
    // Now that all interferences have been dropped, delete the actual objects
    // themselves.
    for (unsigned i = 0, e = DeadFunctions.size(); i != e; ++i) {
      RemoveUnusedGlobalValue(*DeadFunctions[i]);
      M.getFunctionList().erase(DeadFunctions[i]);
    }
    NumFunctions += DeadFunctions.size();
    Changed = true;
  }

  if (!DeadGlobalVars.empty()) {
    for (unsigned i = 0, e = DeadGlobalVars.size(); i != e; ++i) {
      RemoveUnusedGlobalValue(*DeadGlobalVars[i]);
      M.getGlobalList().erase(DeadGlobalVars[i]);
    }
    NumVariables += DeadGlobalVars.size();
    Changed = true;
  }

  // Now delete any dead aliases.
  if (!DeadAliases.empty()) {
    for (unsigned i = 0, e = DeadAliases.size(); i != e; ++i) {
      RemoveUnusedGlobalValue(*DeadAliases[i]);
      M.getAliasList().erase(DeadAliases[i]);
    }
    NumAliases += DeadAliases.size();
    Changed = true;
  }

  // Make sure that all memory is released
  AliveGlobals.clear();

  return Changed;
}

void GlobalDCERanges::MarkValueAsNeeded(Value* User, Value* Used, uint64_t Offset, uint64_t Size, bool Traverse) {

  if(Constant* C = dyn_cast<Constant>(Used))
    MarkUsedGlobalsAsNeeded(User, C, Offset, Size, Traverse);

}

void GlobalDCERanges::InstructionIsNeeded(Value* User, Instruction* I) {

  uint64_t UseOffset = 0;
  uint64_t UseSize = ULONG_MAX;

  // Try to be finer grained than just "referring to a global means it is needed".

  if(LoadInst* LI = dyn_cast<LoadInst>(I)) {
    MarkValueAsNeeded(I->getParent()->getParent(), LI->getPointerOperand(), 0, DL->getTypeStoreSize(LI->getType()), true);
  }
  else if(StoreInst* SI = dyn_cast<StoreInst>(I)) {
    MarkValueAsNeeded(I->getParent()->getParent(), SI->getPointerOperand(), 0, DL->getTypeStoreSize(SI->getValueOperand()->getType()), true);
    MarkValueAsNeeded(I->getParent()->getParent(), SI->getValueOperand(), 0, ULONG_MAX, false);
  }
  else {
    for (User::op_iterator U = I->op_begin(), E = I->op_end(); U != E; ++U)
      MarkValueAsNeeded(User, *U, UseOffset, UseSize, true);
  }

}

bool GlobalDCERanges::AddUsedBytes(GlobalValue* G, uint64_t Offset, uint64_t Size) {
  
  std::pair<GlobalValue*, std::vector<bool> > KV(G, std::vector<bool>());

  std::pair<DenseMap<GlobalValue*, std::vector<bool> >::iterator, bool> Ins =
    AliveGlobals.insert(KV);

  if(Ins.second) {

    // Not seen this global before.
    
    if(Size != ULONG_MAX) {
      // Record seen bytes
      Ins.first->second.resize(Offset + Size, false);
      for(uint32_t i = Offset, ilim = Offset + Size; i != ilim; ++i)
	Ins.first->second[i] = true;
    }
    
    // Else empty vector signifies "all seen". Either way we've changed something.
    return true;

  }

  // All bytes referenced already used?
  if(Ins.first->second.empty())
    return false;

  // All bytes will be used?
  if(Size == ULONG_MAX) {
    Ins.first->second.clear();
    return true;
  }

  // One or more bytes not yet used?
  bool Ret = false;

  if(Offset + Size > Ins.first->second.size())
    Ins.first->second.resize(Offset + Size, false);

  for(uint32_t i = Offset, ilim = Offset + Size; i != ilim; ++i) {
    if(!Ins.first->second[i]) {
      Ins.first->second[i] = true;
      Ret = true;
    }
  }

  return Ret;

}

/// GlobalIsNeeded - the specific global value as needed, and
/// recursively mark anything that it uses as also needed.
void GlobalDCERanges::GlobalIsNeeded(Value* User, GlobalValue *G, uint64_t Offset, uint64_t Size) {

  errs() << ((User && User->hasName()) ? User->getName() : "(unknown)") << " -> " << (G->hasName() ? G->getName() : "(unknown)");
  if(Offset != 0 || Size != ULONG_MAX) {
    errs() << " (range " << Offset << "-";
    if(Size == ULONG_MAX)
      errs() << "[end]";
    else
      errs() << (Offset + Size);
    errs() << ")";
  }
  errs() << "\n";

  // If all referenced bytes have been covered then we're done.
  if(!AddUsedBytes(G, Offset, Size))
    return;

  if (GlobalVariable *GV = dyn_cast<GlobalVariable>(G)) {
    // If this is a global variable, we must make sure to add any global values
    // referenced by the initializer to the alive set.
    if (GV->hasInitializer())
      MarkUsedGlobalsAsNeeded(GV, GV->getInitializer(), Offset, Size);
  } else if (GlobalAlias *GA = dyn_cast<GlobalAlias>(G)) {
    // The target of a global alias is needed.
    MarkUsedGlobalsAsNeeded(GA, GA->getAliasee(), Offset, Size);
  } else {
    // Otherwise this must be a function object.  We have to scan the body of
    // the function looking for constants and global values which are used as
    // operands.  Any operands of these types must be processed to ensure that
    // any globals used will be marked as needed.
    Function *F = cast<Function>(G);

    for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB)
      for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I)
	InstructionIsNeeded(User, I);
  }

}

uint64_t GlobalDCERanges::getGEPOffset(GEPOperator* GEP) {

  uint64_t Offset = 0;

  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
       ++I, ++GTI) {
    ConstantInt* OpC = cast<ConstantInt>(*I);
    if (OpC->isZero()) continue;
    
    // Handle a struct and array indices which add their offset to the pointer.
    if (StructType *STy = dyn_cast<StructType>(*GTI)) {
      Offset += DL->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
    } else {
      uint64_t Size = DL->getTypeAllocSize(GTI.getIndexedType());
      Offset += OpC->getSExtValue()*Size;
    }
  }

  return Offset;

}

void GlobalDCERanges::MarkUsedGlobalsAsNeeded(Value* User, Constant *C, uint64_t Offset, uint64_t Size, bool Traverse) {
  
  // Traverse pointer, drop range constraint.
  if (GlobalValue *GV = dyn_cast<GlobalValue>(C)) {
    if(Traverse)
      GlobalIsNeeded(User, GV, Offset, Size);
    else
      GlobalIsNeeded(User, GV);
    return;
  }
  
  // Look for special cases that allow preserving an Offset / Size:
  if(Size != ULONG_MAX || Offset != 0) {

    bool doSubElements = false;
    uint64_t StartE, StartOff, EndE, EndOff;

    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {

      if(GEPOperator* GEP = dyn_cast<GEPOperator>(CE)) {

	// Bump by offset.
	uint64_t GEPOff = getGEPOffset(GEP);
	MarkUsedGlobalsAsNeeded(User, CE->getOperand(0), Offset + GEPOff, Size, Traverse);
	return;

      }
      else if(CE->getOpcode() == Instruction::BitCast) {

	MarkUsedGlobalsAsNeeded(User, CE->getOperand(0), Offset, Size, Traverse);
	return;

      }

    }
    else if(ConstantArray* CA = dyn_cast<ConstantArray>(C)) {

      Type* EType = CA->getType()->getElementType();
      uint64_t ESize = (DL->getTypeSizeInBits(EType) + 7) / 8;
    
      StartE = Offset / ESize;
      StartOff = Offset % ESize;
      if(Size == ULONG_MAX) {
	EndE = CA->getNumOperands() - 1;
	EndOff = ULONG_MAX;
      }
      else {
	EndE = (Offset + Size) / ESize;
	EndOff = (Offset + Size) % ESize;
      }
      doSubElements = true;

    }
    else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(C)) {

      if(const StructLayout* SL = DL->getStructLayout(CS->getType())) {
      
	StartE = SL->getElementContainingOffset(Offset);
	StartOff = Offset - SL->getElementOffset(StartE);
	if(Size == ULONG_MAX) {
	  EndE = CS->getNumOperands() - 1;
	  EndOff = ULONG_MAX;
	}
	else {
	  EndE = SL->getElementContainingOffset(Offset + Size);
	  EndOff = (Offset + Size) - SL->getElementOffset(EndE);      
	}
	doSubElements = true;

      }

    }

    if(doSubElements) {

      for(uint64_t El = StartE; El <= EndE; ++El) {
	
	uint64_t ElSize;
	if(El != EndE)
	  ElSize = ULONG_MAX;
	else if(EndOff == ULONG_MAX)
	  ElSize = ULONG_MAX;
	else
	  ElSize = EndOff - StartOff;
	
	if(ElSize != 0)
	  MarkUsedGlobalsAsNeeded(User, cast<Constant>(C->getOperand(El)), StartOff, ElSize);
	
	StartOff = 0;

      }

      return;

    }

  }
  
  // Otherwise, use the whole thing.
  // Loop over all of the operands of the constant, adding any globals they
  // use to the list of needed globals.
  for (User::op_iterator I = C->op_begin(), E = C->op_end(); I != E; ++I)
    if (Constant *OpC = dyn_cast<Constant>(*I))
      MarkUsedGlobalsAsNeeded(User, OpC);
}

// RemoveUnusedGlobalValue - Loop over all of the uses of the specified
// GlobalValue, looking for the constant pointer ref that may be pointing to it.
// If found, check to see if the constant pointer ref is safe to destroy, and if
// so, nuke it.  This will reduce the reference count on the global value, which
// might make it deader.
//
bool GlobalDCERanges::RemoveUnusedGlobalValue(GlobalValue &GV) {
  if (GV.use_empty()) return false;
  GV.removeDeadConstantUsers();
  return GV.use_empty();
}
