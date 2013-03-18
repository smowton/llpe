//===-- GlobalDCE.cpp - DCE unreachable internal functions ----------------===//
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

#define DEBUG_TYPE "globaldce"
#include "llvm/Transforms/IPO.h"
#include "llvm/Constants.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
using namespace llvm;

STATISTIC(NumAliases  , "Number of global aliases removed");
STATISTIC(NumFunctions, "Number of functions removed");
STATISTIC(NumVariables, "Number of global variables removed");

static cl::opt<bool> AssumeAsmDoesNotCall("globaldce-assume-asm-does-not-call");

namespace {
  struct GlobalDCE : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    GlobalDCE() : ModulePass(ID) {}

    // run - Do the GlobalDCE pass on the specified module, optionally updating
    // the specified callgraph to reflect the changes.
    //
    bool runOnModule(Module &M);

  private:
    SmallPtrSet<GlobalValue*, 32> AliveGlobals;
    SmallPtrSet<Function*, 32> StoredFunctions;
    bool uncertainCallFound;

    /// GlobalIsNeeded - mark the specific global value as needed, and
    /// recursively mark anything that it uses as also needed.
    bool ScanLiveGlobal(GlobalValue *GV);
    bool MarkUsedGlobals(Constant *C, bool Needed);

    bool RemoveUnusedGlobalValue(GlobalValue &GV);
  };
}

char GlobalDCE::ID = 0;
INITIALIZE_PASS(GlobalDCE, "globaldce",
                "Dead Global Elimination", false, false);

ModulePass *llvm::createGlobalDCEPass() { return new GlobalDCE(); }

static Function* cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name) {

  Function* NewF = Function::Create(F->getFunctionType(), LT, Name, F->getParent());

  Function::arg_iterator DestI = NewF->arg_begin();
  for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
       I != E; ++I, ++DestI)
    DestI->setName(I->getName());
  
  NewF->copyAttributesFrom(F);
  
  return NewF;

}

static bool alreadyStub(Function* F) {

  if(F->size() == 1 && F->begin()->size() == 1) {
    if(ReturnInst* RI = dyn_cast<ReturnInst>(F->begin()->begin())) {
      Constant* C = dyn_cast<Constant>(RI->getOperand(0));
      if(C && C->isNullValue())
	return true;
    }
  }

  return false;

}

bool GlobalDCE::runOnModule(Module &M) {

  uncertainCallFound = false;
  bool Changed = false;
  
  // Loop over the module, adding globals which are obviously necessary.
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Functions with external linkage are needed if they have a body
    if (!I->hasLocalLinkage() && !I->hasLinkOnceLinkage() &&
        !I->isDeclaration() && !I->hasAvailableExternallyLinkage())
      AliveGlobals.insert(I);
  }

  for (Module::global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Externally visible & appending globals are needed, if they have an
    // initializer.
    if (!I->hasLocalLinkage() && !I->hasLinkOnceLinkage() &&
        !I->isDeclaration() && !I->hasAvailableExternallyLinkage())
      AliveGlobals.insert(I);
  }

  for (Module::alias_iterator I = M.alias_begin(), E = M.alias_end();
       I != E; ++I) {
    Changed |= RemoveUnusedGlobalValue(*I);
    // Externally visible aliases are needed.
    if (!I->hasLocalLinkage() && !I->hasLinkOnceLinkage())
      AliveGlobals.insert(I);
  }

  bool LoopChanged = true;

  while(LoopChanged) {

    LoopChanged = false;
    
    // Not sure if SmallPtrSet iterators are invalidated by insert, so...
    std::vector<GlobalValue*> ToCheck;
    ToCheck.reserve(AliveGlobals.size());
    ToCheck.insert(ToCheck.end(), AliveGlobals.begin(), AliveGlobals.end());

    for(std::vector<GlobalValue*>::iterator it = ToCheck.begin(), itend = ToCheck.end(); it != itend; ++it) {

      LoopChanged |= ScanLiveGlobal(*it);

    }

  }

  // Now that all globals which are needed are in the AliveGlobals set, we loop
  // through the program, deleting those which are not alive.
  //

  // The first pass is to drop initializers of global variables which are dead.
  std::vector<GlobalVariable*> DeadGlobalVars;   // Keep track of dead globals
  for (Module::global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I)
    if (!AliveGlobals.count(I)) {
      DeadGlobalVars.push_back(I);         // Keep track of dead globals
      I->setInitializer(0);
    }

  // The second pass drops the bodies of functions which are dead...
  std::vector<Function*> DeadFunctions;
  SmallPtrSet<Function*, 32> IgnoreFunctions;
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I) {

    if(IgnoreFunctions.count(I))
      continue;

    if (!AliveGlobals.count(I)) {

      // Externs need to stay around even if we only use them in a non-call context.
      if(I->isDeclaration() && StoredFunctions.count(cast<Function>(I)))
	continue;

      if(alreadyStub(I))
	continue;

      DeadFunctions.push_back(I);         // Keep track of dead globals

      if (!I->isDeclaration()) {

	if(StoredFunctions.count(cast<Function>(I))) {

	  DEBUG(dbgs() << "Replace " << I->getName() << " with dummy\n");

	  // The function might be used as a token, but can't be called.
	  // Replace with a dummy:
	  Function* DummyF = cloneEmptyFunction(I, I->getLinkage(), I->getName() + ".dummy");
	  BasicBlock* DummyBB = BasicBlock::Create(I->getContext(), "dummyret", DummyF);
	  const FunctionType* DummyT = DummyF->getFunctionType();
	  if(DummyT->getReturnType()->isVoidTy())
	    ReturnInst::Create(I->getContext(), DummyBB);
	  else {
	    Constant* DummyRet = Constant::getNullValue(DummyT->getReturnType());
	    ReturnInst::Create(I->getContext(), DummyRet, DummyBB);
	  }

	  I->replaceAllUsesWith(DummyF);
	  IgnoreFunctions.insert(DummyF);

	}
	else {
	  
	  DEBUG(dbgs() << "Delete " << I->getName() << "\n");

	}

	I->deleteBody();

      }

    }

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

// G is needed -- mark any globals it may directly use as alive, and any it stores
// but does not otherwise use as stored. Return true if anything new enters either set.
bool GlobalDCE::ScanLiveGlobal(GlobalValue *G) {

  bool Changed = false;

  if (GlobalVariable *GV = dyn_cast<GlobalVariable>(G)) {
    // If this is a global variable, we must make sure to add any global values
    // referenced by the initializer to the alive set.
    // The initialisers can be regarded as stored rather than called -- a callsite
    // is needed for them ever to be used.
    if (GV->hasInitializer())
      Changed |= MarkUsedGlobals(GV->getInitializer(), false);
  } else if (GlobalAlias *GA = dyn_cast<GlobalAlias>(G)) {
    // The target of a global alias is needed.
    Changed |= MarkUsedGlobals(GA->getAliasee(), true);
  } else {
    // Otherwise this must be a function object.  We have to scan the body of
    // the function looking for constants and global values which are used as
    // operands.  Any operands of these types must be processed to ensure that
    // any globals used will be marked as needed.
    Function *F = cast<Function>(G);

    for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
      for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {

	if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

	  if(Constant* ValueC = dyn_cast<Constant>(SI->getValueOperand()))
	    Changed |= MarkUsedGlobals(ValueC, false);
	  if(Constant* PointerC = dyn_cast<Constant>(SI->getPointerOperand()))
	    Changed |= MarkUsedGlobals(PointerC, true);

	  continue;

	}
	else if(CallInst* CI = dyn_cast<CallInst>(I)) {

	  if(!CI->getCalledFunction() && !uncertainCallFound) {
	    if(!AssumeAsmDoesNotCall) {
	      Changed = true;
	      DEBUG(dbgs() << "Assuming used -> callable due to " << *CI << "\n");
	      uncertainCallFound = true;
	    }
	  }
	  // Fall through to address operands conventionally:

	}
	else if(InvokeInst* II = dyn_cast<InvokeInst>(I)) {

	  if(!II->getCalledFunction() && !uncertainCallFound) {
	    Changed = true;
	    DEBUG(dbgs() << "Assuming used -> callable due to " << *II << "\n");
	    uncertainCallFound = true;
	  }

	}

	for (User::op_iterator U = I->op_begin(), E = I->op_end(); U != E; ++U) {
	  
	  if (Constant *C = dyn_cast<Constant>(*U))
	    Changed |= MarkUsedGlobals(C, true);

	}

      }

    }

  }

  return Changed;

}

// Again return true if anything new is added.
bool GlobalDCE::MarkUsedGlobals(Constant *C, bool Needed) {

  if (GlobalValue *GV = dyn_cast<GlobalValue>(C)) {
    if(Function* F = dyn_cast<Function>(GV)) {
      if(!Needed && !uncertainCallFound)
	return StoredFunctions.insert(F);
    }
    return AliveGlobals.insert(GV);
  }

  bool Changed = false;
  
  // Loop over all of the operands of the constant, adding any globals they
  // use to the list of needed globals.
  for (User::op_iterator I = C->op_begin(), E = C->op_end(); I != E; ++I)
    if (Constant *OpC = dyn_cast<Constant>(*I))
      Changed |= MarkUsedGlobals(OpC, Needed);

  return Changed;

}

// RemoveUnusedGlobalValue - Loop over all of the uses of the specified
// GlobalValue, looking for the constant pointer ref that may be pointing to it.
// If found, check to see if the constant pointer ref is safe to destroy, and if
// so, nuke it.  This will reduce the reference count on the global value, which
// might make it deader.
//
bool GlobalDCE::RemoveUnusedGlobalValue(GlobalValue &GV) {
  if (GV.use_empty()) return false;
  GV.removeDeadConstantUsers();
  return GV.use_empty();
}
