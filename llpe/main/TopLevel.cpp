//===-- TopLevel.cpp ------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/TargetLibraryInfo.h"

#define DEBUG_TYPE "llpe-toplevel"

using namespace llvm;

// This file contains the pass' master runOnModule entry point, and specialisation context and pass
// initialisation functions.

// Initialised by the LLVM pass manager infrastructure.

char LLPEAnalysisPass::ID = 0;

static cl::opt<std::string> RootFunctionName("llpe-root", cl::init("main"));

static RegisterPass<LLPEAnalysisPass> X("llpe-analysis", "LLPE Analysis",
						 false /* Only looks at CFG */,
						 true /* Analysis Pass */);

// Constructors for the main analysis container classes:

InlineAttempt::InlineAttempt(LLPEAnalysisPass* Pass, Function& F, 
			     ShadowInstruction* _CI, int depth,
			     bool pathCond) : 
  IntegrationAttempt(Pass, F, 0, depth, 0)
{ 

  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);

  sharing = 0;
  enabled = true;
  isModel = false;
  isPathCondition = pathCond;
  hasVFSOps = false;
  registeredSharable = false;
  active = false;
  instructionsCommitted = false;
  emittedAlloca = false;
  blocksReachableOnFailure = 0;
  CommitF = 0;
  targetCallInfo = 0;
  integrationGoodnessValid = false;
  backupTlStore = 0;
  backupDSEStore = 0;
  isStackTop = false;
  DT = pass->DTs[&F];
  if(_CI) {
    Callers.push_back(_CI);
    uniqueParent = _CI->parent->IA;
  }
  else {
    uniqueParent = 0;
  }

  prepareShadows();

}

PeelIteration::PeelIteration(LLPEAnalysisPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, 
			     Function& F, int iter, int depth) :
  IntegrationAttempt(Pass, F, PP->L, depth, 0),
  iterationCount(iter),
  parentPA(PP),
  parent(P),
  iterStatus(IterationStatusUnknown)
{ 
  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);
  prepareShadows();
}

PeelAttempt::PeelAttempt(LLPEAnalysisPass* Pass, IntegrationAttempt* P, Function& _F, 
			 const ShadowLoopInvar* _L, int depth) 
  : pass(Pass), parent(P), F(_F), residualInstructions(-1), nesting_depth(depth), stack_depth(0), 
    enabled(true), L(_L), totalIntegrationGoodness(0), integrationGoodnessValid(false)
{

  SeqNumber = Pass->IAs.size();
  Pass->IAs.push_back(this);

  getOrCreateIteration(0);

}

// General destructor. Free all instruction instances etc relating to this context.

IntegrationAttempt::~IntegrationAttempt() {

  // !BBs indicates we've already been cleaned up (but not deallocated yet).
  if(!BBs)
    return;

  release_assert(pass->IAs.size() > SeqNumber);
  pass->IAs[SeqNumber] = 0;

  for(IAIterator II = child_calls_begin(this), IE = child_calls_end(this); II != IE; II++) {
    II->second->dropReferenceFrom(II->first);
  } 
  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator PI = peelChildren.begin(), PE = peelChildren.end(); PI != PE; PI++) {
    delete (PI->second);
  }

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(BBs[i]) {

      ShadowBB* BB = BBs[i];

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	if(BB->insts[j].i.PB)
	  deleteIV(BB->insts[j].i.PB);

      }

      delete BB;

    }

  }

  delete[] BBs;

}

// Also free argument-related storage.

InlineAttempt::~InlineAttempt() {
  
  if(!isUnsharable())
    pass->removeSharableFunction(this);

  for(uint32_t i = 0; i < argShadows.size(); ++i) {

    if(argShadows[i].i.PB)
      deleteIV(argShadows[i].i.PB);

  }

  delete[] &(argShadows[0]);

}

// Caller SI will no longer target this function instance. Used when function sharing
// has been used, but is no longer appropriate due to diverging circumstances.

void InlineAttempt::dropReferenceFrom(ShadowInstruction* SI) {

  if(Callers.size() == 1) {

    delete this;

  }
  else {

    SmallVector<ShadowInstruction*, 1>::iterator findit = std::find(Callers.begin(), Callers.end(), SI);
    release_assert(findit != Callers.end() && "Caller not in callers list?");
    Callers.erase(findit);

  }

}

PeelAttempt::~PeelAttempt() {

  release_assert(pass->IAs.size() > SeqNumber);
  pass->IAs[SeqNumber] = 0;

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; it++) {
    delete *it;
  }

}

// Free all memory belonging to the pass. The specialisation contexts' destructors will take care of the real work.
void LLPEAnalysisPass::releaseMemory(void) {
  if(RootIA) {
    delete RootIA;
    RootIA = 0;
  }

  std::string command;
  raw_string_ostream ROS(command);
  ROS << "rm -rf " << ihp_workdir;
  ROS.flush();
  
  if(system(command.c_str()) != 0) {

    errs() << "Warning: failed to delete " << ihp_workdir << "\n";

  }
  
}

// Run a simple possible-allocation-sites exploration of V, used in finding out whether root
// function arguments can be simply shown not to alias one another.
// seenValues is used to break loops. If a complete list of possible allocation sites can be found
// return true; otherwise return false and sites is undefined.
static bool getAllocSitesFrom(Value* V, std::vector<Value*>& sites, DenseSet<Value*>& seenValues) {

  if(!seenValues.insert(V).second)
    return true;

  if(isa<GlobalVariable>(V)) {
    
    sites.push_back(V);
    return true;

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {

    Function* F = A->getParent();
    if(F->hasAddressTaken(0)) {

      sites.clear();
      return false;

    }

    for(Value::use_iterator it = F->use_begin(), itend = F->use_end(); it != itend; ++it) {

      if(Instruction* I = dyn_cast<Instruction>(*it)) {

	CallSite CS(I);
	if(!getAllocSitesFrom(CS.getArgument(A->getArgNo()), sites, seenValues))
	  return false;
	
      }

    }

    return true;

  }
  else if(Instruction* I = dyn_cast<Instruction>(V)) {

    switch(I->getOpcode()) {

    case Instruction::Alloca:
      sites.push_back(V);
      return true;
    case Instruction::Call:
    case Instruction::Invoke:
      {
	ImmutableCallSite CS(I);
	if(CS.paramHasAttr(0, Attribute::NoAlias)) {
	  sites.push_back(V);
	  return true;
	}
	break;
      }
    case Instruction::GetElementPtr:
    case Instruction::BitCast:
      return getAllocSitesFrom(I->getOperand(0), sites, seenValues);
    case Instruction::PHI:
      {
	PHINode* PN = cast<PHINode>(I);
	for(uint32_t i = 0, ilim = PN->getNumIncomingValues(); i != ilim; ++i)
	  if(!getAllocSitesFrom(PN->getIncomingValue(i), sites, seenValues))
	    return false;
	return true;
      }
    default:
      break;
    }

    sites.clear();
    return false;

  }
  else {

    sites.clear();
    return false;

  }

}

// Find instructions that may allocate the pointer passed as argument A.
static void getAllocSites(Argument* A, std::vector<Value*>& sites) {

  DenseSet<Value*> seenValues;
  getAllocSitesFrom(A, sites, seenValues);

}

// Initialise symbolic values concerning the arguments to the specialisation root function.
// Pesimistically these could point to anything, but we might be able to show they can't alias one another
// (a la C99 restrict pointers).
void LLPEAnalysisPass::createPointerArguments(InlineAttempt* IA) {

  // Try to establish if any incoming pointer arguments are known not to alias
  // the globals, or each other. If so, allocate each a heap slot.

  std::vector<std::vector<Value*> > argAllocSites;
  
  Function::arg_iterator AI = IA->F.arg_begin(), AE = IA->F.arg_end();
  for(uint32_t i = 0; AI != AE; ++i, ++AI) {

    argAllocSites.push_back(std::vector<Value*>());

    Argument* A = &*AI;
    if(A->getType()->isPointerTy()) {

      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IA->argShadows[i].i.PB);
      if(IVS->SetType == ValSetTypeOldOverdef) {

	std::vector<Value*>& allocs = argAllocSites.back();

	if(forceNoAliasArgs.count(i)) {

	  // Not an allocation site, but doesn't matter for this purpose:
	  // This will force us to conclude the argument doesn't alias globals
	  // or any other arguments.
	  allocs.push_back(A);

	}
	else {

	  // This will leave argAllocSites empty on failure:
	  getAllocSites(A, allocs);

	}

	if(!allocs.empty()) {

	  IVS->SetType = ValSetTypePB;

	  // Create a new heap location for this argument if it has any non-global constituents.
	  // Just note any globals in the alias list.
	  bool anyNonGlobals = false;
	  for(std::vector<Value*>::iterator it = allocs.begin(), itend = allocs.end(); it != itend; ++it) {
	    
	    if(GlobalVariable* GV = dyn_cast<GlobalVariable>(*it)) {
	      
	      ShadowGV* SGV = &shadowGlobals[getShadowGlobalIndex(GV)];
	      IVS->Values.push_back(ImprovedVal(ShadowValue(SGV), 0));

	    }
	    else if(!anyNonGlobals) {

	      // Create location:
	      argStores[i] = ArgStore(heap.size());
	      heap.push_back(AllocData());
	      heap.back().allocIdx = heap.size() - 1;
	      heap.back().isCommitted = false;
	      heap.back().allocValue = ShadowValue(&IA->argShadows[i]);
	      heap.back().allocType = IA->argShadows[i].getType();
	      anyNonGlobals = true;

	    }

	  }

	}

      }

    }
    
  }

  // Now for each argument for which we found a bounded set of alloc sites,
  // give it an initial pointer set corresponding to each other arg it may alias.

  for(uint32_t i = 0, ilim = IA->F.arg_size(); i != ilim; ++i) {

    ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IA->argShadows[i].i.PB);
    std::vector<Value*>& allocs = argAllocSites[i];
    if(!allocs.empty()) {

      // Add each pointer argument location this /may/ alias:
      for(uint32_t j = 0, jlim = IA->F.arg_size(); j != jlim; ++j) {
	
	if(!argAllocSites[j].empty()) {
	  
	  std::vector<Value*>& otherallocs = argAllocSites[j];
	  for(std::vector<Value*>::iterator it = otherallocs.begin(), itend = otherallocs.end(); it != itend; ++it) {
	    
	    if(isa<GlobalVariable>(*it))
	      continue;

	    if(std::find(allocs.begin(), allocs.end(), *it) != allocs.end()) {

	      // i and j share a non-global allocation site, so arg i may alias arg j.
	      
	      IVS->Values.push_back(ImprovedVal(ShadowValue(&IA->argShadows[j]), 0));
	      break;

	    }
    
	  }

	}

      }

    }

  }

}

// Set up special heap objects that correspond to return values from particular functions.
// The function has to return the same object every time (i.e. all calls must-alias other calls).

void LLPEAnalysisPass::createSpecialLocations() {

  for(SmallDenseMap<Function*, SpecialLocationDescriptor>::iterator it = specialLocations.begin(),
	itend = specialLocations.end(); it != itend; ++it) {
    
    it->second.heapIdx = (int32_t)heap.size();
    heap.push_back(AllocData());
    heap.back().allocIdx = heap.size() - 1;
    heap.back().isCommitted = false;
    heap.back().allocValue = ShadowValue(it->first);
    heap.back().allocType = it->first->getFunctionType()->getReturnType();

  }

}

Type* llvm::GInt8Ptr;
Type* llvm::GInt8;
Type* llvm::GInt16;
Type* llvm::GInt32;
Type* llvm::GInt64;

char llvm::ihp_workdir[] = "/tmp/ihp_XXXXXX";

namespace llvm {
  size_t getStringPathConditionCount();
}

// Top-level entry point:

bool LLPEAnalysisPass::runOnModule(Module& M) {

  if(!mkdtemp(ihp_workdir)) {
    errs() << "Failed to create " << ihp_workdir << "\n";
    exit(1);
  }

  TD = &M.getDataLayout();
  GlobalTD = TD;
  GlobalTLI = &getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>()->getTLI();
  GlobalIHP = this;
  GInt8Ptr = Type::getInt8PtrTy(M.getContext());
  GInt8 = Type::getInt8Ty(M.getContext());
  GInt16 = Type::getInt16Ty(M.getContext());
  GInt32 = Type::getInt32Ty(M.getContext());
  GInt64 = Type::getInt64Ty(M.getContext());

  persistPrinter = getPersistPrinter(&M);

  initMRInfo(&M);
  
  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++) {

    if(!MI->isDeclaration()) {
      DominatorTree* NewDT = new DominatorTree();
      NewDT->recalculate(*MI);
      DTs[&*MI] = NewDT;
    }

  }

  Function* FoundF = M.getFunction(RootFunctionName);
  if((!FoundF) || FoundF->isDeclaration()) {

    errs() << "Function " << RootFunctionName << " not found or not defined in this module\n";
    return false;

  }

  Function& F = *FoundF;

  // Mark realloc as an identified object if the function is defined:
  if(Function* Realloc = M.getFunction("realloc")) {

    Realloc->setReturnDoesNotAlias();

  }

  LLVM_DEBUG(dbgs() << "Considering inlining starting at " << F.getName() << ":\n");

  std::vector<Constant*> argConstants(F.arg_size(), 0);
  uint32_t argvIdx = 0xffffffff;
  parseArgs(F, argConstants, argvIdx);

  populateGVCaches(&M);
  initSpecialFunctionsMap(M);
  // Last parameter: reserve extra GV slots for the constants that path condition parsing will produce.
  initShadowGlobals(M, getStringPathConditionCount());
  initBlacklistedFunctions(M);

  InlineAttempt* IA = new InlineAttempt(this, F, 0, 0);
  if(targetCallStack.size()) {

    IA->setTargetCall(targetCallStack[0], 0);

  }

  // Note ignored blocks and path conditions:
  parseArgsPostCreation(IA);

  // Now that all globals have grabbed heap slots, insert extra locations per special function.
  createSpecialLocations();

  argStores = new ArgStore[F.arg_size()];
  
  for(unsigned i = 0; i < F.arg_size(); ++i) {

    if(argConstants[i])
      setParam(IA, i, argConstants[i]);
    else {
      ImprovedValSetSingle* IVS = newIVS();
      IVS->SetType = ValSetTypeOldOverdef;
      IA->argShadows[i].i.PB = IVS;
    }

  }

  if(argvIdx != 0xffffffff) {

    ImprovedValSetSingle* NewIVS = newIVS();
    NewIVS->set(ImprovedVal(ShadowValue(&IA->argShadows[argvIdx]), 0), ValSetTypePB);
    IA->argShadows[argvIdx].i.PB = NewIVS;
    argStores[argvIdx] = ArgStore(heap.size());
    heap.push_back(AllocData());
    heap.back().allocIdx = heap.size() - 1;
    heap.back().isCommitted = false;
    heap.back().allocValue = ShadowValue(&IA->argShadows[argvIdx]);
    heap.back().allocType = IA->argShadows[argvIdx].getType();

  }

  createPointerArguments(IA);
  initGlobalFDStore();

  RootIA = IA;

  errs() << "Interpreting";
  IA->analyse();
  IA->finaliseAndCommit(false);
  fixNonLocalUses();
  errs() << "\n";
  
  if(IHPSaveDOTFiles) {

    // Function sharing is now decided, and hence the graph structure, so create
    // graph tags for the GUI.
    rootTag = RootIA->createTag(0);

  }
    
  return false;

}

void LLPEAnalysisPass::getAnalysisUsage(AnalysisUsage &AU) const {
  
  AU.addRequired<LoopInfoWrapperPass>();
  const PassInfo* BAAInfo = lookupPassInfo(StringRef("basicaa"));
  if(!BAAInfo) {
    errs() << "Couldn't load Basic AA!";
  }
  else {
    AU.addRequiredID(BAAInfo->getTypeInfo());
  }
  //AU.setPreservesAll();
  
}

