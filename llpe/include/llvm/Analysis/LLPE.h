//===-- HypotheticalConstantFolder.h --------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/IntervalMap.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/RecyclingAllocator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <limits.h>
#include <string>
#include <vector>

#define LPDEBUG(x) LLVM_DEBUG(do { printDebugHeader(dbgs()); dbgs() << ": " << x; } while(0))

namespace llvm {

class AAResults;
class PHINode;
class NonLocalDepResult;
class LoadInst;
class raw_ostream;
class ConstantInt;
class Type;
class Argument;
class InvokeInst;
class StoreInst;
class MemTransferInst;
class MemIntrinsic;
class CmpInst;
class InlineAttempt;
class PeelAttempt;
class LLPEAnalysisPass;
class Function;
class DataLayout;
class Loop;
class LoopInfo;
class IntegrationAttempt;
class PtrToIntInst;
class IntToPtrInst;
class BinaryOperator;
class DominatorTree;
template<class, bool> class DominatorTreeBase;
template<class> class DomTreeNodeBase;
class IAWalker;
class BackwardIAWalker;
class ForwardIAWalker;
class raw_string_ostream;
class MemSetInst;
class MemTransferInst;
class ShadowLoopInvar;
class TargetLibraryInfo;
class ShadowBB;
class TrackedStore;

#ifndef LLVM_EFFICIENT_PRINTING
class PersistPrinter { };
#else
class PersistPrinter; // Opaque here, defined in AsmWriter
#endif

inline void release_assert_fail(const char* str) {

  errs() << "Assertion failed: " << str << "\n";
  abort();

}

#define release_assert(x) if(!(x)) { release_assert_fail(#x); }

extern const DataLayout* GlobalTD;
extern AAResults* GlobalAA;
extern TargetLibraryInfo* GlobalTLI;
extern LLPEAnalysisPass* GlobalIHP;

struct ShadowBBVisitor {

  bool doIgnoreEdges;
ShadowBBVisitor(bool ign = false) : doIgnoreEdges(ign) { }

  virtual void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) = 0;
  virtual void enterLoop(PeelAttempt*, void*) { }
  virtual void hitIgnoredEdge() { }

};

// Include structures and functions for working with instruction and argument shadows.
#include "ShadowInlines.h"

class VFSCallModRef;

enum IntegratorType {

  IntegratorTypeIA,
  IntegratorTypePA

};

struct IntegratorTag {

  IntegratorType type;
  void* ptr;
  IntegratorTag* parent;
  std::vector<IntegratorTag*> children;

};

enum PathConditionTypes {
  
  PathConditionTypeInt,
  PathConditionTypeFptr,
  PathConditionTypeString,
  PathConditionTypeIntmem,
  PathConditionTypeFptrmem,
  PathConditionTypeStream,
  PathConditionTypeGlobalInit

};

struct PathCondition {

  uint32_t instStackIdx;
  BasicBlock* instBB;
  uint32_t instIdx;
  uint32_t fromStackIdx;
  BasicBlock* fromBB;
  union {
    Constant* val;
    const char* filename;
  } u;
  uint64_t offset;

PathCondition(uint32_t isi, BasicBlock* ibi, uint32_t ii, uint32_t fsi, BasicBlock* fbi, Constant* v, uint64_t off) :
    instStackIdx(isi), instBB(ibi), instIdx(ii), 
    fromStackIdx(fsi), fromBB(fbi), offset(off) {

      u.val = v;
      
    }

};

struct PathFuncArg {

  uint32_t stackIdx;
  BasicBlock* instBB;
  uint32_t instIdx;

PathFuncArg(uint32_t s, BasicBlock* b, uint32_t i) : stackIdx(s), instBB(b), instIdx(i) {}

};

struct PathFunc {

  uint32_t stackIdx;
  BasicBlock* BB;
  Function* F;
  Function* VerifyF;
  InlineAttempt* IA;
  SmallVector<PathFuncArg, 1> args;

PathFunc(uint32_t f, BasicBlock* _BB, Function* _F, Function* _VF) : stackIdx(f), BB(_BB), F(_F), VerifyF(_VF), IA(0) {}

};

struct SpecialLocationDescriptor {

  uint64_t storeSize;
  LocStore store;
  uint32_t heapIdx;

};

struct PathConditions {

  std::vector<PathCondition> IntPathConditions;
  std::vector<PathCondition> AsDefIntPathConditions;
  std::vector<PathCondition> StringPathConditions;
  std::vector<PathCondition> IntmemPathConditions;
  std::vector<PathCondition> StreamPathConditions;
  std::vector<PathFunc> FuncPathConditions;

  void addForType(PathCondition newCond, PathConditionTypes Ty) {

    switch(Ty) {
    case PathConditionTypeFptr:
    case PathConditionTypeInt:
      {
	if(newCond.instStackIdx == newCond.fromStackIdx &&
	   newCond.instBB == newCond.fromBB) {
	  AsDefIntPathConditions.push_back(newCond);
	}
	else {
	  IntPathConditions.push_back(newCond); 
	}
	break;
      }
    case PathConditionTypeIntmem:
    case PathConditionTypeFptrmem:
    case PathConditionTypeGlobalInit:
      IntmemPathConditions.push_back(newCond); break;
    case PathConditionTypeString:
      StringPathConditions.push_back(newCond); break;
    case PathConditionTypeStream:
      StreamPathConditions.push_back(newCond); break;
    }

  }

};

struct AllocatorFn {

  bool isConstantSize;
  union {
    uint32_t sizeArg;
    ConstantInt* allocSize;
  };
  
AllocatorFn() : isConstantSize(false), allocSize(0) {}
AllocatorFn(uint32_t S) : isConstantSize(false), sizeArg(S) {}
AllocatorFn(ConstantInt* C) : isConstantSize(true), allocSize(C) {}

  static AllocatorFn getConstantSize(ConstantInt* size) {
    return AllocatorFn(size);
  }
  static AllocatorFn getVariableSize(uint32_t arg) {
    return AllocatorFn(arg);
  }

};

struct DeallocatorFn {

  uint32_t arg;

DeallocatorFn() : arg(UINT_MAX) {}
DeallocatorFn(uint32_t a) : arg(a) {}

};

struct ReallocatorFn {

  uint32_t ptrArg;
  uint32_t sizeArg;
  
ReallocatorFn() : ptrArg(UINT_MAX), sizeArg(UINT_MAX) {}
ReallocatorFn(uint32_t pa, uint32_t sa) : ptrArg(pa), sizeArg(sa) {}

};

struct IHPLocationInfo {
  
  void (*getLocation)(ShadowValue CS, ShadowValue& Loc, uint64_t& LocSize);
  uint64_t argIndex;
  uint64_t argSize;

};

struct IHPLocationMRInfo {

  IHPLocationInfo* Location;

};

struct IHPFunctionInfo {

  const char* Name;
  bool NoModRef;
  const IHPLocationMRInfo *LocationDetails;
  const IHPLocationMRInfo* (*getLocationDetailsFor)(ShadowValue);

};

struct OpenStatus {

  std::string Name;
  bool success;

OpenStatus(std::string N, bool Success) : Name(N), success(Success) { }
OpenStatus() : Name(""), success(false) {}

};

struct ReadFile {

  std::string name;
  uint64_t incomingOffset;
  uint32_t readSize;
  bool needsSeek;
  bool isFifo;

ReadFile(std::string n, uint64_t IO, uint32_t RS, bool _isFifo) : name(n), incomingOffset(IO), readSize(RS), needsSeek(true), isFifo(_isFifo) { }

ReadFile() : name(), incomingOffset(0), readSize(0), needsSeek(true) { }

};

struct SeekFile {

  std::string name;
  uint64_t newOffset;
  bool MayDelete;

SeekFile(std::string n, uint64_t Off) : name(n), newOffset(Off), MayDelete(false) { }
SeekFile() : name(), newOffset(0), MayDelete(false) { }

};

struct GlobalStats {
  
  uint32_t dynamicFunctions;
  uint32_t dynamicContexts;
  uint32_t dynamicBlocks;
  uint32_t dynamicInsts;

  uint32_t disabledContexts;

  uint32_t resolvedBranches;
  uint32_t constantInstructions;
  uint32_t pointerInstructions;
  uint32_t setInstructions;
  uint32_t unknownInstructions;
  uint32_t deadInstructions;

  uint32_t residualBlocks;
  uint32_t residualInstructions;
  uint32_t mallocChecks;
  uint32_t fileChecks;
  uint32_t threadChecks;
  uint32_t condChecks;

GlobalStats() : dynamicFunctions(0), dynamicContexts(0), dynamicBlocks(0), dynamicInsts(0),
    disabledContexts(0), resolvedBranches(0), constantInstructions(0), pointerInstructions(0),
    setInstructions(0), unknownInstructions(0), deadInstructions(0), residualBlocks(0),
    residualInstructions(0), mallocChecks(0), fileChecks(0), threadChecks(0), condChecks(0) {}

  void print(raw_ostream& Out) {

    Out << "Dynamic functions: " << dynamicFunctions << "\n";
    Out << "Dynamic contexts: " << dynamicContexts << "\n";
    Out << "Dynamic blocks: " << dynamicBlocks << "\n";
    Out << "Dynamic instructions: " << dynamicInsts << "\n";
    Out << "Disabled contexts: " << disabledContexts << "\n";
    Out << "Resolved branches: " << resolvedBranches << "\n";
    Out << "Constant instructions: " << constantInstructions << "\n";
    Out << "Pointer instructions: " << pointerInstructions << "\n";
    Out << "Set instructions: " << setInstructions << "\n";
    Out << "Unknown instructions: " << unknownInstructions << "\n";
    Out << "Dead instructions: " << deadInstructions << "\n";
    Out << "Residual blocks: " << residualBlocks << "\n";
    Out << "Residual instructons: " << residualInstructions << "\n";
    Out << "Malloc checks: " << mallocChecks << "\n";
    Out << "File checks: " << fileChecks << "\n";
    Out << "Thread checks: " << threadChecks << "\n";
    Out << "Cond checks: " << condChecks << "\n";

  }

};

struct ArgStore {

  uint32_t heapIdx;
  std::vector<std::pair<WeakVH, uint32_t> > PatchRefs;

ArgStore() : heapIdx(0) {}
ArgStore(uint32_t hi) : heapIdx(hi) {}

};

class LLPEAnalysisPass : public ModulePass {

 public:

   DenseMap<Function*, ShadowFunctionInvar*> functionInfo;

   SmallSet<Function*, 4> alwaysInline;
   SmallSet<Function*, 4> alwaysExplore;
   DenseMap<std::pair<Function*, BasicBlock*>, BasicBlock* > optimisticLoopMap;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > alwaysIterLoops;
   DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1 > > assumeEdges;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoops;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoopsWithChildren;
   DenseMap<std::pair<Function*, BasicBlock*>, uint64_t> maxLoopIters;
   DenseSet<Instruction*> simpleVolatileLoads;
   
   DenseMap<ShadowInstruction*, std::string> optimisticForwardStatus;

   const DataLayout* TD;
   AAResults* AA;

   InlineAttempt* RootIA;

   DenseMap<const GlobalVariable*, std::string> GVCache;
   DenseMap<const GlobalVariable*, std::string> GVCacheBrief;

   DenseMap<const Function*, DenseMap<const Value*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Value*, std::string>* > briefFunctionTextCache;

   DenseMap<GlobalVariable*, uint64_t> shadowGlobalsIdx;

   DenseMap<Function*, IHPFunctionInfo> functionMRInfo;

   bool cacheDisabled;

   unsigned mallocAlignment;

   std::vector<IntegratorTag> tags;
   IntegratorTag* rootTag;

   // Pass identifier
   static char ID;

   DenseMap<Function*, DominatorTree*> DTs;

   ImprovedValSetMulti::MapTy::Allocator IMapAllocator;

   SmallPtrSet<Function*, 8> blacklistedFunctions;
   void initBlacklistedFunctions(Module&);

   SmallPtrSet<Function*, 8> splitFunctions;

   DenseMap<Function*, std::vector<InlineAttempt*> > IAsByFunction;

   PathConditions pathConditions;

   SmallDenseMap<Function*, SpecialLocationDescriptor> specialLocations;
   SmallDenseMap<Function*, AllocatorFn, 4> allocatorFunctions;
   SmallDenseMap<Function*, DeallocatorFn, 4> deallocatorFunctions;
   SmallDenseMap<Function*, ReallocatorFn, 4> reallocatorFunctions;
   SmallDenseMap<Function*, Function*> modelFunctions;
   SmallPtrSet<Function*, 4> yieldFunctions;

   ArgStore* argStores;

   std::vector<std::pair<BasicBlock*, uint32_t> > targetCallStack;
   std::vector<InlineAttempt*> targetCallStackIAs;

   SmallSet<uint32_t, 4> forceNoAliasArgs;

   SmallVector<Function*, 4> commitFunctions;

   SmallDenseMap<CallInst*, std::vector<GlobalVariable*>, 4> lockDomains;
   SmallSet<CallInst*, 4> pessimisticLocks;

   // Of an allocation or FD, record instructions that may use it in the emitted program.
   DenseMap<ShadowValue, std::vector<std::pair<ShadowValue, uint32_t> > > indirectDIEUsers;
   // Of a successful copy instruction, records the values read.
   DenseMap<ShadowInstruction*, SmallVector<IVSRange, 4> > memcpyValues;

   DenseMap<ShadowInstruction*, OpenStatus*> forwardableOpenCalls;
   DenseMap<ShadowInstruction*, ReadFile> resolvedReadCalls;
   DenseMap<ShadowInstruction*, SeekFile> resolvedSeekCalls;

   void addSharableFunction(InlineAttempt*);
   void removeSharableFunction(InlineAttempt*);
   InlineAttempt* findIAMatching(ShadowInstruction*);

   ShadowGV* shadowGlobals;

   std::vector<AllocData> heap;
   std::vector<FDGlobalState> fds;

   RecyclingAllocator<BumpPtrAllocator, ImprovedValSetSingle> IVSAllocator;

   bool verboseOverdef;
   bool enableSharing;
   bool verboseSharing;
   bool verbosePCs;
   bool useGlobalInitialisers;

   Function* llioPreludeFn;
   int llioPreludeStackIdx;
   std::string llioConfigFile;
   std::vector<std::string> llioDependentFiles;

   DenseSet<ShadowInstruction*> barrierInstructions;

   bool programSingleThreaded;
   bool omitChecks;
   bool omitMallocChecks;

   DenseSet<std::pair<IntegrationAttempt*, const ShadowLoopInvar*> > latchStoresRetained;

   GlobalStats stats;

   DenseMap<IntegrationAttempt*, std::string> shortHeaders;
   DenseMap<ShadowInstruction*, TrackedStore*> trackedStores;
   DenseMap<ShadowInstruction*, TrackedAlloc*> trackedAllocs;
   DenseMap<Value*, uint32_t> committedHeapAllocations;
   DenseMap<Value*, uint32_t> committedFDs;

   std::vector<void*> IAs;

   PersistPrinter* persistPrinter;

   bool emitFakeDebug;
   DenseMap<Function*, DebugLoc> fakeDebugLocs;
   DISubroutineType* fakeDebugType;

   std::string statsFile;
   unsigned maxContexts;

   explicit LLPEAnalysisPass() : ModulePass(ID), cacheDisabled(false) { 

     mallocAlignment = 0;

   }

   bool runOnModule(Module& Ms);

   void print(raw_ostream &OS, const Module* M) const;

   void releaseMemory(void);

   // Caching text representations of instructions:

   DenseMap<const Value*, std::string>& getFunctionCache(const Function* F, bool brief);
   DenseMap<const GlobalVariable*, std::string>& getGVCache(bool brief);
   void populateGVCaches(const Module*);
   virtual void printValue(raw_ostream& ROS, const Value* V, bool brief);
   virtual void printValue(raw_ostream& ROS, ShadowValue V, bool brief);
   void disableValueCache();

   Constant* loadEnvironment(Module&, std::string&);
   void loadArgv(Function*, std::string&, unsigned argvidx, unsigned& argc);
   void setParam(InlineAttempt* IA, long Idx, Constant* Val);
   void parseArgs(Function& F, std::vector<Constant*>&, uint32_t& argvIdx);
   void parseArgsPostCreation(InlineAttempt* IA);
   void parsePathConditions(cl::list<std::string>& L, PathConditionTypes Ty, InlineAttempt* IA);
   void createSpecialLocations();
   void createPointerArguments(InlineAttempt*);

   virtual void getAnalysisUsage(AnalysisUsage &AU) const;

   bool shouldAlwaysInline(Function* F) {
     return alwaysInline.count(F);
   }

   bool shouldAlwaysExplore(Function* F) {
     return alwaysExplore.count(F);
   }
   
   BasicBlock* getOptimisticEdge(Function* F, BasicBlock* HBB) {
     return optimisticLoopMap.lookup(std::make_pair(F, HBB));
   }

   bool shouldAlwaysIterate(Function* F, BasicBlock* HBB) {
     DenseMap<Function*, SmallSet<BasicBlock*, 1> >::iterator it = alwaysIterLoops.find(F);
     return it != alwaysIterLoops.end() && it->second.count(HBB);
   }
   
   bool shouldAssumeEdge(Function* F, BasicBlock* BB1, BasicBlock* BB2) {
     DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1> >::iterator it = assumeEdges.find(F);
     if(it == assumeEdges.end())
       return false;
     return it->second.count(std::make_pair(BB1, BB2));
   }

   bool shouldIgnoreLoop(Function* F, BasicBlock* HBB) {
     DenseMap<Function*, SmallSet<BasicBlock*, 1> >::iterator it = ignoreLoops.find(F);
     return it != ignoreLoops.end() && it->second.count(HBB);
   }

   bool shouldIgnoreLoopChildren(Function* F, BasicBlock* HBB) {
     DenseMap<Function*, SmallSet<BasicBlock*, 1> >::iterator it = ignoreLoopsWithChildren.find(F);
     return it != ignoreLoopsWithChildren.end() && it->second.count(HBB);
   }

   bool assumeEndsAfter(Function* F, BasicBlock* HBB, uint64_t C) {
     DenseMap<std::pair<Function*, BasicBlock*>, uint64_t>::iterator it = maxLoopIters.find(std::make_pair(F, HBB));
     if(it == maxLoopIters.end())
       return false;
     return it->second == C;
   }

   bool atomicOpIsSimple(Instruction* LI) {

     return programSingleThreaded || simpleVolatileLoads.count(LI);

   }

   unsigned getMallocAlignment();

   ShadowFunctionInvar* getFunctionInvarInfo(Function& F);
   ShadowLoopInvar* getLoopInfo(ShadowFunctionInvar* FInfo,
				DenseMap<BasicBlock*, uint32_t>& BBIndices, 
				const Loop* L,
				DominatorTree*,
				ShadowLoopInvar* Parent);

   void initShadowGlobals(Module&, uint32_t extraSlots);
   uint64_t getShadowGlobalIndex(GlobalVariable* GV) {
     return shadowGlobalsIdx[GV];
   }

   InlineAttempt* getRoot() { return RootIA; }
   IntegratorTag* getRootTag() { return rootTag; }
   void commit();

   IntegratorTag* newTag() {
     
     return new IntegratorTag();

   }

   uint32_t countPathConditionsAtBlockStart(ShadowBBInvar* BB, IntegrationAttempt* IA);
   BasicBlock* parsePCBlock(Function* fStack, std::string& bbName);
   int64_t parsePCInst(BasicBlock* bb, Module* M, std::string& instIndexStr);
   void writeLliowdConfig();

   void initMRInfo(Module*);
   IHPFunctionInfo* getMRInfo(Function*);

   void postCommitStats();

   void fixNonLocalUses();
   void initGlobalFDStore();

   const ShadowLoopInvar* applyIgnoreLoops(const ShadowLoopInvar*, Function*, ShadowFunctionInvar*);

};

// Define a wrapper class for using the IHP's instruction text cache when printing instructions:
template<class T> class PrintCacheWrapper {

  LLPEAnalysisPass& IHP;
  T Val;
  bool brief;

 public:
 
 PrintCacheWrapper(LLPEAnalysisPass& _IHP, T _Val, bool _brief) : IHP(_IHP), Val(_Val), brief(_brief) { }
  void printTo(raw_ostream& ROS) {

    IHP.printValue(ROS, Val, brief);
    
  }

 };

 // Caching instruction text for debug and DOT export:
inline PrintCacheWrapper<const Value*> itcache(const Value& V, bool brief = false) {
  return PrintCacheWrapper<const Value*>(*GlobalIHP, &V, brief);
}
inline PrintCacheWrapper<ShadowValue> itcache(ShadowValue V, bool brief = false) {
  return PrintCacheWrapper<ShadowValue>(*GlobalIHP, V, brief);
}
inline PrintCacheWrapper<ShadowValue> itcache(ShadowInstruction* SI, bool brief = false) {
  return itcache(ShadowValue(SI), brief);
}
inline PrintCacheWrapper<ShadowValue> itcache(ShadowArg* SA, bool brief = false) {
  return itcache(ShadowValue(SA), brief);
}

template<class T> raw_ostream& operator<<(raw_ostream& ROS, PrintCacheWrapper<T> Wrapper) {
  Wrapper.printTo(ROS);
  return ROS;
}

inline void printSV(raw_ostream& RSO, ShadowValue V) {
  RSO << itcache(V);
}

inline ImprovedValSetSingle* newIVS() {

  return new (GlobalIHP->IVSAllocator.Allocate()) ImprovedValSetSingle();

}

inline ImprovedValSetSingle* newOverdefIVS() {

  return new (GlobalIHP->IVSAllocator.Allocate()) ImprovedValSetSingle(ValSetTypeUnknown, true);

}

inline void deleteIVS(ImprovedValSetSingle* I) {

  I->~ImprovedValSetSingle();
  GlobalIHP->IVSAllocator.Deallocate(I);

}

inline void deleteIV(ImprovedValSet* I) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(I))
    deleteIVS(IVS);
  else
    delete cast<ImprovedValSetMulti>(I);
  
}

inline ImprovedValSetSingle* copyIVS(const ImprovedValSetSingle* IVS) {

  return new (GlobalIHP->IVSAllocator.Allocate()) ImprovedValSetSingle(*IVS);  

}

inline ImprovedValSet* copyIV(const ImprovedValSet* IV) {

  if(const ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV))
    return copyIVS(IVS);
  else
    return new ImprovedValSetMulti(*cast<ImprovedValSetMulti>(IV));

}

inline bool copyImprovedVal(ShadowValue V, ImprovedValSet*& OutPB) {

  switch(V.t) {

  case SHADOWVAL_INST:
    OutPB = copyIV(V.u.I->i.PB);
    return IVIsInitialised(OutPB);

  case SHADOWVAL_ARG:
    OutPB = copyIV(V.u.A->i.PB);
    return IVIsInitialised(OutPB);

  case SHADOWVAL_GV:
    {
      ImprovedValSetSingle* NewIVS = newIVS();
      OutPB = NewIVS;
      NewIVS->set(ImprovedVal(V, 0), ValSetTypePB);
      return true;
    }

  case SHADOWVAL_OTHER:
    {
      std::pair<ValSetType, ImprovedVal> VPB = getValPB(V.getVal());
      if(VPB.first == ValSetTypeUnknown)
	return false;
      ImprovedValSetSingle* NewIVS = newIVS();
      OutPB = NewIVS;
      NewIVS->set(VPB.second, VPB.first);
      return true;
    }

  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    {
      ImprovedValSetSingle* NewIVS = newIVS();
      OutPB = NewIVS;
      NewIVS->set(ImprovedVal(V), ValSetTypeScalar);    
      return true;
    }

  case SHADOWVAL_INVAL:
  default:
    release_assert(0 && "getImprovedValSetSingle on uninit value");
    llvm_unreachable("getImprovedValSetSingle on uninit value");

  }

}

raw_ostream& operator<<(raw_ostream&, const IntegrationAttempt&);

// PartialVal: a byte array with support functions for turning it into a Constant. 
struct PartialVal {

  uint64_t* partialBuf;
  bool* partialValidBuf;
  uint64_t partialBufBytes;
  bool loadFinished;

  bool addPartialVal(PartialVal& PV, const DataLayout* TD, std::string* error);
  bool isComplete();
  void combineWith(uint8_t* Other, uint64_t FirstDef, uint64_t FirstNotDef);
  void combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef);
  bool combineWith(Constant* C, uint64_t ConstOffset, uint64_t FirstDef, uint64_t FirstNotDef, std::string* error);
  
  PartialVal(uint64_t nBytes);
  PartialVal(const PartialVal& Other);
  PartialVal& operator=(const PartialVal& Other);
  ~PartialVal();

};

class UnaryPred {
 public:
  virtual bool operator()(Value*) = 0;

};

class OpCallback {
 public:
  virtual void callback(IntegrationAttempt* Ctx, Value* V) = 0;

};

class DIVisitor;

inline bool operator==(const ImprovedValSetSingle& PB1, const ImprovedValSetSingle& PB2) {

  if(PB1.SetType != PB2.SetType)
    return false;

  if(PB1.Overdef != PB2.Overdef)
    return false;

  if(PB1.Overdef)
    return true;

  if(PB1.Values.size() != PB2.Values.size())
    return false;

  // These are sets, so changing the order like this is acceptable
  ImprovedValSetSingle* MPB1 = const_cast<ImprovedValSetSingle*>(&PB1);
  ImprovedValSetSingle* MPB2 = const_cast<ImprovedValSetSingle*>(&PB2);

  std::sort(MPB1->Values.begin(), MPB1->Values.end());
  std::sort(MPB2->Values.begin(), MPB2->Values.end());

  for(unsigned i = 0; i < PB1.Values.size(); ++i)
    if(PB1.Values[i] != PB2.Values[i])
      return false;

  return true;

}

bool operator==(const ImprovedValSetMulti& PB1, const ImprovedValSetMulti& PB2);

inline bool operator!=(const ImprovedValSetSingle& PB1, const ImprovedValSetSingle& PB2) {

  return !(PB1 == PB2);

}

inline bool IVsEqualShallow(ImprovedValSet* IV1, ImprovedValSet* IV2) {

  if(IV1 == IV2)
    return true;

  if(IV1->isMulti != IV2->isMulti)
    return false;

  if(!IV1->isMulti)
    return (*(cast<ImprovedValSetSingle>(IV1))) == (*(cast<ImprovedValSetSingle>(IV2)));
  else
    return (*(cast<ImprovedValSetMulti>(IV1))) == (*(cast<ImprovedValSetMulti>(IV2)));    

}

enum IterationStatus {

  IterationStatusUnknown,
  IterationStatusFinal,
  IterationStatusNonFinal

};

enum WalkInstructionResult {

  WIRContinue,
  WIRStopThisPath,
  WIRStopWholeWalk

};

enum MultiCmpResult {

  MCRTRUE,
  MCRFALSE,
  MCRMAYBE

};

class IAWalker {

 public:

  typedef std::pair<uint32_t, ShadowBB*> WLItem;

 protected:
  WLItem makeWL(uint32_t x, ShadowBB* y) { return std::make_pair(x, y); }

  DenseSet<WLItem> Visited;
  SmallVector<std::pair<WLItem, void*>, 8> Worklist1;
  SmallVector<std::pair<WLItem, void*>, 8> Worklist2;

  SmallVector<std::pair<WLItem, void*>, 8>* PList;
  SmallVector<std::pair<WLItem, void*>, 8>* CList;

  SmallVector<void*, 4> Contexts;
  
  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void* Context) = 0;
  virtual bool shouldEnterCall(ShadowInstruction*, void*) = 0;
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*) = 0;
  virtual WalkInstructionResult walkFromBlock(ShadowBB*, void* Context) {
    return WIRContinue;
  }

  virtual void freeContext(void*) { }
  virtual void* copyContext(void* x) {
    return 0;
  }
  virtual void walkInternal() = 0;

  void* initialContext;

 public:

  bool doIgnoreEdges;

 IAWalker(void* IC = 0, bool ign = false) : PList(&Worklist1), CList(&Worklist2), initialContext(IC), doIgnoreEdges(ign) {
    
    Contexts.push_back(initialContext);

 }

  void walk();
  void queueWalkFrom(uint32_t idx, ShadowBB*, void* context, bool copyContext);

  virtual void enterCall(InlineAttempt* IA, void* Ctx) {}
  virtual void leaveCall(InlineAttempt* IA, void* Ctx) {}
  virtual void enterLoop(PeelAttempt*, void* Ctx) {}
  virtual void leaveLoop(PeelAttempt*, void* Ctx) {}

};

class BackwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(uint32_t, ShadowBB*, void* Ctx, ShadowInstruction*& StoppedCI);
  virtual void walkInternal();

 public:

  virtual WalkInstructionResult reachedTop() { return WIRStopThisPath; }
  virtual WalkInstructionResult mayAscendFromContext(IntegrationAttempt*, void* Ctx) { return WIRContinue; }

  BackwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0, DenseSet<WLItem>* AlreadyVisited = 0, bool ign = false);
  
};

class ForwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(uint32_t, ShadowBB*, void* Ctx, ShadowInstruction*& StoppedCI);
  virtual void walkInternal();
  
 public:

  virtual void hitIgnoredEdge() {}
  virtual bool shouldContinue() { return true; }
  ForwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0, bool ign = false);
  
};

enum BarrierState {

  BARRIER_NONE,
  BARRIER_HERE,
  BARRIER_CHILD

};

enum CommitState {

  COMMIT_NOT_STARTED,
  COMMIT_STARTED,
  COMMIT_DONE,
  COMMIT_FREED

};

class IntegrationAttempt {

protected:

  int improvableInstructions;
  int improvableInstructionsIncludingLoops;
  int improvedInstructions;
  int64_t residualInstructions;

  std::string nestingIndent() const;

 public:

  int nesting_depth;
  int stack_depth;

  LLPEAnalysisPass* pass;

  uint64_t SeqNumber;

  Function& F;
  const ShadowLoopInvar* L;

  ShadowBB** BBs;
  uint32_t nBBs;
  // BBsOffset: offset from indices in the BBs array to invarInfo.BBs.
  // For inlineAttempts this is 0; for loop iterations it is the index of the loop's header
  // within the invar info.
  uint32_t BBsOffset;

  ShadowFunctionInvar* invarInfo;

  int64_t totalIntegrationGoodness;
  bool integrationGoodnessValid;
  uint64_t residualInstructionsHere;

  DenseMap<const ShadowLoopInvar*, PeelAttempt*> peelChildren;

  uint32_t pendingEdges;

  BarrierState barrierState;

  bool tentativeLoadsRun;
  bool readsTentativeData;
  bool containsCheckedReads;

  uint32_t checkedInstructionsHere;
  uint32_t checkedInstructionsChildren;

  BarrierState yieldState;
  CommitState commitState;

  bool mayUnwind;

 IntegrationAttempt(LLPEAnalysisPass* Pass, Function& _F, 
		    const ShadowLoopInvar* _L, int depth, int sdepth) : 
    improvableInstructions(0),
    improvedInstructions(0),
    residualInstructions(-1),
    nesting_depth(depth),
    stack_depth(sdepth),
    pass(Pass),
    F(_F),
    L(_L),
    totalIntegrationGoodness(0),
    integrationGoodnessValid(false),
    peelChildren(1),
    pendingEdges(0),
    barrierState(BARRIER_NONE),
    tentativeLoadsRun(false),
    readsTentativeData(false),
    containsCheckedReads(false),
    checkedInstructionsHere(0),
    checkedInstructionsChildren(0),
    yieldState(BARRIER_NONE),
    commitState(COMMIT_NOT_STARTED),
    mayUnwind(false)  
      { 
      }

  virtual ~IntegrationAttempt();

  Module& getModule();

  Function& getFunction() { return F; }
  
  // virtual for external access:
  virtual bool edgeIsDead(ShadowBBInvar* BB1I, ShadowBBInvar* BB2I);
  bool edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I, bool ignoreThisScope = false);
  bool blockIsDeadRising(ShadowBBInvar& BBI);

  virtual bool entryBlockIsCertain() = 0;
  virtual bool entryBlockAssumed() = 0;

  virtual BasicBlock* getEntryBlock() = 0;
  
  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual void collectAllLoopStats() = 0;
  virtual void printHeader(raw_ostream& OS) const = 0;

  // Simple state-tracking helpers:

  virtual InlineAttempt* getFunctionRoot() = 0;

  ShadowBB* getBB(uint32_t idx, bool* inScope = 0) {

    if(!(idx >= BBsOffset && idx < (BBsOffset + nBBs))) {
      if(inScope)
	*inScope = false;
      return 0;
    }
    else {
      if(inScope)
	*inScope = true;
      return BBs[idx - BBsOffset];
    }

  }

  ShadowBB* getBB(ShadowBBInvar& BBI, bool* inScope = 0) {

    return getBB(BBI.idx, inScope);

  }

  ShadowBB* getOrCreateBB(ShadowBBInvar* BBI);
  ShadowBB* getOrCreateBB(uint32_t);
  // virtual for external access:
  ShadowBBInvar* getBBInvar(uint32_t idx) const;
  ShadowBB* createBB(uint32_t blockIdx);
  ShadowBB* createBB(ShadowBBInvar*);
  ShadowInstructionInvar* getInstInvar(uint32_t blockidx, uint32_t instidx);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx) = 0;
  ShadowInstruction* getInst(uint32_t blockIdx, uint32_t instIdx);
  virtual ShadowInstruction* getInst(ShadowInstructionInvar* SII);

  // The toplevel loop:
  void analyse();
  bool analyse(bool inLoopAnalyser, bool inAnyLoop, uint32_t new_stack_depth);
  bool analyseBlock(uint32_t& BBIdx, bool inLoopAnalyser, bool inAnyLoop, bool skipStoreMerge, const ShadowLoopInvar* MyL);
  bool analyseBlockInstructions(ShadowBB* BB, bool inLoopAnalyser, bool inAnyLoop);
  bool analyseInstruction(ShadowInstruction* SI, bool inLoopAnalyser, bool inAnyLoop, bool& loadedVarargsHere, bool& bail);
  bool analyseLoop(const ShadowLoopInvar*, bool nestedLoop);
  void releaseLatchStores(const ShadowLoopInvar*);
  virtual void getInitialStore(bool inLoopAnalyser) = 0;
  // Toplevel, execute-only version:
  void execute(uint32_t new_stack_depth);
  void executeBlock(ShadowBB*);
  void executeLoop(const ShadowLoopInvar*);

  // Constant propagation:
  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result);
  bool tryEvaluate(ShadowValue V, bool inLoopAnalyser, bool& loadedVararg);
  bool getNewResult(ShadowInstruction* SI, ImprovedValSet*& NewResult, bool& loadedVararg);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSet*& NewPB);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSetSingle& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx);
  void tryEvaluateResult(ShadowInstruction* SI, 
			 std::pair<ValSetType, ImprovedVal>* Ops, 
			 ValSetType& ImpType, ImprovedVal& Improved,
			 unsigned char* needsRuntimeCheck);
  bool tryFoldBitwiseOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  unsigned getAlignment(ShadowValue);
  bool tryFoldPtrAsIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldPointerCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved, unsigned char* needsRuntimeCheck);
  bool tryFoldNonConstCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldOpenCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  void getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs = 0);
  void getOperandRising(ShadowInstruction* SI, uint32_t valOpIdx, ShadowBBInvar* ExitingBB, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs);
  void getCommittedExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs);
  bool tryEvaluateMerge(ShadowInstruction* I, ImprovedValSet*& NewPB);
  bool getMergeValue(SmallVector<ShadowValue, 4>& Vals, ImprovedValSet*& NewPB);
  bool tryEvaluateMultiInst(ShadowInstruction* I, ImprovedValSet*& NewPB);
  bool tryEvaluateMultiCmp(ShadowInstruction* SI, ImprovedValSet*& NewIV);
  MultiCmpResult tryEvaluateMultiEq(ShadowInstruction* SI);
  bool tryGetPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result);
  bool tryGetAsDefPathValue(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result);
  virtual bool tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef);
  bool tryGetPathValueFrom(PathConditions& PC, uint32_t stackDepth, ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef);
  Type* getValueType(ShadowValue);

  // CFG analysis:

  bool createEntryBlock();
  bool tryEvaluateTerminator(ShadowInstruction* SI, bool tagSuccVararg);
  bool checkBlockOutgoingEdges(ShadowInstruction* Terminator);
  IntegrationAttempt* getIAForScope(const ShadowLoopInvar* Scope);
  virtual IntegrationAttempt* getIAForScopeFalling(const ShadowLoopInvar* Scope) = 0;
  bool shouldAssumeEdge(BasicBlock* BB1, BasicBlock* BB2) {
    return pass->shouldAssumeEdge(&F, BB1, BB2);
  }
  void copyLoopExitingDeadEdges(PeelAttempt* LPA);
  virtual IntegrationAttempt* getUniqueParent() = 0;
  void checkBlockStatus(ShadowBB*, bool inLoopAnalyser);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(ShadowInstruction* CI) {
    // Only calls and invokes use tSD at the moment, so no need for a check.
    return (InlineAttempt*)CI->typeSpecificData;
  }
  virtual bool stackIncludesCallTo(Function*) = 0;
  bool shouldInlineFunction(ShadowInstruction*, Function*);
  InlineAttempt* getOrCreateInlineAttempt(ShadowInstruction* CI, bool& created, bool& needsAnalyse);
  bool callCanExpand(ShadowInstruction* Call, InlineAttempt*& Result);
  bool analyseExpandableCall(ShadowInstruction* SI, bool& changed, bool inLoopAnalyser, bool inAnyLoop);
 
  PeelAttempt* getPeelAttempt(const ShadowLoopInvar*);
  PeelAttempt* getOrCreatePeelAttempt(const ShadowLoopInvar*);

  // Load forwarding:

  bool tryResolveLoadFromConstant(ShadowInstruction*, ImprovedVal Ptr, ImprovedValSetSingle& Result);
  bool tryResolveLoadFromVararg(ShadowInstruction* LoadI, ImprovedValSet*& Result);
  bool tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSet*& NewPB, bool& loadedVararg);
  bool getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result);
  virtual void applyMemoryPathConditions(ShadowBB*, bool inLoopAnalyser, bool inAnyLoop);
  void applyMemoryPathConditionsFrom(ShadowBB*, PathConditions&, uint32_t, bool inLoopAnalyser, bool inAnyLoop);
  void applyPathCondition(PathCondition*, PathConditionTypes, ShadowBB*, uint32_t);

  AllocData* getAllocData(ShadowValue);
  ShadowInstruction* getAllocInst(ShadowValue V);

  // Support functions for the generic IA graph walkers:
  void visitLoopExitingBlocksBW(ShadowBBInvar* ExitedBB, ShadowBBInvar* ExitingBB, ShadowBBVisitor*, void* Ctx, bool& firstPred);
  virtual WalkInstructionResult queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) = 0;
  void visitNormalPredecessorsBW(ShadowBB* FromBB, ShadowBBVisitor*, void* Ctx);
  void queueReturnBlocks(BackwardIAWalker* Walker, void*);
  virtual void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) = 0;
  virtual void queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) = 0;
  virtual void popAllocas(OrdinaryLocalStore*) = 0;

  // VFS call forwarding:

  virtual ReadFile* tryGetReadFile(ShadowInstruction* CI);
  bool tryPromoteOpenCall(ShadowInstruction* CI);
  bool tryResolveVFSCall(ShadowInstruction*);
  bool executeStatCall(ShadowInstruction* SI, Function* F, std::string& Filename);
  WalkInstructionResult isVfsCallUsingFD(ShadowInstruction* VFSCall, ShadowInstruction* FD, bool ignoreClose);
  virtual void resolveReadCall(ShadowInstruction*, struct ReadFile);
  virtual void resolveSeekCall(ShadowInstruction*, struct SeekFile);
  bool isResolvedVFSCall(ShadowInstruction*);
  bool VFSCallWillUseFD(ShadowInstruction*);
  bool isUnusedReadCall(ShadowInstruction*);
  OpenStatus& getOpenStatus(ShadowInstruction*);
  void tryKillAllVFSOps();
  void initialiseFDStore(FDStore*);

  // Load forwarding extensions for varargs:
  virtual void getVarArg(int64_t, ImprovedValSet*&) = 0;
  
  // Dead store and allocation elim:

  void DSEHandleRead(ShadowValue PtrOp, uint64_t Size, ShadowBB* BB);
  void DSEHandleWrite(ShadowValue PtrOp, uint64_t Size, ShadowInstruction* Writer, ShadowBB* BB);
  void tryKillStoresInLoop(const ShadowLoopInvar* L, bool commitDisabledHere, bool disableWrites, bool latchToHeader = false);
  void tryKillStoresInUnboundedLoop(const ShadowLoopInvar* UL, bool commitDisabledHere, bool disableWrites);
  void DSEAnalyseInstruction(ShadowInstruction* I, bool commitDisabledHere, bool disableWrites, bool enterCalls, bool& bail);

  // User visitors:
  
  virtual bool visitNextIterationPHI(ShadowInstructionInvar* I, DIVisitor& Visitor);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, DIVisitor& Visitor) = 0;
  void visitUsers(ShadowValue, DIVisitor& Visitor);
  void visitUser(ShadowInstIdx&, DIVisitor& Visitor);

  // Dead instruction elim:

  bool valueIsDead(ShadowValue);
  bool shouldDIE(ShadowInstruction* V);
  virtual void runDIE();

  virtual bool ctxContains(IntegrationAttempt*) = 0;
  void gatherIndirectUsersInLoop(const ShadowLoopInvar*);
  void noteIndirectUse(ShadowValue V, ImprovedValSet* NewPB);
  bool _willBeReplacedOrDeleted(ShadowValue);
  bool willBeReplacedOrDeleted(ShadowValue);
  bool willBeReplacedWithConstantOrDeleted(ShadowValue);


  // Enabling / disabling exploration:

  virtual bool isEnabled() = 0;
  virtual void setEnabled(bool, bool skipStats) = 0;
  bool allAncestorsEnabled();
  virtual bool commitsOutOfLine() = 0;
  virtual bool mustCommitOutOfLine() = 0;

  // Estimating inlining / unrolling benefit:

  virtual void findProfitableIntegration();
  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&);
  int64_t getResidualInstructions();

  // DOT export:

  void inheritDiagnosticsFrom(IntegrationAttempt*);
  void countTentativeInstructions();
  void printRHS(ShadowValue, raw_ostream& Out);
  void printOutgoingEdge(ShadowBBInvar* BBI, ShadowBB* BB, ShadowBBInvar* SBI, ShadowBB* SB, uint32_t i, bool useLabels, const ShadowLoopInvar* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief);
  void describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const ShadowLoopInvar* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBBInvar*, 4>* forceSuccessors, bool brief, bool plain = false);
  void describeScopeAsDOT(const ShadowLoopInvar* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief, SmallVector<std::string, 4>* deferredEdges);
  void describeLoopAsDOT(const ShadowLoopInvar* L, uint32_t headerIdx, raw_ostream& Out, bool brief);
  void describeAsDOT(raw_ostream& Out, std::string& otherpath, bool brief);
  std::string getValueColour(ShadowValue, std::string& textColour, bool plain = false);
  std::string getGraphPath(std::string prefix);
  void describeTreeAsDOT(std::string path);
  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) = 0;
  bool blockLiveInAnyScope(ShadowBBInvar* BB);
  virtual void printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB);
  void getSavedDotName(bool brief, std::string& Out);
  void saveDOT2(bool brief);
  void saveDOT();

  void printWithCache(const Value* V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  void printWithCache(ShadowValue V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  // Data export for the Integrator pass:

  virtual std::string getShortHeader() = 0;
  bool hasChildren();
  virtual bool canDisable() = 0;
  unsigned getTotalInstructions();
  unsigned getElimdInstructions();
  int64_t getTotalInstructionsIncludingLoops();
  IntegratorTag* createTag(IntegratorTag* parent);
  virtual void addExtraTags(IntegratorTag* myTag);

  // Saving our results as a bitcode file:

  void prepareCommit();
  virtual std::string getCommittedBlockPrefix() = 0;
  virtual void commitCFG();
  virtual BasicBlock* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  ShadowBB* getBBFalling(ShadowBBInvar* BBI);
  virtual ShadowBB* getBBFalling2(ShadowBBInvar* BBI) = 0;
  void populatePHINode(ShadowBB* BB, ShadowInstruction* I, PHINode* NewPB);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void fixupHeaderPHIs(ShadowBB* BB);
  void emitTerminator(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  bool emitVFSCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBB);
  void emitCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBB);
  Instruction* emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  bool synthCommittedPointer(ShadowValue I, SmallVector<CommittedBlock, 1>::iterator emitBB);
  bool synthCommittedPointer(ShadowValue*, Type*, ImprovedVal, BasicBlock* emitBB, Value*&);
  bool canSynthMTI(ShadowInstruction* I);
  bool canSynthVal(ShadowValue* I, ValSetType Ty, const ImprovedVal& IV);
  bool canSynthPointer(ShadowValue* I, ImprovedVal IV);
  void emitChunk(ShadowInstruction* I, BasicBlock* emitBB, SmallVector<IVSRange, 4>::iterator chunkBegin, SmallVector<IVSRange, 4>::iterator chunkEnd, SmallVector<Instruction*, 4>& newInstructions);
  bool trySynthMTI(ShadowInstruction* I, BasicBlock* emitBB);
  Value* trySynthVal(ShadowValue* I, Type* targetType, ValSetType Ty, const ImprovedVal& IV, BasicBlock* emitBB);
  bool trySynthInst(ShadowInstruction* I, BasicBlock* emitBB, Value*& Result);
  bool trySynthArg(ShadowArg* A, BasicBlock* emitBB, Value*& Result);
  void emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, SmallVector<CommittedBlock, 1>::iterator& emitBB);
  void commitLoopInstructions(const ShadowLoopInvar* ScopeL, uint32_t& i);
  void commitInstructions();
  bool isCommitted() { 
    return commitState == COMMIT_DONE || commitState == COMMIT_FREED;
  }
  bool commitStarted() {
    return commitState != COMMIT_NOT_STARTED;
  }
  Value* getCommittedValue(ShadowValue SV);
  Value* getCommittedValueOrBlock(ShadowInstruction* I, uint32_t idx, ConstantInt*& failValue, BasicBlock*& failBlock);
  BasicBlock* getInvokeNormalSuccessor(ShadowInstruction*, bool& toCheckBlock);
  void releaseMemoryPostCommit();
  BasicBlock* createBasicBlock(LLVMContext& Ctx, const Twine& Name, Function* AddF, bool isEntryBlock, bool isFailedBlock);
  BasicBlock* CloneBasicBlockFrom(const BasicBlock* BB,
				  ValueToValueMapTy& VMap,
				  const Twine &NameSuffix, 
				  Function* F,
				  uint32_t startIdx);
  void addPatchRequest(ShadowValue Needed, Instruction* PatchI, uint32_t PatchOp);
  virtual void inheritCommitBlocksAndFunctions(std::vector<BasicBlock*>& NewCBs, std::vector<BasicBlock*>& NewFCBs, std::vector<Function*>& NewFs) = 0;
  void markAllocationsAndFDsCommitted();

  // Function sharing

  void noteDependency(ShadowValue V);
  void noteMalloc(ShadowInstruction* SI);
  void noteVFSOp();
  void mergeChildDependencies(InlineAttempt* ChildIA);
  virtual void sharingInit();
  virtual void sharingCleanup();

  // Conditional specialisation

  void checkTargetStack(ShadowInstruction* SI, InlineAttempt* IA);
  bool isExceptionEdge(ShadowBBInvar*, ShadowBBInvar*);
  bool edgeBranchesToUnspecialisedCode(ShadowBBInvar*, ShadowBBInvar*);
  bool hasLiveIgnoredEdges(ShadowBB*);
  virtual void initFailedBlockCommit();
  virtual void finishFailedBlockCommit();
  uint32_t collectSpecIncomingEdges(uint32_t blockIdx, uint32_t instIdx, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& edges);
  Value* getSpecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, Instruction* InsertBefore);
  Value* getSpecValueAnyType(uint32_t blockIdx, uint32_t instIdx, Value* V);
  virtual void commitSimpleFailedBlock(uint32_t i);
  void getSplitInsts(ShadowBBInvar*, bool* splits);
  void getLocalSplitInsts(ShadowBB*, bool*);
  bool hasSplitInsts(ShadowBB*);
  virtual void createFailedBlock(uint32_t idx);
  void collectSpecPreds(ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds);
  void collectCallFailingEdges(ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds);
  virtual void populateFailedBlock(uint32_t idx);
  virtual void populateFailedHeaderPHIs(const ShadowLoopInvar*);
  Value* emitCompareCheck(Value* realInst, const ImprovedValSetSingle* IVS, BasicBlock* emitBB);
  Instruction* emitCompositeCheck(Value*, Value*, BasicBlock* emitBB);
  Value* emitAsExpectedCheck(ShadowInstruction* SI, BasicBlock* emitBB);
  SmallVector<CommittedBlock, 1>::iterator emitExitPHIChecks(SmallVector<CommittedBlock, 1>::iterator emitIt, ShadowBB* BB);
  Value* emitMemcpyCheck(ShadowInstruction* SI, BasicBlock* emitBB);
  SmallVector<CommittedBlock, 1>::iterator emitOrdinaryInstCheck(SmallVector<CommittedBlock, 1>::iterator emitIt, ShadowInstruction* SI);
  SmallVector<CommittedBlock, 1>::iterator emitPathConditionChecks(ShadowBB* BB);
  ShadowValue getPathConditionSV(uint32_t instStackIdx, BasicBlock* instBB, uint32_t instIdx);
  ShadowValue getPathConditionSV(PathCondition& Cond);
  void emitPathConditionCheck(PathCondition& Cond, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt);
  void emitPathConditionChecksIn(std::vector<PathCondition>& Conds, PathConditionTypes Ty, ShadowBB* BB, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& emitBlockIt);
  void emitPathConditionChecks2(ShadowBB* BB, PathConditions& PC, uint32_t stackIdx, SmallVector<CommittedBlock, 1>::iterator& it);
  bool hasSpecialisedCompanion(ShadowBBInvar* BBI);
  void gatherPathConditionEdges(uint32_t bbIdx, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>* preds, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* IApreds);
  virtual void noteAsExpectedChecks(ShadowBB* BB);
  void noteAsExpectedChecksFrom(ShadowBB* BB, std::vector<PathCondition>& PCs, uint32_t stackIdx);
  bool requiresBreakCode(ShadowInstruction*);
  bool subblockEndsWithSpecialTest(uint32_t idx,
				   SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator it, 
				   SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator lastit);
  bool instSpecialTest(uint32_t blockIdx, uint32_t instIdx);
  bool gatherInvokeBreaks(uint32_t predBlockIdx, uint32_t BBIdx, ShadowInstIdx predOp, 
			  Value* predV, SmallVector<std::pair<Value*, BasicBlock*>, 4>* newPreds,
			  SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* newEdgeSources);
  bool hasInvokeBreaks(uint32_t breakFrom, uint32_t breakTo);
  bool gatherTopOfBlockVFSChecks(uint32_t BBIdx, ShadowInstIdx predOp, Value* predV,
				 SmallVector<std::pair<Value*, BasicBlock*>, 4>* newPreds, 
				 SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>* newEdgeSources);
  bool hasTopOfBlockVFSChecks(uint32_t BBIdx);

  // Tentative load determination
  
  ThreadLocalState shouldCheckCopy(ShadowInstruction& SI, ShadowValue PtrOp, ShadowValue LenSV);
  ThreadLocalState shouldCheckLoadFrom(ShadowInstruction& SI, ImprovedVal& Ptr, uint64_t LoadSize);
  ThreadLocalState shouldCheckLoad(ShadowInstruction& SI);
  void findTentativeLoadsInLoop(const ShadowLoopInvar* L, bool commitDisabledHere, bool secondPass, bool latchToHeader = false);
  void findTentativeLoadsInUnboundedLoop(const ShadowLoopInvar* L, bool commitDisabledHere, bool secondPass);
  void TLAnalyseInstruction(ShadowInstruction&, bool commitDisabledHere, bool secondPass, bool inLoopAnalyser);
  bool requiresRuntimeCheck2(ShadowValue V, bool includeSpecialChecks);
  bool containsTentativeLoads();
  void addCheckpointFailedBlocks();
  void squashUnavailableObjects(ShadowInstruction& SI, ImprovedValSet*, bool inLoopAnalyser);
  void squashUnavailableObjects(ShadowInstruction& SI, bool inLoopAnalyser);
  bool squashUnavailableObject(ShadowInstruction& SI, const ImprovedValSetSingle& IVS, bool inLoopAnalyser, ShadowValue ReadPtr, int64_t ReadOffset, uint64_t ReadSize);
  void replaceUnavailableObjects(ShadowInstruction& SI, bool inLoopAnalyser);

  // Function splitting in the commit stage
  
  virtual uint64_t findSaveSplits();
  void inheritCommitFunction();
  
  // Stat collection and printing:

  void collectAllBlockStats();
  void collectBlockStats(ShadowBBInvar* BBI, ShadowBB* BB);
  void collectLoopStats(const ShadowLoopInvar*);
  void collectStats();
  virtual void preCommitStats(bool enabledHere);

  void print(raw_ostream& OS) const;
  // Callable from GDB
  void dump() const;

  virtual void describe(raw_ostream& Stream) const = 0;
  virtual void describeBrief(raw_ostream& Stream) const = 0;
  virtual std::string getFunctionName();

  void printDebugHeader(raw_ostream& Str) {
    printHeader(Str);
  }

  void dumpMemoryUsage(int indent = 0);

};

enum StoreKind {

  StoreKindTL,
  StoreKindDSE

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  PeelAttempt* parentPA;

public:

  PeelIteration(LLPEAnalysisPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, int iter, int depth);
 
  IntegrationAttempt* parent;

  IterationStatus iterStatus;

  PeelIteration* getNextIteration();
  PeelIteration* getOrCreateNextIteration(); 

  virtual BasicBlock* getEntryBlock(); 

  ShadowValue getLoopHeaderForwardedOperand(ShadowInstruction* SI); 

  void checkFinalIteration(); 
  void dropExitingStoreRefs();
  void dropLatchStoreRef();

  virtual InlineAttempt* getFunctionRoot() {
    return parent->getFunctionRoot();
  }

  void visitVariant(ShadowInstructionInvar* VI, DIVisitor& Visitor); 
  virtual bool visitNextIterationPHI(ShadowInstructionInvar* I, DIVisitor& Visitor); 

  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out); 

  virtual void describe(raw_ostream& Stream) const;
  virtual void describeBrief(raw_ostream& Stream) const;

  virtual void collectAllLoopStats(); 

  virtual std::string getShortHeader(); 

  virtual bool canDisable(); 
  virtual bool isEnabled(); 
  virtual void setEnabled(bool, bool skipStats); 

  virtual void getVarArg(int64_t, ImprovedValSet*&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  virtual bool stackIncludesCallTo(Function*); 

  virtual WalkInstructionResult queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* ctx); 
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc); 

  virtual bool entryBlockIsCertain(); 
  virtual bool entryBlockAssumed(); 

  bool allExitEdgesDead(); 
  void dropExitingStoreRef(uint32_t, uint32_t);

  void prepareShadows();
  virtual std::string getCommittedBlockPrefix();
  virtual BasicBlock* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, DIVisitor& Visitor);

  virtual void getInitialStore(bool inLoopAnalyser);

  virtual IntegrationAttempt* getIAForScopeFalling(const ShadowLoopInvar* Scope);
  virtual void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual IntegrationAttempt* getUniqueParent();
  virtual ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx);
  virtual bool commitsOutOfLine();
  virtual bool mustCommitOutOfLine();
  virtual void popAllocas(OrdinaryLocalStore*);

  virtual void printHeader(raw_ostream& OS) const;

  void setExitingStores(void*, StoreKind);
  void setExitingStore(void*, ShadowBBInvar*, const ShadowLoopInvar*, StoreKind);

  virtual void inheritCommitBlocksAndFunctions(std::vector<BasicBlock*>& NewCBs, std::vector<BasicBlock*>& NewCFBs, std::vector<Function*>& NewFs);

  ShadowBB* getUniqueExitingBlock2(ShadowBBInvar* BBI, const ShadowLoopInvar* exitLoop, bool& bail);
  ShadowBB* getUniqueExitingBlock();
  
  std::string getLName() const;

};

class ProcessExternalCallback;

class PeelAttempt {
   // Not a subclass of IntegrationAttempt -- this is just a helper.

   LLPEAnalysisPass* pass;
   IntegrationAttempt* parent;
   Function& F;

   uint64_t SeqNumber;

   int64_t residualInstructions;

   int nesting_depth;
   int stack_depth;

   bool enabled;

 public:

   const ShadowLoopInvar* L;

   int64_t totalIntegrationGoodness;
   bool integrationGoodnessValid;

   std::vector<PeelIteration*> Iterations;
   std::vector<BasicBlock*> CommitBlocks;
   std::vector<BasicBlock*> CommitFailedBlocks;
   std::vector<Function*> CommitFunctions;

   PeelAttempt(LLPEAnalysisPass* Pass, IntegrationAttempt* P, Function& _F, const ShadowLoopInvar* _L, int depth);
   ~PeelAttempt();

   bool analyse(uint32_t parent_stack_depth, bool& readsTentativeData, bool& containsCheckedReads);

   PeelIteration* getIteration(unsigned iter); 
   PeelIteration* getOrCreateIteration(unsigned iter); 

   void visitVariant(ShadowInstructionInvar* VI, DIVisitor& Visitor); 
   
   void describeTreeAsDOT(std::string path); 

   void collectStats(); 
   void printHeader(raw_ostream& OS) const; 
   void printDebugHeader(raw_ostream& OS) const {
     printHeader(OS);
   }
   void print(raw_ostream& OS) const; 

   std::string nestingIndent() const; 

   std::string getShortHeader(); 
   bool hasChildren(); 
   bool isEnabled(); 
   void setEnabled(bool, bool skipStats); 
   
   void dumpMemoryUsage(int indent); 

   int64_t getResidualInstructions(); 
   void findProfitableIntegration();

   bool isTerminated() {
     return Iterations.back()->iterStatus == IterationStatusFinal;
   }

   void dropExitingStoreRefs();
   void dropNonterminatedStoreRefs();

   bool containsTentativeLoads();

   IntegratorTag* createTag(IntegratorTag* parent);

   void releaseCommittedChildren();

   std::string getLName() const;

};

// Members only needed for an IA with a target call
struct IATargetInfo {

  uint32_t targetCallBlock;
  uint32_t targetCallInst;
  uint32_t targetStackDepth;
  DenseSet<uint32_t> mayReachTarget;

IATargetInfo(uint32_t tCB, uint32_t tCI, uint32_t tSD) : 
    targetCallBlock(tCB), 
    targetCallInst(tCI),
    targetStackDepth(tSD) {}

};

struct SharingState {

  OrdinaryLocalStore* storeAtEntry;
  DenseMap<ShadowValue, ImprovedValSet*> externalDependencies;
  SmallPtrSet<ShadowInstruction*, 4> escapingMallocs;

SharingState() : storeAtEntry(0) { }

};

class InlineAttempt : public IntegrationAttempt { 

 public:

  InlineAttempt(LLPEAnalysisPass* Pass, Function& F, ShadowInstruction* _CI, int depth, bool isPathCond = false);

  virtual ~InlineAttempt();

  SmallVector<ShadowInstruction*, 1> Callers;
  ShadowInstruction* activeCaller;
  IntegrationAttempt* uniqueParent;

  Function* CommitF;
  Function::iterator firstFailedBlock;
  std::vector<BasicBlock*> CommitBlocks;
  std::vector<BasicBlock*> CommitFailedBlocks;
  std::vector<Function*> CommitFunctions;
  BasicBlock* entryBlock;
  BasicBlock* returnBlock;
  PHINode* returnPHI;
  BasicBlock* failedReturnBlock;
  PHINode* failedReturnPHI;

  ImmutableArray<ShadowArg> argShadows;

  std::vector<AllocData> localAllocas;
  AllocData& getAllocaWithIdx(uint32_t i) {
    return localAllocas[i];
  }

  bool hasVFSOps : 1;
  bool registeredSharable : 1;
  bool active : 1;
  bool instructionsCommitted : 1;
  bool emittedAlloca : 1;
  bool isModel : 1;
  bool isPathCondition : 1;
  bool enabled : 1;
  bool isStackTop : 1;

  IATargetInfo* targetCallInfo;

  SharingState* sharing;

  DominatorTree* DT;
  SmallDenseMap<uint32_t, uint32_t, 8>* blocksReachableOnFailure;
  std::vector<SmallVector<std::pair<BasicBlock*, uint32_t>, 1> > failedBlocks;
  ValueToValueMapTy* failedBlockMap;
  // Indexes from CLONED instruction/block to replacement PHI node to use in that block.
  DenseMap<std::pair<Instruction*, BasicBlock*>, PHINode*>* PHIForwards;
  DenseSet<PHINode*>* ForwardingPHIs;

  TLLocalStore* backupTlStore;
  DSELocalStore* backupDSEStore;

  ImprovedValSet* returnValue;

  bool isUnsharable() {
    return hasVFSOps || isModel || (sharing && !sharing->escapingMallocs.empty()) || Callers.empty();
  }
  
  bool isShared() {
    return Callers.size() > 1;
  }

  virtual BasicBlock* getEntryBlock(); 

  virtual InlineAttempt* getFunctionRoot() {
    return this;
  }

  bool isOwnCallUnused(); 

  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out); 
  
  virtual void describe(raw_ostream& Stream) const; 
  virtual void describeBrief(raw_ostream& Stream) const; 
  
  virtual void collectAllLoopStats(); 

  virtual std::string getShortHeader(); 

  virtual bool canDisable(); 
  virtual bool isEnabled(); 
  virtual void setEnabled(bool, bool skipStats); 

  virtual void getVarArg(int64_t, ImprovedValSet*&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  int64_t NonFPArgIdxToArgIdx(int64_t idx);
  int64_t FPArgIdxToArgIdx(int64_t idx);

  virtual bool stackIncludesCallTo(Function*); 

  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&); 
  virtual void findProfitableIntegration(); 

  virtual WalkInstructionResult queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* ctx);
  virtual void queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual bool entryBlockIsCertain(); 
  virtual bool entryBlockAssumed(); 

  bool analyseWithArgs(ShadowInstruction* Caller, bool withinUnboundedLoop, bool inAnyLoop, uint32_t parent_stack_depth); 
  bool analyseNoArgs(bool withinUnboundedLoop, bool inAnyLoop, uint32_t parent_stack_depth); 

  void prepareShadows();
  void getLiveReturnVals(SmallVector<ShadowValue, 4>& Vals);
  void visitLiveReturnBlocks(ShadowBBVisitor& V);
  std::string getCommittedBlockPrefix();
  BasicBlock* getCommittedEntryBlock();
  virtual void runDIE();
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, DIVisitor& Visitor);

  Value* getArgCommittedValue(ShadowArg* SA, BasicBlock* emitBB);
  Value* getArgCommittedValue(ShadowArg* SA, Instruction* insertBefore);
  Value* getArgCommittedValue2(ShadowArg* SA, BasicBlock* emitBB, Instruction* insertBefore);
  void commitArgsAndInstructions();

  virtual void getInitialStore(bool inLoopAnalyser);

  // Function sharing:

  void clearExternalDependencies();
  virtual void sharingInit();
  void dumpSharingState();
  virtual void sharingCleanup();
  bool matchesCallerEnvironment(ShadowInstruction* SI);
  InlineAttempt* getWritableCopyFrom(ShadowInstruction* SI);
  void dropReferenceFrom(ShadowInstruction* SI);

  virtual IntegrationAttempt* getIAForScopeFalling(const ShadowLoopInvar* Scope);
  virtual void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual IntegrationAttempt* getUniqueParent();
  bool isRootMainCall();
  virtual ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx);
  virtual bool commitsOutOfLine();
  virtual bool mustCommitOutOfLine();
  void executeCall(uint32_t new_stack_depth);
  void releaseCallLatchStores();
  virtual bool tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef);
  virtual void applyMemoryPathConditions(ShadowBB*, bool inLoopAnalyser, bool inAnyLoop);
  void addIgnoredBlock(std::string& name);
  virtual void addExtraTags(IntegratorTag* myTag);
  void addExtraTagsFrom(PathConditions&, IntegratorTag* myTag);

  // Conditional specialisation:
  void addBlockAndPreds(uint32_t idx, DenseSet<uint32_t>& Set);
  void markBlockAndSuccsReachableUnspecialised(uint32_t idx, uint32_t instIdx);
  void setTargetCall(std::pair<BasicBlock*, uint32_t>& arg, uint32_t stackIdx);
  virtual BasicBlock* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  bool hasFailedReturnPath();
  virtual void initFailedBlockCommit();
  virtual void finishFailedBlockCommit();
  void markBBAndPreds(ShadowBBInvar* UseBBI, uint32_t instIdx, std::vector<std::pair<Instruction*, uint32_t> >& predBlocks, ShadowBBInvar* LimitBBI);
  bool isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx);
  void gatherSpecToUnspecEdges(uint32_t predBlockIdx, uint32_t BBIdx, ShadowInstIdx predOp, 
			       Value* predV, SmallVector<std::pair<Value*, BasicBlock*>, 4>& newPreds);
  bool isSimpleMergeBlock(uint32_t i);
  BasicBlock::iterator skipMergePHIs(BasicBlock::iterator it);
  void createForwardingPHIs(ShadowInstructionInvar& OrigSI, Instruction* NewI);
  Value* getLocalFailedValue(Value* V, BasicBlock*);
  Value* tryGetLocalFailedValue(Value* V, BasicBlock*);
  Value* getUnspecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, BasicBlock* BB, Instruction* InsertBefore);
  BasicBlock::iterator commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx);
  void remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t blockIdx, uint32_t instIdx, bool skipTestedInst, bool skipTerm);
  virtual void commitSimpleFailedBlock(uint32_t i);
  virtual void popAllocas(OrdinaryLocalStore*);
  virtual void createFailedBlock(uint32_t idx);
  virtual void populateFailedBlock(uint32_t idx);
  virtual void populateFailedHeaderPHIs(const ShadowLoopInvar* PopulateL);
  BasicBlock* getSubBlockForInst(uint32_t, uint32_t);

  void tryKillStores(bool commitDisabledHere, bool disableWrites);

  void findTentativeLoads(bool commitDisabledHere, bool secondPass);

  virtual void printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB);
  virtual void noteAsExpectedChecks(ShadowBB* BB);

  virtual void printHeader(raw_ostream& OS) const;

  virtual void preCommitStats(bool enabledHere);

  virtual uint64_t findSaveSplits();
  void splitCommitHere();

  void gatherIndirectUsers();
  InlineAttempt* getStackFrameCtx(int32_t);
  void prepareCommitCall();
  void fixNonLocalStackUses();
  virtual void commitCFG();
  void releaseBackupStores();
  void releaseCommittedChildren();

  void postCommitOptimise();
  void finaliseAndCommit(bool inLoopAnalyser);
  void inheritCommitFunctionCall(bool);

  virtual void inheritCommitBlocksAndFunctions(std::vector<BasicBlock*>& NewCBs, std::vector<BasicBlock*>& NewFCBs, std::vector<Function*>& NewFs);

};

struct IAIterator {

  const IntegrationAttempt* parent;
  uint32_t blockIdx;
  uint32_t instIdx;

  std::pair<ShadowInstruction*, InlineAttempt*> D;

  IAIterator() {
    blockIdx = 0;
    instIdx = 0;
    parent = 0;
  }

  IAIterator(const IntegrationAttempt* IA, bool isEnd) {
    
    parent = IA;
    
    if(isEnd) {
      blockIdx = parent->nBBs;
      instIdx = 0;
    }
    else {
      blockIdx = 0;
      instIdx = 0;
      advanceToNextCall();
    }

  }

IAIterator(const IAIterator& other) : parent(other.parent), blockIdx(other.blockIdx), instIdx(other.instIdx) {}
  
  void advanceToNextCall() {

    for(; blockIdx < parent->nBBs; ++blockIdx) {
      
      if(parent->BBs[blockIdx]) {
      
	for(; instIdx < parent->BBs[blockIdx]->insts.size(); ++instIdx) {
	  
	  if(parent->BBs[blockIdx]->insts[instIdx].typeSpecificData)
	    return;
	  
	}

      }

      instIdx = 0;

    }

  }

  struct IAIterator& operator++() {
    ++instIdx;
    advanceToNextCall();
    return *this;
  }

  struct IAIterator operator++(int) {
    IAIterator cpy = *this;
    ++instIdx;
    advanceToNextCall();
    return cpy;
  }

  bool operator==(const IAIterator& other) {

    return parent == other.parent && blockIdx == other.blockIdx && instIdx == other.instIdx;

  }

  bool operator!=(const IAIterator& other) {

    return !((*this) == other);

  }

  const std::pair<ShadowInstruction*, InlineAttempt*>& operator*() {

    release_assert(blockIdx < parent->nBBs);
    ShadowInstruction* SI = &parent->BBs[blockIdx]->insts[instIdx];
    D = std::make_pair(SI, (InlineAttempt*)SI->typeSpecificData);
    return D;
    
  }

  const std::pair<ShadowInstruction*, InlineAttempt*>* operator->() {
    return &operator*();
  }

};

 inline IAIterator child_calls_begin(const IntegrationAttempt* IA) {
   return IAIterator(IA, false);
 }

 inline IAIterator child_calls_end(const IntegrationAttempt* IA) {
   return IAIterator(IA, true);
 }

inline int32_t getFrameSize(InlineAttempt* IA) {
  return IA->invarInfo->frameSize;
}

inline bool hasNoCallers(InlineAttempt* IA) {

  return IA->Callers.empty();

}

inline ShadowValue getStackAllocationWithIndex(InlineAttempt* IA, uint32_t i) {
  return IA->getAllocaWithIdx(i).allocValue;
}

inline IntegrationAttempt* ShadowValue::getCtx() const {

  switch(t) {
  case SHADOWVAL_ARG:
    return u.A->IA;
  case SHADOWVAL_INST:
    return u.I->parent->IA;
  default:
    return 0;
  }

}

 Constant* extractAggregateMemberAt(Constant* From, int64_t Offset, Type* Target, uint64_t TargetSize, const DataLayout*);
 Constant* constFromBytes(unsigned char*, Type*, const DataLayout*);
 bool allowTotalDefnImplicitCast(Type* From, Type* To);
 bool allowTotalDefnImplicitPtrToInt(Type* From, Type* To, const DataLayout*);
 std::string ind(int i);
 const ShadowLoopInvar* immediateChildLoop(const ShadowLoopInvar* Parent, const ShadowLoopInvar* Child);
 Constant* getConstReplacement(Value*, IntegrationAttempt*);
 Constant* intFromBytes(const uint64_t*, unsigned, unsigned, llvm::LLVMContext&);
 
 // Implemented in Transforms/Integrator/SimpleVFSEval.cpp, so only usable with -integrator
 bool getFileBytes(std::string& strFileName, uint64_t realFilePos, uint64_t realBytes, std::vector<Constant*>& arrayBytes, LLVMContext& Context, std::string& errors);

 // Implemented in VMCore/AsmWriter.cpp, since that file contains a bunch of useful private classes
 // if LLVM has been patched appropriately; otherwise stubbed out with simple implementations in Print.cpp.
 PersistPrinter* getPersistPrinter(Module*);
 void getInstructionsText(PersistPrinter*, const Function* IF, DenseMap<const Value*, std::string>& IMap, DenseMap<const Value*, std::string>& BriefMap);
 void getGVText(PersistPrinter*, const Module* M, DenseMap<const GlobalVariable*, std::string>& GVMap, DenseMap<const GlobalVariable*, std::string>& BriefGVMap);

 bool isGlobalIdentifiedObject(ShadowValue VC);
 bool shouldQueueOnInst(Instruction* I, IntegrationAttempt* ICtx);
 uint32_t getInitialBytesOnStack(Function& F);
 uint32_t getInitialFPBytesOnStack(Function& F);

 bool GetDefinedRange(ShadowValue DefinedBase, int64_t DefinedOffset, uint64_t DefinedSize,
		      ShadowValue DefinerBase, int64_t DefinerOffset, uint64_t DefinerSize,
		      uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset);

 bool willBeDeleted(ShadowValue);

 bool instructionCounts(Instruction* I);

 Function* getCalledFunction(ShadowInstruction*);

 int64_t getSpilledVarargAfter(ShadowInstruction* CI, int64_t OldArg);

 bool blockCertainlyExecutes(ShadowBB*);
 bool blockAssumedToExecute(ShadowBB*);

 Function* cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name, bool addFailedReturnFlag);

 Constant* getGVOffset(Constant* GV, int64_t Offset, Type* targetType);


 // Load forwarding v3 functions:
 bool addIVToPartialVal(const ImprovedVal& IV, ValSetType SetType, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error);
 bool addIVSToPartialVal(const ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error);
 void readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, bool& shouldTryMulti, std::string* error);
 void readValRange(ShadowValue& V, int64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, ImprovedValSetMulti** ResultMulti, std::string* error);
 void executeStoreInst(ShadowInstruction* StoreSI);
 void executeMemsetInst(ShadowInstruction* MemsetSI);
 bool executeAtomicRMW(ShadowInstruction* SI, ImprovedValSet*& OldPB, bool& loadedVararg);
 bool executeCmpXchg(ShadowInstruction* SI, ImprovedValSet*& OldPB, bool& loadedVararg);
 void propagateStoreFlags(ImprovedValSetSingle& WrittenPtr, ImprovedValSetSingle& WrittenVal, ShadowBB* StoreBB);

 void getIVSSubVals(const ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest);
 void getIVSSubVal(const ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, ImprovedValSetSingle& Dest);
 void getConstSubVals(ShadowValue FromSV, uint64_t Offset, uint64_t TargetSize, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest);
 Constant* valsToConst(SmallVector<IVSRange, 4>& subVals, uint64_t TargetSize, Type* targetType);
 void getConstSubVal(ShadowValue FromSV, uint64_t Offset, uint64_t TargetSize, Type* TargetType, ImprovedValSetSingle& Result);
 Constant* getSubConst(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* targetType = 0);
 void clearRange(ImprovedValSetMulti* M, uint64_t Offset, uint64_t Size);
 void replaceRangeWithPB(ImprovedValSet* Target, const ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size);
 void replaceRangeWithPBs(ImprovedValSet* Target, const SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size);
 void truncateConstVal(ImprovedValSetMulti::MapIt& it, uint64_t off, uint64_t size, ImprovedValSetMulti::MapIt& replacementStart);
 void truncateRight(ImprovedValSetMulti::MapIt& it, uint64_t n);
 void truncateLeft(ImprovedValSetMulti::MapIt& it, uint64_t n, ImprovedValSetMulti::MapIt& replacementStart);
 bool canTruncate(const ImprovedValSetSingle& S);

 void readValRangeMultiFrom(uint64_t Offset, uint64_t Size, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore, uint64_t ASize);
 void readValRangeMulti(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, SmallVector<IVSRange, 4>& Results);
 void executeMemcpyInst(ShadowInstruction* MemcpySI);
 void executeVaCopyInst(ShadowInstruction* SI);
 void executeAllocInst(ShadowInstruction* SI, AllocData&, Type* AllocType, uint64_t AllocSize, int32_t frame, uint32_t idx);
 void executeAllocaInst(ShadowInstruction* SI);
 void executeMallocLikeInst(ShadowInstruction* SI);
 void executeReallocInst(ShadowInstruction* SI, Function*);
 void executeFreeInst(ShadowInstruction* SI, Function*);
 void executeCopyInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowInstruction*);
 void executeVaStartInst(ShadowInstruction* SI);
 void executeReadInst(ShadowInstruction* ReadSI, std::string& Filename, uint64_t FileOffset, uint64_t Size);
 void executeUnexpandedCall(ShadowInstruction* SI);
 bool clobberSyscallModLocations(Function* F, ShadowInstruction* SI);
 void executeWriteInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowInstruction*);
 void writeExtents(SmallVector<IVSRange, 4>& copyValues, ShadowValue& Ptr, int64_t Offset, uint64_t Size, ShadowBB* BB);

 Constant* PVToConst(PartialVal& PV, uint64_t Size, LLVMContext&);

 bool doBlockStoreMerge(ShadowBB* BB);
 void doCallStoreMerge(ShadowInstruction* SI);
 void doCallStoreMerge(ShadowBB* BB, InlineAttempt* IA);

 void doBlockFDStoreMerge(ShadowBB* BB);
 void doCallFDStoreMerge(ShadowBB* BB, InlineAttempt* IA);

 void initSpecialFunctionsMap(Module& M);
 
 void printPB(raw_ostream& out, ImprovedValSetSingle PB, bool brief = false);

 ShadowValue& getAllocWithIdx(int32_t);
 AllocData& addHeapAlloc(ShadowInstruction*);

 IntegratorTag* searchFunctions(IntegratorTag* thisTag, std::string&, IntegratorTag*& startAt);

 GlobalVariable* getStringArray(std::string& bytes, Module& M, bool addNull=false);

 uint32_t findBlock(ShadowFunctionInvar* SFI, BasicBlock* BB);
 uint32_t findBlock(ShadowFunctionInvar* SFI, StringRef name);
 InlineAttempt* getIAWithTargetStackDepth(InlineAttempt* IA, uint32_t depth);

 Constant* getConstAsType(Constant*, Type*);
 Value* getValAsType(Value* V, Type* Ty, Instruction* insertBefore);
 Value* getValAsType(Value* V, Type* Ty, BasicBlock* insertAtEnd);

 void valueEscaped(ShadowValue, ShadowBB*);
 void intersectSets(DenseSet<ShadowValue>* Target, MutableArrayRef<DenseSet<ShadowValue>* > Merge);

 bool requiresRuntimeCheck(ShadowValue V, bool includeSpecialChecks);
 PHINode* makePHI(Type* Ty, const Twine& Name, BasicBlock* emitBB);
 
 void printPathCondition(PathCondition& PC, PathConditionTypes t, ShadowBB* BB, raw_ostream& Out, bool HTMLEscaped);
 void emitRuntimePrint(BasicBlock* BB, std::string& message, Value* param, Instruction* insertBefore = 0);
 void escapePercent(std::string&);

 void clearAsExpectedChecks(ShadowBB*);
 void noteLLIODependency(std::string&);

 const GlobalValue* getUnderlyingGlobal(const GlobalValue* V);

 enum specialfunctions {

   SF_MALLOC,
   SF_REALLOC,
   SF_FREE,
   SF_VASTART,
   SF_VACOPY,
   SF_SAMEOBJECT

 };

 extern DenseMap<Function*, specialfunctions> SpecialFunctionMap;
   
 inline bool functionIsBlacklisted(Function* F) {
   
   return GlobalIHP->blacklistedFunctions.count(F);
   
 }

 void noteBarrierInst(ShadowInstruction*);
 void executeSameObject(ShadowInstruction*);

 void doTLStoreMerge(ShadowBB* BB);
 void doTLCallMerge(ShadowBB* BB, InlineAttempt* IA);

 void doDSEStoreMerge(ShadowBB* BB);
 void doDSECallMerge(ShadowBB* BB, InlineAttempt* IA);

 void TLWalkPathConditions(ShadowBB* BB, bool contextEnabled, bool secondPass);
 void rerunTentativeLoads(ShadowInstruction*, InlineAttempt*, bool inLoopAnalyser);
 void patchReferences(std::vector<std::pair<WeakVH, uint32_t> >& Refs, Value* V);
 void forwardReferences(Value* Fwd, Module* M);
 Module* getGlobalModule();
 void setAllNeededTop(DSELocalStore*);
 bool IHPFoldIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, SmallVector<uint64_t, 4>& OpInts, ValSetType& ImpType, ImprovedVal& Improved);
 void DeleteDeadInstruction(Instruction *I);
 void createTopOrderingFrom(BasicBlock* BB, std::vector<BasicBlock*>& Result, SmallSet<BasicBlock*, 8>& Visited, LoopInfo* LI, const Loop* MyL);

 extern char ihp_workdir[];
 extern bool IHPSaveDOTFiles;

} // Namespace LLVM

#endif
