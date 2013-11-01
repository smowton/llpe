
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/IntervalMap.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Pass.h"
#include "llvm/Value.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constant.h"
#include "llvm/Argument.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/GlobalValue.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/RecyclingAllocator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <limits.h>
#include <string>
#include <vector>

#define LPDEBUG(x) DEBUG(do { printDebugHeader(dbgs()); dbgs() << ": " << x; } while(0))

namespace llvm {

class Function;
class BasicBlock;
class Instruction;
class AliasAnalysis;
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
class TerminatorInst;
class InlineAttempt;
class PeelAttempt;
class IntegrationHeuristicsPass;
class Function;
class LoopInfo;
class DataLayout;
class AliasAnalysis;
class Loop;
class IntegrationAttempt;
class PtrToIntInst;
class IntToPtrInst;
class BinaryOperator;
class DominatorTree;
template<class> class DominatorTreeBase;
template<class> class DomTreeNodeBase;
class IAWalker;
class BackwardIAWalker;
class ForwardIAWalker;
class raw_string_ostream;
class MemSetInst;
class MemTransferInst;
class ShadowLoopInvar;
class TargetLibraryInfo;
class EQTDDataStructures;
class ShadowBB;

inline void release_assert_fail(const char* str) {

  errs() << "Assertion failed: " << str << "\n";
  abort();

}

#define release_assert(x) if(!(x)) { release_assert_fail(#x); }

extern DataLayout* GlobalTD;
extern AliasAnalysis* GlobalAA;
extern TargetLibraryInfo* GlobalTLI;
extern EQTDDataStructures* GlobalDSA;
extern IntegrationHeuristicsPass* GlobalIHP;

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
  PathConditionTypeString,
  PathConditionTypeIntmem,
  PathConditionTypeFptrmem

};

struct PathCondition {

  uint32_t instStackIdx;
  BasicBlock* instBB;
  uint32_t instIdx;
  uint32_t fromStackIdx;
  BasicBlock* fromBB;
  Constant* val;
  uint64_t offset;

PathCondition(uint32_t isi, BasicBlock* ibi, uint32_t ii, uint32_t fsi, BasicBlock* fbi, Constant* v, uint64_t off) :
    instStackIdx(isi), instBB(ibi), instIdx(ii), 
    fromStackIdx(fsi), fromBB(fbi), val(v), offset(off) {}

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
  std::vector<PathFunc> FuncPathConditions;

  void addForType(PathCondition newCond, PathConditionTypes Ty) {

    switch(Ty) {
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
      IntmemPathConditions.push_back(newCond); break;
    case PathConditionTypeString:
      StringPathConditions.push_back(newCond); break;
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
  bool MayDelete;

OpenStatus(std::string N, bool Success) : Name(N), success(Success), MayDelete(false) { }
OpenStatus() : Name(""), success(false), MayDelete(false) {}

};

struct ReadFile {

  struct OpenStatus* openArg;
  uint64_t incomingOffset;
  uint32_t readSize;
  bool needsSeek;

ReadFile(struct OpenStatus* O, uint64_t IO, uint32_t RS) : openArg(O), incomingOffset(IO), readSize(RS), needsSeek(true) { }

ReadFile() : openArg(0), incomingOffset(0), readSize(0), needsSeek(true) { }

};

struct SeekFile {

  struct OpenStatus* openArg;
  uint64_t newOffset;
  bool MayDelete;

SeekFile(struct OpenStatus* O, uint64_t Off) : openArg(O), newOffset(Off), MayDelete(false) { }
SeekFile() : openArg(0), newOffset(0), MayDelete(false) { }

};

struct CloseFile {

  struct OpenStatus* openArg;
  bool MayDelete;
  ShadowInstruction* openInst;

CloseFile(struct OpenStatus* O, ShadowInstruction* I) : openArg(O), MayDelete(false), openInst(I) {}
CloseFile() : openArg(0), MayDelete(false), openInst(0) {}

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

class IntegrationHeuristicsPass : public ModulePass {

 public:

   DenseMap<Function*, LoopInfo*> LIs;
   DenseMap<Function*, ShadowFunctionInvar*> functionInfo;

   SmallSet<Function*, 4> alwaysInline;
   SmallSet<Function*, 4> alwaysExplore;
   DenseMap<const Loop*, std::pair<BasicBlock*, BasicBlock*> > optimisticLoopMap;
   DenseSet<const Loop*> alwaysIterLoops;
   DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1 > > assumeEdges;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoops;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > expandCallsLoops;
   DenseMap<std::pair<Function*, BasicBlock*>, uint64_t> maxLoopIters;
   DenseSet<LoadInst*> simpleVolatileLoads;
   
   DenseMap<ShadowInstruction*, std::string> optimisticForwardStatus;

   DataLayout* TD;
   AliasAnalysis* AA;

   InlineAttempt* RootIA;

   DenseMap<const GlobalVariable*, std::string> GVCache;
   DenseMap<const GlobalVariable*, std::string> GVCacheBrief;

   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > briefFunctionTextCache;

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

   DenseMap<Function*, std::vector<InlineAttempt*> > IAsByFunction;

   PathConditions pathConditions;

   SmallDenseMap<Function*, SpecialLocationDescriptor> specialLocations;
   SmallDenseMap<Function*, AllocatorFn, 4> allocatorFunctions;
   SmallDenseMap<Function*, DeallocatorFn, 4> deallocatorFunctions;
   SmallDenseMap<Function*, ReallocatorFn, 4> reallocatorFunctions;
   SmallDenseMap<Function*, Function*> modelFunctions;
   SmallPtrSet<Function*, 4> yieldFunctions;
   bool useDSA;

   std::pair<LocStore, uint32_t>* argStores;

   std::vector<std::pair<BasicBlock*, uint32_t> > targetCallStack;

   SmallSet<uint32_t, 4> forceNoAliasArgs;

   SmallVector<Function*, 4> commitFunctions;

   SmallDenseMap<CallInst*, std::vector<GlobalVariable*>, 4> lockDomains;
   SmallSet<CallInst*, 4> pessimisticLocks;

   DenseMap<ShadowInstruction*, AllocData> allocations;
   // Of an allocation or FD, record instructions that may use it in the emitted program.
   DenseMap<ShadowInstruction*, std::vector<ShadowValue> > indirectDIEUsers;
   // Of a successful copy instruction, records the values read.
   DenseMap<ShadowInstruction*, SmallVector<IVSRange, 4> > memcpyValues;

   DenseMap<ShadowInstruction*, OpenStatus*> forwardableOpenCalls;
   DenseMap<ShadowInstruction*, ReadFile> resolvedReadCalls;
   DenseMap<ShadowInstruction*, SeekFile> resolvedSeekCalls;
   DenseMap<ShadowInstruction*, CloseFile> resolvedCloseCalls;   
  
   void addSharableFunction(InlineAttempt*);
   void removeSharableFunction(InlineAttempt*);
   InlineAttempt* findIAMatching(ShadowInstruction*);

   uint64_t SeqNumber;
   bool mustRecomputeDIE;

   ShadowGV* shadowGlobals;

   std::vector<ShadowValue> heap;

   RecyclingAllocator<BumpPtrAllocator, ImprovedValSetSingle> IVSAllocator;

   bool verboseOverdef;
   bool enableSharing;
   bool verboseSharing;
   bool verbosePCs;

   Function* llioPreludeFn;
   std::string llioConfigFile;
   std::vector<std::string> llioDependentFiles;

   DenseSet<ShadowInstruction*> barrierInstructions;

   bool programSingleThreaded;

   DenseSet<std::pair<IntegrationAttempt*, const Loop*> > latchStoresRetained;

   GlobalStats stats;

   explicit IntegrationHeuristicsPass() : ModulePass(ID), cacheDisabled(false) { 

     mallocAlignment = 0;
     SeqNumber = 0;
     mustRecomputeDIE = false;

   }

   bool runOnModule(Module& M);

   void print(raw_ostream &OS, const Module* M) const;

   void releaseMemory(void);

   // Caching text representations of instructions:

   DenseMap<const Instruction*, std::string>& getFunctionCache(const Function* F, bool brief);
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

   void estimateIntegrationBenefit();

   virtual void getAnalysisUsage(AnalysisUsage &AU) const;

   bool shouldAlwaysInline(Function* F) {
     return alwaysInline.count(F);
   }

   bool shouldAlwaysExplore(Function* F) {
     return alwaysExplore.count(F);
   }
   
   std::pair<BasicBlock*, BasicBlock*> getOptimisticEdge(const Loop* L) {
     return optimisticLoopMap.lookup(L);
   }

   bool shouldAlwaysIterate(const Loop* L) {
     return alwaysIterLoops.count(L);
   }
   
   bool shouldAssumeEdge(Function* F, BasicBlock* BB1, BasicBlock* BB2) {
     DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1> >::iterator it = assumeEdges.find(F);
     if(it == assumeEdges.end())
       return false;
     return it->second.count(std::make_pair(BB1, BB2));
   }

   bool shouldIgnoreLoop(Function* F, BasicBlock* HBB) {
     DenseMap<Function*, SmallSet<BasicBlock*, 1> >::iterator it = ignoreLoops.find(F);
     if(it == ignoreLoops.end())
       return false;
     return it->second.count(HBB);
   }

   bool shouldExpandLoopCalls(Function* F, BasicBlock* HBB) {
     DenseMap<Function*, SmallSet<BasicBlock*, 1> >::iterator it = expandCallsLoops.find(F);
     if(it == expandCallsLoops.end())
       return false;
     return it->second.count(HBB);
   }

  const Loop* applyIgnoreLoops(const Loop*);

   bool assumeEndsAfter(Function* F, BasicBlock* HBB, uint64_t C) {
     DenseMap<std::pair<Function*, BasicBlock*>, uint64_t>::iterator it = maxLoopIters.find(std::make_pair(F, HBB));
     if(it == maxLoopIters.end())
       return false;
     return it->second == C;
   }

   bool volatileLoadIsSimple(LoadInst* LI) {

     return programSingleThreaded || simpleVolatileLoads.count(LI);

   }

   void runDSEAndDIE();
   void rerunDSEAndDIE();

   unsigned getMallocAlignment();

   ShadowFunctionInvar* getFunctionInvarInfo(Function& F);
   void getLoopInfo(DenseMap<const Loop*, ShadowLoopInvar*>& LoopInfo, 
		    DenseMap<BasicBlock*, uint32_t>& BBIndices, 
		    const Loop* L,
		    DominatorTree*);

   void initShadowGlobals(Module&, bool useInitialisers, uint32_t extraSlots);
   uint64_t getShadowGlobalIndex(GlobalVariable* GV) {
     return shadowGlobalsIdx[GV];
   }

   LocStore& getArgStore(ShadowArg*);

   uint64_t getSeq() {
     return SeqNumber++;
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

   void postCommitOptimise();
   void postCommitOptimiseF(Function* F);

   void initMRInfo(Module*);
   IHPFunctionInfo* getMRInfo(Function*);

   void releaseStoreMemory();

   void postCommitStats();

};

// Define a wrapper class for using the IHP's instruction text cache when printing instructions:
template<class T> class PrintCacheWrapper {

  IntegrationHeuristicsPass& IHP;
  T Val;
  bool brief;

 public:
 
 PrintCacheWrapper(IntegrationHeuristicsPass& _IHP, T _Val, bool _brief) : IHP(_IHP), Val(_Val), brief(_brief) { }
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

  GlobalIHP->IVSAllocator.Deallocate(I);

}

inline void deleteIV(ImprovedValSet* I) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(I))
    deleteIVS(IVS);
  else
    delete cast<ImprovedValSetMulti>(I);
  
}

inline ImprovedValSetSingle* copyIVS(ImprovedValSetSingle* IVS) {

  return new (GlobalIHP->IVSAllocator.Allocate()) ImprovedValSetSingle(*IVS);  

}

inline ImprovedValSet* copyIV(ImprovedValSet* IV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV))
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

  case SHADOWVAL_INVAL:
  default:
    release_assert(0 && "getImprovedValSetSingle on uninit value");
    llvm_unreachable();

  }

}

inline LocStore& ShadowValue::getBaseStore() {

  switch(t) {
  case SHADOWVAL_INST:
    return u.I->getAllocData()->store;
  case SHADOWVAL_GV:
    return u.GV->store;
  case SHADOWVAL_OTHER:
    {
      Function* KeyF = cast<Function>(u.V);
      return GlobalIHP->specialLocations[KeyF].store;
    }
  case SHADOWVAL_ARG:
    return GlobalIHP->getArgStore(u.A);
  default:
    assert(0 && "getBaseStore on non-inst, non-GV value");
    llvm_unreachable();
  }

}

raw_ostream& operator<<(raw_ostream&, const IntegrationAttempt&);

// Define PartialVal, a container that gives a resolution to a load attempt, either wholly with a value
// or partially with a Constant plus a byte extent and offset from which that Constant should be read.

enum PartialValType {

  PVEmpty,
  PVTotal,
  PVPartial,
  PVByteArray

};

struct PartialVal {

  // Might be empty, an SV, a constant with bounding parameters, or an array of bytes.
  PartialValType type;

  ImprovedVal TotalIV;
  ValSetType TotalIVType;

  // Used if it's a bounded constant:
  Constant* C;
  uint64_t ReadOffset;

  // Used if it's an array of bytes
  uint64_t* partialBuf;
  bool* partialValidBuf;
  uint64_t partialBufBytes;
  bool loadFinished;

  uint64_t markPaddingBytes(Type*);

  bool addPartialVal(PartialVal& PV, DataLayout* TD, std::string* error);
  bool isComplete();
  bool* getValidArray(uint64_t);
  bool convertToBytes(uint64_t, DataLayout*, std::string* error);
  bool combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, DataLayout* TD, std::string* error);

  void initByteArray(uint64_t);
  
  PartialVal(ValSetType TotalType, ImprovedVal Total) : 
  type(PVTotal), TotalIV(Total), TotalIVType(TotalType), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
  PartialVal(Constant* _C, uint64_t Off) : 
  type(PVPartial), TotalIV(), C(_C), ReadOffset(Off), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
 PartialVal() :
  type(PVEmpty), TotalIV(), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
  PartialVal(uint64_t nBytes); // Byte array constructor
  PartialVal(const PartialVal& Other);
  PartialVal& operator=(const PartialVal& Other);
  ~PartialVal();

  bool isPartial() { return type == PVPartial; }
  bool isTotal() { return type == PVTotal; }
  bool isEmpty() { return type == PVEmpty; }
  bool isByteArray() { return type == PVByteArray; }
  
  static PartialVal getPartial(Constant* _C, uint64_t Off) {
    return PartialVal(_C, Off);
  }

  static PartialVal getTotal(ValSetType Type, ImprovedVal IV) {
    return PartialVal(Type, IV);
  }
  
  static PartialVal getByteArray(uint64_t size) {
    return PartialVal(size);
  }

};

#define PVNull PartialVal()

inline bool operator==(PartialVal V1, PartialVal V2) {
  if(V1.type == PVEmpty && V2.type == PVEmpty)
    return true;
  else if(V1.type == PVTotal && V2.type == PVTotal)
    return V1.TotalIV == V2.TotalIV;
  else if(V1.type == PVPartial && V2.type == PVPartial)
    return ((V1.C == V2.C) &&
	    (V1.ReadOffset == V2.ReadOffset));
  else if(V1.type == PVByteArray && V2.type == PVByteArray) {
    if(V1.partialBufBytes != V2.partialBufBytes)
      return false;
    for(unsigned i = 0; i < V1.partialBufBytes; ++i) {
      if(V1.partialValidBuf[i] != V2.partialValidBuf[i])
	return false;
      if(V1.partialValidBuf[i] && (((char*)V1.partialBuf)[i]) != (((char*)V2.partialBuf)[i]))
	return false;
      return true;
    }
  }

  return false;
}

inline bool operator!=(PartialVal V1, PartialVal V2) {
   return !(V1 == V2);
}

class UnaryPred {
 public:
  virtual bool operator()(Value*) = 0;

};

class OpCallback {
 public:
  virtual void callback(IntegrationAttempt* Ctx, Value* V) = 0;

};

class VisitorContext {
public:

  virtual void visit(ShadowInstruction* UserI) = 0;
  virtual void notifyUsersMissed() = 0;
  virtual bool shouldContinue() = 0;

};

inline bool operator==(ImprovedValSetSingle& PB1, ImprovedValSetSingle& PB2) {

  if(PB1.SetType != PB2.SetType)
    return false;

  if(PB1.Overdef != PB2.Overdef)
    return false;

  if(PB1.Overdef)
    return true;

  if(PB1.Values.size() != PB2.Values.size())
    return false;

  std::sort(PB1.Values.begin(), PB1.Values.end());
  std::sort(PB2.Values.begin(), PB2.Values.end());

  for(unsigned i = 0; i < PB1.Values.size(); ++i)
    if(PB1.Values[i] != PB2.Values[i])
      return false;

  return true;

}

bool operator==(ImprovedValSetMulti& PB1, ImprovedValSetMulti& PB2);

inline bool operator!=(ImprovedValSetSingle& PB1, ImprovedValSetSingle& PB2) {

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

  IntegrationHeuristicsPass* pass;

  uint64_t SeqNumber;

  Function& F;
  const Loop* L;

  ShadowBB** BBs;
  uint32_t nBBs;
  // BBsOffset: offset from indices in the BBs array to invarInfo.BBs.
  // For inlineAttempts this is 0; for loop iterations it is the index of the loop's header
  // within the invar info.
  uint32_t BBsOffset;

  ShadowFunctionInvar* invarInfo;

  int64_t totalIntegrationGoodness;
  int64_t nDependentLoads;

  DenseMap<ShadowInstruction*, InlineAttempt*> inlineChildren;
  DenseMap<const Loop*, PeelAttempt*> peelChildren;

  uint32_t pendingEdges;

  BarrierState barrierState;

  bool tentativeLoadsRun;

  uint32_t checkedInstructionsHere;
  uint32_t checkedInstructionsChildren;

  BarrierState yieldState;

 IntegrationAttempt(IntegrationHeuristicsPass* Pass, Function& _F, 
		    const Loop* _L, int depth, int sdepth) : 
    improvableInstructions(0),
    improvedInstructions(0),
    residualInstructions(-1),
    nesting_depth(depth),
    stack_depth(sdepth),
    pass(Pass),
    F(_F),
    L(_L),
    totalIntegrationGoodness(0),
    nDependentLoads(0),
    inlineChildren(1),
    peelChildren(1),
    pendingEdges(0),
    barrierState(BARRIER_NONE),
    tentativeLoadsRun(false),
    checkedInstructionsHere(0),
    checkedInstructionsChildren(0),
    yieldState(BARRIER_NONE)
      { 
      }

  virtual ~IntegrationAttempt();

  Module& getModule();

  void markContextDead();

  Function& getFunction() { return F; }
  
  // virtual for external access:
  virtual bool edgeIsDead(ShadowBBInvar* BB1I, ShadowBBInvar* BB2I);
  bool edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I, bool ignoreThisScope = false);
  bool blockIsDeadRising(ShadowBBInvar& BBI);

  const Loop* applyIgnoreLoops(const Loop*);

  virtual bool entryBlockIsCertain() = 0;
  virtual bool entryBlockAssumed() = 0;

  virtual BasicBlock* getEntryBlock() = 0;
  
  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual void collectAllLoopStats() = 0;
  virtual void printHeader(raw_ostream& OS) const = 0;
  virtual bool isOptimisticPeel() = 0;

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
  virtual ShadowBBInvar* getBBInvar(uint32_t idx);
  ShadowBB* getUniqueBBRising(ShadowBBInvar* BBI);
  ShadowBB* createBB(uint32_t blockIdx);
  ShadowBB* createBB(ShadowBBInvar*);
  ShadowInstructionInvar* getInstInvar(uint32_t blockidx, uint32_t instidx);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx) = 0;
  ShadowInstruction* getInst(uint32_t blockIdx, uint32_t instIdx);
  virtual ShadowInstruction* getInst(ShadowInstructionInvar* SII);
  ShadowInstruction* getMostLocalInst(uint32_t blockIdx, uint32_t instIdx);

  // The toplevel loop:
  void analyse();
  bool analyse(bool inLoopAnalyser, bool inAnyLoop, uint32_t new_stack_depth);
  bool analyseBlock(uint32_t& BBIdx, bool inLoopAnalyser, bool inAnyLoop, bool skipStoreMerge, const Loop* MyL);
  bool analyseBlockInstructions(ShadowBB* BB, bool skipSuccessorCreation, bool inLoopAnalyser, bool inAnyLoop);
  bool analyseLoop(const Loop*, bool nestedLoop);
  void releaseLatchStores(const Loop*);
  virtual void getInitialStore() = 0;
  // Toplevel, execute-only version:
  void execute(uint32_t new_stack_depth);
  void executeBlock(ShadowBB*);
  void executeLoop(const Loop*);


  // Constant propagation:

  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result);
  bool tryEvaluate(ShadowValue V, bool inLoopAnalyser, bool& loadedVararg);
  bool getNewPB(ShadowInstruction* SI, ImprovedValSet*& NewPB, bool& loadedVararg);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSet*& NewPB);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSetSingle& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx);
  void tryEvaluateResult(ShadowInstruction* SI, 
			 std::pair<ValSetType, ImprovedVal>* Ops, 
			 ValSetType& ImpType, ImprovedVal& Improved,
			 unsigned char* needsRuntimeCheck);
  bool tryFoldBitwiseOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldPtrAsIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldPointerCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved, unsigned char* needsRuntimeCheck);
  bool tryFoldNonConstCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldOpenCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  void getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs = 0, bool readFromNonTerminatedLoop = false);
  void getOperandRising(ShadowInstruction* SI, uint32_t valOpIdx, ShadowBBInvar* ExitingBB, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs, bool readFromNonTerminatedLoop);
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

  // CFG analysis:

  bool createEntryBlock();
  bool tryEvaluateTerminator(ShadowInstruction* SI, bool tagSuccVararg);
  bool tryEvaluateTerminatorInst(ShadowInstruction* SI);
  IntegrationAttempt* getIAForScope(const Loop* Scope);
  virtual IntegrationAttempt* getIAForScopeFalling(const Loop* Scope) = 0;
  void setBlockStatus(ShadowBBInvar* BB, ShadowBBStatus);
  bool shouldAssumeEdge(BasicBlock* BB1, BasicBlock* BB2) {
    return pass->shouldAssumeEdge(&F, BB1, BB2);
  }
  void copyLoopExitingDeadEdges(PeelAttempt* LPA);
  virtual IntegrationAttempt* getUniqueParent() = 0;
  void checkBlockStatus(ShadowBB*, bool inLoopAnalyser);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(ShadowInstruction* CI);
  virtual bool stackIncludesCallTo(Function*) = 0;
  bool shouldInlineFunction(ShadowInstruction*, Function*);
  InlineAttempt* getOrCreateInlineAttempt(ShadowInstruction* CI, bool ignoreScope, bool& created, bool& needsAnalyse);
  bool callCanExpand(ShadowInstruction* Call, InlineAttempt*& Result);
  bool analyseExpandableCall(ShadowInstruction* SI, bool& changed, bool inLoopAnalyser, bool inAnyLoop);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  bool tryResolveLoadFromConstant(ShadowInstruction*, ImprovedVal Ptr, ImprovedValSetSingle& Result);
  bool tryResolveLoadFromVararg(ShadowInstruction* LoadI, ImprovedValSet*& Result);
  bool tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSet*& NewPB, bool& loadedVararg);
  bool getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result);
  virtual void applyMemoryPathConditions(ShadowBB*);
  void applyMemoryPathConditionsFrom(ShadowBB*, PathConditions&, uint32_t);
  void applyPathCondition(PathCondition*, PathConditionTypes, ShadowBB*, uint32_t);
  ShadowValue getPathConditionOperand(uint32_t stackIdx, BasicBlock* BB, uint32_t instIdx);

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

  virtual int64_t tryGetIncomingOffset(ShadowInstruction*);
  virtual ReadFile* tryGetReadFile(ShadowInstruction* CI);
  bool tryPromoteOpenCall(ShadowInstruction* CI);
  void tryPromoteAllCalls();
  bool tryResolveVFSCall(ShadowInstruction*);
  bool executeStatCall(ShadowInstruction* SI, Function* F, std::string& Filename);
  WalkInstructionResult isVfsCallUsingFD(ShadowInstruction* VFSCall, ShadowInstruction* FD, bool ignoreClose);
  virtual void resolveReadCall(ShadowInstruction*, struct ReadFile);
  virtual void resolveSeekCall(ShadowInstruction*, struct SeekFile);
  bool isResolvedVFSCall(ShadowInstruction*);
  bool VFSCallWillUseFD(ShadowInstruction*);
  bool isUnusedReadCall(ShadowInstruction*);
  bool isCloseCall(ShadowInstruction*);
  OpenStatus& getOpenStatus(ShadowInstruction*);
  void tryKillAllVFSOps();
  void markCloseCall(ShadowInstruction*);

  // Load forwarding extensions for varargs:
  virtual void getVarArg(int64_t, ImprovedValSet*&) = 0;
  void disableChildVarargsContexts();
  bool isVarargsTainted();
  
  // Dead store and allocation elim:

  void DSEHandleRead(ShadowValue PtrOp, uint64_t Size, ShadowBB* BB);
  void DSEHandleWrite(ShadowValue PtrOp, uint64_t Size, ShadowInstruction* Writer, ShadowBB* BB);
  void tryKillStoresInLoop(const Loop* L, bool commitDisabledHere, bool disableWrites, bool latchToHeader = false);

  // User visitors:
  
  virtual bool visitNextIterationPHI(ShadowInstructionInvar* I, VisitorContext& Visitor);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor) = 0;
  void visitUsers(ShadowValue, VisitorContext& Visitor);
  void visitUser(ShadowInstIdx&, VisitorContext& Visitor);

  // Dead instruction elim:

  bool valueIsDead(ShadowValue);
  bool shouldDIE(ShadowInstruction* V);
  virtual void runDIE();
  void resetDeadInstructions();

  virtual bool ctxContains(IntegrationAttempt*) = 0;
  bool shouldCheckPB(ShadowValue);
  void analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);

  // Enabling / disabling exploration:

  virtual bool isEnabled() = 0;
  virtual void setEnabled(bool, bool skipStats) = 0;
  bool unsharedContextAvailable();
  bool allocasAvailableFrom(IntegrationAttempt*);
  bool heapObjectsAvailableFrom(IntegrationAttempt*);
  virtual bool commitsOutOfLine() = 0;

  // Estimating inlining / unrolling benefit:

  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&);
  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&);
  int64_t getResidualInstructions();
  virtual void reduceDependentLoads(int64_t) = 0;
  void countDependentLoads();
  void propagateDependentLoads();

  // DOT export:

  bool noteChildBarriers();
  bool noteChildYields();
  void countTentativeInstructions();
  void printRHS(ShadowValue, raw_ostream& Out);
  void printOutgoingEdge(ShadowBBInvar* BBI, ShadowBB* BB, ShadowBBInvar* SBI, ShadowBB* SB, uint32_t i, bool useLabels, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief);
  void describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBBInvar*, 4>* forceSuccessors, bool brief, bool plain = false);
  void describeScopeAsDOT(const Loop* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief, SmallVector<std::string, 4>* deferredEdges);
  void describeLoopAsDOT(const Loop* L, uint32_t headerIdx, raw_ostream& Out, bool brief);
  void describeAsDOT(raw_ostream& Out, bool brief);
  std::string getValueColour(ShadowValue, std::string& textColour, bool plain = false);
  std::string getGraphPath(std::string prefix);
  void describeTreeAsDOT(std::string path);
  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) = 0;
  bool blockLiveInAnyScope(ShadowBBInvar* BB);
  virtual void printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB);

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
  void localPrepareCommit();
  virtual std::string getCommittedBlockPrefix() = 0;
  void commitCFG();
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
  bool canSynthVal(ShadowInstruction* I, ValSetType Ty, ImprovedVal& IV);
  bool canSynthPointer(ShadowValue* I, ImprovedVal IV);
  bool canSynthMTI(ShadowInstruction* I);
  void emitChunk(ShadowInstruction* I, BasicBlock* emitBB, SmallVector<IVSRange, 4>::iterator chunkBegin, SmallVector<IVSRange, 4>::iterator chunkEnd);
  bool trySynthMTI(ShadowInstruction* I, BasicBlock* emitBB);
  Value* trySynthVal(ShadowInstruction* I, Type* targetType, ValSetType Ty, ImprovedVal& IV, BasicBlock* emitBB);
  bool trySynthInst(ShadowInstruction* I, BasicBlock* emitBB, Value*& Result);
  void emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, SmallVector<CommittedBlock, 1>::iterator& emitBB);
  void commitLoopInstructions(const Loop* ScopeL, uint32_t& i);
  void commitInstructions();

  // Function sharing

  void noteDependency(ShadowValue V);
  void noteMalloc(ShadowInstruction* SI);
  void noteVFSOp();
  void mergeChildDependencies(InlineAttempt* ChildIA);
  virtual void sharingInit();
  virtual void sharingCleanup();

  // Conditional specialisation

  void checkTargetStack(ShadowInstruction* SI, InlineAttempt* IA);
  bool shouldIgnoreEdge(ShadowBBInvar*, ShadowBBInvar*);
  bool hasLiveIgnoredEdges(ShadowBB*);
  virtual void initFailedBlockCommit();
  virtual void finishFailedBlockCommit();
  uint32_t collectSpecIncomingEdges(uint32_t blockIdx, uint32_t instIdx, SmallVector<std::pair<BasicBlock*, IntegrationAttempt*>, 4>& edges);
  Value* getSpecValue(uint32_t blockIdx, uint32_t instIdx, Value* V);
  virtual void commitSimpleFailedBlock(uint32_t i);
  void getSplitInsts(ShadowBBInvar*, bool* splits);
  virtual void createFailedBlock(uint32_t idx);
  void collectSpecPreds(ShadowBBInvar* predBlock, uint32_t predIdx, ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds);
  void collectCallFailingEdges(ShadowBBInvar* predBlock, uint32_t predIdx, ShadowBBInvar* instBlock, uint32_t instIdx, SmallVector<std::pair<Value*, BasicBlock*>, 4>& preds);
  virtual void populateFailedBlock(uint32_t idx);
  virtual void populateFailedHeaderPHIs(const Loop*);
  Value* emitCompareCheck(Value* realInst, ImprovedValSetSingle* IVS, BasicBlock* emitBB);
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

  // Tentative load determination
  
  ThreadLocalState shouldCheckCopy(ShadowInstruction& SI, ShadowValue PtrOp, ShadowValue LenSV);
  ThreadLocalState shouldCheckLoadFrom(ShadowInstruction& SI, ImprovedVal& Ptr, uint64_t LoadSize);
  ThreadLocalState shouldCheckLoad(ShadowInstruction& SI);
  void findTentativeLoadsInLoop(const Loop* L, bool commitDisabledHere, bool secondPass, bool latchToHeader = false);
  void resetTentativeLoads();
  bool requiresRuntimeCheck2(ShadowValue V, bool includeSpecialChecks);
  bool containsTentativeLoads();
  void addCheckpointFailedBlocks();

  // Stat collection and printing:

  void collectAllBlockStats();
  void collectBlockStats(ShadowBBInvar* BBI, ShadowBB* BB);
  void collectLoopStats(const Loop*);
  void collectStats();
  virtual void preCommitStats(bool enabledHere);

  void print(raw_ostream& OS) const;
  // Callable from GDB
  void dump() const;

  virtual void describe(raw_ostream& Stream) const = 0;
  virtual void describeBrief(raw_ostream& Stream) const = 0;
  virtual std::string getFunctionName();
  virtual int getIterCount() = 0;

  void printDebugHeader(raw_ostream& Str) {
    printHeader(Str);
  }

  void dumpMemoryUsage(int indent = 0);

  void testLoadWalk(LoadInst* LI);

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  PeelAttempt* parentPA;

public:

  PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, int iter, int depth);

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

  void visitVariant(ShadowInstructionInvar* VI, VisitorContext& Visitor); 
  virtual bool visitNextIterationPHI(ShadowInstructionInvar* I, VisitorContext& Visitor); 

  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out); 

  virtual void describe(raw_ostream& Stream) const;
  virtual void describeBrief(raw_ostream& Stream) const;

  virtual void collectAllLoopStats(); 

  virtual std::string getShortHeader(); 

  virtual bool canDisable(); 
  virtual bool isEnabled(); 
  virtual void setEnabled(bool, bool skipStats); 

  virtual bool isOptimisticPeel(); 

  virtual void getVarArg(int64_t, ImprovedValSet*&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  virtual bool stackIncludesCallTo(Function*); 

  virtual void reduceDependentLoads(int64_t); 

  virtual WalkInstructionResult queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* ctx); 
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc); 

  virtual bool entryBlockIsCertain(); 
  virtual bool entryBlockAssumed(); 

  bool isOnlyExitingIteration(); 
  bool allExitEdgesDead(); 
  void dropExitingStoreRef(uint32_t, uint32_t);

  virtual int getIterCount() {
    return iterationCount;
  }

  void prepareShadows();
  virtual std::string getCommittedBlockPrefix();
  virtual BasicBlock* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor);

  virtual void getInitialStore();

  virtual IntegrationAttempt* getIAForScopeFalling(const Loop* Scope);
  virtual void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual IntegrationAttempt* getUniqueParent();
  virtual ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx);
  virtual bool commitsOutOfLine();
  virtual void popAllocas(OrdinaryLocalStore*);

  virtual void printHeader(raw_ostream& OS) const;

};

class ProcessExternalCallback;

class PeelAttempt {
   // Not a subclass of IntegrationAttempt -- this is just a helper.

   IntegrationHeuristicsPass* pass;
   IntegrationAttempt* parent;
   Function& F;

   uint64_t SeqNumber;

   std::string HeaderStr;

   int64_t residualInstructions;

   int nesting_depth;
   int stack_depth;
   int debugIndent;

   bool enabled;

 public:

   const Loop* L;

   int64_t totalIntegrationGoodness;
   int64_t nDependentLoads;

   ShadowLoopInvar* invarInfo;

   std::vector<PeelIteration*> Iterations;

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, const Loop* _L, int depth);
   ~PeelAttempt();

   bool analyse(uint32_t parent_stack_depth);

   PeelIteration* getIteration(unsigned iter); 
   PeelIteration* getOrCreateIteration(unsigned iter); 

   void visitVariant(ShadowInstructionInvar* VI, VisitorContext& Visitor); 
   
   void describeTreeAsDOT(std::string path); 

   bool allNonFinalIterationsDoNotExit(); 

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
   
   void reduceDependentLoads(int64_t); 

   void dumpMemoryUsage(int indent); 

   int64_t getResidualInstructions(); 
   void findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty);
   void countDependentLoads(); 
   void propagateDependentLoads(); 

   bool isTerminated() {
     return Iterations.back()->iterStatus == IterationStatusFinal;
   }

   void getShadowInfo();

   void dropExitingStoreRefs();
   void dropNonterminatedStoreRefs();

   bool containsTentativeLoads();

  IntegratorTag* createTag(IntegratorTag* parent);

 };

// Members only needed for an IA with a target call
struct IATargetInfo {

  uint32_t targetCallBlock;
  uint32_t targetCallInst;
  uint32_t targetStackDepth;
  DenseSet<uint32_t> mayReachTarget;
  DenseSet<uint32_t> mayFollowTarget;

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

  InlineAttempt(IntegrationHeuristicsPass* Pass, Function& F, ShadowInstruction* _CI, int depth, bool isPathCond = false);

  virtual ~InlineAttempt();

  SmallVector<ShadowInstruction*, 1> Callers;
  ShadowInstruction* activeCaller;

  Function* CommitF;
  BasicBlock* returnBlock;
  PHINode* returnPHI;
  BasicBlock* failedReturnBlock;
  PHINode* failedReturnPHI;

  ImmutableArray<ShadowArg> argShadows;

  std::vector<ShadowInstruction*> localAllocas;
  ShadowInstruction* getAllocaWithIdx(uint32_t i) {
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

  IATargetInfo* targetCallInfo;

  SharingState* sharing;

  DominatorTree* DT;
  SmallDenseMap<uint32_t, uint32_t, 8>* blocksReachableOnFailure;
  std::vector<SmallVector<std::pair<BasicBlock*, uint32_t>, 1> > failedBlocks;
  ValueToValueMapTy* failedBlockMap;
  // Indexes from CLONED instruction/block to replacement PHI node to use in that block.
  DenseMap<std::pair<Instruction*, BasicBlock*>, PHINode*>* PHIForwards;
  DenseSet<PHINode*>* ForwardingPHIs;

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

  virtual bool isOptimisticPeel(); 

  virtual void getVarArg(int64_t, ImprovedValSet*&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  int64_t NonFPArgIdxToArgIdx(int64_t idx);
  int64_t FPArgIdxToArgIdx(int64_t idx);

  virtual void reduceDependentLoads(int64_t); 

  virtual int getIterCount() {
    return -1;
  }

  virtual bool stackIncludesCallTo(Function*); 

  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&); 
  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&); 

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
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor);

  Value* getArgCommittedValue(ShadowArg* SA);
  void commitArgsAndInstructions();

  void resetDeadArgsAndInstructions();

  virtual void getInitialStore();

  // Function sharing:

  void clearExternalDependencies();
  virtual void sharingInit();
  void dumpSharingState();
  virtual void sharingCleanup();
  bool matchesCallerEnvironment(ShadowInstruction* SI);
  InlineAttempt* getWritableCopyFrom(ShadowInstruction* SI);
  void dropReferenceFrom(ShadowInstruction* SI);

  virtual IntegrationAttempt* getIAForScopeFalling(const Loop* Scope);
  virtual void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual IntegrationAttempt* getUniqueParent();
  bool isRootMainCall();
  virtual ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  virtual ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx);
  virtual bool commitsOutOfLine();
  void executeCall(uint32_t new_stack_depth);
  void releaseCallLatchStores();
  virtual bool tryGetPathValue2(ShadowValue V, ShadowBB* UserBlock, std::pair<ValSetType, ImprovedVal>& Result, bool asDef);
  virtual void applyMemoryPathConditions(ShadowBB*);
  void addIgnoredBlock(std::string& name);
  virtual void addExtraTags(IntegratorTag* myTag);
  void addExtraTagsFrom(PathConditions&, IntegratorTag* myTag);

  // Conditional specialisation:
  void addBlockAndSuccs(uint32_t idx, DenseSet<uint32_t>& Set, bool skipFirst);
  void addBlockAndPreds(uint32_t idx, DenseSet<uint32_t>& Set);
  void markBlockAndSuccsFailed(uint32_t idx, uint32_t instIdx);
  void setTargetCall(std::pair<BasicBlock*, uint32_t>& arg, uint32_t stackIdx);
  virtual BasicBlock* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  void getFailedReturnBlocks(SmallVector<BasicBlock*, 4>& rets);
  bool hasFailedReturnPath();
  virtual void initFailedBlockCommit();
  virtual void finishFailedBlockCommit();
  void markBBAndPreds(ShadowBBInvar* UseBBI, uint32_t instIdx, std::vector<std::pair<Instruction*, uint32_t> >& predBlocks, ShadowBBInvar* LimitBBI);
  bool isSpecToUnspecEdge(uint32_t predBlockIdx, uint32_t BBIdx);
  bool isSimpleMergeBlock(uint32_t i);
  BasicBlock::iterator skipMergePHIs(BasicBlock::iterator it);
  void createForwardingPHIs(ShadowInstructionInvar& OrigSI, Instruction* NewI);
  Value* getLocalFailedValue(Value* V, BasicBlock*);
  Value* tryGetLocalFailedValue(Value* V, BasicBlock*);
  Value* getUnspecValue(uint32_t blockIdx, uint32_t instIdx, Value* V, BasicBlock* BB);
  BasicBlock::iterator commitFailedPHIs(BasicBlock* BB, BasicBlock::iterator BI, uint32_t BBIdx);
  void remapFailedBlock(BasicBlock::iterator BI, BasicBlock* BB, uint32_t blockIdx, uint32_t instIdx, bool skipTestedInst, bool skipTerm);
  virtual void commitSimpleFailedBlock(uint32_t i);
  virtual void popAllocas(OrdinaryLocalStore*);
  virtual void createFailedBlock(uint32_t idx);
  virtual void populateFailedBlock(uint32_t idx);
  virtual void populateFailedHeaderPHIs(const Loop* PopulateL);
  BasicBlock* getSubBlockForInst(uint32_t, uint32_t);

  void tryKillStores(bool commitDisabledHere, bool disableWrites);

  void findTentativeLoads(bool commitDisabledHere, bool secondPass);
  void rerunTentativeLoads();

  virtual void printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB);
  virtual void noteAsExpectedChecks(ShadowBB* BB);

  virtual void printHeader(raw_ostream& OS) const;

  virtual void preCommitStats(bool enabledHere);
  
};

inline int32_t getFrameSize(InlineAttempt* IA) {
  return IA->invarInfo->frameSize;
}

inline bool hasNoCallers(InlineAttempt* IA) {

  return IA->Callers.empty();

}

inline ShadowValue getStackAllocationWithIndex(InlineAttempt* IA, uint32_t i) {
  return IA->getAllocaWithIdx(i);
}

inline IntegrationAttempt* ShadowValue::getCtx() {

  switch(t) {
  case SHADOWVAL_ARG:
    return u.A->IA;
  case SHADOWVAL_INST:
    return u.I->parent->IA;
  default:
    return 0;
  }

}

 Constant* extractAggregateMemberAt(Constant* From, int64_t Offset, Type* Target, uint64_t TargetSize, DataLayout*);
 Constant* constFromBytes(unsigned char*, Type*, DataLayout*);
 bool allowTotalDefnImplicitCast(Type* From, Type* To);
 bool allowTotalDefnImplicitPtrToInt(Type* From, Type* To, DataLayout*);
 std::string ind(int i);
 const Loop* immediateChildLoop(const Loop* Parent, const Loop* Child);
 Constant* getConstReplacement(Value*, IntegrationAttempt*);
 Constant* intFromBytes(const uint64_t*, unsigned, unsigned, llvm::LLVMContext&);
 
 // Implemented in Transforms/Integrator/SimpleVFSEval.cpp, so only usable with -integrator
 bool getFileBytes(std::string& strFileName, uint64_t realFilePos, uint64_t realBytes, std::vector<Constant*>& arrayBytes, LLVMContext& Context, std::string& errors);

 // Implemented in Support/AsmWriter.cpp, since that file contains a bunch of useful private classes
 void getInstructionsText(const Function* IF, DenseMap<const Instruction*, std::string>& IMap, DenseMap<const Instruction*, std::string>& BriefMap);
 void getGVText(const Module* M, DenseMap<const GlobalVariable*, std::string>& GVMap, DenseMap<const GlobalVariable*, std::string>& BriefGVMap);

 bool isGlobalIdentifiedObject(ShadowValue VC);
 bool shouldQueueOnInst(Instruction* I, IntegrationAttempt* ICtx);
 uint32_t getInitialBytesOnStack(Function& F);
 uint32_t getInitialFPBytesOnStack(Function& F);

 bool GetDefinedRange(ShadowValue DefinedBase, int64_t DefinedOffset, uint64_t DefinedSize,
		      ShadowValue DefinerBase, int64_t DefinerOffset, uint64_t DefinerSize,
		      uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset);

 bool getPBFromCopy(ShadowValue copySource, ShadowInstruction* copyInst, uint64_t ReadOffset, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t ReadSize, Type* originalType, bool* validBytes, ImprovedValSetSingle& NewPB, std::string& error, BasicBlock* ctBB, IntegrationAttempt* ctIA);
 bool getMemsetPV(ShadowInstruction* MSI, uint64_t nbytes, PartialVal& NewPV, std::string& error);
 bool getMemcpyPB(ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, Type* originalType, bool* validBytes, PartialVal& NewPV, ImprovedValSetSingle& NewPB, std::string& error, BasicBlock* ctBB, IntegrationAttempt* ctIA);
 bool getVaStartPV(ShadowInstruction* CI, int64_t ReadOffset, PartialVal& NewPV, std::string& error);
 bool getReallocPB(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, Type* originalType, bool* validBytes, ImprovedValSetSingle& NewPB, std::string& error, BasicBlock* ctBB, IntegrationAttempt* ctIA);
 bool getVaCopyPB(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, Type* originalType, bool* validBytes, ImprovedValSetSingle& NewPB, std::string& error, BasicBlock* ctBB, IntegrationAttempt* ctIA);
 bool getReadPV(ShadowInstruction* SI, uint64_t nbytes, int64_t ReadOffset, PartialVal& NewPV, std::string& error);

 enum SVAAResult {
   SVNoAlias,
   SVMayAlias,
   SVPartialAlias,
   SVMustAlias
 };

 SVAAResult tryResolveImprovedValSetSingles(ImprovedValSetSingle& PB1, uint64_t V1Size, ImprovedValSetSingle& PB2, uint64_t V2Size, bool usePBKnowledge);
 SVAAResult tryResolveImprovedValSetSingles(ShadowValue V1Base, int64_t V1Offset, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge);
 SVAAResult tryResolveImprovedValSetSingles(ShadowValue V1, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge);
 
 bool basesAlias(ShadowValue, ShadowValue);

 bool tryCopyDeadEdges(ShadowBB* FromBB, ShadowBB* ToBB, bool& changed);

 bool willBeDeleted(ShadowValue);
 bool willBeReplacedOrDeleted(ShadowValue);
 bool willBeReplacedWithConstantOrDeleted(ShadowValue);

 bool instructionCounts(Instruction* I);

 Function* getCalledFunction(ShadowInstruction*);

 int64_t getSpilledVarargAfter(ShadowInstruction* CI, int64_t OldArg);

 bool blockCertainlyExecutes(ShadowBB*);
 bool blockAssumedToExecute(ShadowBB*);

 Function* cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name, bool addFailedReturnFlag);

 Constant* getGVOffset(Constant* GV, int64_t Offset, Type* targetType);


 // Load forwarding v3 functions:
 bool addIVSToPartialVal(ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error);
 void readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, bool& shouldTryMulti, std::string* error);
 void readValRange(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, ImprovedValSetMulti** ResultMulti, std::string* error);
 void executeStoreInst(ShadowInstruction* StoreSI);
 void executeMemsetInst(ShadowInstruction* MemsetSI);
 void propagateStoreFlags(ImprovedValSetSingle& WrittenPtr, ImprovedValSetSingle& WrittenVal, ShadowBB* StoreBB);

 void getIVSSubVals(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest);
 void getIVSSubVal(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, ImprovedValSetSingle& Dest);
 void getConstSubVals(Constant* FromC, uint64_t Offset, uint64_t TargetSize, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest);
 Constant* valsToConst(SmallVector<IVSRange, 4>& subVals, uint64_t TargetSize, Type* targetType);
 void getConstSubVal(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* TargetType, ImprovedValSetSingle& Result);
 Constant* getSubConst(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* targetType = 0);
 void clearRange(ImprovedValSetMulti* M, uint64_t Offset, uint64_t Size);
 void replaceRangeWithPB(ImprovedValSet* Target, ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size);
 void replaceRangeWithPBs(ImprovedValSet* Target, SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size);
 void truncateConstVal(ImprovedValSetMulti::MapIt& it, uint64_t off, uint64_t size);
 void truncateRight(ImprovedValSetMulti::MapIt& it, uint64_t n);
 void truncateLeft(ImprovedValSetMulti::MapIt& it, uint64_t n);
 bool canTruncate(ImprovedValSetSingle& S);

 void readValRangeMultiFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore);
 void readValRangeMulti(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, SmallVector<IVSRange, 4>& Results);
 void executeMemcpyInst(ShadowInstruction* MemcpySI);
 void executeVaCopyInst(ShadowInstruction* SI);
 void executeAllocInst(ShadowInstruction* SI, Type* AllocType, uint64_t AllocSize, bool trackAlloc);
 void executeAllocaInst(ShadowInstruction* SI);
 void executeMallocLikeInst(ShadowInstruction* SI);
 void executeReallocInst(ShadowInstruction* SI, Function*);
 void executeFreeInst(ShadowInstruction* SI, Function*);
 void executeCopyInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowInstruction*);
 void executeVaStartInst(ShadowInstruction* SI);
 void executeReadInst(ShadowInstruction* ReadSI, OpenStatus& OS, uint64_t FileOffset, uint64_t Size);
 void executeUnexpandedCall(ShadowInstruction* SI);
 bool clobberSyscallModLocations(Function* F, ShadowInstruction* SI);
 void executeWriteInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowInstruction*);
 void writeExtents(SmallVector<IVSRange, 4>& copyValues, ShadowValue& Ptr, int64_t Offset, uint64_t Size, ShadowBB* BB);

 Constant* PVToConst(PartialVal& PV, raw_string_ostream* RSO, uint64_t Size, LLVMContext&);

 void commitStoreToBase(OrdinaryLocalStore* Map);
 void commitFrameToBase(SharedStoreMap<LocStore, OrdinaryStoreExtraState>* Map);
 bool doBlockStoreMerge(ShadowBB* BB);
 void doCallStoreMerge(ShadowInstruction* SI);
 void doCallStoreMerge(ShadowBB* BB, InlineAttempt* IA);
 
 void initSpecialFunctionsMap(Module& M);
 
 void printPB(raw_ostream& out, ImprovedValSetSingle PB, bool brief = false);

 ShadowValue& getAllocWithIdx(int32_t);
 void addHeapAlloc(ShadowInstruction*);

 IntegratorTag* searchFunctions(IntegratorTag* thisTag, std::string&, IntegratorTag*& startAt);

 GlobalVariable* getStringArray(std::string& bytes, Module& M, bool addNull=false);

 uint32_t findBlock(ShadowFunctionInvar* SFI, BasicBlock* BB);
 uint32_t findBlock(ShadowFunctionInvar* SFI, StringRef name);
 InlineAttempt* getIAWithTargetStackDepth(InlineAttempt* IA, uint32_t depth);

 Value* getCommittedValue(ShadowValue SV);
 Value* getValAsType(Value* V, Type* Ty, Instruction* insertBefore);
 Value* getValAsType(Value* V, Type* Ty, BasicBlock* insertAtEnd);

 void valueEscaped(ShadowValue, ShadowBB*);
 void intersectSets(DenseSet<ShadowValue>* Target, MutableArrayRef<DenseSet<ShadowValue>* > Merge);

 bool requiresRuntimeCheck(ShadowValue V, bool includeSpecialChecks);
 PHINode* makePHI(Type* Ty, const Twine& Name, BasicBlock* emitBB);
 
 void releaseIndirectUse(ShadowValue V, ImprovedValSet* OldPB);
 void noteIndirectUse(ShadowValue V, ImprovedValSet* NewPB);
 void printPathCondition(PathCondition& PC, PathConditionTypes t, ShadowBB* BB, raw_ostream& Out, bool HTMLEscaped);
 void emitRuntimePrint(BasicBlock* BB, std::string& message, Value* param);
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
   
 struct IntAAProxy {

   virtual bool isNoAliasPBs(ShadowValue Ptr1Base, int64_t Ptr1Offset, uint64_t Ptr1Size, ShadowValue Ptr2, uint64_t Ptr2Size);

 };

 inline bool functionIsBlacklisted(Function* F) {
   
   return GlobalIHP->blacklistedFunctions.count(F);
   
 }

 void noteBarrierInst(ShadowInstruction*);
 void executeSameObject(ShadowInstruction*);

} // Namespace LLVM

#endif
