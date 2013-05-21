
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/IntervalMap.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Pass.h"
#include "llvm/Value.h"
#include "llvm/Constant.h"
#include "llvm/Argument.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/GlobalValue.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Support/raw_ostream.h"

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
class PostDominatorTree;
class LoopWrapper;
template<class> class DominatorTreeBase;
class BBWrapper;
template<class> class DomTreeNodeBase;
class IAWalker;
class BackwardIAWalker;
class ForwardIAWalker;
class raw_string_ostream;
class MemSetInst;
class MemTransferInst;
class ShadowLoopInvar;
class TargetLibraryInfo;
 class VFSCallAliasAnalysis;

bool functionIsBlacklisted(Function*);

inline void release_assert_fail(const char* str) {

  errs() << "Assertion failed: " << str << "\n";
  abort();

}

#define release_assert(x) if(!(x)) { release_assert_fail(#x); }

extern DataLayout* GlobalTD;
extern AliasAnalysis* GlobalAA;
extern VFSCallAliasAnalysis* GlobalVFSAA;
extern TargetLibraryInfo* GlobalTLI;
extern IntegrationHeuristicsPass* GlobalIHP;

// Include structures and functions for working with instruction and argument shadows.
#include "ShadowInlines.h"

class VFSCallModRef;

class IntegrationHeuristicsPass : public ModulePass {

   DenseMap<Function*, LoopInfo*> LIs;
   DenseMap<Function*, DenseMap<Instruction*, const Loop*>* > invariantInstScopes;
   DenseMap<Function*, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* > invariantEdgeScopes;
   DenseMap<Function*, DenseMap<BasicBlock*, const Loop*>* > invariantBlockScopes;
   DenseMap<Function*, ShadowFunctionInvar*> functionInfo;

   DenseMap<const Loop*, std::pair<LoopWrapper*, DominatorTreeBase<BBWrapper>*> > LoopPDTs;

   SmallSet<Function*, 4> alwaysInline;
   SmallSet<Function*, 4> alwaysExplore;
   DenseMap<const Loop*, std::pair<BasicBlock*, BasicBlock*> > optimisticLoopMap;
   DenseSet<const Loop*> alwaysIterLoops;
   DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1 > > assumeEdges;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoops;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > expandCallsLoops;
   DenseMap<std::pair<Function*, BasicBlock*>, uint64_t> maxLoopIters;

   DataLayout* TD;
   AliasAnalysis* AA;

   InlineAttempt* RootIA;

   DenseMap<const GlobalVariable*, std::string> GVCache;
   DenseMap<const GlobalVariable*, std::string> GVCacheBrief;

   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > briefFunctionTextCache;

   DenseMap<GlobalVariable*, uint64_t> shadowGlobalsIdx;

   LocStore argvStore;

   bool cacheDisabled;

   unsigned mallocAlignment;

 public:

   static char ID;

   uint64_t SeqNumber;
   bool mustRecomputeDIE;

   ShadowGV* shadowGlobals;

   explicit IntegrationHeuristicsPass() : ModulePass(ID), cacheDisabled(false) { 

     mallocAlignment = 0;
     SeqNumber = 0;
     mustRecomputeDIE = false;

   }

   bool runOnModule(Module& M);

   void print(raw_ostream &OS, const Module* M) const;

   void releaseMemory(void);

   void createInvariantScopes(Function*, DenseMap<Instruction*, const Loop*>*&, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>*&, DenseMap<BasicBlock*, const Loop*>*&);
   DenseMap<Instruction*, const Loop*>& getInstScopes(Function* F);
   DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& getEdgeScopes(Function* F);
   DenseMap<BasicBlock*, const Loop*>& getBlockScopes(Function* F);

   DomTreeNodeBase<BBWrapper>* getPostDomTreeNode(const Loop*, ShadowBBInvar*, ShadowFunctionInvar&);

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

   void runDSEAndDIE();
   void rerunDSEAndDIE();

   unsigned getMallocAlignment();

   ShadowFunctionInvar* getFunctionInvarInfo(Function& F);
   void getLoopInfo(DenseMap<const Loop*, ShadowLoopInvar*>& LoopInfo, 
		    DenseMap<BasicBlock*, uint32_t>& BBIndices, 
		    const Loop* L);

   void initShadowGlobals(Module&);
   uint64_t getShadowGlobalIndex(GlobalVariable* GV) {
     return shadowGlobalsIdx[GV];
   }

   LocStore& getArgStore(ShadowArg*);

   uint64_t getSeq() {
     return SeqNumber++;
   }

   InlineAttempt* getRoot() { return RootIA; }
   void commit();
  
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

inline LocStore& ShadowValue::getBaseStore() {

  switch(t) {
  case SHADOWVAL_INST:
    release_assert(u.I->store.store && "getBaseStore on instruction without one");
    return u.I->store;
  case SHADOWVAL_GV:
    return u.GV->store;
  case SHADOWVAL_ARG:
    return GlobalIHP->getArgStore(u.A);
  default:
    assert(0 && "getBaseStore on non-inst, non-GV value");
    llvm_unreachable();
  }

}

template<class T> raw_ostream& operator<<(raw_ostream& ROS, PrintCacheWrapper<T> Wrapper) {
  Wrapper.printTo(ROS);
  return ROS;
}

raw_ostream& operator<<(raw_ostream&, const IntegrationAttempt&);

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

// Characteristics for using ShadowValues in hashsets (DenseSet, or as keys in DenseMaps)
template<> struct DenseMapInfo<ShadowValue> {
  
  typedef DenseMapInfo<int> TypeInfo;
  typedef DenseMapInfo<void*> VoidInfo;
  typedef DenseMapInfo<std::pair<int, void*> > PairInfo;

  static inline ShadowValue getEmptyKey() {
    return ShadowValue((Value*)VoidInfo::getEmptyKey());
  }

  static inline ShadowValue getTombstoneKey() {
    return ShadowValue((Value*)VoidInfo::getTombstoneKey());
  }

  static unsigned getHashValue(const ShadowValue& V) {
    void* hashPtr;
    switch(V.t) {
    case SHADOWVAL_INVAL:
      hashPtr = 0; break;
    case SHADOWVAL_ARG:
      hashPtr = V.u.A; break;
    case SHADOWVAL_INST:
      hashPtr = V.u.I; break;
    case SHADOWVAL_GV:
      hashPtr = V.u.GV; break;
    case SHADOWVAL_OTHER:
      hashPtr = V.u.V; break;
    default:
      release_assert(0 && "Bad value type");
      hashPtr = 0;
    }
    return PairInfo::getHashValue(std::make_pair((int)V.t, hashPtr));
  }

  static bool isEqual(const ShadowValue& V1, const ShadowValue& V2) {
    return V1 == V2;
  }

 };

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

  bool addPartialVal(PartialVal& PV, DataLayout* TD, std::string& error);
  bool isComplete();
  bool* getValidArray(uint64_t);
  bool convertToBytes(uint64_t, DataLayout*, std::string& error);
  bool combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, DataLayout* TD, std::string& error);

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

typedef std::pair<std::pair<std::pair<BasicBlock*, ShadowValue>, uint64_t>, uint64_t> LFCacheKey;

#define LFCK(x,y,z,w) std::make_pair(std::make_pair(std::make_pair(x, y), z), w)

struct OpenStatus {

  std::string Name;
  bool success;
  bool FDEscapes;
  bool MayDelete;

OpenStatus(std::string N, bool Success, bool Esc) : Name(N), success(Success), FDEscapes(Esc), MayDelete(false) { }
OpenStatus() : Name(""), success(false), FDEscapes(false), MayDelete(false) {}

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

class Callable {
 public:

  virtual void callback(IntegrationAttempt*) = 0;

};

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

inline bool operator!=(ImprovedValSetSingle& PB1, ImprovedValSetSingle& PB2) {

  return !(PB1 == PB2);

}

enum IterationStatus {

  IterationStatusUnknown,
  IterationStatusFinal,
  IterationStatusNonFinal

};

enum IntegratorType {

  IntegratorTypeIA,
  IntegratorTypePA

};

struct IntegratorTag {

  IntegratorType type;
  void* ptr;

};

enum WalkInstructionResult {

  WIRContinue,
  WIRStopThisPath,
  WIRStopWholeWalk

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

 IAWalker(void* IC = 0) : PList(&Worklist1), CList(&Worklist2), initialContext(IC) {
    
    Contexts.push_back(initialContext);

 }

  void walk();
  void queueWalkFrom(uint32_t idx, ShadowBB*, void* context, bool copyContext);

};

class BackwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(uint32_t, ShadowBB*, void* Ctx, ShadowInstruction*& StoppedCI);
  virtual void walkInternal();

 public:

  virtual WalkInstructionResult reachedTop() { return WIRStopThisPath; }
  virtual WalkInstructionResult mayAscendFromContext(IntegrationAttempt*, void* Ctx) { return WIRContinue; }

  BackwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0, DenseSet<WLItem>* AlreadyVisited = 0);
  
};

class ForwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(uint32_t, ShadowBB*, void* Ctx, ShadowInstruction*& StoppedCI);
  virtual void walkInternal();
  
 public:

  ForwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0);
  
};

struct ShadowBBVisitor {

  virtual void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) = 0;

};

class IntegrationAttempt {

protected:

  // Analyses created by the Pass.
  DenseMap<Function*, LoopInfo*>& LI;

  std::string HeaderStr;

  int improvableInstructions;
  int improvableInstructionsIncludingLoops;
  int improvedInstructions;
  int64_t residualInstructions;
  SmallVector<CallInst*, 4> unexploredCalls;
  SmallVector<const Loop*, 4> unexploredLoops;

  DenseMap<LoadInst*, std::string> normalLFFailures;

  DenseMap<CallInst*, OpenStatus*> forwardableOpenCalls;
  DenseMap<CallInst*, ReadFile> resolvedReadCalls;
  DenseMap<CallInst*, SeekFile> resolvedSeekCalls;
  DenseMap<CallInst*, CloseFile> resolvedCloseCalls;

  DenseMap<Instruction*, std::string> optimisticForwardStatus;

  // Inline attempts / peel attempts which are currently ignored because they've been opted out.
  // These may include inlines / peels which are logically two loop levels deep, 
  // because they were created when a parent loop was opted out but then opted in again.
  DenseSet<CallInst*> ignoreIAs;
  DenseSet<const Loop*> ignorePAs;

  bool commitStarted;
  // The LoopInfo belonging to the function which is being specialised
  LoopInfo* MasterLI;

  bool contextTaintedByVarargs;

  std::string nestingIndent() const;

  int nesting_depth;

 public:

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

  bool contextIsDead;

  struct IntegratorTag tag;

  int64_t totalIntegrationGoodness;
  int64_t nDependentLoads;

  IntegrationAttempt* parent;

  DenseMap<CallInst*, InlineAttempt*> inlineChildren;
  DenseMap<const Loop*, PeelAttempt*> peelChildren;
    
 IntegrationAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, 
		    const Loop* _L, DenseMap<Function*, LoopInfo*>& _LI, int depth) : 
    LI(_LI),
    improvableInstructions(0),
    improvedInstructions(0),
    residualInstructions(-1),
    forwardableOpenCalls(2),
    resolvedReadCalls(2),
    resolvedSeekCalls(2),
    resolvedCloseCalls(2),
    ignoreIAs(2),
    ignorePAs(2),
    commitStarted(false),
    contextTaintedByVarargs(false),
    nesting_depth(depth),
    pass(Pass),
    F(_F),
    L(_L),
    contextIsDead(false),
    totalIntegrationGoodness(0),
    nDependentLoads(0),
    parent(P),
    inlineChildren(1),
    peelChildren(1)
      { 
	this->tag.ptr = (void*)this;
	this->tag.type = IntegratorTypeIA;
      }

  virtual ~IntegrationAttempt();

  Module& getModule();

  void markContextDead();

  Function& getFunction() { return F; }
  
  void callWithScope(Callable& C, const Loop* LScope);

  // virtual for external access:
  virtual bool edgeIsDead(ShadowBBInvar* BB1I, ShadowBBInvar* BB2I);
  bool edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I, bool ignoreThisScope = false);

  const Loop* applyIgnoreLoops(const Loop*);

  virtual bool entryBlockIsCertain() = 0;
  virtual bool entryBlockAssumed() = 0;

  virtual BasicBlock* getEntryBlock() = 0;
  virtual bool hasParent();
  bool isRootMainCall();
  
  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual void collectAllLoopStats() = 0;
  void printHeader(raw_ostream& OS) const;
  virtual bool isOptimisticPeel() = 0;

  // Simple state-tracking helpers:

  virtual InlineAttempt* getFunctionRoot() = 0;
  ShadowBB* getBB(ShadowBBInvar& BBI, bool* inScope = 0);
  ShadowBB* getBB(uint32_t idx, bool* inScope = 0);
  ShadowBB* getOrCreateBB(ShadowBBInvar* BBI);
  ShadowBB* getOrCreateBB(uint32_t);
  // virtual for external access:
  virtual ShadowBBInvar* getBBInvar(uint32_t idx);
  ShadowBB* getUniqueBBRising(ShadowBBInvar* BBI);
  ShadowBB* createBB(uint32_t blockIdx);
  ShadowBB* createBB(ShadowBBInvar*);
  ShadowInstructionInvar* getInstInvar(uint32_t blockidx, uint32_t instidx);
  ShadowInstruction* getInstFalling(ShadowBBInvar* BB, uint32_t instIdx);
  ShadowInstruction* getInst(uint32_t blockIdx, uint32_t instIdx);
  virtual ShadowInstruction* getInst(ShadowInstructionInvar* SII);
  bool instResolvedAsInvariant(ShadowInstruction* SI);
  ShadowInstruction* getMostLocalInst(uint32_t blockIdx, uint32_t instIdx);

  // The toplevel loop:
  void analyse();
  bool analyse(bool inLoopAnalyser);
  bool analyseBlock(uint32_t& BBIdx, bool inLoopAnalyser, bool skipStoreMerge, const Loop* MyL);
  bool analyseBlockInstructions(ShadowBB* BB, bool skipSuccessorCreation, bool inLoopAnalyser);
  bool analyseLoop(const Loop*, bool nestedLoop);
  void releaseLatchStores(const Loop*);
  virtual void getInitialStore() = 0;

  // Constant propagation:

  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSetSingle& result);
  bool tryEvaluate(ShadowValue V, bool inLoopAnalyser, bool& loadedVararg);
  bool getNewPB(ShadowInstruction* SI, ImprovedValSetSingle& NewPB, bool& loadedVararg);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSetSingle& NewPB);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSetSingle& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx);
  void tryEvaluateResult(ShadowInstruction* SI, 
			 std::pair<ValSetType, ImprovedVal>* Ops, 
			 ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldBitwiseOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldPtrAsIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldPointerCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldNonConstCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  bool tryFoldOpenCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved);
  void getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs = 0);
  void getOperandRising(ShadowInstruction* SI, uint32_t valOpIdx, ShadowBBInvar* ExitingBB, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs);
  void getCommittedExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs = 0);
  void getCommittedOperandRising(ShadowInstruction* SI, uint32_t valOpIdx, ShadowBBInvar* ExitingBB, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs);
  bool tryEvaluateMerge(ShadowInstruction* I, ImprovedValSetSingle& NewPB);

  // CFG analysis:

  bool createEntryBlock();
  void createBBAndPostDoms(uint32_t idx, ShadowBBStatus newStatus);
  bool tryEvaluateTerminator(ShadowInstruction* SI, bool tagSuccVararg);
  bool tryEvaluateTerminatorInst(ShadowInstruction* SI);
  IntegrationAttempt* getIAForScope(const Loop* Scope);
  IntegrationAttempt* getIAForScopeFalling(const Loop* Scope);
  void setBlockStatus(ShadowBBInvar* BB, ShadowBBStatus);
  bool shouldAssumeEdge(BasicBlock* BB1, BasicBlock* BB2) {
    return pass->shouldAssumeEdge(&F, BB1, BB2);
  }
  void copyLoopExitingDeadEdges(PeelAttempt* LPA);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(CallInst* CI);
  virtual bool stackIncludesCallTo(Function*) = 0;
  bool shouldInlineFunction(ShadowInstruction*, Function*);
  InlineAttempt* getOrCreateInlineAttempt(ShadowInstruction* CI, bool ignoreScope, bool& created);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  bool tryResolveLoadFromConstant(ShadowInstruction*, ImprovedValSetSingle& Result, std::string& error);
  bool tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSetSingle& NewPB, bool& loadedVararg);
  bool getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result);

  // Support functions for the generic IA graph walkers:
  void visitLoopExitingBlocksBW(ShadowBBInvar* ExitedBB, ShadowBBInvar* ExitingBB, ShadowBBVisitor*, void* Ctx, bool& firstPred);
  virtual WalkInstructionResult queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) = 0;
  void visitNormalPredecessorsBW(ShadowBB* FromBB, ShadowBBVisitor*, void* Ctx);
  void queueReturnBlocks(BackwardIAWalker* Walker, void*);
  void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);
  virtual void queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) = 0;
  virtual void cleanupLocalStore();

  // VFS call forwarding:

  bool openCallSucceeds(Value*);
  virtual int64_t tryGetIncomingOffset(CallInst*);
  virtual ReadFile* tryGetReadFile(CallInst* CI);
  bool tryPromoteOpenCall(ShadowInstruction* CI);
  void tryPromoteAllCalls();
  bool tryResolveVFSCall(ShadowInstruction*);
  WalkInstructionResult isVfsCallUsingFD(ShadowInstruction* VFSCall, ShadowInstruction* FD, bool ignoreClose);
  virtual void resolveReadCall(CallInst*, struct ReadFile);
  virtual void resolveSeekCall(CallInst*, struct SeekFile);
  bool isResolvedVFSCall(const Instruction*);
  bool VFSCallWillUseFD(const Instruction*);
  bool isSuccessfulVFSCall(const Instruction*);
  bool isUnusedReadCall(ShadowInstruction*);
  bool isCloseCall(CallInst*);
  OpenStatus& getOpenStatus(CallInst*);
  void tryKillAllVFSOps();
  void markCloseCall(CallInst*);

  // Load forwarding extensions for varargs:
  virtual void getVarArg(int64_t, ImprovedValSetSingle&) = 0;
  void disableChildVarargsContexts();
  bool isVarargsTainted();
  
  // Dead store and allocation elim:

  bool tryKillStore(ShadowInstruction* SI);
  bool tryKillMemset(ShadowInstruction* MI);
  bool tryKillMTI(ShadowInstruction* MTI);
  bool tryKillAlloc(ShadowInstruction* Alloc);
  bool tryKillRead(ShadowInstruction*, ReadFile&);
  bool tryKillWriterTo(ShadowInstruction* Writer, ShadowValue WritePtr, uint64_t Size);
  bool DSEHandleWrite(ShadowValue Writer, uint64_t WriteSize, ShadowValue StorePtr, uint64_t Size, ShadowValue StoreBase, int64_t StoreOffset, std::vector<bool>* deadBytes);
  bool isLifetimeEnd(ShadowValue Alloc, ShadowInstruction* I);
  WalkInstructionResult noteBytesWrittenBy(ShadowInstruction* I, ShadowValue StorePtr, ShadowValue StoreBase, int64_t StoreOffset, uint64_t Size, std::vector<bool>* writtenBytes);
  bool callUsesPtr(ShadowInstruction*, ShadowValue, uint64_t Size);
  void tryKillAllMTIs();
  void tryKillAllStores();
  void tryKillAllAllocs();

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
  bool tryForwardLoadPB(LoadInst*, bool finalise, ImprovedValSetSingle& out, BasicBlock* optBB, IntegrationAttempt* optIA);
  bool shouldCheckPB(ShadowValue);
  void analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);

  // PBLF Caching
  ImprovedValSetSingle* getLFPBCacheEntry(LFCacheKey& Key);
  void deleteLFPBCacheEntry(LFCacheKey& Key);
  ImprovedValSetSingle* createLFPBCacheEntry(LFCacheKey& Key);

  // Enabling / disabling exploration:

  void enablePeel(const Loop*);
  void disablePeel(const Loop*);
  bool loopIsEnabled(const Loop*);
  void enableInline(CallInst*);
  void disableInline(CallInst*);
  bool inlineIsEnabled(CallInst*);
  virtual bool isEnabled() = 0;
  virtual void setEnabled(bool) = 0;
  bool isAvailable();
  bool isAvailableFromCtx(IntegrationAttempt*);
  bool isVararg();

  // Estimating inlining / unrolling benefit:

  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&);
  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&);
  int64_t getResidualInstructions();
  virtual void reduceDependentLoads(int64_t) = 0;
  void countDependentLoads();
  void propagateDependentLoads();

  // DOT export:

  void printRHS(ShadowValue, raw_ostream& Out);
  void printOutgoingEdge(ShadowBBInvar* BBI, ShadowBB* BB, ShadowBBInvar* SBI, ShadowBB* SB, uint32_t i, bool useLabels, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief);
 void describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBBInvar*, 4>* forceSuccessors, bool brief);
  void describeScopeAsDOT(const Loop* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief, SmallVector<std::string, 4>* deferredEdges);
  void describeLoopAsDOT(const Loop* L, uint32_t headerIdx, raw_ostream& Out, bool brief);
  void describeAsDOT(raw_ostream& Out, bool brief);
  std::string getValueColour(ShadowValue);
  std::string getGraphPath(std::string prefix);
  void describeTreeAsDOT(std::string path);
  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) = 0;
  bool blockLiveInAnyScope(ShadowBBInvar* BB);

  void printWithCache(const Value* V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  void printWithCache(ShadowValue V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  // Data export for the Integrator pass:

  virtual std::string getShortHeader() = 0;
  virtual IntegratorTag* getParentTag() = 0;
  bool hasChildren();
  unsigned getNumChildren();
  IntegratorTag* getChildTag(unsigned);
  virtual bool canDisable() = 0;
  unsigned getTotalInstructions();
  unsigned getElimdInstructions();
  int64_t getTotalInstructionsIncludingLoops();
  IntegrationAttempt* searchFunctions(std::string&, IntegrationAttempt*& startAt);

  // Saving our results as a bitcode file:

  void prepareCommit();
  void localPrepareCommit();
  virtual std::string getCommittedBlockPrefix() = 0;
  void commitCFG();
  virtual ShadowBB* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  ShadowBB* getBBFalling(ShadowBBInvar* BBI);
  ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  void populatePHINode(ShadowBB* BB, ShadowInstruction* I, PHINode* NewPB);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void fixupHeaderPHIs(ShadowBB* BB);
  void emitTerminator(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  bool emitVFSCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void emitCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock*& emitBB);
  Instruction* emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  bool synthCommittedPointer(ShadowValue, BasicBlock* emitBB);
  void emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, BasicBlock*& emitBB);
  void commitLoopInvariants(PeelAttempt*, uint32_t startIdx);
  void commitLoopInstructions(const Loop* ScopeL, uint32_t& i);
  void commitInstructions();

  // Stat collection and printing:

  void collectAllBlockStats();
  void collectBlockStats(ShadowBBInvar* BBI, ShadowBB* BB);
  void collectLoopStats(const Loop*);
  void collectStats();

  void print(raw_ostream& OS) const;
  // Callable from GDB
  void dump() const;

  virtual void describe(raw_ostream& Stream) const = 0;
  virtual void describeBrief(raw_ostream& Stream) const = 0;
  virtual std::string getFunctionName();
  virtual int getIterCount() = 0;

  virtual bool isBlacklisted(Function* F) {
    return functionIsBlacklisted(F);
  }

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

  PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, int iter, int depth);

  IterationStatus iterStatus;

  PeelIteration* getNextIteration();
  PeelIteration* getOrCreateNextIteration(); 

  virtual BasicBlock* getEntryBlock(); 

  ShadowValue getLoopHeaderForwardedOperand(ShadowInstruction* SI); 

  void checkFinalIteration(); 
  void dropExitingStoreRefs();
  void dropLatchStoreRef();

  virtual InlineAttempt* getFunctionRoot(); 

  void visitVariant(ShadowInstructionInvar* VI, VisitorContext& Visitor); 
  virtual bool visitNextIterationPHI(ShadowInstructionInvar* I, VisitorContext& Visitor); 

  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out); 

  virtual void describe(raw_ostream& Stream) const;
  virtual void describeBrief(raw_ostream& Stream) const;

  virtual void collectAllLoopStats(); 

  virtual std::string getShortHeader(); 
  virtual IntegratorTag* getParentTag(); 

  virtual bool canDisable(); 
  virtual bool isEnabled(); 
  virtual void setEnabled(bool); 

  virtual bool isOptimisticPeel(); 

  virtual void getVarArg(int64_t, ImprovedValSetSingle&); 

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
  virtual ShadowBB* getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSetSingle& result);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor);

  virtual void getInitialStore();

};

class ProcessExternalCallback;

class PeelAttempt {
   // Not a subclass of IntegrationAttempt -- this is just a helper.

   IntegrationHeuristicsPass* pass;
   IntegrationAttempt* parent;
   Function& F;

   uint64_t SeqNumber;

   std::string HeaderStr;

   DenseMap<Function*, LoopInfo*>& LI;

   int64_t residualInstructions;

   int nesting_depth;
   int debugIndent;

 public:

   const Loop* L;

   struct IntegratorTag tag;

   int64_t totalIntegrationGoodness;
   int64_t nDependentLoads;

   ShadowLoopInvar* invarInfo;

   std::vector<PeelIteration*> Iterations;

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, const Loop* _L, int depth);
   ~PeelAttempt();

   bool analyse();

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
   IntegratorTag* getParentTag(); 
   bool hasChildren(); 
   unsigned getNumChildren(); 
   IntegratorTag* getChildTag(unsigned); 
   bool isEnabled(); 
   void setEnabled(bool); 
   
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

 };

class InlineAttempt : public IntegrationAttempt { 

  ShadowInstruction* CI;

 public:

  InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, ShadowInstruction* _CI, int depth);

  Function* CommitF;
  BasicBlock* returnBlock;
  PHINode* returnPHI;

  ShadowArg* argShadows;

  SmallVector<ShadowInstruction*, 4> localAllocas;

  virtual BasicBlock* getEntryBlock(); 

  virtual InlineAttempt* getFunctionRoot(); 

  bool isOwnCallUnused(); 

  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out); 
  
  virtual void describe(raw_ostream& Stream) const; 
  virtual void describeBrief(raw_ostream& Stream) const; 
  
  virtual void collectAllLoopStats(); 

  virtual std::string getShortHeader(); 
  virtual IntegratorTag* getParentTag(); 

  virtual bool canDisable(); 
  virtual bool isEnabled(); 
  virtual void setEnabled(bool); 


  virtual bool isOptimisticPeel(); 

  virtual void getVarArg(int64_t, ImprovedValSetSingle&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  bool getArgBasePointer(Argument*, ImprovedValSetSingle&); 

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

  bool analyseWithArgs(bool withinUnboundedLoop); 

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
  virtual void cleanupLocalStore();
  
};

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

 ImprovedValSetSingle tryForwardLoadSubquery(ShadowInstruction* StartInst, ShadowValue LoadPtr, ShadowValue LoadPtrBase, int64_t LoadPtrOffset, uint64_t LoadSize, Type* originalType, PartialVal& ResolvedSoFar, std::string& error, DenseSet<BackwardIAWalker::WLItem>&);
 ImprovedValSetSingle tryForwardLoadArtificial(ShadowInstruction* StartInst, ShadowValue LoadBase, int64_t LoadOffset, uint64_t LoadSize, Type* targetType, bool* alreadyValidBytes, std::string& error, BasicBlock* ctBB, IntegrationAttempt* ctIA, bool inAnalyser, bool optimistic);

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

 SVAAResult aliasSVs(ShadowValue V1, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge);
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

 bool edgeIsDead(ShadowBB* BB1, ShadowBBInvar* BB2I);

 int64_t getSpilledVarargAfter(ShadowInstruction* CI, int64_t OldArg);

 bool blockCertainlyExecutes(ShadowBB*);
 bool blockAssumedToExecute(ShadowBB*);

 Function* cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name);

 Constant* getGVOffset(Constant* GV, int64_t Offset, Type* targetType);


 // Load forwarding v3 functions:
 bool addIVSToPartialVal(ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string& error);
 void readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, std::string& error);
 void readValRange(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, std::string& error);
 void executeStoreInst(ShadowInstruction* StoreSI);
 void executeMemsetInst(ShadowInstruction* MemsetSI);

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

 void readValRangeMultiFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore);
 void readValRangeMulti(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, SmallVector<IVSRange, 4>& Results);
 void executeMemcpyInst(ShadowInstruction* MemcpySI);
 void executeVaCopyInst(ShadowInstruction* SI);
 void executeAllocInst(ShadowInstruction* SI, Type* AllocType, uint64_t AllocSize);
 void executeAllocaInst(ShadowInstruction* SI);
 void executeMallocInst(ShadowInstruction* SI);
 void executeReallocInst(ShadowInstruction* SI);
 void executeCopyInst(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowBB* BB);
 void executeVaStartInst(ShadowInstruction* SI);
 void executeReadInst(ShadowInstruction* ReadSI, OpenStatus& OS, uint64_t FileOffset, uint64_t Size);
 void executeUnexpandedCall(ShadowInstruction* SI);
 void executeWriteInst(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowBB* StoreBB);

 ImprovedValSetSingle PVToPB(PartialVal& PV, raw_string_ostream& RSO, uint64_t Size, LLVMContext&);
 ShadowValue PVToSV(PartialVal& PV, raw_string_ostream& RSO, uint64_t Size, LLVMContext&);

 void commitStoreToBase(LocalStoreMap* Map);
 void doBlockStoreMerge(ShadowBB* BB);
 void doCallStoreMerge(ShadowInstruction* SI);
 
 void initSpecialFunctionsMap(Module& M);
 
 void printPB(raw_ostream& out, ImprovedValSetSingle PB, bool brief = false);

 struct IntAAProxy {

   virtual bool isNoAliasPBs(ShadowValue Ptr1Base, int64_t Ptr1Offset, uint64_t Ptr1Size, ShadowValue Ptr2, uint64_t Ptr2Size);

 };

 struct MergeBlockVisitor : public ShadowBBVisitor {
   
   bool newMapValid;
   LocalStoreMap* newMap;
   SmallPtrSet<LocalStoreMap*, 4> seenMaps;
   bool mergeToBase;
   bool useVarargMerge;
   
 MergeBlockVisitor(bool mtb, bool uvm = false) : newMapValid(false), newMap(0), mergeToBase(mtb), useVarargMerge(uvm) { }
   
   void mergeStores(ShadowBB* BB, LocStore* mergeFromStore, LocStore* mergeToStore, ShadowValue& MergeV);
   void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx);

 };

} // Namespace LLVM

#endif
