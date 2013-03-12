
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
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
#include "llvm/Support/raw_ostream.h"

#include <limits.h>
#include <string>
#include <vector>

#define LPDEBUG(x) DEBUG(do { printDebugHeader(dbgs()); dbgs() << ": " << x; } while(0))

namespace llvm {

class Function;
class BasicBlock;
class Instruction;
class TargetData;
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
class TargetData;
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
class NormalLoadForwardWalker;
class PBLoadForwardWalker;
class MemSetInst;
class MemTransferInst;
class ShadowLoopInvar;

bool functionIsBlacklisted(Function*);

inline void release_assert_fail(const char* str) {

  errs() << "Assertion failed: " << str << "\n";
  abort();

}

#define release_assert(x) if(!(x)) { release_assert_fail(#x); }

// Include structures and functions for working with instruction and argument shadows.
#include "ShadowInlines.h"

extern TargetData* GlobalTD;
extern AliasAnalysis* GlobalAA;

class IntegrationHeuristicsPass : public ModulePass {

   DenseMap<Function*, LoopInfo*> LIs;
   DenseMap<Function*, DenseMap<Instruction*, const Loop*>* > invariantInstScopes;
   DenseMap<Function*, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* > invariantEdgeScopes;
   DenseMap<Function*, DenseMap<BasicBlock*, const Loop*>* > invariantBlockScopes;
   DenseMap<Function*, ShadowFunctionInvar> functionInfo;

   DenseMap<const Loop*, std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> > LoopPDTs;

   SmallSet<Function*, 4> alwaysInline;
   DenseMap<const Loop*, std::pair<BasicBlock*, BasicBlock*> > optimisticLoopMap;
   DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1 > > assumeEdges;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoops;
   DenseMap<std::pair<Function*, BasicBlock*>, uint64_t> maxLoopIters;

   TargetData* TD;
   AliasAnalysis* AA;

   InlineAttempt* RootIA;

   DenseMap<const GlobalVariable*, std::string> GVCache;
   DenseMap<const GlobalVariable*, std::string> GVCacheBrief;

   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > briefFunctionTextCache;

   bool cacheDisabled;

   unsigned mallocAlignment;

 public:

   static char ID;

   uint64_t SeqNumber;
   bool mustRecomputeDIE;

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

   DomTreeNodeBase<const BBWrapper>* getPostDomTreeNode(const Loop*, ShadowBBInvar*, ShadowFunctionInvar&);

   // Caching text representations of instructions:

   DenseMap<const Instruction*, std::string>& getFunctionCache(const Function* F, bool brief);
   DenseMap<const GlobalVariable*, std::string>& getGVCache(bool brief);
   void populateGVCaches(const Module*);
   void printValue(raw_ostream& ROS, const Value* V, bool brief);
   void printValue(raw_ostream& ROS, ShadowValue V, bool brief);
   void disableValueCache();

   Constant* loadEnvironment(Module&, std::string&);
   void loadArgv(Function*, std::string&, unsigned argvidx, unsigned& argc);
   void setParam(IntegrationAttempt* IA, Function& F, long Idx, Constant* Val);
   void parseArgs(InlineAttempt* RootIA, Function& F);

   void estimateIntegrationBenefit();

   virtual void getAnalysisUsage(AnalysisUsage &AU) const;

   bool shouldAlwaysInline(Function* F) {
     return alwaysInline.count(F);
   }
   
   std::pair<BasicBlock*, BasicBlock*> getOptimisticEdge(const Loop* L) {
     return optimisticLoopMap.lookup(L);
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

   ShadowFunctionInvar& getFunctionInvarInfo(Function& F);
   void getLoopInfo(DenseMap<const Loop*, ShadowLoopInvar*>& LoopInfo, 
		    DenseMap<BasicBlock*, uint32_t>& BBIndices, 
		    const Loop* L);

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

template<class T> raw_ostream& operator<<(raw_ostream& ROS, PrintCacheWrapper<T> Wrapper) {
  Wrapper.printTo(ROS);
  return ROS;
}

raw_ostream& operator<<(raw_ostream&, const IntegrationAttempt&);

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
  // Value is tainted by varargs at any point?
  bool isVarargTainted;

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

  uint64_t markPaddingBytes(const Type*);

  bool addPartialVal(PartialVal& PV, TargetData* TD, std::string& error);
  bool isComplete();
  bool* getValidArray(uint64_t);
  bool convertToBytes(uint64_t, TargetData*, std::string& error);
  bool combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, TargetData* TD, std::string& error);

  void initByteArray(uint64_t);
  
  PartialVal(ValSetType TotalType, ImprovedVal Total) : 
  type(PVTotal), isVarargTainted(false), TotalIV(Total), TotalIVType(TotalType), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
  PartialVal(Constant* _C, uint64_t Off) : 
  type(PVPartial), isVarargTainted(false), TotalIV(), C(_C), ReadOffset(Off), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
 PartialVal() :
  type(PVEmpty), isVarargTainted(false), TotalIV(), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
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

inline bool operator==(PointerBase& PB1, PointerBase& PB2) {

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

inline bool operator!=(PointerBase& PB1, PointerBase& PB2) {

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

class LoopPBAnalyser {

  SmallVector<ShadowValue, 64> PBQueue1;
  SmallVector<ShadowValue, 64> PBQueue2;
  
  SmallVector<ShadowValue, 64>* PBProduceQ;

  DenseSet<ShadowValue> inLoopVCs;

public:

  BasicBlock* CacheThresholdBB;
  IntegrationAttempt* CacheThresholdIA;
  
  LoopPBAnalyser(BasicBlock* CTBB, IntegrationAttempt* CTIA) : CacheThresholdBB(CTBB), CacheThresholdIA(CTIA) {
    PBProduceQ = &PBQueue1;
  }

  void queueUpdatePB(ShadowValue VC) {
    PBProduceQ->push_back(VC);
  }

  void queueIfConsidered(ShadowValue VC) {
    if(inLoopVCs.count(VC))
      queueUpdatePB(VC);
  }

  void addVal(ShadowValue V) {
    inLoopVCs.insert(V);
    queueUpdatePB(V);
  }

  void runPointerBaseSolver(bool finalise, std::vector<ShadowValue>* modifiedVCs);
  void run();

};

enum WalkInstructionResult {

  WIRContinue,
  WIRStopThisPath,
  WIRStopWholeWalk

};

class IAWalker {

 protected:

  typedef std::pair<uint32_t, ShadowBB*> WLItem;
  WLItem makeWL(uint32_t x, ShadowBB* y) { return std::make_pair(x, y); }

  DenseSet<WLItem> Visited;
  SmallVector<std::pair<WLItem, void*>, 8> Worklist1;
  SmallVector<std::pair<WLItem, void*>, 8> Worklist2;

  SmallVector<std::pair<WLItem, void*>, 8>* PList;
  SmallVector<std::pair<WLItem, void*>, 8>* CList;

  SmallVector<void*, 4> Contexts;
  
  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void* Context) = 0;
  virtual bool shouldEnterCall(ShadowInstruction*) = 0;
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

  virtual bool reachedTop() { return true; }
  virtual bool mayAscendFromContext(IntegrationAttempt*, void* Ctx) { return true; }

  BackwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0);
  
};

class ForwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(uint32_t, ShadowBB*, void* Ctx, ShadowInstruction*& StoppedCI);
  virtual void walkInternal();
  
 public:

  ForwardIAWalker(uint32_t idx, ShadowBB* BB, bool skipFirst, void* IC = 0);
  
};

class IntegrationAttempt {

protected:

  IntegrationHeuristicsPass* pass;

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
  DenseMap<Instruction*, std::string> pessimisticForwardStatus;

  // Inline attempts / peel attempts which are currently ignored because they've been opted out.
  // These may include inlines / peels which are logically two loop levels deep, 
  // because they were created when a parent loop was opted out but then opted in again.
  DenseSet<CallInst*> ignoreIAs;
  DenseSet<const Loop*> ignorePAs;

  DenseMap<LFCacheKey, PointerBase> LFPBCache;

  bool commitStarted;
  // The LoopInfo belonging to the function which is being specialised
  LoopInfo* MasterLI;

  bool contextTaintedByVarargs;

  std::string nestingIndent() const;

  int nesting_depth;
  uint64_t SeqNumber;

 public:

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
  pass(Pass),
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
  bool edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I);

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
  ShadowInstruction* getInst(ShadowInstructionInvar* SII);
  bool instResolvedAsInvariant(ShadowInstruction* SI);
  ShadowInstruction* getMostLocalInst(uint32_t blockIdx, uint32_t instIdx);

  // The toplevel loop:
  void analyse();
  void analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);
  void analyseBlock(uint32_t& BBIdx, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);
  void analyseBlockInstructions(ShadowBB* BB, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);

  // Constant propagation:

  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, PointerBase& result);
  bool tryEvaluate(ShadowValue V, bool finalise, LoopPBAnalyser* LPBA, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);
  bool getNewPB(ShadowInstruction* SI, bool finalise, PointerBase& NewPB, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA, bool inLoopAnalyser);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, PointerBase& NewPB);
  bool tryEvaluateOrdinaryInst(ShadowInstruction* SI, PointerBase& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx);
  bool tryEvaluateResult(ShadowInstruction* SI, 
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
  bool tryEvaluateMerge(ShadowInstruction* I, bool finalise, PointerBase& NewPB);

  // CFG analysis:

  void createEntryBlock();
  void createBBAndPostDoms(uint32_t idx, ShadowBBStatus newStatus);
  void tryEvaluateTerminator(ShadowInstruction* SI);
  void tryEvaluateTerminatorInst(ShadowInstruction* SI);
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
  InlineAttempt* getOrCreateInlineAttempt(ShadowInstruction* CI);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  bool tryResolveLoadFromConstant(ShadowInstruction*, PointerBase& Result, std::string& error);
  bool tryForwardLoadPB(ShadowInstruction* LI, bool finalise, PointerBase& NewPB, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA, bool inLoopAnalyser);
  bool getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result);

  // Support functions for the generic IA graph walkers:
  void queueLoopExitingBlocksBW(ShadowBBInvar* ExitedBB, ShadowBBInvar* ExitingBB, BackwardIAWalker* Walker, void* Ctx, bool& firstPred);
  virtual bool queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx) = 0;
  void queueNormalPredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* Ctx);
  void queueReturnBlocks(BackwardIAWalker* Walker, void*);
  void queueSuccessorsFWFalling(ShadowBBInvar* BB, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);
  virtual void queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) = 0;

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
  bool isSuccessfulVFSCall(const Instruction*);
  bool isUnusedReadCall(ShadowInstruction*);
  bool isCloseCall(CallInst*);
  OpenStatus& getOpenStatus(CallInst*);
  void tryKillAllVFSOps();
  void markCloseCall(CallInst*);

  // Load forwarding extensions for varargs:
  virtual void getVarArg(int64_t, PointerBase&) = 0;
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

  // Pointer base analysis
  void queueUpdatePB(ShadowValue, LoopPBAnalyser*);
  void queueUsersUpdatePB(ShadowValue V, LoopPBAnalyser*);
  void queueUserUpdatePB(ShadowInstructionInvar*, LoopPBAnalyser*);
  void queueUsersUpdatePBFalling(ShadowInstructionInvar* I, LoopPBAnalyser*);
  void queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser*);
  void queueUsersUpdatePBLocal(ShadowInstructionInvar* I, LoopPBAnalyser*);
  void queuePBUpdateAllUnresolvedVCsInScope(const Loop* L, LoopPBAnalyser*);
  void queuePBUpdateIfUnresolved(ShadowValue, LoopPBAnalyser*);
  void queueUpdatePBWholeLoop(const Loop*, LoopPBAnalyser*);
  void printPB(raw_ostream& out, PointerBase PB, bool brief = false);
  virtual bool ctxContains(IntegrationAttempt*) = 0;
  bool tryForwardLoadPB(LoadInst*, bool finalise, PointerBase& out, BasicBlock* optBB, IntegrationAttempt* optIA);
  bool shouldCheckPB(ShadowValue);
  void analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);

  // PBLF Caching
  PointerBase* getLFPBCacheEntry(LFCacheKey& Key);
  void deleteLFPBCacheEntry(LFCacheKey& Key);
  PointerBase* createLFPBCacheEntry(LFCacheKey& Key);

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
  void describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBB*, 4>* forceSuccessors, bool brief);
  void describeLoopAsDOT(const Loop* L, uint32_t headerIdx, raw_ostream& Out, bool brief);
  void describeAsDOT(raw_ostream& Out, bool brief);
  std::string getValueColour(ShadowValue);
  std::string getGraphPath(std::string prefix);
  void describeTreeAsDOT(std::string path);
  virtual bool getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) = 0;
  bool blockLiveInAnyScope(ShadowBBInvar* BB);

  // Caching instruction text for debug and DOT export:
  PrintCacheWrapper<const Value*> itcache(const Value& V, bool brief = false) const {
    return PrintCacheWrapper<const Value*>(*pass, &V, brief);
  }
  PrintCacheWrapper<ShadowValue> itcache(ShadowValue V, bool brief = false) const {
    return PrintCacheWrapper<ShadowValue>(*pass, V, brief);
  }
  PrintCacheWrapper<ShadowValue> itcache(ShadowInstruction* SI, bool brief = false) const {
    return itcache(ShadowValue(SI), brief);
  }
  PrintCacheWrapper<ShadowValue> itcache(ShadowArg* SA, bool brief = false) const {
    return itcache(ShadowValue(SA), brief);
  }

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
  virtual ShadowBB* getSuccessorBB(ShadowBB* BB, uint32_t succIdx);
  ShadowBB* getBBFalling(ShadowBBInvar* BBI);
  ShadowBB* getBBFalling2(ShadowBBInvar* BBI);
  void populatePHINode(ShadowBB* BB, ShadowInstruction* I, PHINode* NewPB);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void fixupHeaderPHIs(ShadowBB* BB);
  void emitTerminator(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  bool emitVFSCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void emitCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock*& emitBB);
  Instruction* emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  void synthCommittedPointer(ShadowValue, BasicBlock* emitBB);
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

  virtual void getVarArg(int64_t, PointerBase&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  virtual bool stackIncludesCallTo(Function*); 

  virtual void reduceDependentLoads(int64_t); 

  virtual bool queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* ctx); 
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc); 

  virtual bool entryBlockIsCertain(); 
  virtual bool entryBlockAssumed(); 

  bool isOnlyExitingIteration(); 
  bool allExitEdgesDead(); 

  virtual int getIterCount() {
    return iterationCount;
  }

  void prepareShadows();
  virtual std::string getCommittedBlockPrefix();
  virtual ShadowBB* getSuccessorBB(ShadowBB* BB, uint32_t succIdx);
  virtual void emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB);
  virtual bool tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, PointerBase& result);
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor);

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

   void analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);

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
   
   void queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser*); 

   void reduceDependentLoads(int64_t); 

   void dumpMemoryUsage(int indent); 

   int64_t getResidualInstructions(); 
   void findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty);
   void countDependentLoads(); 
   void propagateDependentLoads(); 

   void disableVarargsContexts(); 

   bool isTerminated() {
     return Iterations.back()->iterStatus == IterationStatusFinal;
   }

   // Caching instruction text for debug and DOT export:
   PrintCacheWrapper<const Value*> itcache(const Value& V) const {
     return parent->itcache(V);
   }
   PrintCacheWrapper<ShadowValue> itcache(ShadowValue V) const {
     return parent->itcache(V);
   }

   void getShadowInfo();

 };

class InlineAttempt : public IntegrationAttempt { 

  ShadowInstruction* CI;

 public:

  InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, ShadowInstruction* _CI, int depth);

  Function* CommitF;
  BasicBlock* returnBlock;
  PHINode* returnPHI;

  ShadowArg* argShadows;

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

  virtual void getVarArg(int64_t, PointerBase&); 

  virtual bool ctxContains(IntegrationAttempt*); 

  bool getArgBasePointer(Argument*, PointerBase&); 
  void queueUpdateCall(LoopPBAnalyser*); 
  void queueCheckAllArgs(LoopPBAnalyser*); 

  int64_t getSpilledVarargAfter(int64_t arg); 

  virtual void reduceDependentLoads(int64_t); 

  virtual int getIterCount() {
    return -1;
  }

  virtual bool stackIncludesCallTo(Function*); 

  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&); 
  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&); 

  virtual bool queuePredecessorsBW(ShadowBB* FromBB, BackwardIAWalker* Walker, void* ctx);
  virtual void queueSuccessorsFW(ShadowBB* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(ShadowBB* PresentBlock, ShadowBBInvar* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual bool entryBlockIsCertain(); 
  virtual bool entryBlockAssumed(); 

  void disableVarargsContexts(); 

  void analyseWithArgs(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA); 

  void prepareShadows();
  void getLiveReturnVals(SmallVector<ShadowValue, 4>& Vals);
  std::string getCommittedBlockPrefix();
  BasicBlock* getCommittedEntryBlock();
  virtual void runDIE();
  virtual void visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor);

  Value* getArgCommittedValue(ShadowArg* SA);
  void commitArgsAndInstructions();

};

 Constant* extractAggregateMemberAt(Constant* From, int64_t Offset, const Type* Target, uint64_t TargetSize, TargetData*);
 Constant* constFromBytes(unsigned char*, const Type*, TargetData*);
 bool allowTotalDefnImplicitCast(const Type* From, const Type* To);
 bool allowTotalDefnImplicitPtrToInt(const Type* From, const Type* To, TargetData*);
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

 PointerBase tryForwardLoadSubquery(ShadowInstruction* StartInst, ShadowValue LoadPtr, ShadowValue LoadPtrBase, int64_t LoadPtrOffset, uint64_t LoadSize, const Type* originalType, PartialVal& ResolvedSoFar, std::string& error);
 PointerBase tryForwardLoadArtificial(ShadowInstruction* StartInst, ShadowValue LoadBase, int64_t LoadOffset, uint64_t LoadSize, const Type* targetType, bool* alreadyValidBytes, std::string& error);
 std::string describePBWalker(NormalLoadForwardWalker& Walker, IntegrationAttempt*);

 bool GetDefinedRange(ShadowValue DefinedBase, int64_t DefinedOffset, uint64_t DefinedSize,
		      ShadowValue DefinerBase, int64_t DefinerOffset, uint64_t DefinerSize,
		      uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset);

 bool getPBFromCopy(ShadowValue copySource, ShadowInstruction* copyInst, uint64_t ReadOffset, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t ReadSize, const Type* originalType, bool* validBytes, PointerBase& NewPB, std::string& error);
 bool getMemsetPV(ShadowInstruction* MSI, uint64_t nbytes, PartialVal& NewPV, std::string& error);
 bool getMemcpyPB(ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, const Type* originalType, bool* validBytes, PartialVal& NewPV, PointerBase& NewPB, std::string& error);
 bool getVaStartPV(ShadowInstruction* CI, int64_t ReadOffset, PartialVal& NewPV, std::string& error);
 bool getReallocPB(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, const Type* originalType, bool* validBytes, PointerBase& NewPB, std::string& error);
 bool getVaCopyPB(ShadowInstruction* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, const Type* originalType, bool* validBytes, PointerBase& NewPB, std::string& error);
 bool getReadPV(ShadowInstruction* SI, uint64_t nbytes, int64_t ReadOffset, PartialVal& NewPV, std::string& error);

 enum SVAAResult {
   SVNoAlias,
   SVMayAlias,
   SVMustAlias
 };

 SVAAResult aliasSVs(ShadowValue V1, unsigned V1Size, ShadowValue V2, unsigned V2Size, bool usePBKnowledge);
 SVAAResult tryResolvePointerBases(PointerBase& PB1, unsigned V1Size, PointerBase& PB2, unsigned V2Size, bool usePBKnowledge);
 SVAAResult tryResolvePointerBases(ShadowValue V1Base, int64_t V1Offset, unsigned V1Size, ShadowValue V2, unsigned V2Size, bool usePBKnowledge);
 SVAAResult tryResolvePointerBases(ShadowValue V1, unsigned V1Size, ShadowValue V2, unsigned V2Size, bool usePBKnowledge);
 
 bool basesAlias(ShadowValue, ShadowValue);

 bool tryCopyDeadEdges(ShadowBB* FromBB, ShadowBB* ToBB);

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

 extern bool mainDIE;

} // Namespace LLVM

#endif
