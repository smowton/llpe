
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
#include "llvm/Analysis/MemoryDependenceAnalysis.h"

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
class CallInst;
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

enum va_arg_type {
  
  va_arg_type_none,
  va_arg_type_baseptr,
  va_arg_type_fp,
  va_arg_type_nonfp

};

typedef struct { 

  Value* first; 
  IntegrationAttempt* second;
  int64_t offset;
  int64_t va_arg;

  static const int64_t noOffset = LLONG_MAX;

  // Values of va_arg:
  static const int64_t not_va_arg = -1;
  static const int64_t va_baseptr = -2;
  static const int64_t first_nonfp_arg = 0;
  static const int64_t first_fp_arg = 0x00010000;
  static const int64_t max_arg = 0x00020000;

  bool isPtrAsInt() {
    return offset != noOffset;
  }

  bool isVaArg() {
    return va_arg != not_va_arg;
  }

  int getVaArgType() {

    if(va_arg == not_va_arg)
      return va_arg_type_none;
    else if(va_arg == va_baseptr)
      return va_arg_type_baseptr;
    else if(va_arg >= first_nonfp_arg && va_arg < first_fp_arg)
      return va_arg_type_nonfp;
    else if(va_arg >= first_fp_arg && va_arg < max_arg)
      return va_arg_type_fp;
    else
      assert(0 && "Bad va_arg value\n");
    return va_arg_type_none;

  }

  int64_t getVaArg() {

    switch(getVaArgType()) {
    case va_arg_type_fp:
      return va_arg - first_fp_arg;
    case va_arg_type_nonfp:
      return va_arg;
    default:
      assert(0);
    }

  }

} ValCtx;

inline bool operator==(ValCtx V1, ValCtx V2) {
  return V1.first == V2.first && V1.second == V2.second && V1.offset == V2.offset && V1.va_arg == V2.va_arg;
}

inline bool operator!=(ValCtx V1, ValCtx V2) {
   return !(V1 == V2);
}

inline bool operator<(ValCtx V1, ValCtx V2) {
  if(V1.first != V2.first)
    return V1.first < V2.first;

  if(V1.second != V2.second)
    return V1.second < V2.second;

  if(V1.offset != V2.offset)
    return V1.offset < V2.offset;

  return V1.va_arg < V2.va_arg;
}

inline bool operator<=(ValCtx V1, ValCtx V2) {
  return V1 < V2 || V1 == V2;
}

inline bool operator>(ValCtx V1, ValCtx V2) {
  return !(V1 <= V2);
}

inline bool operator>=(ValCtx V1, ValCtx V2) {
  return !(V1 < V2);
}

enum IntegratorWQItemType {

   TryEval,
   CheckBlock,
   CheckLoad,
   OpenPush

};

// A cheesy hack to make a value type that acts like a dynamic dispatch hierarchy
struct IntegratorWQItem {

  IntegrationAttempt* ctx;
  IntegratorWQItemType type;
  union {
    LoadInst* LI;
    Value* V;
    BasicBlock* BB;
    struct {
      CallInst* OpenI;
      ValCtx OpenProgress;
    } OpenArgs;
    IntegrationHeuristicsPass* IHP;
  } u;

 IntegratorWQItem(IntegrationAttempt* c, LoadInst* L) : ctx(c), type(CheckLoad) { u.LI = L; }
 IntegratorWQItem(IntegrationAttempt* c, Value* V) : ctx(c), type(TryEval) { u.V = V; }
 IntegratorWQItem(IntegrationAttempt* c, BasicBlock* BB) : ctx(c), type(CheckBlock) { u.BB = BB; }
 IntegratorWQItem(IntegrationAttempt* c, CallInst* OpenI, ValCtx OpenProgress) : ctx(c), type(OpenPush) { u.OpenArgs.OpenI = OpenI; u.OpenArgs.OpenProgress = OpenProgress; }
IntegratorWQItem() { }

  void execute();
  void describe(raw_ostream& s);

};

// PointerBase: an SCCP-like value giving candidate constants or pointer base addresses for a value.
// May be: 
// overdefined (overflowed, or defined by an unknown)
// defined (known set of possible values)
// undefined (implied by absence from map)
// Note Value members may be null (signifying a null pointer) without being Overdef.

#define PBMAX 16

enum ValSetType {

  ValSetTypeUnknown,
  ValSetTypePB,
  ValSetTypeScalar

};

bool extractCEBase(Constant* C, ValCtx& VC);
bool functionIsBlacklisted(Function*);

struct PointerBase {

  ValSetType Type;
  SmallVector<ValCtx, 4> Values;
  bool Overdef;

PointerBase() : Type(ValSetTypeUnknown), Overdef(false) { }
PointerBase(ValSetType T) : Type(T), Overdef(false) { }
PointerBase(ValSetType T, bool OD) : Type(T), Overdef(OD) { }

  bool isInitialised() {
    return Overdef || Values.size() > 0;
  }
  
  PointerBase& insert(ValCtx VC) {
    if(Overdef)
      return *this;
    if(std::count(Values.begin(), Values.end(), VC))
      return *this;
    if(Values.size() + 1 > PBMAX) {
      setOverdef();
    }
    else {
      Values.push_back(VC);
    }
    return *this;
  }

  PointerBase& merge(PointerBase& OtherPB) {
    if(OtherPB.Overdef) {
      setOverdef();
    }
    else if(isInitialised() && OtherPB.Type != Type) {
      setOverdef();
    }
    else {
      Type = OtherPB.Type;
      for(SmallVector<ValCtx, 4>::iterator it = OtherPB.Values.begin(), it2 = OtherPB.Values.end(); it != it2 && !Overdef; ++it)
	insert(*it);
    }
    return *this;
  }

  void setOverdef() {

    Values.clear();
    Overdef = true;

  }

  static PointerBase get(ValCtx VC);
  static PointerBase get(ValCtx VC, ValSetType t) { return PointerBase(t).insert(VC); }
  static PointerBase getOverdef() { return PointerBase(ValSetTypeUnknown, true); }
  
};

class IntegrationHeuristicsPass : public ModulePass {

   DenseMap<Function*, LoopInfo*> LIs;
   DenseMap<Function*, DenseMap<Instruction*, const Loop*>* > invariantInstScopes;
   DenseMap<Function*, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>* > invariantEdgeScopes;
   DenseMap<Function*, DenseMap<BasicBlock*, const Loop*>* > invariantBlockScopes;

   DenseMap<Function*, PostDominatorTree*> PDTs;
   DenseMap<const Loop*, std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> > LoopPDTs;

   DenseMap<Function*, BasicBlock*> uniqueReturnBlocks;

   SmallSet<Function*, 4> alwaysInline;
   DenseMap<const Loop*, std::pair<BasicBlock*, BasicBlock*> > optimisticLoopMap;
   DenseMap<Function*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 1 > > assumeEdges;
   DenseMap<Function*, SmallSet<BasicBlock*, 1> > ignoreLoops;
   DenseMap<std::pair<Function*, BasicBlock*>, uint64_t> maxLoopIters;

   TargetData* TD;
   AliasAnalysis* AA;

   SmallVector<IntegratorWQItem, 64> workQueue1;
   SmallVector<IntegratorWQItem, 64> workQueue2;

   SmallVector<IntegratorWQItem, 64>* produceQueue;

   SmallVector<ValCtx, 64> dieQueue1;
   SmallVector<ValCtx, 64> dieQueue2;

   SmallVector<ValCtx, 64>* produceDIEQueue;

   SmallVector<ValCtx, 64> PBQueue1;
   SmallVector<ValCtx, 64> PBQueue2;

   SmallVector<ValCtx, 64>* PBProduceQ;

   std::vector<ValCtx> pendingPBChecks1;
   std::vector<ValCtx> pendingPBChecks2;
   std::vector<ValCtx>* producePendingPBChecks;

   uint64_t PBGeneration;

   IntegrationAttempt* RootIA;

   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > briefFunctionTextCache;
   bool cacheDisabled;

   unsigned mallocAlignment;

 public:

   static char ID;

   uint64_t SeqNumber;

   uint64_t PBLFAs;
   uint64_t PBLFAsCached;

   DenseMap<ValCtx, PointerBase> PBsConsideredThisRun;

   explicit IntegrationHeuristicsPass() : ModulePass(ID), cacheDisabled(false) { 

     PBProduceQ = &PBQueue2;
     producePendingPBChecks = &pendingPBChecks2;
     produceDIEQueue = &dieQueue2;
     produceQueue = &workQueue2;
     PBGeneration = 0;
     mallocAlignment = 0;
     SeqNumber = 0;

   }

   bool runOnModule(Module& M);

   void queueTryEvaluate(IntegrationAttempt* ctx, Value* val);
   void queueCheckBlock(IntegrationAttempt* ctx, BasicBlock* BB);
   void queueCheckLoad(IntegrationAttempt* ctx, LoadInst* LI);
   void queueOpenPush(ValCtx OpenInst, ValCtx OpenProgress);
   void queueDIE(IntegrationAttempt* ctx, Value* val);

   void print(raw_ostream &OS, const Module* M) const;

   void releaseMemory(void);

   void createInvariantScopes(Function*, DenseMap<Instruction*, const Loop*>*&, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>*&, DenseMap<BasicBlock*, const Loop*>*&);
   DenseMap<Instruction*, const Loop*>& getInstScopes(Function* F);
   DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& getEdgeScopes(Function* F);
   DenseMap<BasicBlock*, const Loop*>& getBlockScopes(Function* F);

   BasicBlock* getUniqueReturnBlock(Function* F);

   void runQueues();
   bool runQueue();
   void runDIEQueue();

   void revertLoadsFromFoldedContexts();
   void retryLoadsFromFoldedContexts();

   PostDominatorTree* getPostDomTree(Function*);
   DomTreeNodeBase<const BBWrapper>* getPostDomTreeNode(const Loop*, BasicBlock*);

   // Caching text representations of instructions:

   DenseMap<const Instruction*, std::string>& getFunctionCache(const Function* F, bool brief);
   void printValue(raw_ostream& ROS, const Value* V, bool brief);
   void printValue(raw_ostream& ROS, ValCtx VC, bool brief);
   void printValue(raw_ostream& ROS, const MemDepResult& Res, bool brief);
   void disableValueCache();

   Constant* loadEnvironment(Module&, std::string&);
   void loadArgv(Function*, std::string&, unsigned argvidx, unsigned& argc);
   void setParam(IntegrationAttempt* IA, Function& F, long Idx, Constant* Val);
   void parseArgs(InlineAttempt* RootIA, Function& F);

   void runPointerBaseSolver(bool finalise, std::vector<ValCtx>*);
   bool runPointerBaseSolver();
   void queueUpdatePB(IntegrationAttempt* IA, Value* V);
   void queueNewPBWork(uint64_t& newVCs, uint64_t& changedVCs);

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

   bool assumeEndsAfter(Function* F, BasicBlock* HBB, uint64_t C) {
     DenseMap<std::pair<Function*, BasicBlock*>, uint64_t>::iterator it = maxLoopIters.find(std::make_pair(F, HBB));
     if(it == maxLoopIters.end())
       return false;
     return it->second == C;
   }

   void queuePendingPBUpdate(ValCtx VC) {
     producePendingPBChecks->push_back(VC);
   }

   void addPessimisticSolverWork();

   unsigned getMallocAlignment();

   uint64_t getSeq() {
     return SeqNumber++;
   }

   IntegrationAttempt* getRoot() { return RootIA; }
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

#define VCNull (make_vc(0, 0))
 
inline ValCtx make_vc(Value* V, IntegrationAttempt* H, int64_t Off = ValCtx::noOffset, int64_t VaArg = ValCtx::not_va_arg) {

  ValCtx newCtx = {V, H, Off, VaArg};
  return newCtx;

}

inline ValCtx const_vc(Constant* C) {

  return make_vc(C, 0);

}

// Characteristics for using ValCtxs in hashsets (DenseSet, or as keys in DenseMaps)
template<> struct DenseMapInfo<ValCtx> {
  
  typedef DenseMapInfo<Value*> VInfo;
  typedef DenseMapInfo<IntegrationAttempt*> IAInfo;
  typedef DenseMapInfo<std::pair<Value*, IntegrationAttempt*> > PairInfo;

  static inline ValCtx getEmptyKey() {
    return make_vc(VInfo::getEmptyKey(), IAInfo::getEmptyKey());
  }

  static inline ValCtx getTombstoneKey() {
    return make_vc(VInfo::getTombstoneKey(), IAInfo::getTombstoneKey());
  }

  static unsigned getHashValue(const ValCtx& VC) {
    return PairInfo::getHashValue(std::make_pair(VC.first, VC.second));
  }

  static bool isEqual(const ValCtx& V1, const ValCtx& V2) {
    return V1 == V2;
  }

 };

// Define PartialVal, a container that gives a resolution to a load attempt, either wholly with a ValCtx
// or partially with a Constant plus a byte extent and offset from which that Constant should be read.

enum PartialValType {

  PVInvalid,
  PVTotal,
  PVPartial

};

struct PartialVal {

  PartialValType type;
  ValCtx TotalVC;
  uint64_t FirstDef;
  uint64_t FirstNotDef;
  Constant* C;
  uint64_t ReadOffset;

 PartialVal(ValCtx Total) : 
  type(PVTotal), TotalVC(Total), FirstDef(0), FirstNotDef(0), C(0), ReadOffset(0) { }
 PartialVal(uint64_t FD, uint64_t FND, Constant* _C, uint64_t Off) : 
  type(PVPartial), TotalVC(VCNull), FirstDef(FD), FirstNotDef(FND), C(_C), ReadOffset(Off) { }
 PartialVal() :
  type(PVInvalid), TotalVC(VCNull), FirstDef(0), FirstNotDef(0), C(0), ReadOffset(0) { }

  bool isPartial() { return type == PVPartial; }
  bool isTotal() { return type == PVTotal; }
  
  static PartialVal getPartial(uint64_t FD, uint64_t FND, Constant* _C, uint64_t Off) {
    return PartialVal(FD, FND, _C, Off);
  }

  static PartialVal getTotal(ValCtx VC) {
    return PartialVal(VC);
  }

};

#define PVNull PartialVal()

inline bool operator==(PartialVal V1, PartialVal V2) {
  if(V1.type == PVInvalid && V2.type == PVInvalid)
    return true;
  else if(V1.type == PVTotal && V2.type == PVTotal)
    return V1.TotalVC == V2.TotalVC;
  else if(V1.type == PVPartial && V2.type == PVPartial)
    return ((V1.FirstDef == V2.FirstDef) &&
	    (V1.FirstNotDef == V2.FirstNotDef) &&
	    (V1.C == V2.C) &&
	    (V1.ReadOffset == V2.ReadOffset));

  return false;
}

inline bool operator!=(PartialVal V1, PartialVal V2) {
   return !(V1 == V2);
}

enum SymSubclasses {

  SThunk,
  SGEP,
  SCast

};

class SymExpr { 

public:
  static inline bool classof(const SymExpr*) { return true; }
  virtual void describe(raw_ostream& OS, IntegrationAttempt*) = 0;
  virtual int getSymType() const = 0;

};

class SymThunk : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SThunk; }
  static inline bool classof(const SymThunk*) { return true; }
  ValCtx RealVal;

  SymThunk(ValCtx R) : RealVal(R) { }
  void describe(raw_ostream& OS, IntegrationAttempt*);
  int getSymType() const { return SThunk; }

};

class SymGEP : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SGEP; }
  static inline bool classof(const SymGEP*) { return true; }
  SmallVector<Value*, 4> Offsets; // Really all ConstantInts

  SymGEP(SmallVector<Value*, 4> Offs) : Offsets(Offs) { }

  void describe(raw_ostream& OS, IntegrationAttempt*);
  int getSymType() const { return SGEP; }

};

class SymCast : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SCast; }
  static inline bool classof(const SymCast*) { return true; }
  const Type* ToType;

  SymCast(const Type* T) : ToType(T) { }

  void describe(raw_ostream& OS, IntegrationAttempt*);
  int getSymType() const { return SCast; }

};

class LoadForwardAttempt;
class LFARealization;
class LFAQueryable;

struct OpenStatus {

  std::string Name;
  bool success;
  bool FDEscapes;
  ValCtx LatestResolvedUser;
  ValCtx FirstUser;

OpenStatus(ValCtx O, std::string N, bool Success, bool Esc) : Name(N), success(Success), FDEscapes(Esc), LatestResolvedUser(O), FirstUser(VCNull) { }

OpenStatus() : Name(""), success(false), FDEscapes(false), LatestResolvedUser(VCNull) {}

};

struct ReadFile {

  struct OpenStatus* openArg;
  uint64_t incomingOffset;
  uint32_t readSize;
  ValCtx NextUser;

ReadFile(struct OpenStatus* O, uint64_t IO, uint32_t RS) : openArg(O), incomingOffset(IO), readSize(RS), NextUser(VCNull) { }

ReadFile() : openArg(0), incomingOffset(0), readSize(0) { }

};

struct SeekFile {

  struct OpenStatus* openArg;
  uint64_t newOffset;
  ValCtx NextUser;

SeekFile(struct OpenStatus* O, uint64_t Off) : openArg(O), newOffset(Off), NextUser(VCNull) { }
  
SeekFile() : openArg(0), newOffset(0) { }

};

struct CloseFile {

  struct OpenStatus* openArg;
  bool canRemove;

CloseFile(struct OpenStatus* O) : openArg(O), canRemove(false) {}
CloseFile() : openArg(0), canRemove(false) {}

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

  virtual void visit(IntegrationAttempt* Context, Instruction* UserI) = 0;
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

enum LoadForwardMode {

  LFMNormal,
  LFMPB

};

class IntegrationAttempt {

protected:

  IntegrationHeuristicsPass* pass;

  // Analyses created by the Pass.
  DenseMap<Function*, LoopInfo*>& LI;
  TargetData* TD;
  AliasAnalysis* AA;

  Function& F;

  std::string HeaderStr;

  DenseMap<Instruction*, const Loop*>& invariantInsts;
  DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges;
  DenseMap<BasicBlock*, const Loop*>& invariantBlocks;

  DenseMap<Value*, ValCtx> improvedValues;

  SmallSet<BasicBlock*, 4> deadBlocks;
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> deadEdges;
  SmallSet<BasicBlock*, 4> certainBlocks;

  // Instructions which have no users (discounting side-effects) after discounting instructions
  // which will be RAUW'd or deleted on commit.
  DenseSet<Value*> deadValues;
  // Instructions which write memory, but whose results are never read. These may be deleted.
  DenseSet<Value*> unusedWriters;
  // A list of dead stores and allocations which in the course of being found dead traversed this context.
  // These should be discounted as unused writes if we are folded.
  DenseSet<ValCtx> unusedWritersTraversingThisContext;

  int improvableInstructions;
  int improvedInstructions;
  SmallVector<CallInst*, 4> unexploredCalls;
  SmallVector<const Loop*, 4> unexploredLoops;

  SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4> CFGBlockedLoads;
  DenseMap<Instruction*, SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4> > InstBlockedLoads;
  DenseMap<LoadInst*, MemDepResult> LastLoadFailures;
  DenseMap<LoadInst*, SmallVector<NonLocalDepResult, 4> > LastLoadOverdefs;

  SmallVector<std::pair<ValCtx, ValCtx>, 4> CFGBlockedOpens;
  DenseMap<Instruction*, SmallVector<std::pair<ValCtx, ValCtx>, 4> > InstBlockedOpens;

  SmallVector<ValCtx, 1> BlockedVALoads;

  DenseMap<CallInst*, OpenStatus*> forwardableOpenCalls;
  DenseMap<CallInst*, ReadFile> resolvedReadCalls;
  DenseMap<CallInst*, SeekFile> resolvedSeekCalls;
  DenseMap<CallInst*, CloseFile> resolvedCloseCalls;

  // Pointers resolved down to their base object, but not necessarily the offset:
  DenseMap<Value*, PointerBase> pointerBases;
  DenseMap<LoadInst*, std::vector<ValCtx> > defOrClobberCache;
  DenseMap<LoadInst*, std::string> failedLFACache;
  DenseMap<Instruction*, DenseSet<std::pair<LoadInst*, IntegrationAttempt*> > > memWriterEffects;
  DenseMap<CallInst*, std::vector<std::pair<LoadInst*, IntegrationAttempt*> > > callBlockedPBLoads;
  DenseSet<std::pair<LoadInst*, IntegrationAttempt*> > CFGDependentPBLoads;
  DenseMap<Instruction*, std::string> optimisticForwardStatus;
  DenseMap<Instruction*, std::string> pessimisticForwardStatus;

  // Inline attempts / peel attempts which are currently ignored because they've been opted out.
  // These may include inlines / peels which are logically two loop levels deep, 
  // because they were created when a parent loop was opted out but then opted in again.
  DenseSet<CallInst*> ignoreIAs;
  DenseSet<const Loop*> ignorePAs;

  // A map from the Values used in all of the above to the clones of Instructions produced at commit time
  ValueMap<const Value*, Value*> CommittedValues;
  bool commitStarted;
  // The LoopInfo belonging to the function which is being specialised
  LoopInfo* MasterLI;

  std::string nestingIndent() const;

  int nesting_depth;
  uint64_t SeqNumber;

 public:

  bool contextIsDead;

  struct IntegratorTag tag;

  IntegrationAttempt* parent;

  DenseMap<CallInst*, InlineAttempt*> inlineChildren;
  DenseMap<const Loop*, PeelAttempt*> peelChildren;
    
 IntegrationAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA,
		    DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth) : 
  pass(Pass),
    LI(_LI),
    TD(_TD), 
    AA(_AA), 
    F(_F),
    invariantInsts(_invariantInsts),
    invariantEdges(_invariantEdges),
    invariantBlocks(_invariantBlocks),
    improvedValues(4),
    deadValues(4),
    unusedWriters(4),
    unusedWritersTraversingThisContext(2),
    improvableInstructions(0),
    improvedInstructions(0),
    InstBlockedLoads(4),
    InstBlockedOpens(2),
    forwardableOpenCalls(2),
    resolvedReadCalls(2),
    resolvedSeekCalls(2),
    resolvedCloseCalls(2),
    ignoreIAs(2),
    ignorePAs(2),
    CommittedValues(2),
    commitStarted(false),
    nesting_depth(depth),
    contextIsDead(false),
    parent(P),
    inlineChildren(1),
    peelChildren(1)
      { 
	this->tag.ptr = (void*)this;
	this->tag.type = IntegratorTypeIA;
      }

  ~IntegrationAttempt();

  Module& getModule();

  virtual AliasAnalysis* getAA();

  void markContextDead();
  virtual ValCtx getDefaultVC(Value*);
  virtual ValCtx getReplacement(Value* V);
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*);
  virtual bool blockIsDead(BasicBlock*);

  Function& getFunction() { return F; }
  
  const Loop* getValueScope(Value*);
  ValCtx getLocalReplacement(Value*);
  ValCtx getReplacementUsingScope(Value* V, const Loop* LScope);
  ValCtx getReplacementUsingScopeRising(Instruction* I, BasicBlock* ExitingBlock, BasicBlock* ExitBlock, const Loop* LScope);
  ValCtx getPtrAsIntReplacement(Value* V);
  void callWithScope(Callable& C, const Loop* LScope);
  ValCtx getDefaultVCWithScope(Value*, const Loop*);

  const Loop* getEdgeScope(BasicBlock*, BasicBlock*);
  bool edgeIsDeadWithScope(BasicBlock*, BasicBlock*, const Loop*);
  bool edgeIsDeadWithScopeRising(BasicBlock*, BasicBlock*, const Loop*);

  const Loop* applyIgnoreLoops(const Loop*);
  const Loop* getBlockScope(BasicBlock*);
  // The variant version ignores block-liveness invariance, but does apply flattened loops.
  const Loop* getBlockScopeVariant(BasicBlock*);
  bool blockIsDeadWithScope(BasicBlock*, const Loop*);

  bool blockIsCertain(BasicBlock*);

  bool shouldForwardValue(ValCtx);

  virtual ValCtx getUltimateUnderlyingObject(Value*);

  virtual BasicBlock* getEntryBlock() = 0;
  virtual bool hasParent();
  bool isRootMainCall();
  
  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual const Loop* getLoopContext() = 0;
  virtual Instruction* getEntryInstruction() = 0;
  virtual void collectAllLoopStats() = 0;
  void printHeader(raw_ostream& OS) const;
  virtual void queueTryEvaluateOwnCall() = 0;
  virtual bool isOptimisticPeel() = 0;

  // Simple state-tracking helpers:

  virtual void setReplacement(Value*, ValCtx);
  void eraseReplacement(Value*);
  bool isUnresolved(Value*);
  bool hasResolvedPB(Value*);
  void setEdgeDead(BasicBlock*, BasicBlock*);
  void setBlockDead(BasicBlock*);

  virtual Constant* getConstReplacement(Value* V);
  virtual Function* getCalledFunction(CallInst*);
  
  virtual InlineAttempt* getFunctionRoot() = 0;

  // Constant propagation:

  bool shouldTryEvaluate(Value* ArgV, bool verbose = true);
  bool shouldInvestigateUser(Value* ArgV, bool verbose, Value* UsedV);

  ValCtx getPHINodeValue(PHINode*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  void tryEvaluate(Value*);
  virtual ValCtx tryEvaluateResult(Value*);
  virtual void investigateUsers(Value* V, bool queueOptimistic = true);

  void queueTryEvaluateGeneric(Instruction* UserI, Value* Used);

  bool tryFoldPointerCmp(CmpInst* CmpI, ValCtx&);
  ValCtx tryFoldPtrToInt(Instruction*);
  ValCtx tryFoldIntToPtr(Instruction*);
  bool tryFoldPtrAsIntOp(Instruction*, ValCtx&);
  //bool tryFoldVarargAdd(BinaryOperator*, ValCtx&);

  // CFG analysis:

  bool shouldCheckBlock(BasicBlock* BB);
  virtual bool shouldCheckEdge(BasicBlock* FromBB, BasicBlock* ToBB) = 0;
  void checkBlock(BasicBlock* BB);
  void checkSuccessors(BasicBlock* BB);
  void checkBlockPHIs(BasicBlock*);
  void markBlockCertain(BasicBlock* BB);
  void checkEdge(BasicBlock*, BasicBlock*);
  void checkEdge(BasicBlock*, BasicBlock*, const Loop*);
  void checkVariantEdge(BasicBlock*, BasicBlock*, const Loop* Scope);
  void checkLocalEdge(BasicBlock*, BasicBlock*);
  virtual bool checkLoopSpecialEdge(BasicBlock*, BasicBlock*);
  PostDominatorTree* getPostDomTree();
  bool shouldAssumeEdge(BasicBlock* BB1, BasicBlock* BB2) {
    return pass->shouldAssumeEdge(&F, BB1, BB2);
  }
  void eraseBlockValues(BasicBlock*);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(CallInst* CI);
  InlineAttempt* getOrCreateInlineAttempt(CallInst* CI);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  void checkLoad(LoadInst* LI);
  ValCtx tryForwardLoad(LoadInst*);
  ValCtx tryForwardLoad(LoadForwardAttempt&, Instruction* StartBefore);
  MemDepResult tryResolveLoad(LoadForwardAttempt&);
  MemDepResult tryResolveLoad(LoadForwardAttempt&, Instruction* StartBefore, ValCtx& ConstResult);
  ValCtx getForwardedValue(LoadForwardAttempt&, MemDepResult Res);
  bool tryResolveLoadFromConstant(LoadInst*, ValCtx& Result);
  
  bool forwardLoadIsNonLocal(LFAQueryable&, MemDepResult& Result, SmallVector<BasicBlock*, 4>* StartBlocks, bool& MayDependOnParent);
  void getDefn(const MemDepResult& Res, ValCtx& VCout);
  void getDependencies(LFAQueryable& LFA, SmallVector<BasicBlock*, 4>* StartBlocks, SmallVector<NonLocalDepResult, 4>& Results);
  void addPBResults(LoadForwardAttempt& RealLFA, SmallVector<NonLocalDepResult, 4>& Results, bool populateCache);
  MemDepResult getUniqueDependency(LFAQueryable&, SmallVector<BasicBlock*, 4>* StartBlocks, bool& MayDependOnParent, bool& OnlyDependsOnParent);

  virtual MemDepResult tryForwardExprFromParent(LoadForwardAttempt&) = 0;
  MemDepResult tryResolveLoadAtChildSite(IntegrationAttempt* IA, LoadForwardAttempt&);
  bool tryResolveExprFrom(LoadForwardAttempt& LFA, Instruction* Where, MemDepResult& Result, SmallVector<BasicBlock*, 4>* StartBlocks, bool& MayDependOnParent);
  bool tryResolveExprFrom(LoadForwardAttempt& LFA, Instruction* Where, MemDepResult& Result, ValCtx& ConstResult, bool& MayDependOnParent);
  bool tryResolveExprUsing(LFARealization& LFAR, MemDepResult& Result, SmallVector<BasicBlock*, 4>* StartBlocks, bool& MayDependOnParent);

  virtual bool tryForwardLoadThroughCall(LoadForwardAttempt&, CallInst*, MemDepResult&, bool& mayDependOnParent);
  virtual bool tryForwardLoadThroughLoop(BasicBlock* BB, LoadForwardAttempt&, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result);

  void addBlockedLoad(Instruction* BlockedOn, IntegrationAttempt* RetryCtx, LoadInst* RetryLI);
  void addCFGBlockedLoad(IntegrationAttempt* RetryCtx, LoadInst* RetryLI);
  virtual void queueLoopExpansionBlockedLoad(Instruction*, IntegrationAttempt*, LoadInst*);

  void queueWorkBlockedOn(Instruction* SI);
  void queueCFGBlockedLoads();
  void queueCheckAllLoadsInScope(const Loop*);
  void queueCheckAllInstructionsInScope(const Loop*);
  void queuePBCheckAllInstructionsInScope(const Loop*);

  void setLoadOverdef(LoadInst* LI, SmallVector<NonLocalDepResult, 4>& Res);

  // VFS call forwarding:

  virtual bool isForwardableOpenCall(Value*);
  bool openCallSucceeds(Value*);
  virtual int64_t tryGetIncomingOffset(Value*);
  virtual ReadFile* tryGetReadFile(CallInst* CI);
  void tryPromoteOpenCall(CallInst* CI);
  void tryPromoteAllCalls();
  void queueInitialWork();
  void tryPushOpen(CallInst*, ValCtx);
  virtual bool tryPushOpenFrom(ValCtx&, ValCtx, ValCtx, OpenStatus&, bool, SmallVector<ValCtx, 2>& Defs, SmallVector<ValCtx, 2>& Clobbers);
  bool setVFSSuccessor(CallInst* VFSCall, ValCtx OpenInst, ValCtx LastReadInst, OpenStatus& OS);
  ValCtx getSuccessorVC(BasicBlock* BB);
  void queueSuccessorVCFalling(Instruction* I, SmallSet<ValCtx, 8>& Visited, SmallVector<ValCtx, 8>& PList, bool& CFGTrouble, const Loop* SuccLoop);
  void queueSuccessorVCs(ValCtx, ValCtx, BasicBlock* BB, SmallSet<ValCtx, 8>& Visited, SmallVector<ValCtx, 8>& PList, bool& CFGTrouble);
  virtual bool checkLoopIteration(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) = 0;
  virtual bool checkOrQueueLoopIteration(ValCtx, ValCtx, BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) = 0;
  bool vfsCallBlocksOpen(CallInst*, ValCtx, ValCtx, OpenStatus&, bool&, bool&);
  ValCtx tryFoldOpenCmp(CmpInst* CmpI, ConstantInt* CmpInt, bool flip);
  bool tryFoldOpenCmp(CmpInst* CmpI, ValCtx&);
  virtual void resolveReadCall(CallInst*, struct ReadFile);
  virtual void resolveSeekCall(CallInst*, struct SeekFile);
  void setNextUser(CallInst* CI, ValCtx U);
  void setNextUser(OpenStatus& OS, ValCtx U);
  virtual void addBlockedOpen(ValCtx, ValCtx);
  void queueCFGBlockedOpens();
  bool isResolvedVFSCall(const Instruction*);
  bool isSuccessfulVFSCall(const Instruction*);
  bool isUnusedReadCall(CallInst*);
  ValCtx getNextVFSUser(CallInst*);
  bool isCloseCall(CallInst*);

  // Tricky load forwarding (stolen from GVN)

  ValCtx handlePartialDefnByConst(LoadForwardAttempt&, uint64_t, uint64_t, Constant*, ValCtx);
  ValCtx handlePartialDefn(LoadForwardAttempt&, uint64_t, uint64_t, ValCtx);
  ValCtx handleTotalDefn(LoadForwardAttempt&, ValCtx);
  ValCtx handleTotalDefn(LoadForwardAttempt&, Constant*);

  bool AnalyzeLoadFromClobberingWrite(LoadForwardAttempt&,
				     Value *WritePtr, IntegrationAttempt* WriteCtx,
				     uint64_t WriteSizeInBits,
				     uint64_t& FirstDef, 
				     uint64_t& FirstNotDef, 
				     uint64_t& ReadOffset);

  bool AnalyzeLoadFromClobberingWrite(LoadForwardAttempt&,
				     ValCtx StoreBase, int64_t StoreOffset,
				     uint64_t WriteSizeInBits,
				     uint64_t& FirstDef, 
				     uint64_t& FirstNotDef, 
				     uint64_t& ReadOffset);
				     
  bool AnalyzeLoadFromClobberingStore(LoadForwardAttempt&, StoreInst *DepSI, IntegrationAttempt* DepSICtx,
				     uint64_t& FirstDef, 
				     uint64_t& FirstNotDef, 
				     uint64_t& ReadOffset);

  bool AnalyzeLoadFromClobberingMemInst(LoadForwardAttempt&, MemIntrinsic *MI, IntegrationAttempt* MICtx,
				       uint64_t& FirstDef, 
				       uint64_t& FirstNotDef, 
				       uint64_t& ReadOffset);

  Constant* offsetConstantInt(Constant* SourceC, int64_t Offset, const Type* targetTy);
  ValCtx GetBaseWithConstantOffset(Value *Ptr, IntegrationAttempt* PtrCtx, int64_t &Offset);
  bool CanCoerceMustAliasedValueToLoad(Value *StoredVal, const Type *LoadTy);
  Constant* CoerceConstExprToLoadType(Constant *StoredVal, const Type *LoadedTy);
  bool GetDefinedRange(ValCtx DefinedBase, int64_t DefinedOffset, uint64_t DefinedSizeBits,
		       ValCtx DefinerBase, int64_t DefinerOffset, uint64_t DefinerSizeBits,
		       uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset);
  PartialVal tryResolveClobber(LoadForwardAttempt& LFA, ValCtx Clobber, bool isEntryNonLocal);
  PartialVal tryForwardFromCopy(LoadForwardAttempt& LFA, ValCtx Clobber, const Type* subTargetType, Value* copySource, Instruction* copyInst, uint64_t OffsetCI, uint64_t FirstDef, uint64_t FirstNotDef);
  // Load forwarding extensions for varargs:
  void queueBlockedVAs();
  void blockVA(ValCtx);
  virtual void getVarArg(int64_t, ValCtx&) = 0;
  int64_t getSpilledVarargAfter(CallInst* CI, int64_t OldArg);
  
  // Dead store and allocation elim:

  bool tryKillStore(StoreInst* SI);
  bool tryKillMemset(MemIntrinsic* MI);
  bool tryKillMTI(MemTransferInst* MTI);
  bool tryKillAlloc(Instruction* Alloc);
  bool tryKillRead(CallInst*, ReadFile&);
  bool tryKillWriterTo(Instruction* Writer, Value* WritePtr, uint64_t Size);
  bool DSEHandleWrite(ValCtx Writer, uint64_t WriteSize, ValCtx StorePtr, uint64_t Size, ValCtx StoreBase, int64_t StoreOffset, bool* deadBytes);
  bool isLifetimeEnd(ValCtx Alloc, Instruction* I);
  void addTraversingInst(ValCtx);
  virtual bool tryKillStoreFrom(ValCtx& Start, ValCtx StorePtr, ValCtx StoreBase, int64_t StoreOffset, bool* deadBytes, uint64_t Size, bool skipFirst, bool& Killed);
  bool CollectMTIsFrom(ValCtx& Start, std::vector<ValCtx>& MTIs);
  void tryKillAllMTIs();
  bool tryKillAllStoresFrom(ValCtx& Start);
  void tryKillAllStores();
  bool tryKillAllAllocsFrom(ValCtx& Start);
  void tryKillAllAllocs();

  // User visitors:
  
  virtual bool visitNextIterationPHI(Instruction* I, VisitorContext& Visitor);
  virtual void visitExitPHI(Instruction* UserI, VisitorContext& Visitor);
  void visitExitPHIWithScope(Instruction* UserI, VisitorContext& Visitor, const Loop*);
  void visitUsers(Value* V, VisitorContext& Visitor);
  void visitUser(Value* UI, VisitorContext& Visitor);

  // Operand visitors:

  void walkOperand(Value* V, OpCallback& CB);
  virtual bool walkHeaderPHIOperands(PHINode*, OpCallback&) = 0;
  virtual void walkOperands(Value* V, OpCallback& CB);

  // Dead instruction elim:

  bool valueIsDead(Value* V);
  bool shouldDIE(Value* V);
  void queueDIE(Value* V, IntegrationAttempt* Ctx);
  void queueDIE(Value* V);
  bool valueWillBeRAUWdOrDeleted(Value* V);
  bool valueWillNotUse(Value* V, ValCtx);
  bool inDeadValues(Value* V);
  void queueDIEOperands(Value* V);
  void tryKillValue(Value* V);
  virtual void queueAllLiveValuesMatching(UnaryPred& P);
  void queueAllReturnInsts();
  void queueAllLiveValues();

  // Pointer base analysis
  bool getPointerBaseLocal(Value* V, PointerBase& OutPB);
  bool getPointerBaseRising(Value* V, PointerBase& OutPB, const Loop* VL);
  virtual bool getPointerBaseFalling(Value* V, PointerBase& OutPB);
  bool getPointerBase(Value* V, PointerBase& OutPB, Instruction* UserI);
  void erasePointerBase(Value*);
  bool getValSetOrReplacement(Value* V, PointerBase& OutPB, Instruction* UserI = 0);
  bool getMergeBasePointer(Instruction* I, bool finalise, PointerBase& NewPB);
  bool updateBasePointer(Value* V, bool finalise);
  bool updateBinopValSet(Instruction* I, PointerBase& PB);
  bool updateUnaryValSet(Instruction* I, PointerBase &PB);
  void queueUpdatePB(IntegrationAttempt*, Value*, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);
  void queueUsersUpdatePB(Value* V, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);
  void queueUserUpdatePB(Value*, Instruction* User, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);
  void queueUsersUpdatePBFalling(Instruction* I, const Loop* IL, Value* V, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);
  void queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);
  void resolvePointerBase(Value* V, PointerBase&);
  void queuePendingWorkFromUpdatedPB(Value* V, PointerBase&);
  void queuePBUpdateAllUnresolvedVCsInScope(const Loop* L);
  void queuePBUpdateIfUnresolved(Value *V);
  void queueUpdatePBWholeLoop(const Loop*);
  virtual bool updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB) = 0;
  void printPB(raw_ostream& out, PointerBase PB, bool brief = false);
  virtual bool ctxContains(IntegrationAttempt*) = 0;
  virtual bool basesMayAlias(ValCtx VC1, ValCtx VC2);
  bool tryForwardLoadPB(LoadInst*, bool finalise, PointerBase& out);
  void addMemWriterEffect(Instruction*, LoadInst*, IntegrationAttempt*);
  void removeMemWriterEffect(Instruction* I, LoadInst* LI, IntegrationAttempt* Ctx);
  void addStartOfScopePB(LoadForwardAttempt&);
  void addStoreToLoadSolverWork(Value* V);
  std::pair<IntegrationAttempt*, const Loop*> getOutermostUnboundLoop(const Loop* childLoop);
  std::pair<IntegrationAttempt*, const Loop*> getOutermostUnboundLoop(CallInst*);
  virtual std::pair<IntegrationAttempt*, const Loop*> getOutermostUnboundLoop() = 0;
  std::pair<IntegrationAttempt*, const Loop*> getOutermostLoop(Value* V);
  bool shouldCheckPB(Value*);

  // PBA caching:
  void zapDefOrClobberCache(LoadInst* LI);
  void addCallBlockedPBLoad(CallInst* CI, LoadInst* LI, IntegrationAttempt* IA);
  void addCFGDependentPBLoad(LoadInst* LI, IntegrationAttempt* IA);
  void dismissCallBlockedPBLoads(CallInst* CI);
  void localCFGChanged();

  std::string describeLFA(LoadForwardAttempt& LFA);
  void printConsiderCount(DenseMap<ValCtx, int>& in, int n);

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
  void revertDSEandDAE();
  void revertDeadValue(Value*);
  void tryKillAndQueue(Instruction*);
  void getRetryStoresAndAllocs(std::vector<ValCtx>&);
  void retryStoresAndAllocs(std::vector<ValCtx>&);
  void revertLoadsFromFoldedContexts();
  void retryLoadsFromFoldedContexts();
  void walkLoadsFromFoldedContexts(bool revert);

  // DOT export:

  void printRHS(Value*, raw_ostream& Out);
  void printOutgoingEdge(BasicBlock* BB, BasicBlock* SB, unsigned i, bool useLabels, SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>* deferEdges, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief);
  void describeBlockAsDOT(BasicBlock* BB, SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4 >* deferEdges, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<BasicBlock*, 4>* ForceSuccessors, bool brief);
  void describeLoopAsDOT(const Loop* L, raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted);
  virtual void describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted) = 0;
  void describeAsDOT(raw_ostream& Out, bool brief);
  std::string getValueColour(Value* I);
  std::string getGraphPath(std::string prefix);
  void describeTreeAsDOT(std::string path);
  virtual bool getSpecialEdgeDescription(BasicBlock* FromBB, BasicBlock* ToBB, raw_ostream& Out) = 0;

  // Caching instruction text for debug and DOT export:
  PrintCacheWrapper<const Value*> itcache(const Value& V, bool brief = false) const {
    return PrintCacheWrapper<const Value*>(*pass, &V, brief);
  }
  PrintCacheWrapper<ValCtx> itcache(ValCtx VC, bool brief = false) const {
    return PrintCacheWrapper<ValCtx>(*pass, VC, brief);
  }
  PrintCacheWrapper<const MemDepResult&> itcache(const MemDepResult& MDR, bool brief = false) const {
    return PrintCacheWrapper<const MemDepResult&>(*pass, MDR, brief);
  }

  void printWithCache(const Value* V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  void printWithCache(ValCtx VC, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, VC, brief);
  }

  void printWithCache(const MemDepResult& Res, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, Res, brief);
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

  // Saving our results as a bitcode file:

  void commit();
  void commitInContext(LoopInfo* MasterLI, ValueMap<const Value*, Value*>& valMap);
  void commitPointers();
  void deleteInstruction(Instruction*);
  void tryDeleteDeadBlock(BasicBlock*, bool);
  virtual void deleteDeadBlocks(bool) = 0;
  void replaceKnownBranch(BasicBlock*, TerminatorInst*);
  virtual void replaceKnownBranches() = 0;
  void commitLocalConstants(ValueMap<const Value*, Value*>& VM);
  Instruction* getCommittedValue(Value*);
  void prepareCommit();
  virtual void localPrepareCommit();
  void removeBlockFromLoops(BasicBlock*);
  void foldVFSCalls();
  void markOrDeleteCloseCall(CallInst*, IntegrationAttempt*);
  virtual bool getLoopBranchTarget(BasicBlock* FromBB, TerminatorInst* TI, TerminatorInst* ReplaceTI, BasicBlock*& Target) = 0;
  
  void commitLocalPointers();

  // Stat collection and printing:

  void collectAllBlockStats();
  void collectBlockStats(BasicBlock* BB);
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

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  const Loop* L;
  PeelAttempt* parentPA;

  BasicBlock* LHeader;
  BasicBlock* LLatch;

  PeelIteration* getNextIteration();
  PeelIteration* getOrCreateNextIteration();

public:

  PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
		AliasAnalysis* _AA, const Loop* _L, DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
		DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int iter, int depth);

  IterationStatus iterStatus;

  virtual Instruction* getEntryInstruction();
  virtual BasicBlock* getEntryBlock();
  virtual const Loop* getLoopContext();

  virtual bool checkLoopSpecialEdge(BasicBlock*, BasicBlock*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  virtual void queueTryEvaluateOwnCall();

  virtual bool shouldCheckEdge(BasicBlock* FromBB, BasicBlock* ToBB);

  void queueCheckExitBlock(BasicBlock* BB);
  void checkExitEdge(BasicBlock*, BasicBlock*);
  void checkFinalIteration();

  virtual MemDepResult tryForwardExprFromParent(LoadForwardAttempt&);

  virtual bool checkLoopIteration(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);
  virtual bool checkOrQueueLoopIteration(ValCtx, ValCtx, BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);

  virtual InlineAttempt* getFunctionRoot();

  virtual void visitExitPHI(Instruction* UserI, VisitorContext& Visitor);
  void visitVariant(Instruction* VI, const Loop* VILoop, VisitorContext& Visitor);
  virtual bool visitNextIterationPHI(Instruction* I, VisitorContext& Visitor);

  virtual bool walkHeaderPHIOperands(PHINode* PN, OpCallback& CB);

  virtual bool getSpecialEdgeDescription(BasicBlock* FromBB, BasicBlock* ToBB, raw_ostream& Out);

  virtual void describe(raw_ostream& Stream) const;
  virtual void describeBrief(raw_ostream& Stream) const;

  virtual void collectAllLoopStats();

  virtual std::string getShortHeader();
  virtual IntegratorTag* getParentTag();

  virtual bool canDisable();
  virtual bool isEnabled();
  virtual void setEnabled(bool);

  virtual void deleteDeadBlocks(bool);
  virtual void replaceKnownBranches();

  virtual bool isOptimisticPeel();

  virtual bool getLoopBranchTarget(BasicBlock* FromBB, TerminatorInst* TI, TerminatorInst* ReplaceTI, BasicBlock*& Target);
  virtual void localPrepareCommit();

  virtual void getVarArg(int64_t, ValCtx&);

  virtual bool updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB);

  virtual bool ctxContains(IntegrationAttempt*);

  virtual void describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted);

  virtual std::pair<IntegrationAttempt*, const Loop*> getOutermostUnboundLoop();

  bool isOnlyExitingIteration();
  bool allExitEdgesDead();
  void getLoadForwardStartBlocks(SmallVector<BasicBlock*, 4>& Blocks, bool includeExitingBlocks);

  virtual int getIterCount() {
    return iterationCount;
  }

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
   TargetData* TD;
   AliasAnalysis* AA;

   const Loop* L;

   DenseMap<Instruction*, const Loop*>& invariantInsts;
   DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges;
   DenseMap<BasicBlock*, const Loop*>& invariantBlocks;

   int nesting_depth;
   int debugIndent;

 public:

   struct IntegratorTag tag;

   std::vector<BasicBlock*> LoopBlocks;
   std::vector<PeelIteration*> Iterations;

   std::pair<BasicBlock*, BasicBlock*> OptimisticEdge;

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
	       DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, const Loop* _L, int depth);
   ~PeelAttempt();

   SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;

   PeelIteration* getIteration(unsigned iter);
   PeelIteration* getOrCreateIteration(unsigned iter);

   ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);

   MemDepResult tryForwardExprFromParent(LoadForwardAttempt&, int originIter);
   bool tryForwardExprFromIter(LoadForwardAttempt&, int originIter, MemDepResult& Result, bool& MayDependOnParent, bool includeExitingBlocks);

   void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);

   bool tryForwardLoadThroughLoop(BasicBlock* BB, LoadForwardAttempt& LFA, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result);

   void visitVariant(Instruction* VI, const Loop* VILoop, VisitorContext& Visitor);
   void queueAllLiveValuesMatching(UnaryPred& P);
   
   void revertDSEandDAE();
   void revertExternalUsers();
   void callExternalUsers(ProcessExternalCallback& PEC);
   void retryExternalUsers();
   void getRetryStoresAndAllocs(std::vector<llvm::ValCtx>&);
   void walkLoadsFromFoldedContexts(bool);
   
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

   void eraseBlockValues(BasicBlock*);

   void removeBlockFromLoops(BasicBlock*);
   
   void queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);

   void dumpMemoryUsage(int indent);

   // Caching instruction text for debug and DOT export:
   PrintCacheWrapper<const Value*> itcache(const Value& V) const {
     return parent->itcache(V);
   }
   PrintCacheWrapper<ValCtx> itcache(ValCtx VC) const {
     return parent->itcache(VC);
   }
   PrintCacheWrapper<const MemDepResult&> itcache(const MemDepResult& MDR) const {
     return parent->itcache(MDR);
   }

 };

class InlineAttempt : public IntegrationAttempt { 

  CallInst* CI;
  BasicBlock* UniqueReturnBlock;

 public:

  InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, 
		DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth);

  virtual ValCtx tryEvaluateResult(Value*);
  
  virtual Instruction* getEntryInstruction();
  virtual BasicBlock* getEntryBlock();
  virtual const Loop* getLoopContext();

  virtual bool shouldCheckEdge(BasicBlock* FromBB, BasicBlock* ToBB);
  
  virtual MemDepResult tryForwardExprFromParent(LoadForwardAttempt&);
  bool tryForwardLoadFromExit(LoadForwardAttempt&, MemDepResult&, bool&);

  virtual void queueTryEvaluateOwnCall();
  
  ValCtx tryGetReturnValue();
  
  ValCtx getImprovedCallArgument(Argument* A);

  virtual bool checkLoopIteration(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);
  virtual bool checkOrQueueLoopIteration(ValCtx, ValCtx, BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);

  virtual InlineAttempt* getFunctionRoot();

  bool isOwnCallUnused();

  virtual bool walkHeaderPHIOperands(PHINode* PN, OpCallback& CB);
  virtual void walkOperands(Value* V, OpCallback& CB);
  virtual void queueAllLiveValuesMatching(UnaryPred& P);

  virtual bool getSpecialEdgeDescription(BasicBlock* FromBB, BasicBlock* ToBB, raw_ostream& Out);
  
  virtual void describe(raw_ostream& Stream) const;
  virtual void describeBrief(raw_ostream& Stream) const;
  
  virtual void collectAllLoopStats();

  virtual std::string getShortHeader();
  virtual IntegratorTag* getParentTag();

  virtual bool canDisable();
  virtual bool isEnabled();
  virtual void setEnabled(bool);

  virtual void deleteDeadBlocks(bool);
  virtual void replaceKnownBranches();

  virtual bool isOptimisticPeel();

  virtual bool getLoopBranchTarget(BasicBlock* FromBB, TerminatorInst* TI, TerminatorInst* ReplaceTI, BasicBlock*& Target);

  virtual void getVarArg(int64_t, ValCtx&);

  virtual bool updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB);

  virtual bool ctxContains(IntegrationAttempt*);

  bool getArgBasePointer(Argument*, PointerBase&);
  void queueUpdateCall(bool queueInLoopNow, bool pendInLoop, bool pendOutOfLoop);

  virtual void describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted);

  int64_t getSpilledVarargAfter(int64_t arg);

  virtual std::pair<IntegrationAttempt*, const Loop*> getOutermostUnboundLoop();

  virtual int getIterCount() {
    return -1;
  }

};

class LoadForwardAttempt;

class LFAQueryable {

 public:

  virtual LoadInst* getOriginalInst() = 0;
  virtual IntegrationAttempt* getOriginalCtx() = 0;
  virtual LoadInst* getQueryInst() = 0;
  virtual LoadForwardAttempt& getLFA() = 0;

};

class LoadForwardAttempt : public LFAQueryable {

  LoadInst* LI;
  IntegrationAttempt* originalCtx;
  SmallVector<SymExpr*, 4> Expr;
  bool ExprValid;
  int64_t ExprOffset;

  ValCtx Result;
  uint64_t* partialBuf;
  bool* partialValidBuf;
  uint64_t partialBufBytes;
  bool mayBuildFromBytes;

  const Type* targetType;

  TargetData* TD;

  bool buildSymExpr(Value* Ptr, IntegrationAttempt* Ctx);

 public:

  SmallVector<std::string, 1> OverdefReasons;
  SmallVector<ValCtx, 8> DefOrClobberInstructions;
  SmallVector<ValCtx, 8> IgnoredClobbers;
  SmallVector<IntegrationAttempt*, 8> TraversedCtxs;

  SmallSet<PeelAttempt*, 8> exploredLoops;

  PointerBase PB;
  bool ReachedTop;
  std::string ReachedTopStr;
  bool CompletelyExplored;
  bool PBOptimistic;
  LoadForwardMode Mode;

  virtual LoadInst* getOriginalInst();
  virtual IntegrationAttempt* getOriginalCtx();
  virtual LoadInst* getQueryInst();
  virtual LoadForwardAttempt& getLFA();  

  void describeSymExpr(raw_ostream& Str);
  bool tryBuildSymExpr(Value* Ptr = 0, IntegrationAttempt* Ctx = 0);
  bool canBuildSymExpr(Value* Ptr = 0, IntegrationAttempt* Ctx = 0);
  int64_t getSymExprOffset();
  void setSymExprOffset(int64_t);

  SmallVector<SymExpr*, 4>* getSymExpr();

  ValCtx getBaseVC();
  IntegrationAttempt* getBaseContext();

  unsigned char* getPartialBuf(uint64_t nbytes);
  bool* getBufValid();
  bool* tryGetBufValid();

  // This might not equal the type of the original load!
  // This happens when we're making proxy or sub-queries.
  const Type* getTargetTy();

  bool addPartialVal(PartialVal&);
  bool isComplete();
  ValCtx getResult();

  uint64_t markPaddingBytes(bool*, const Type*);

  void setPBOverdef(std::string reason) {
    OverdefReasons.push_back(reason);
    PB = PointerBase::getOverdef();
  }

  void addPBDefn(PointerBase& NewPB) {
    bool WasOverdef = PB.Overdef;
    PB.merge(NewPB);
    if(PB.Overdef && (!WasOverdef) && (!NewPB.Overdef))
      OverdefReasons.push_back("Fan-in");
  }

  bool PBIsViable() {
    return PBOptimistic || ((!PB.Overdef) && PB.Values.size() > 0);
  }

  bool PBIsOverdef() {
    return PB.Overdef;
  }

  void reachedTop(std::string s) {
    
    setPBOverdef(s);
    ReachedTop = true;
    ReachedTopStr = s;

  }

  LoadForwardAttempt(LoadInst* _LI, IntegrationAttempt* C, LoadForwardMode M, TargetData*, const Type* T = 0);
  ~LoadForwardAttempt();

   // Caching instruction text for debug and DOT export:
   PrintCacheWrapper<const Value*> itcache(const Value& V) const {
     return originalCtx->itcache(V);
   }
   PrintCacheWrapper<ValCtx> itcache(ValCtx VC) const {
     return originalCtx->itcache(VC);
   }
   PrintCacheWrapper<const MemDepResult&> itcache(const MemDepResult& MDR) const {
     return originalCtx->itcache(MDR);
   }

  void printDebugHeader(raw_ostream& Str) { 
    originalCtx->printDebugHeader(Str);
  }

};

class LFARealization : public LFAQueryable {

  LoadForwardAttempt& LFA;
  LoadInst* QueryInst;
  Instruction* FakeBase;
  Instruction* InsertPoint;
  SmallVector<Instruction*, 4> tempInstructions;
  
 public:

  virtual LoadInst* getOriginalInst();
  virtual IntegrationAttempt* getOriginalCtx();
  virtual LoadInst* getQueryInst();
  virtual LoadForwardAttempt& getLFA();

  LFARealization(LoadForwardAttempt& LFA, IntegrationAttempt* Ctx, Instruction* Insert);
  ~LFARealization();

  Instruction* getFakeBase();

  void printDebugHeader(raw_ostream& Str) { 
    LFA.getOriginalCtx()->printDebugHeader(Str);
  }

};

class LFARMapping {

  LFARealization& LFAR;
  IntegrationAttempt* Ctx;

 public:

  LFARMapping(LFARealization& LFAR, IntegrationAttempt* Ctx);
  ~LFARMapping();

};

 ValCtx extractAggregateMemberAt(Constant* From, int64_t Offset, const Type* Target, uint64_t TargetSize, TargetData*);
 Constant* constFromBytes(unsigned char*, const Type*, TargetData*);
 bool allowTotalDefnImplicitCast(const Type* From, const Type* To);
 bool allowTotalDefnImplicitPtrToInt(const Type* From, const Type* To, TargetData*);
 std::string ind(int i);
 const Loop* immediateChildLoop(const Loop* Parent, const Loop* Child);
 Constant* getConstReplacement(Value*, IntegrationAttempt*);
 Constant* intFromBytes(const uint64_t*, unsigned, unsigned, llvm::LLVMContext&);
 bool containsPointerTypes(const Type*);
 
 // Implemented in Transforms/Integrator/SimpleVFSEval.cpp, so only usable with -integrator
 bool getFileBytes(std::string& strFileName, uint64_t realFilePos, uint64_t realBytes, std::vector<Constant*>& arrayBytes, LLVMContext& Context, std::string& errors);

 // Implemented in Support/AsmWriter.cpp, since that file contains a bunch of useful private classes
 void getInstructionsText(const Function* IF, DenseMap<const Instruction*, std::string>& IMap, DenseMap<const Instruction*, std::string>& BriefMap);

 bool isGlobalIdentifiedObject(ValCtx VC);
 bool shouldQueueOnInst(Instruction* I, IntegrationAttempt* ICtx);
 uint32_t getInitialBytesOnStack(Function& F);
 uint32_t getInitialFPBytesOnStack(Function& F);

} // Namespace LLVM

#endif
