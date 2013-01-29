
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

struct BIC {
  BasicBlock::iterator it;
  BasicBlock* BB;
  IntegrationAttempt* ctx;

BIC(BasicBlock::iterator _it, BasicBlock* _BB, IntegrationAttempt* _ctx) : it(_it), BB(_BB), ctx(_ctx) { }
BIC(Instruction* I, IntegrationAttempt* _ctx);
};

inline bool operator==(const BIC& B1, const BIC& B2) {
  return B1.it == B2.it && B1.BB == B2.BB && B1.ctx == B2.ctx;
}

inline bool operator!=(const BIC& B1, const BIC& B2) {
  return !(B1 == B2);
}

inline bool operator<(const BIC& B1, const BIC& B2) {

  if(B1.BB != B2.BB) 
    return B1.BB < B2.BB;
  if(B1.it != B2.it)
    return ((Instruction*)B1.it) < ((Instruction*)B2.it);
  return B1.ctx < B2.ctx;
    
}

inline bool operator>(const BIC& B1, const BIC& B2) {
  return B2 < B1;
}

inline bool operator<=(const BIC& B1, const BIC& B2) {
  return B1 < B2 || B1 == B2;
}

inline bool operator>=(const BIC& B1, const BIC& B2) {
  return B1 > B2 || B1 == B2;
}



extern TargetData* GlobalTD;

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

   SmallVector<ValCtx, 64> dieQueue1;
   SmallVector<ValCtx, 64> dieQueue2;

   SmallVector<ValCtx, 64>* produceDIEQueue;

   IntegrationAttempt* RootIA;

   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > functionTextCache;
   DenseMap<const Function*, DenseMap<const Instruction*, std::string>* > briefFunctionTextCache;
   bool cacheDisabled;

   unsigned mallocAlignment;

 public:

   static char ID;

   uint64_t SeqNumber;

   explicit IntegrationHeuristicsPass() : ModulePass(ID), cacheDisabled(false) { 

     produceDIEQueue = &dieQueue2;
     mallocAlignment = 0;
     SeqNumber = 0;

   }

   bool runOnModule(Module& M);

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

   PostDominatorTree* getPostDomTree(Function*);
   DomTreeNodeBase<const BBWrapper>* getPostDomTreeNode(const Loop*, BasicBlock*);

   // Caching text representations of instructions:

   DenseMap<const Instruction*, std::string>& getFunctionCache(const Function* F, bool brief);
   void printValue(raw_ostream& ROS, const Value* V, bool brief);
   void printValue(raw_ostream& ROS, ValCtx VC, bool brief);
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

   bool assumeEndsAfter(Function* F, BasicBlock* HBB, uint64_t C) {
     DenseMap<std::pair<Function*, BasicBlock*>, uint64_t>::iterator it = maxLoopIters.find(std::make_pair(F, HBB));
     if(it == maxLoopIters.end())
       return false;
     return it->second == C;
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

  PVEmpty,
  PVTotal,
  PVPartial,
  PVByteArray

};

struct PartialVal {

  // Might be empty, a VC, a constant with bounding parameters, or an array of bytes.
  PartialValType type;
  // Value is tainted by varargs at any point?
  bool isVarargTainted;

  // Used if it's a VC:
  ValCtx TotalVC;

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
  
 PartialVal(ValCtx Total) : 
  type(PVTotal), isVarargTainted(false), TotalVC(Total), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
 PartialVal(Constant* _C, uint64_t Off) : 
  type(PVPartial), isVarargTainted(false), TotalVC(VCNull), C(_C), ReadOffset(Off), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
 PartialVal() :
  type(PVEmpty), isVarargTainted(false), TotalVC(VCNull), C(0), ReadOffset(0), partialBuf(0), partialValidBuf(0), partialBufBytes(0), loadFinished(false) { }
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

  static PartialVal getTotal(ValCtx VC) {
    return PartialVal(VC);
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
    return V1.TotalVC == V2.TotalVC;
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

typedef std::pair<std::pair<std::pair<BasicBlock*, ValCtx>, uint64_t>, uint64_t> LFCacheKey;

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
  ValCtx openVC;

CloseFile(struct OpenStatus* O, ValCtx VC) : openArg(O), MayDelete(false), openVC(VC) {}
CloseFile() : openArg(0), MayDelete(false), openVC(VCNull) {}

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

class LoopPBAnalyser {

  SmallVector<ValCtx, 64> PBQueue1;
  SmallVector<ValCtx, 64> PBQueue2;
  
  SmallVector<ValCtx, 64>* PBProduceQ;

  DenseSet<ValCtx> inLoopVCs;

public:

  BasicBlock* CacheThresholdBB;
  IntegrationAttempt* CacheThresholdIA;
  
  LoopPBAnalyser(BasicBlock* CTBB, IntegrationAttempt* CTIA) : CacheThresholdBB(CTBB), CacheThresholdIA(CTIA) {
    PBProduceQ = &PBQueue1;
  }

  void queueUpdatePB(ValCtx VC) {
    PBProduceQ->push_back(VC);
  }

  void queueIfConsidered(ValCtx VC) {
    if(inLoopVCs.count(VC))
      queueUpdatePB(VC);
  }

  void addVC(ValCtx VC) {
    inLoopVCs.insert(VC);
    queueUpdatePB(VC);
  }

  void runPointerBaseSolver(bool finalise, std::vector<ValCtx>* modifiedVCs);
  void run();

};

enum WalkInstructionResult {

  WIRContinue,
  WIRStopThisPath,
  WIRStopWholeWalk

};

class IAWalker {

 protected:

  SmallSet<BIC, 8> Visited;
  SmallVector<std::pair<BIC, void*>, 8> Worklist1;
  SmallVector<std::pair<BIC, void*>, 8> Worklist2;

  SmallVector<std::pair<BIC, void*>, 8>* PList;
  SmallVector<std::pair<BIC, void*>, 8>* CList;

  SmallVector<void*, 4> Contexts;
  
  virtual WalkInstructionResult walkInstruction(Instruction*, IntegrationAttempt*, void* Context) = 0;
  virtual bool shouldEnterCall(CallInst*, IntegrationAttempt*) = 0;
  virtual bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*, void*) = 0;
  virtual WalkInstructionResult walkFromBlock(BasicBlock*, IntegrationAttempt*, void* Context) {
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
  void queueWalkFrom(BIC, void* context, bool copyContext);

};

class BackwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(BIC, void* Ctx, CallInst*& StoppedCI);
  virtual void walkInternal();

 public:

  virtual bool reachedTop() { return true; }
  virtual bool mayAscendFromContext(IntegrationAttempt*, void* Ctx) { return true; }

  BackwardIAWalker(Instruction*, IntegrationAttempt*, bool skipFirst, void* IC = 0);
  
};

class ForwardIAWalker : public IAWalker {
  
  WalkInstructionResult walkFromInst(BIC, void* Ctx, CallInst*& StoppedCI);
  virtual void walkInternal();
  
 public:

  ForwardIAWalker(Instruction*, IntegrationAttempt*, bool skipFirst, void* IC = 0);
  
};

class IntegrationAttempt {

protected:

  IntegrationHeuristicsPass* pass;

  // Analyses created by the Pass.
  DenseMap<Function*, LoopInfo*>& LI;
  TargetData* TD;
  AliasAnalysis* AA;

  std::string HeaderStr;

  DenseMap<Instruction*, const Loop*>& invariantInsts;
  DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges;
  DenseMap<BasicBlock*, const Loop*>& invariantBlocks;

  DenseMap<Value*, ValCtx> improvedValues;

  DenseSet<BasicBlock*> deadBlocks;
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> deadEdges;
  SmallSet<BasicBlock*, 4> certainBlocks;
  SmallSet<BasicBlock*, 4> assumedCertainBlocks;

  // Instructions which have no users (discounting side-effects) after discounting instructions
  // which will be RAUW'd or deleted on commit.
  DenseSet<Value*> deadValues;
  // Instructions which write memory, but whose results are never read. These may be deleted.
  DenseSet<Value*> unusedWriters;
  // A list of dead stores and allocations which in the course of being found dead traversed this context.
  // These should be discounted as unused writes if we are folded.
  DenseSet<ValCtx> unusedWritersTraversingThisContext;

  // Map from pointer-typed instructions to loads that will resolve to them.
  DenseMap<Instruction*, SmallVector<ValCtx, 4> > instIndirectUsers;

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

  // Pointers resolved down to their base object, but not necessarily the offset:
  DenseMap<Value*, PointerBase> pointerBases;
  DenseMap<Instruction*, DenseSet<std::pair<LoadInst*, IntegrationAttempt*> > > memWriterEffects;
  DenseMap<Instruction*, std::string> optimisticForwardStatus;
  DenseMap<Instruction*, std::string> pessimisticForwardStatus;

  // Inline attempts / peel attempts which are currently ignored because they've been opted out.
  // These may include inlines / peels which are logically two loop levels deep, 
  // because they were created when a parent loop was opted out but then opted in again.
  DenseSet<CallInst*> ignoreIAs;
  DenseSet<const Loop*> ignorePAs;

  DenseMap<LFCacheKey, PointerBase> LFPBCache;

  // A map from the Values used in all of the above to the clones of Instructions produced at commit time
  ValueMap<const Value*, Value*> CommittedValues;
  bool commitStarted;
  // The LoopInfo belonging to the function which is being specialised
  LoopInfo* MasterLI;

  bool contextTaintedByVarargs;

  std::string nestingIndent() const;

  int nesting_depth;
  uint64_t SeqNumber;

 public:

  Function& F;

  bool contextIsDead;

  struct IntegratorTag tag;

  int64_t totalIntegrationGoodness;
  int64_t nDependentLoads;

  IntegrationAttempt* parent;

  DenseMap<CallInst*, InlineAttempt*> inlineChildren;
  DenseMap<const Loop*, PeelAttempt*> peelChildren;
    
 IntegrationAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA,
		    DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth) : 
  pass(Pass),
    LI(_LI),
    TD(_TD), 
    AA(_AA), 
    invariantInsts(_invariantInsts),
    invariantEdges(_invariantEdges),
    invariantBlocks(_invariantBlocks),
    improvedValues(4),
    deadValues(4),
    unusedWriters(4),
    unusedWritersTraversingThisContext(2),
    improvableInstructions(0),
    improvedInstructions(0),
    residualInstructions(-1),
    forwardableOpenCalls(2),
    resolvedReadCalls(2),
    resolvedSeekCalls(2),
    resolvedCloseCalls(2),
    ignoreIAs(2),
    ignorePAs(2),
    CommittedValues(2),
    commitStarted(false),
    contextTaintedByVarargs(false),
    nesting_depth(depth),
    F(_F),
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

  virtual bool entryBlockIsCertain() = 0;
  virtual bool entryBlockAssumed() = 0;
  bool blockCertainlyExecutes(BasicBlock*);
  bool blockAssumed(BasicBlock*);
  bool blockAssumedToExecute(BasicBlock*);

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
  virtual bool isOptimisticPeel() = 0;

  // Simple state-tracking helpers:

  virtual void setReplacement(Value*, ValCtx);
  void eraseReplacement(Value*);
  bool isUnresolved(Value*);
  bool hasResolvedPB(Value*);
  void setEdgeDead(BasicBlock*, BasicBlock*);
  void setBlockDead(BasicBlock*);

  virtual Constant* getConstReplacement(Value* V);
  virtual Function* getCalledFunction(const CallInst*);
  virtual Function* getCalledFunction(const InvokeInst*);
  virtual Function* getCalledFunction(const Instruction*);
  
  virtual InlineAttempt* getFunctionRoot() = 0;

  // The toplevel loop:
  void analyse();
  void analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);
  void analyseBlock(BasicBlock* BB, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);
  void analyseBlockInstructions(BasicBlock* BB, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);
  void createTopOrderingFrom(BasicBlock* BB, std::vector<BasicBlock*>& Result, SmallSet<BasicBlock*, 8>& Visited, const Loop* MyL, bool enterLoops);

  // Constant propagation:

  bool shouldTryEvaluate(Value* ArgV, bool verbose = true);
  bool shouldInvestigateUser(Value* ArgV, bool verbose, Value* UsedV);

  ValCtx getPHINodeValue(PHINode*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  void tryEvaluate(Value*);
  virtual ValCtx tryEvaluateResult(Value*);

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
  void markBlockAssumed(BasicBlock* BB);
  void checkEdge(BasicBlock*, BasicBlock*);
  void checkEdge(BasicBlock*, BasicBlock*, const Loop*);
  void checkVariantEdge(BasicBlock*, BasicBlock*, const Loop* Scope);
  void checkLocalEdge(BasicBlock*, BasicBlock*);
  bool checkLoopSpecialEdge(BasicBlock*, BasicBlock*);
  PostDominatorTree* getPostDomTree();
  bool shouldAssumeEdge(BasicBlock* BB1, BasicBlock* BB2) {
    return pass->shouldAssumeEdge(&F, BB1, BB2);
  }
  void eraseBlockValues(BasicBlock*);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(CallInst* CI);
  virtual bool stackIncludesCallTo(Function*) = 0;
  bool shouldInlineFunction(CallInst* CI);
  InlineAttempt* getOrCreateInlineAttempt(CallInst* CI);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  void checkLoad(LoadInst* LI);
  bool tryResolveLoadFromConstant(LoadInst*, ValCtx& Result);
  PartialVal tryForwardLoadTypeless(Instruction* StartInst, ValCtx LoadPtr, uint64_t LoadSize, bool* alreadyValidBytes, std::string& error);
  ValCtx tryForwardLoad(Instruction* StartInst, ValCtx LoadPtr, const Type* TargetType, uint64_t LoadSize, raw_string_ostream&);
  PartialVal tryForwardLoadSubquery(Instruction* StartInst, ValCtx LoadPtr, uint64_t LoadSize, PartialVal& resolvedSoFar, std::string& error);
  ValCtx tryForwardLoad(LoadInst* LI);
  ValCtx getWalkerResult(NormalLoadForwardWalker& Walker, const Type* TargetType, raw_string_ostream&);

  // Support functions for the generic IA graph walkers:
  void queueLoopExitingBlocksBW(BasicBlock* ExitedBB, BasicBlock* ExitingBB, const Loop* ExitingBBL, BackwardIAWalker* Walker, void* Ctx, bool& firstPred);
  virtual bool queuePredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* ctx) = 0;
  void queueNormalPredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* ctx);
  void queueSuccessorsFWFalling(BasicBlock* BB, const Loop* SuccLoop, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);
  virtual void queueSuccessorsFW(BasicBlock* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(BasicBlock* PresentBlock, BasicBlock* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc) = 0;

  // VFS call forwarding:

  virtual bool isForwardableOpenCall(Value*);
  bool openCallSucceeds(Value*);
  virtual int64_t tryGetIncomingOffset(CallInst*);
  virtual ReadFile* tryGetReadFile(CallInst* CI);
  bool tryPromoteOpenCall(CallInst* CI);
  void tryPromoteAllCalls();
  bool tryResolveVFSCall(CallInst*);
  WalkInstructionResult isVfsCallUsingFD(CallInst* VFSCall, ValCtx FD, bool);
  ValCtx tryFoldOpenCmp(CmpInst* CmpI, ConstantInt* CmpInt, bool flip);
  bool tryFoldOpenCmp(CmpInst* CmpI, ValCtx&);
  virtual void resolveReadCall(CallInst*, struct ReadFile);
  virtual void resolveSeekCall(CallInst*, struct SeekFile);
  bool isResolvedVFSCall(const Instruction*);
  bool isSuccessfulVFSCall(const Instruction*);
  bool isUnusedReadCall(CallInst*);
  bool isCloseCall(CallInst*);
  OpenStatus& getOpenStatus(CallInst*);
  void tryKillAllVFSOps();
  void markCloseCall(CallInst*);
  virtual void recordAllParentContexts(ValCtx VC, SmallSet<InlineAttempt*, 8>& seenIAs, SmallSet<PeelAttempt*, 8>& seenPAs) = 0;
  void recordDependentContexts(CallInst* CI, SmallVector<ValCtx, 4>& Deps);

  // Tricky load forwarding (stolen from GVN)

  bool GetDefinedRange(ValCtx DefinedBase, int64_t DefinedOffset, uint64_t DefinedSizeBits,
		       ValCtx DefinerBase, int64_t DefinerOffset, uint64_t DefinerSizeBits,
		       uint64_t& FirstDef, uint64_t& FirstNotDef, uint64_t& ReadOffset);

  bool getPVFromCopy(Value* copySource, Instruction* copyInst, uint64_t ReadOffset, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t ReadSize, bool* validBytes, PartialVal& NewPV, std::string& error);
  bool getMemsetPV(MemSetInst* I, uint64_t nbytes, PartialVal& NewPV, std::string& error);
  bool getMemcpyPV(MemTransferInst* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error);
  bool getVaStartPV(CallInst* CI, int64_t ReadOffset, PartialVal& NewPV, std::string& error);
  bool getVaCopyPV(CallInst* CI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error);
  bool getReadPV(CallInst* CI, uint64_t nbytes, int64_t ReadOffset, PartialVal& NewPV, std::string& error);

  // Load forwarding extensions for varargs:
  virtual void getVarArg(int64_t, ValCtx&) = 0;
  int64_t getSpilledVarargAfter(CallInst* CI, int64_t OldArg);
  void disableChildVarargsContexts();
  bool isVarargsTainted();
  
  // Dead store and allocation elim:

  bool tryKillStore(StoreInst* SI);
  bool tryKillMemset(MemIntrinsic* MI);
  bool tryKillMTI(MemTransferInst* MTI);
  bool tryKillAlloc(Instruction* Alloc);
  bool tryKillRead(CallInst*, ReadFile&);
  bool tryKillWriterTo(Instruction* Writer, Value* WritePtr, uint64_t Size);
  bool DSEHandleWrite(ValCtx Writer, uint64_t WriteSize, ValCtx StorePtr, uint64_t Size, ValCtx StoreBase, int64_t StoreOffset, std::vector<bool>* deadBytes);
  bool isLifetimeEnd(ValCtx Alloc, Instruction* I);
  void addTraversingInst(ValCtx);
  WalkInstructionResult noteBytesWrittenBy(Instruction* I, ValCtx StorePtr, ValCtx StoreBase, int64_t StoreOffset, uint64_t Size, std::vector<bool>* writtenBytes);
  bool callUsesPtr(CallInst* CI, ValCtx StorePtr, uint64_t Size);
  void tryKillAllMTIs();
  void tryKillAllMTIsFromBB(BasicBlock*, SmallSet<BasicBlock*, 8>&);
  void tryKillAllStores();
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
  bool valueWillBeReplacedWithConstantOrDeleted(Value* V);
  bool valueWillBeRAUWdOrDeleted(Value* V);
  virtual bool loopHeaderPhiWillCopy(Value* V, ValCtx OtherVC) = 0;
  bool valueWillNotUse(Value* V, ValCtx, bool mustReplWithConstant = false);
  bool valueWillBeDeleted(Value* V);
  bool inDeadValues(Value* V);
  void replaceDeadValue(Value* V, ValCtx);
  void queueDIEOperands(Value* V);
  void tryKillValue(Value* V);
  virtual void queueAllLiveValuesMatching(UnaryPred& P);
  void queueAllReturnInsts();
  void queueAllLiveValues();
  void addForwardedInst(Instruction*, ValCtx);

  // Pointer base analysis
  bool getPointerBaseLocal(Value* V, PointerBase& OutPB);
  bool getPointerBaseRising(Value* V, PointerBase& OutPB, const Loop* VL);
  virtual bool getPointerBaseFalling(Value* V, PointerBase& OutPB);
  bool getPointerBase(Value* V, PointerBase& OutPB, Instruction* UserI);
  bool getValSetOrReplacement(Value* V, PointerBase& OutPB, Instruction* UserI = 0);
  bool getMergeBasePointer(Instruction* I, bool finalise, PointerBase& NewPB);
  bool updateBasePointer(Value* V, bool finalise, LoopPBAnalyser* LPBA, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);
  bool updateBinopValSet(Instruction* I, PointerBase& PB);
  bool updateUnaryValSet(Instruction* I, PointerBase &PB);
  void queueUpdatePB(IntegrationAttempt*, Value*, LoopPBAnalyser*);
  void queueUsersUpdatePB(Value* V, LoopPBAnalyser*);
  void queueUserUpdatePB(Value*, Instruction* User, LoopPBAnalyser*);
  void queueUsersUpdatePBFalling(Instruction* I, const Loop* IL, Value* V, LoopPBAnalyser*);
  void queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, LoopPBAnalyser*);
  void resolvePointerBase(Value* V, PointerBase&);
  void queuePBUpdateAllUnresolvedVCsInScope(const Loop* L, LoopPBAnalyser*);
  void queuePBUpdateIfUnresolved(Value *V, LoopPBAnalyser*);
  void queueUpdatePBWholeLoop(const Loop*, LoopPBAnalyser*);
  virtual bool updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB) = 0;
  void printPB(raw_ostream& out, PointerBase PB, bool brief = false);
  virtual bool ctxContains(IntegrationAttempt*) = 0;
  virtual bool basesMayAlias(ValCtx VC1, ValCtx VC2);
  bool tryForwardLoadPB(LoadInst*, bool finalise, PointerBase& out, BasicBlock* optBB, IntegrationAttempt* optIA);
  std::string describePBWalker(PBLoadForwardWalker& Walker);
  void addMemWriterEffect(Instruction*, LoadInst*, IntegrationAttempt*);
  void addStoreToLoadSolverWork(Value* V);
  bool shouldCheckPB(Value*);
  void analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA);
  void tryPromoteSingleValuedPB(Value* V);

  // PBLF Caching
  PointerBase* getLFPBCacheEntry(LFCacheKey& Key);
  void deleteLFPBCacheEntry(LFCacheKey& Key);
  PointerBase* createLFPBCacheEntry(LFCacheKey& Key);

  // Enabling / disabling exploration:

  void enablePeel(const Loop*);
  uint64_t disablePeel(const Loop*, bool simulateOnly);
  bool loopIsEnabled(const Loop*);
  void enableInline(CallInst*);
  uint64_t disableInline(CallInst*, bool simulateOnly);
  bool inlineIsEnabled(CallInst*);
  virtual bool isEnabled() = 0;
  virtual void setEnabled(bool) = 0;
  bool isAvailable();
  bool isAvailableFromCtx(IntegrationAttempt*);
  bool isVararg();
  uint64_t revertDSEandDAE(bool simulateOnly);
  uint64_t revertDeadValue(Value*, bool simulateOnly);
  void tryKillAndQueue(Instruction*);
  void getRetryStoresAndAllocs(std::vector<ValCtx>&);
  void retryStoresAndAllocs(std::vector<ValCtx>&);
  uint64_t revertLoadsFromFoldedContexts(bool simulateOnly);
  void retryLoadsFromFoldedContexts();
  uint64_t walkLoadsFromFoldedContexts(bool revert, bool simulateOnly);
  void revertDeadVFSOp(CallInst* CI);
  void retryDeadVFSOp(CallInst* CI);

  // Estimating inlining / unrolling benefit:

  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&);
  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&);
  int64_t getResidualInstructions();
  virtual void reduceDependentLoads(int64_t) = 0;
  void countDependentLoads();
  void propagateDependentLoads();

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

  void printWithCache(const Value* V, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, V, brief);
  }

  void printWithCache(ValCtx VC, raw_ostream& ROS, bool brief = false) {
    pass->printValue(ROS, VC, brief);
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
  void removeBlockFromLoops(BasicBlock*, const Loop*);
  void foldVFSCalls();
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

  void testLoadWalk(LoadInst* LI);

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  const Loop* L;
  PeelAttempt* parentPA;

  BasicBlock* LHeader;
  BasicBlock* LLatch;

public:

  PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
		AliasAnalysis* _AA, const Loop* _L, DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
		DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int iter, int depth);

  IterationStatus iterStatus;

  PeelIteration* getNextIteration();
  PeelIteration* getOrCreateNextIteration();

  virtual Instruction* getEntryInstruction();
  virtual BasicBlock* getEntryBlock();
  virtual const Loop* getLoopContext();

  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);

  virtual bool shouldCheckEdge(BasicBlock* FromBB, BasicBlock* ToBB);

  void checkExitEdge(BasicBlock*, BasicBlock*);
  void checkFinalIteration();

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

  virtual bool stackIncludesCallTo(Function*);

  virtual void reduceDependentLoads(int64_t);

  virtual bool queuePredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(BasicBlock* PresentBlock, BasicBlock* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual void recordAllParentContexts(ValCtx VC, SmallSet<InlineAttempt*, 8>& seenIAs, SmallSet<PeelAttempt*, 8>& seenPAs);

  virtual bool loopHeaderPhiWillCopy(Value* V, ValCtx OtherVC);

  virtual bool entryBlockIsCertain();
  virtual bool entryBlockAssumed();

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

   SmallVector<ValCtx, 4> deadVFSOpsTraversingHere;

   int64_t residualInstructions;

   int nesting_depth;
   int debugIndent;

 public:

   struct IntegratorTag tag;

   int64_t totalIntegrationGoodness;
   int64_t nDependentLoads;

   std::vector<BasicBlock*> LoopBlocks;
   std::vector<PeelIteration*> Iterations;

   std::pair<BasicBlock*, BasicBlock*> OptimisticEdge;

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
	       DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, const Loop* _L, int depth);
   ~PeelAttempt();

   void analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);

   SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;

   PeelIteration* getIteration(unsigned iter);
   PeelIteration* getOrCreateIteration(unsigned iter);

   ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);

   void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);

   void visitVariant(Instruction* VI, const Loop* VILoop, VisitorContext& Visitor);
   void queueAllLiveValuesMatching(UnaryPred& P);
   
   uint64_t revertDSEandDAE(bool);
   uint64_t revertExternalUsers(bool);
   void callExternalUsers(ProcessExternalCallback& PEC);
   void retryExternalUsers();
   void getRetryStoresAndAllocs(std::vector<llvm::ValCtx>&);
   uint64_t walkLoadsFromFoldedContexts(bool, bool);
   
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

   void removeBlockFromLoops(BasicBlock*, const Loop*);
   
   void queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, LoopPBAnalyser*);

   void reduceDependentLoads(int64_t);

   void dumpMemoryUsage(int indent);

   int64_t getResidualInstructions();
   void findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty);
   void countDependentLoads();
   void propagateDependentLoads();

   void disableVarargsContexts();

   void recordAllParentContexts(ValCtx VC, SmallSet<InlineAttempt*, 8>& seenIAs, SmallSet<PeelAttempt*, 8>& seenPAs);

   void revertDeadVFSOps();
   void retryDeadVFSOps();

   // Caching instruction text for debug and DOT export:
   PrintCacheWrapper<const Value*> itcache(const Value& V) const {
     return parent->itcache(V);
   }
   PrintCacheWrapper<ValCtx> itcache(ValCtx VC) const {
     return parent->itcache(VC);
   }

 };

class InlineAttempt : public IntegrationAttempt { 

  CallInst* CI;
  BasicBlock* UniqueReturnBlock;
  SmallVector<ValCtx, 4> deadVFSOpsTraversingHere;

 public:

  InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, 
		DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth);

  virtual ValCtx tryEvaluateResult(Value*);
  
  virtual Instruction* getEntryInstruction();
  virtual BasicBlock* getEntryBlock();
  virtual const Loop* getLoopContext();

  virtual bool shouldCheckEdge(BasicBlock* FromBB, BasicBlock* ToBB);
  
  ValCtx tryGetReturnValue();
  
  ValCtx getImprovedCallArgument(Argument* A);

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
  void queueUpdateCall(LoopPBAnalyser*);

  virtual void describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted);

  int64_t getSpilledVarargAfter(int64_t arg);

  virtual void reduceDependentLoads(int64_t);

  virtual int getIterCount() {
    return -1;
  }

  virtual bool stackIncludesCallTo(Function*);

  virtual void findResidualFunctions(DenseSet<Function*>&, DenseMap<Function*, unsigned>&);
  virtual void findProfitableIntegration(DenseMap<Function*, unsigned>&);

  virtual bool queuePredecessorsBW(BasicBlock* FromBB, BackwardIAWalker* Walker, void* ctx);
  virtual void queueSuccessorsFW(BasicBlock* BB, ForwardIAWalker* Walker, void* ctx);
  virtual bool queueNextLoopIterationFW(BasicBlock* PresentBlock, BasicBlock* NextBlock, ForwardIAWalker* Walker, void* Ctx, bool& firstSucc);

  virtual void recordAllParentContexts(ValCtx VC, SmallSet<InlineAttempt*, 8>& seenIAs, SmallSet<PeelAttempt*, 8>& seenPAs);

  virtual void localPrepareCommit();

  virtual bool loopHeaderPhiWillCopy(Value* V, ValCtx OtherVC);

  virtual bool entryBlockIsCertain();
  virtual bool entryBlockAssumed();

  void revertDeadVFSOps();
  void retryDeadVFSOps();

  void disableVarargsContexts();

  void analyseWithArgs(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA);

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
 ValCtx getAsPtrAsInt(ValCtx VC, const Type* Target);
 ValCtx GetBaseWithConstantOffset(Value *Ptr, IntegrationAttempt* PtrCtx, int64_t &Offset);

#define release_assert(x) if(!(x)) { release_assert_fail(#x); }
 void release_assert_fail(const char*);

} // Namespace LLVM

#endif
