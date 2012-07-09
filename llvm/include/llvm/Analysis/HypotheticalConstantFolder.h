
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Pass.h"
#include "llvm/Value.h"
#include "llvm/Constant.h"

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
class MemDepResult;
class NonLocalDepResult;
class LoadInst;
class raw_ostream;
class ConstantInt;
class Type;
class Argument;
class CallInst;
class StoreInst;
class MemIntrinsic;
class CmpInst;

class HCFParentCallbacks;

typedef struct { Value* first; HCFParentCallbacks* second; } ValCtx;

inline bool operator==(ValCtx V1, ValCtx V2) {
  return V1.first == V2.first && V1.second == V2.second;
}

inline bool operator!=(ValCtx V1, ValCtx V2) {
   return !(V1 == V2);
}

raw_ostream& operator<<(raw_ostream&, const ValCtx&);
raw_ostream& operator<<(raw_ostream&, const MemDepResult&);
raw_ostream& operator<<(raw_ostream&, const HCFParentCallbacks&);

#define VCNull (make_vc(0, 0))

inline ValCtx make_vc(Value* V, HCFParentCallbacks* H) {

  ValCtx newCtx = {V, H};
  return newCtx;

}

inline ValCtx const_vc(Constant* C) {

  return make_vc(C, 0);

}

enum SymSubclasses {

  SThunk,
  SGEP,
  SCast

};

class SymExpr { 

public:
  static inline bool classof(const SymExpr*) { return true; }
  virtual void describe(raw_ostream& OS) = 0;
  virtual int getSymType() const = 0;

};

class SymThunk : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SThunk; }
  static inline bool classof(const SymThunk*) { return true; }
  ValCtx RealVal;

  SymThunk(ValCtx R) : RealVal(R) { }
  void describe(raw_ostream& OS);
  int getSymType() const { return SThunk; }

};

class SymGEP : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SGEP; }
  static inline bool classof(const SymGEP*) { return true; }
  SmallVector<Value*, 4> Offsets; // Really all ConstantInts

  SymGEP(SmallVector<Value*, 4> Offs) : Offsets(Offs) { }

  void describe(raw_ostream& OS);
  int getSymType() const { return SGEP; }

};

class SymCast : public SymExpr {

public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SCast; }
  static inline bool classof(const SymCast*) { return true; }
  const Type* ToType;

  SymCast(const Type* T) : ToType(T) { }

  void describe(raw_ostream& OS);
  int getSymType() const { return SCast; }

};

class LoadForwardAttempt;
class LFARealization;
class LFAQueryable;

struct OpenStatus {

  std::string Name;
  bool FDEscapes;
  ValCtx LatestResolvedUser;

  OpenStatus(ValCtx O, std::string N, bool Esc) : Name(N), FDEscapes(Esc), LatestResolvedUser(O) { }

OpenStatus() : Name(""), FDEscapes(false), LatestResolvedUser(VCNull) {}

};

struct ReadFile {

  struct OpenStatus* openArg;
  uint64_t incomingOffset;
  uint32_t readSize;

  ReadFile(struct OpenStatus* O, uint64_t IO, uint32_t RS) : openArg(O), incomingOffset(IO), readSize(RS) { }

ReadFile() : openArg(0), incomingOffset(0), readSize(0) { }

};

struct SeekFile {

  struct OpenStatus* openArg;
  uint64_t newOffset;

SeekFile(struct OpenStatus* O, uint64_t Off) : openArg(O), newOffset(Off) { }
  
SeekFile() : openArg(0), newOffset(0) { }

};

// Interface exposed to Memory Dependence Analysis and other external analyses that the integrator uses.
class HCFParentCallbacks {

 public:

  virtual ValCtx getReplacement(Value*) = 0;
  virtual Constant* getConstReplacement(Value* V) = 0;
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*) = 0;
  virtual bool blockIsDead(BasicBlock*) = 0;
  virtual BasicBlock* getEntryBlock() = 0;
  virtual ValCtx getDefaultVC(Value*) = 0;
  virtual bool tryForwardLoadThroughCall(LoadForwardAttempt&, CallInst*, MemDepResult&) = 0;
  virtual bool tryForwardLoadThroughLoopFromBB(BasicBlock* BB, LoadForwardAttempt&, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result) = 0;
  virtual void describe(raw_ostream&) const = 0;
  virtual ValCtx getUltimateUnderlyingObject(Value*) = 0;
  virtual bool isForwardableOpenCall(Value*) = 0;
  virtual int64_t tryGetIncomingOffset(Value*) = 0;
  virtual ReadFile* tryGetReadFile(CallInst* CI) = 0;
  virtual void setReplacement(Value*, ValCtx) = 0;
  virtual void investigateUsers(Value* V) = 0;
  virtual void resolveReadCall(CallInst*, struct ReadFile) = 0;
  virtual void resolveSeekCall(CallInst*, struct SeekFile) = 0;
  virtual void addBlockedOpen(ValCtx, ValCtx) = 0;
  virtual bool tryPushOpenFrom(ValCtx&, ValCtx, ValCtx, OpenStatus&, bool) = 0;

};

class InlineAttempt;
class PeelAttempt;
class IntegrationAttempt;
class IntegrationHeuristicsPass;

class Function;
class LoopInfo;
class TargetData;
class AliasAnalysis;
class Loop;

enum IterationStatus {

  IterationStatusUnknown,
  IterationStatusFinal,
  IterationStatusNonFinal

};

class IntegrationAttempt : public HCFParentCallbacks {

protected:

  IntegrationHeuristicsPass* pass;
  IntegrationAttempt* parent;

  // Analyses created by the Pass.
  DenseMap<Function*, LoopInfo*> LI;
  TargetData* TD;
  AliasAnalysis* AA;

  Function& F;

  DenseMap<Instruction*, const Loop*>& invariantInsts;
  DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges;
  DenseMap<BasicBlock*, const Loop*>& invariantBlocks;

  DenseMap<CallInst*, InlineAttempt*> inlineChildren;
  DenseMap<const Loop*, PeelAttempt*> peelChildren;
    
  DenseMap<Value*, ValCtx> improvedValues;

  SmallSet<BasicBlock*, 4> deadBlocks;
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> deadEdges;
  SmallSet<BasicBlock*, 8> certainBlocks;

  int improvableInstructions;
  int improvedInstructions;
  SmallVector<CallInst*, 4> unexploredCalls;
  SmallVector<const Loop*, 4> unexploredLoops;

  SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4> CFGBlockedLoads;
  DenseMap<Instruction*, SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4> > InstBlockedLoads;

  SmallVector<std::pair<ValCtx, ValCtx>, 4> CFGBlockedOpens;
  DenseMap<Instruction*, SmallVector<std::pair<ValCtx, ValCtx>, 4> > InstBlockedOpens;

  DenseMap<CallInst*, OpenStatus> forwardableOpenCalls;
  DenseMap<CallInst*, ReadFile> resolvedReadCalls;
  DenseMap<CallInst*, SeekFile> resolvedSeekCalls;

  std::string nestingIndent() const;

  int nesting_depth;

  public:

 IntegrationAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA,
		    DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int depth) : 
  pass(Pass),
    parent(P),
    LI(_LI),
    TD(_TD), 
    AA(_AA), 
    F(_F),
    invariantInsts(_invariantInsts),
    invariantEdges(_invariantEdges),
    invariantBlocks(_invariantBlocks),
    improvableInstructions(0),
    improvedInstructions(0),
    nesting_depth(depth)
      { }

  ~IntegrationAttempt();

  // Implement HCFParentCallbacks (partially):

  virtual ValCtx getDefaultVC(Value*);
  virtual ValCtx getReplacement(Value* V);
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*);
  virtual bool blockIsDead(BasicBlock*);

  // Helpers for the above:

  const Loop* getValueScope(Value*);
  ValCtx getReplacementUsingScope(Value*, const Loop*);
  ValCtx getDefaultVCWithScope(Value*, const Loop*);

  const Loop* getEdgeScope(BasicBlock*, BasicBlock*);
  bool edgeIsDeadWithScope(BasicBlock*, BasicBlock*, const Loop*);

  const Loop* getBlockScope(BasicBlock*);
  bool blockIsDeadWithScope(BasicBlock*, const Loop*);

  bool blockIsCertain(BasicBlock*);

  bool shouldForwardValue(ValCtx);

  virtual ValCtx getUltimateUnderlyingObject(Value*);
  
  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual const Loop* getLoopContext() = 0;
  virtual Instruction* getEntryInstruction() = 0;
  virtual void collectAllBlockStats() = 0;
  virtual void printHeader(raw_ostream& OS) const = 0;
  virtual void queueTryEvaluateOwnCall() = 0;

  // Simple state-tracking helpers:

  virtual void setReplacement(Value*, ValCtx);
  void eraseReplacement(Value*);
  bool isUnresolved(Value*);
  void setEdgeDead(BasicBlock*, BasicBlock*);
  void setBlockDead(BasicBlock*);

  virtual Constant* getConstReplacement(Value* V);

  // Constant propagation:

  virtual bool shouldTryEvaluate(Value* ArgV, bool verbose = true);

  ValCtx getPHINodeValue(PHINode*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  void tryEvaluate(Value*);
  virtual ValCtx tryEvaluateResult(Value*);
  virtual void investigateUsers(Value* V);

  virtual void queueTryEvalExitPHI(Instruction* UserI);
  virtual bool queueImproveNextIterationPHI(Instruction* I);
  void queueTryEvaluateGeneric(Instruction* UserI, Value* Used);

  // CFG analysis:

  bool shouldCheckBlock(BasicBlock* BB);
  void checkBlock(BasicBlock* BB);
  void checkEdge(BasicBlock*, BasicBlock*);
  void checkVariantEdge(BasicBlock*, BasicBlock*, const Loop* Scope);
  void checkLocalEdge(BasicBlock*, BasicBlock*);
  virtual bool checkLoopSpecialEdge(BasicBlock*, BasicBlock*);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(CallInst* CI);
  InlineAttempt* getOrCreateInlineAttempt(CallInst* CI);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  void checkLoad(LoadInst* LI);
  ValCtx tryForwardLoad(LoadInst*);
  bool forwardLoadIsNonLocal(LFAQueryable&, ValCtx& Result, llvm::Instruction*& DefInst);
  ValCtx getDefn(const MemDepResult& Res);
  MemDepResult getUniqueDependency(LFAQueryable&, Value*& Address);

  virtual ValCtx tryForwardExprFromParent(LoadForwardAttempt&) = 0;
  ValCtx tryResolveLoadAtChildSite(IntegrationAttempt* IA, LoadForwardAttempt&);
  bool tryResolveExprFrom(LoadForwardAttempt& LFA, Instruction* Where, ValCtx& Result, Instruction*& DefInst);
  bool tryResolveExprUsing(LFARealization& LFAR, ValCtx& Result, Instruction*& DefInst);

  bool tryForwardLoadThroughCall(LoadForwardAttempt&, CallInst*, MemDepResult&);
  bool tryForwardLoadThroughLoopFromBB(BasicBlock* BB, LoadForwardAttempt&, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result);

  void queueWorkBlockedOn(Instruction* SI);
  void queueCheckAllLoads();

  // VFS call forwarding:

  virtual bool isForwardableOpenCall(Value*);
  virtual int64_t tryGetIncomingOffset(Value*);
  virtual ReadFile* tryGetReadFile(CallInst* CI);
  void tryPromoteOpenCall(CallInst* CI);
  void tryPromoteAllCalls();
  void queueInitialWork();
  void tryPushOpen(CallInst*, ValCtx);
  virtual bool tryPushOpenFrom(ValCtx&, ValCtx, ValCtx, OpenStatus&, bool);
  virtual bool checkLoopIterationOrExit(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) = 0;
  bool vfsCallBlocksOpen(CallInst*, ValCtx, ValCtx, OpenStatus&, bool&, bool&);
  ValCtx tryFoldOpenCmp(CmpInst* CmpI, ConstantInt* CmpInt, bool flip);
  virtual void resolveReadCall(CallInst*, struct ReadFile);
  virtual void resolveSeekCall(CallInst*, struct SeekFile);
  virtual void addBlockedOpen(ValCtx, ValCtx);
  void queueCFGBlockedOpens();

  // Tricky load forwarding (stolen from GVN)

  int AnalyzeLoadFromClobberingWrite(const Type *LoadTy, Value *LoadPtr,
				     Value *WritePtr, HCFParentCallbacks* WriteCtx,
				     uint64_t WriteSizeInBits);
  int AnalyzeLoadFromClobberingStore(const Type *LoadTy, Value *LoadPtr, StoreInst *DepSI, HCFParentCallbacks* DepSICtx);
  int AnalyzeLoadFromClobberingMemInst(const Type *LoadTy, Value *LoadPtr, MemIntrinsic *MI, HCFParentCallbacks* MICtx);
  ValCtx GetBaseWithConstantOffset(Value *Ptr, HCFParentCallbacks* PtrCtx, int64_t &Offset);
  bool CanCoerceMustAliasedValueToLoad(Value *StoredVal, const Type *LoadTy);
  Constant* CoerceConstExprToLoadType(Constant *StoredVal, const Type *LoadedTy);
  ValCtx tryResolveClobber(LoadInst *LI, Value* Address, ValCtx Clobber);

  // Stat collection and printing:

  void collectBlockStats(BasicBlock* BB);
  void collectLoopStats(const Loop*);
  void collectStats();
  void print(raw_ostream& OS) const;
  // Callable from GDB
  void dump() const;

  void printDebugHeader(raw_ostream& Str) {
    printHeader(Str);
  }

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  const Loop* L;
  PeelAttempt* parentPA;

  PeelIteration* getNextIteration();
  PeelIteration* getOrCreateNextIteration();

public:

 PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
	       AliasAnalysis* _AA, const Loop* _L, DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& _invariantEdges, 
	       DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, int iter, int depth) :
  IntegrationAttempt(Pass, P, F, _LI, _TD, _AA, _invariantInsts, _invariantEdges, _invariantBlocks, depth),
    iterationCount(iter),
    L(_L),
    parentPA(PP),
    iterStatus(IterationStatusUnknown)
    { }

  IterationStatus iterStatus;

  virtual ValCtx getReplacement(Value* V);
  virtual ValCtx getDefaultVC(Value* V);

  virtual Instruction* getEntryInstruction();
  virtual BasicBlock* getEntryBlock();
  virtual const Loop* getLoopContext();

  virtual bool checkLoopSpecialEdge(BasicBlock*, BasicBlock*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  virtual bool queueImproveNextIterationPHI(Instruction* I);
  void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);
  virtual void queueTryEvaluateOwnCall();
  virtual void queueTryEvalExitPHI(Instruction* UserI);

  void queueCheckExitBlock(BasicBlock* BB);
  void checkFinalIteration();

  virtual ValCtx tryForwardExprFromParent(LoadForwardAttempt&);

  virtual bool checkLoopIterationOrExit(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);

  virtual void describe(raw_ostream& Stream) const;

  virtual void collectAllBlockStats();
  virtual void printHeader(raw_ostream&) const;

};

class PeelAttempt {
   // Not a subclass of IntegrationAttempt -- this is just a helper.

   IntegrationHeuristicsPass* pass;
   IntegrationAttempt* parent;
   Function& F;

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

   std::vector<PeelIteration*> Iterations;

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
	       DenseMap<Instruction*, const Loop*>& _invariantInsts, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& invariantEdges, DenseMap<BasicBlock*, const Loop*>& _invariantBlocks, const Loop* _L, int depth);
   ~PeelAttempt();

   SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;

   PeelIteration* getIteration(unsigned iter);
   PeelIteration* getOrCreateIteration(unsigned iter);

   ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);

   ValCtx tryForwardExprFromParent(LoadForwardAttempt&, int originIter);
   bool tryForwardExprFromIter(LoadForwardAttempt&, int originIter, Instruction*& defInst, ValCtx& VC, int& defIter);

   void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);

   bool tryForwardLoadThroughLoopFromBB(BasicBlock* BB, LoadForwardAttempt& LFA, BasicBlock*& PreheaderOut, SmallVectorImpl<NonLocalDepResult> &Result);

   void collectStats();
   void printHeader(raw_ostream& OS) const;
   void printDebugHeader(raw_ostream& OS) const {
     printHeader(OS);
   }
   void print(raw_ostream& OS) const;

   std::string nestingIndent() const;

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
  
  virtual ValCtx tryForwardExprFromParent(LoadForwardAttempt&);
  bool tryForwardLoadFromExit(LoadForwardAttempt&, MemDepResult&);

  virtual void queueTryEvaluateOwnCall();
  
  ValCtx tryGetReturnValue();
  
  ValCtx getImprovedCallArgument(Argument* A);

  virtual bool checkLoopIterationOrExit(BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start);
  
  virtual void describe(raw_ostream& Stream) const;
  
  virtual void collectAllBlockStats();
  virtual void printHeader(raw_ostream&) const;

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

  DenseMap<std::pair<BasicBlock*, const Loop*>, MemDepResult> lastIterCache;
  DenseMap<const Loop*, MemDepResult> otherItersCache;

  bool buildSymExpr();

 public:

  virtual LoadInst* getOriginalInst();
  virtual IntegrationAttempt* getOriginalCtx();
  virtual LoadInst* getQueryInst();
  virtual LoadForwardAttempt& getLFA();  

  void describeSymExpr(raw_ostream& Str);
  bool tryBuildSymExpr();
  bool canBuildSymExpr();

  SmallVector<SymExpr*, 4>* getSymExpr();

  ValCtx getBaseVC();
  HCFParentCallbacks* getBaseContext();

  std::pair<DenseMap<std::pair<BasicBlock*, const Loop*>, MemDepResult>::iterator, bool> getLastIterCache(BasicBlock* FromBB, const Loop* L);
  std::pair<DenseMap<const Loop*, MemDepResult>::iterator, bool> getOtherItersCache(const Loop* L);

  LoadForwardAttempt(LoadInst* _LI, IntegrationAttempt* C);
  ~LoadForwardAttempt();

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

enum IntegratorWQItemType {

   TryEval,
   CheckBlock,
   CheckLoad,
   OpenPush

};

// A cheesy hack to make a value type that acts like a dynamic dispatch hierarchy
class IntegratorWQItem {

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
  } u;

public:

 IntegratorWQItem(IntegrationAttempt* c, LoadInst* L) : ctx(c), type(CheckLoad) { u.LI = L; }
 IntegratorWQItem(IntegrationAttempt* c, Value* V) : ctx(c), type(TryEval) { u.V = V; }
 IntegratorWQItem(IntegrationAttempt* c, BasicBlock* BB) : ctx(c), type(CheckBlock) { u.BB = BB; }
 IntegratorWQItem(IntegrationAttempt* c, CallInst* OpenI, ValCtx OpenProgress) : ctx(c), type(OpenPush) { u.OpenArgs.OpenI = OpenI; u.OpenArgs.OpenProgress = OpenProgress; }

  void execute();
  void describe(raw_ostream& s);

};

class IntegrationHeuristicsPass : public ModulePass {

   DenseMap<Function*, LoopInfo*> LIs;
   DenseMap<Function*, DenseMap<Instruction*, const Loop*> > invariantInstScopes;
   DenseMap<Function*, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*> > invariantEdgeScopes;
   DenseMap<Function*, DenseMap<BasicBlock*, const Loop*> > invariantBlockScopes;

   DenseMap<Function*, BasicBlock*> uniqueReturnBlocks;

   TargetData* TD;
   AliasAnalysis* AA;

   SmallVector<InlineAttempt*, 4> rootAttempts;

   SmallVector<IntegratorWQItem, 64> workQueue1;
   SmallVector<IntegratorWQItem, 64> workQueue2;

   SmallVector<IntegratorWQItem, 64>* produceQueue;

 public:

   static char ID;

   explicit IntegrationHeuristicsPass() : ModulePass(ID) { }
   bool runOnModule(Module& M);

   void queueTryEvaluate(IntegrationAttempt* ctx, Value* val) {

     assert(ctx && val && "Queued a null value");
     produceQueue->push_back(IntegratorWQItem(ctx, val));
     
   }

   void queueCheckBlock(IntegrationAttempt* ctx, BasicBlock* BB) {

     assert(ctx && BB && "Queued a null block");
     produceQueue->push_back(IntegratorWQItem(ctx, BB));

   }

   void queueCheckLoad(IntegrationAttempt* ctx, LoadInst* LI) {

     assert(ctx && LI && "Queued a null load");
     produceQueue->push_back(IntegratorWQItem(ctx, LI));

   }

   void queueOpenPush(ValCtx OpenInst, ValCtx OpenProgress) {

     assert(OpenInst.first && OpenInst.second && OpenProgress.first && OpenProgress.second && "Queued an invalid open push");
     produceQueue->push_back(IntegratorWQItem((IntegrationAttempt*)OpenInst.second, cast<CallInst>(OpenInst.first), OpenProgress));

   }

   void print(raw_ostream &OS, const Module* M) const {
     for(SmallVector<InlineAttempt*, 4>::const_iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
       (*II)->print(OS);
   }

   void releaseMemory(void) {
     for(SmallVector<InlineAttempt*, 4>::iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
       delete *II;
   }

   void createInvariantScopes(Function*, DenseMap<Instruction*, const Loop*>*&, DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>*&, DenseMap<BasicBlock*, const Loop*>*&);
   DenseMap<Instruction*, const Loop*>& getInstScopes(Function* F);
   DenseMap<std::pair<BasicBlock*, BasicBlock*>, const Loop*>& getEdgeScopes(Function* F);
   DenseMap<BasicBlock*, const Loop*>& getBlockScopes(Function* F);

   BasicBlock* getUniqueReturnBlock(Function* F);

   virtual void getAnalysisUsage(AnalysisUsage &AU) const;

 };

 std::string ind(int i);
 const Loop* immediateChildLoop(const Loop* Parent, const Loop* Child);
 Constant* getConstReplacement(Value*, HCFParentCallbacks*);

} // Namespace LLVM

#endif
