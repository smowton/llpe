
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Pass.h"

#include <string>
#include <vector>

#define LPDEBUG(x) do { printHeader(dbgs()); dbgs() << ": " << x; } while(0)

namespace llvm {

class Function;
class Value;
class Constant;
class BasicBlock;
class Instruction;
class TargetData;
class AliasAnalysis;
class PHINode;
class MemDepResult;
class LoadInst;
class raw_ostream;
class ConstantInt;
class Type;
class Argument;

class HCFParentCallbacks;

typedef std::pair<Value*, HCFParentCallbacks*> ValCtx;

raw_ostream& operator<<(raw_ostream&, const ValCtx&);
raw_ostream& operator<<(raw_ostream&, const MemDepResult&);
raw_ostream& operator<<(raw_ostream&, const HCFParentCallbacks&);

#define VCNull (std::make_pair<Value*, HCFParentCallbacks*>(0, 0))

inline ValCtx const_vc(Constant* C) {

  return std::make_pair<Constant*, HCFParentCallbacks*>(C, 0);

}

inline ValCtx make_vc(Value* V, HCFParentCallbacks* H) {

  return std::make_pair(V, H);

}

bool shouldForwardValue(Value* V);

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

// Interface exposed to Memory Dependence Analysis and other external analyses that the integrator uses.
class HCFParentCallbacks {

 public:

  virtual ValCtx getReplacement(Value*) = 0;
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*) = 0;
  virtual bool blockIsDead(BasicBlock*) = 0;
  virtual BasicBlock* getEntryBlock() = 0;
  virtual ValCtx getDefaultVC(Value*) = 0;
  virtual void describe(raw_ostream&) const = 0;

};

class InlineAttempt;
class PeelAttempt;
class IntegrationAttempt;
class IntegrationHeuristicsPass;

 class Function;
 class LoopInfo;
 class TargetData;
 class AliasAnalysis;
 class CallInst;
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

  std::string nestingIndent() const;

  int nesting_depth;

  public:

 IntegrationAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, 
		    int depth) : 
  pass(Pass),
    parent(P),
    LI(_LI),
    TD(_TD), 
    AA(_AA), 
    F(_F),
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



  // Pure virtuals to be implemented by PeelIteration or InlineAttempt:

  virtual const Loop* getLoopContext() = 0;
  virtual Instruction* getEntryInstruction() = 0;
  virtual void collectAllBlockStats() = 0;
  virtual void printHeader(raw_ostream& OS) const = 0;
  virtual void queueTryEvaluateOwnCall() = 0;

  // Simple state-tracking helpers:

  void setReplacement(Value*, ValCtx);
  void setEdgeDead(BasicBlock*, BasicBlock*);
  void setBlockDead(BasicBlock*);

  Constant* getConstReplacement(Value* V);

  // Constant propagation:

  virtual bool shouldTryEvaluate(Value* ArgV);

  ValCtx getPHINodeValue(PHINode*);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  void tryEvaluate(Value*);
  virtual ValCtx tryEvaluateResult(Value*);
  void investigateUsers(Value* V);

  virtual void queueTryEvalExitPHI(Instruction* UserI);
  bool queueImproveNextIterationPHI(Instruction* I);
  void queueTryEvaluateGeneric(Instruction* UserI, Value* Used);

  // CFG analysis:

  bool shouldCheckBlock(BasicBlock* BB);
  void checkBlock(BasicBlock* BB);
  virtual bool checkLoopSpecialBlock(BasicBlock* BB);
  
  // Child (inlines, peels) management

  InlineAttempt* getInlineAttempt(CallInst* CI);
  InlineAttempt* getOrCreateInlineAttempt(CallInst* CI);
 
  PeelAttempt* getPeelAttempt(const Loop*);
  PeelAttempt* getOrCreatePeelAttempt(const Loop*);

  // Load forwarding:

  void checkLoad(LoadInst* LI);
  ValCtx tryForwardLoad(LoadInst*);
  bool forwardLoadIsNonLocal(LoadInst* LoadI, ValCtx& Result, IntegrationAttempt* originCtx);
  ValCtx getDefn(const MemDepResult& Res);
  MemDepResult getUniqueDependency(LoadInst* LI);

  bool buildSymExpr(LoadInst* LoadI, SmallVector<SymExpr*, 4>& Expr);
  void realiseSymExpr(SmallVector<SymExpr*, 4>& in, Instruction* Where, Instruction*& FakeBaseObject, LoadInst*& Accessor, SmallVector<Instruction*, 4>& tempInstructions);
  void destroySymExpr(SmallVector<Instruction*, 4>& tempInstructions);

  virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx) = 0;
  ValCtx tryResolveLoadAtChildSite(IntegrationAttempt* IA, SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx);
  bool tryResolveExprFrom(SmallVector<SymExpr*, 4>& Expr, Instruction* Where, ValCtx& Result, IntegrationAttempt* originCtx);
  bool tryResolveExprUsing(SmallVector<SymExpr*, 4>& Expr, Instruction* FakeBase, LoadInst* Accessor, ValCtx& Result, IntegrationAttempt* originCtx);

  void queueLoadsBlockedOn(Instruction* SI);
  void queueCheckAllLoads();

  // Stat collection and printing:

  void collectBlockStats(BasicBlock* BB);
  void collectLoopStats(const Loop*);
  void collectStats();
  void print(raw_ostream& OS) const;

};

class PeelIteration : public IntegrationAttempt {

  int iterationCount;
  const Loop* L;
  PeelAttempt* parentPA;

  PeelIteration* getOrCreateNextIteration();

public:

 PeelIteration(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, PeelAttempt* PP, Function& F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD,
	       AliasAnalysis* _AA, const Loop* _L, int iter, int depth) :
  IntegrationAttempt(Pass, P, F, _LI, _TD, _AA, depth),
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

  virtual bool checkLoopSpecialBlock(BasicBlock* BB);
  virtual bool getLoopHeaderPHIValue(PHINode* PN, ValCtx& result);
  virtual bool queueImproveNextIterationPHI(Instruction* I);
  void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);
  virtual void queueTryEvaluateOwnCall();
  virtual void queueTryEvalExitPHI(Instruction* UserI);

  void queueCheckExitBlock(BasicBlock* BB);
  void checkFinalIteration();

  virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx);

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
   std::vector<PeelIteration*> Iterations;
   int nesting_depth;
   int debugIndent;

 public:

   PeelAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& _F, DenseMap<Function*, LoopInfo*>& _LI, TargetData* _TD, AliasAnalysis* _AA, const Loop* _L, int depth);
   ~PeelAttempt();

   SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;

   PeelIteration* getIteration(unsigned iter);
   PeelIteration* getOrCreateIteration(unsigned iter);

   ValCtx getReplacement(Value* V, int frameIndex, int sourceIteration);

   ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, int originIter, IntegrationAttempt* originCtx);

   void queueTryEvaluateVariant(Instruction* VI, const Loop* VILoop, Value* Used);

   void collectStats();
   void printHeader(raw_ostream& OS) const;
   void print(raw_ostream& OS) const;

   std::string nestingIndent() const;

 };

class InlineAttempt : public IntegrationAttempt { 

  CallInst* CI;

 public:

 InlineAttempt(IntegrationHeuristicsPass* Pass, IntegrationAttempt* P, Function& F, DenseMap<Function*, LoopInfo*>& LI, TargetData* TD, AliasAnalysis* AA, CallInst* _CI, int depth) 
   : 
   IntegrationAttempt(Pass, P, F, LI, TD, AA, depth),
     CI(_CI)
     { }

   virtual ValCtx tryEvaluateResult(Value*);

   virtual Instruction* getEntryInstruction();
   virtual BasicBlock* getEntryBlock();
   virtual const Loop* getLoopContext();

   virtual ValCtx tryForwardExprFromParent(SmallVector<SymExpr*, 4>& Expr, IntegrationAttempt* originCtx);

   virtual void queueTryEvaluateOwnCall();

   ValCtx tryGetReturnValue();

   ValCtx getImprovedCallArgument(Argument* A);

   virtual void describe(raw_ostream& Stream) const;

   virtual void collectAllBlockStats();
   virtual void printHeader(raw_ostream&) const;

};

enum IntegratorWQItemType {

   TryEval,
   CheckBlock,
   CheckLoad

};

// A cheesy hack to make a value type that acts like a dynamic dispatch hierarchy
class IntegratorWQItem {

  IntegrationAttempt* ctx;
  IntegratorWQItemType type;
  void* operand;

public:

IntegratorWQItem(IntegrationAttempt* c, IntegratorWQItemType t, void* op) : ctx(c), type(t), operand(op) { }

  void execute();
  void describe(raw_ostream& s);

};

class IntegrationHeuristicsPass : public ModulePass {

   DenseMap<Function*, LoopInfo*> LIs;
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

     produceQueue->push_back(IntegratorWQItem(ctx, TryEval, val));
     
   }

   void queueCheckBlock(IntegrationAttempt* ctx, BasicBlock* BB) {

     produceQueue->push_back(IntegratorWQItem(ctx, CheckBlock, BB));

   }

   void queueCheckLoad(IntegrationAttempt* ctx, LoadInst* LI) {

     produceQueue->push_back(IntegratorWQItem(ctx, CheckLoad, LI));

   }

   void print(raw_ostream &OS, const Module* M) const {
     for(SmallVector<InlineAttempt*, 4>::const_iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
       (*II)->print(OS);
   }

   void releaseMemory(void) {
     for(SmallVector<InlineAttempt*, 4>::iterator II = rootAttempts.begin(), IE = rootAttempts.end(); II != IE; II++)
       delete *II;
   }

   virtual void getAnalysisUsage(AnalysisUsage &AU) const {

     AU.addRequired<AliasAnalysis>();
     AU.addRequired<LoopInfo>();
     AU.setPreservesAll();

   }

 };

 std::string ind(int i);

} // Namespace LLVM

#endif
