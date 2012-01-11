
#ifndef LLVM_HYPO_CONSTFOLD_H
#define LLVM_HYPO_CONSTFOLD_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"

#include <string>

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

class HCFParentCallbacks;

typedef std::pair<Value*, HCFParentCallbacks*> ValCtx;

raw_ostream &operator<<(raw_ostream&, const ValCtx&);
raw_ostream &operator<<(raw_ostream&, const MemDepResult&);
raw_ostream &operator<<(raw_ostream&, const HCFParentCallbacks&);

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

class HCFParentCallbacks {

 public:

  virtual ValCtx tryForwardLoad(LoadInst*) = 0;
  virtual ValCtx getReplacement(Value*) = 0;
  virtual void setReplacement(Value*, ValCtx) = 0;
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*) = 0;
  virtual void setEdgeDead(BasicBlock*, BasicBlock*) = 0;
  virtual bool shouldIgnoreBlockForConstProp(BasicBlock*) = 0;
  virtual bool shouldIgnoreBlockForDCE(BasicBlock*) = 0;
  virtual bool shouldIgnoreEdge(BasicBlock*, BasicBlock*) = 0;
  virtual bool shouldIgnoreInstruction(Instruction*) = 0;
  virtual bool blockIsDead(BasicBlock*) = 0;
  virtual void setBlockDead(BasicBlock*) = 0;
  virtual BasicBlock* getEntryBlock() = 0;
  virtual ValCtx getDefaultVC(Value*) = 0;
  virtual void describe(raw_ostream&) const = 0;

};

class HypotheticalConstantFolder {

  Function* F;
  AliasAnalysis* AA;
  TargetData* TD;

  SmallVector<BasicBlock*, 4> BlocksImproved;

  int debugIndent;

  HCFParentCallbacks& parent;

  ValCtx getReplacement(Value*);
  Constant* getConstReplacement(Value*);
  bool blockIsDead(BasicBlock*);

  void realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void realGetImprovementBenefit(Value* V, ValCtx);
  void tryGetImprovementBenefit(Value* V, ValCtx, bool force = false);
  void getImprovementBenefit(Value* V, ValCtx);
  void getPHINodeBenefit(PHINode* PN);

  bool improveLoadInsts();
  bool improvePHINodes();
  bool collectDeadBlocks();

  std::string dbgind();

 public:

 HypotheticalConstantFolder(Function* FIn,
			    AliasAnalysis* _AA,
			    TargetData* _TD,
			    HCFParentCallbacks& P) : 
  F(FIn), AA(_AA), TD(_TD), debugIndent(0), parent(P) { 

  }

  void getBenefit(Value*, ValCtx);
  void killEdge(BasicBlock* B1, BasicBlock* B2);

  void setDebugIndent(int d) { debugIndent = d; }

};

} // Namespace LLVM

#endif
