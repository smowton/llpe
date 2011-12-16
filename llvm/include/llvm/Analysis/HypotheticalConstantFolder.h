
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
  std::pair<Value*, int> RealVal;

  SymThunk(std::pair<Value*, int> R) : RealVal(R) { }
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

  virtual std::pair<Value*, int> tryForwardLoad(LoadInst*) = 0;
  virtual std::pair<Value*, int> getReplacement(Value*, int frameIndex = 0) = 0;
  virtual void setReplacement(Value*, std::pair<Value*, int>) = 0;
  virtual bool edgeIsDead(BasicBlock*, BasicBlock*) = 0;
  virtual void setEdgeDead(BasicBlock*, BasicBlock*) = 0;
  virtual bool shouldIgnoreBlock(BasicBlock*) = 0;

};

class HypotheticalConstantFolder {

  Function* F;
  AliasAnalysis* AA;
  TargetData* TD;

  int debugIndent;

  HCFParentCallbacks& parent;

  void realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void realGetImprovementBenefit(Value* V, std::pair<Value*, int>);
  void getImprovementBenefit(Value* V, std::pair<Value*, int>);
  void getPHINodeBenefit(PHINode* PN);
  std::string dbgind();

 public:

 HypotheticalConstantFolder(Function* FIn,
			    AliasAnalysis* _AA,
			    TargetData* _TD,
			    HCFParentCallbacks& P) : 
  F(FIn), AA(_AA), TD(_TD), debugIndent(0), parent(P) { 

  }

  void getBenefit(const SmallVector<std::pair<Value*, Constant*>, 4>& roots);

  void setDebugIndent(int d) { debugIndent = d; }

  bool blockIsDead(BasicBlock* BB);

};

} // Namespace LLVM

#endif
