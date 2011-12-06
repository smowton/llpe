
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
  SOuter,
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
  Value* RealVal;

  SymThunk(Value* R) : RealVal(R) { }
  void describe(raw_ostream& OS);
  int getSymType() const { return SThunk; }

};

class SymOuter : public SymExpr { 

 public:
  static inline bool classof(const SymExpr* S) { return S->getSymType() == SOuter; }
  static inline bool classof(const SymOuter*) { return true; }
  void describe(raw_ostream& OS);
  int getSymType() const { return SOuter; }

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

  virtual void tryResolveInParentContext(SmallVector<SymExpr*, 4>& in, SmallVector<SymExpr*, 4>& out) = 0;
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

  void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void getConstantBenefit(Value* V, Constant* C);
  void realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void realGetConstantBenefit(Value* V, Constant* C);
  void getPHINodeBenefit(PHINode* PN);
  bool tryForwardLoad(LoadInst* LI, const MemDepResult& Res);
  bool tryForwardLoadFromParent(LoadInst*);
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

  static bool blockIsDead(BasicBlock* BB, const SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& ignoreEdges);

};

} // Namespace LLVM

#endif
