
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

class HypotheticalConstantFolder {

  Function* F;
  DenseMap<Value*, Constant*>& constInstructions;
  // Edges considered removed for the purpose of estimating constant prop benefit
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& ignoreEdges;
  SmallSet<BasicBlock*, 4>& outBlocks;
  SmallVector<Instruction*, 16>& eliminatedInstructions;
  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>& eliminatedEdges;

  AliasAnalysis* AA;
  TargetData* TD;

  int debugIndent;

  void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void getConstantBenefit(Value* V, Constant* C);
  void realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
  void realGetConstantBenefit(Value* V, Constant* C);
  void getPHINodeBenefit(PHINode* PN);
  bool tryForwardLoad(LoadInst* LI, const MemDepResult& Res);
  std::string dbgind();

 public:

 HypotheticalConstantFolder(Function* FIn,
			    DenseMap<Value*, Constant*>& insts, 
			    SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& edges, 
			    SmallSet<BasicBlock*, 4>& oobBlocks, 
			    SmallVector<Instruction*, 16>& elimResult, 
			    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>& edgeResult,
			    AliasAnalysis* _AA,
			    TargetData* _TD) : 
  F(FIn), constInstructions(insts), ignoreEdges(edges), outBlocks(oobBlocks), 
    eliminatedInstructions(elimResult), eliminatedEdges(edgeResult), AA(_AA), TD(_TD), debugIndent(0) { 

  }

  void getBenefit(const SmallVector<std::pair<Value*, Constant*>, 4>& roots);

  void setDebugIndent(int d) { debugIndent = d; }

  static bool blockIsDead(BasicBlock* BB, const SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& ignoreEdges);

};

} // Namespace LLVM

#endif
