// Implement a cache of textual representations of instructions, mostly for debug mode.
// Otherwise the operator<< implementation completely indexes the bitcode file on every run.
// This is also punitively expensive for the DOT output code.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instruction.h"
#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FormattedStream.h"

using namespace llvm;

DenseMap<const Instruction*, std::string>& IntegrationHeuristicsPass::getFunctionCache(const Function* F, bool brief) {

  DenseMap<const Function*, DenseMap<const Instruction*, std::string>* >& Map = brief ? briefFunctionTextCache : functionTextCache;
  DenseMap<const Function*, DenseMap<const Instruction*, std::string>* >::iterator FI = Map.find(F);
  
  if(FI == Map.end()) {
    DenseMap<const Instruction*, std::string>* FullMap = functionTextCache[F] = new DenseMap<const Instruction*, std::string>();
    DenseMap<const Instruction*, std::string>* BriefMap = briefFunctionTextCache[F] = new DenseMap<const Instruction*, std::string>();
    getInstructionsText(F, *FullMap, *BriefMap);
    return brief ? *BriefMap : *FullMap;
  }
  else {
    return *(FI->second);
  }

}

void IntegrationHeuristicsPass::populateGVCaches(const Module* M) {

  getGVText(M, GVCache, GVCacheBrief);

}

DenseMap<const GlobalVariable*, std::string>& IntegrationHeuristicsPass::getGVCache(bool brief) {

  return brief ? GVCacheBrief : GVCache;

}

void IntegrationHeuristicsPass::printValue(raw_ostream& ROS, const Value* V, bool brief) {

  if(!cacheDisabled) {

    if(const Instruction* I = dyn_cast<Instruction>(V)) {

      DenseMap<const Instruction*, std::string>& Map = getFunctionCache(I->getParent()->getParent(), brief);
      ROS << Map[I];
      return;

    }
    else if(const GlobalVariable* GV = dyn_cast<GlobalVariable>(V)) {

      DenseMap<const GlobalVariable*, std::string>& Map = getGVCache(brief);
      ROS << Map[GV];
      return;

    }

  }

  if(brief) {

    if(const GlobalValue* GV = dyn_cast<GlobalValue>(V)) {
     
      ROS << GV->getName();
      return;

    }

    // Otherwise print in full:

  }

  ROS << *V;

}

void IntegrationHeuristicsPass::printValue(raw_ostream& Stream, ShadowValue V, bool brief) {

  if(V.isInval()) {
    Stream << "NULL";
  }
  else if(Value* V2 = V.getVal()) {
    printValue(Stream, V2, brief);
  }
  else if(ShadowInstruction* SI = V.getInst()) {
    printValue(Stream, SI->invar->I, brief);
    Stream << "@";
    SI->parent->IA->describe(Stream);
  }
  else if(ShadowArg* SA = V.getArg()) {
    printValue(Stream, SA->invar->A, brief);
  }
  else if(ShadowGV* GV = V.getGV()) {
    printValue(Stream, GV->G, brief);
  }

}

void IntegrationHeuristicsPass::disableValueCache() {

  cacheDisabled = true;
  
}

void SharedStoreMap::print(raw_ostream& RSO, bool brief) {

  uint32_t i = 0;
  for(std::vector<LocStore>::iterator it = store.begin(), itend = store.end(); it != itend; ++it, ++i) {

    RSO << itcache(IA->getAllocaWithIdx(i)) << ": ";
    it->store->print(RSO, brief);
    RSO << "\n";

  }

}

void SharedTreeNode::print(raw_ostream& RSO, bool brief, uint32_t height, uint32_t idx) {

  if(height == 0) {
    
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
      if(!children[i])
	continue;
      RSO << itcache(getAllocWithIdx(idx + i)) << ": ";
      ((ImprovedValSet*)children[i])->print(RSO, brief);
      RSO << "\n";
    }

  }
  else {
  
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
      if(!children[i])
	continue;
      uint32_t newIdx = idx | (i << (HEAPTREEORDERLOG2 * height));
      ((SharedTreeNode*)children[i])->print(RSO, brief, height - 1, newIdx);
    }
     
  } 

}

void LocalStoreMap::print(raw_ostream& RSO, bool brief) {

  errs() << "--- Stack ---\n";
  for(uint32_t i = 0; i < frames.size(); ++i) {
    if(i != 0)
      errs() << "---frame boundary---\n";
    frames[i]->print(RSO, brief);
  }
  errs() << "--- End stack ---\n--- Heap ---\n";
  if(!heap.root)
    errs() << "(empty)\n";
  else
    heap.root->print(RSO, brief, heap.height - 1, 0);
  errs() << "--- End heap ---\n";

}
