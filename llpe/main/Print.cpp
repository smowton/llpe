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

DenseMap<const Value*, std::string>& IntegrationHeuristicsPass::getFunctionCache(const Function* F, bool brief) {

  DenseMap<const Function*, DenseMap<const Value*, std::string>* >& Map = brief ? briefFunctionTextCache : functionTextCache;
  DenseMap<const Function*, DenseMap<const Value*, std::string>* >::iterator FI = Map.find(F);
  
  if(FI == Map.end()) {
    DenseMap<const Value*, std::string>* FullMap = functionTextCache[F] = new DenseMap<const Value*, std::string>();
    DenseMap<const Value*, std::string>* BriefMap = briefFunctionTextCache[F] = new DenseMap<const Value*, std::string>();
    getInstructionsText(persistPrinter, F, *FullMap, *BriefMap);
    return brief ? *BriefMap : *FullMap;
  }
  else {
    return *(FI->second);
  }

}

void IntegrationHeuristicsPass::populateGVCaches(const Module* M) {

  getGVText(persistPrinter, M, GVCache, GVCacheBrief);

}

DenseMap<const GlobalVariable*, std::string>& IntegrationHeuristicsPass::getGVCache(bool brief) {

  return brief ? GVCacheBrief : GVCache;

}

void IntegrationHeuristicsPass::printValue(raw_ostream& ROS, const Value* V, bool brief) {

  if(!cacheDisabled) {

    if(isa<Instruction>(V) || isa<Argument>(V)) {

      const Function* VF;
      if(const Instruction* I = dyn_cast<Instruction>(V))
	VF = I->getParent()->getParent();
      else
	VF = cast<Argument>(V)->getParent();

      DenseMap<const Value*, std::string>& Map = getFunctionCache(VF, brief);
      ROS << Map[V];
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
  else if(V.isConstantInt()) {
    Stream << (*V.getNonPointerType()) << " " << V.u.CI;
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
  else if(V.isPtrIdx()) {
    if(V.u.PtrOrFd.frame == -1)
      Stream << "G/H alloc " << V.u.PtrOrFd.idx;
    else
      Stream << "S alloc " << V.u.PtrOrFd.frame << " / " << V.u.PtrOrFd.idx;
  }
  else if(V.isFdIdx()) {
    Stream << "FD ";
    if(V.t == SHADOWVAL_FDIDX64)
      Stream << "[64] ";
    Stream << V.u.PtrOrFd.idx;
  }

}

void IntegrationHeuristicsPass::disableValueCache() {

  cacheDisabled = true;
  
}

void DSEMapPointer::print(raw_ostream& RSO, bool brief) {

  if(!M)
    return;

  for(DSEMapTy::iterator it = M->begin(), itend = M->end(); it != itend; ++it) {

    errs() << it.start() << "-" << it.stop() << ": { ";
    const DSEMapEntry& entry = it.value();

    for(DSEMapEntry::const_iterator eit = entry.begin(), eend = entry.end(); eit != eend; ++eit) {

      TrackedStore* TS = *eit;

      if(eit != entry.begin())
	RSO << ", ";
      if(!TS)
	RSO << "NULL!";
      else if(TS->isNeeded) {
	RSO << "[needed]";
      }
      else {
	if(!TS->isCommitted)
	  RSO << itcache(TS->I, brief);
	else if(!TS->committedInsts)
	  RSO << "[committed-unknown]";
	else {
	  RSO << "[committed] ";
	  for(uint32_t i = 0, ilim = TS->nCommittedInsts; i != ilim; ++i) {
	    if(i != 0)
	      RSO << ", ";
	    RSO << (*(TS->committedInsts[i]));
	  }
	  RSO << " in block " << cast<Instruction>((Value*)TS->committedInsts[0])->getParent()->getName();	  
	}
	RSO << " (" << TS->outstandingBytes << ")";
      }

    }

    errs() << " }\n";

  }

}
