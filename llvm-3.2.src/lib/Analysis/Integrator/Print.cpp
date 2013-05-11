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

}


void IntegrationAttempt::printPB(raw_ostream& out, ImprovedValSetSingle PB, bool brief) {

  switch(PB.Type) {
  case ValSetTypeScalar:
    out << "S "; break;
  case ValSetTypePB:
    out << "PB "; break;
  case ValSetTypeFD:
    out << "FD "; break;
  case ValSetTypeVarArg:
    out << "VA "; break;
  case ValSetTypeUnknown:
    out << "U "; break;
  }

  if(PB.Overdef)
    out << "Overdef";
  else {
    out << "{ ";
    for(SmallVector<ImprovedVal, 4>::iterator it = PB.Values.begin(), it2 = PB.Values.end(); it != it2; ++it) {

      if(it != PB.Values.begin())
	out << ", ";
      out << itcache(it->V, brief);
      if(PB.Type == ValSetTypePB) {
	if(it->Offset == LLONG_MAX)
	  out << " + ?";
	else
	  out << " + " << it->Offset;
      }
      else if(PB.Type == ValSetTypeVarArg) {
	out << " #" << it->Offset;
      }
    }
    out << " }";
  }

}

void IntegrationHeuristicsPass::disableValueCache() {

  cacheDisabled = true;
  
}
