//===- Print.cpp ----------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// Implement a cache of textual representations of instructions, mostly for debug mode.
// Otherwise the operator<< implementation completely indexes the bitcode file on every run.
// This is also punitively expensive for the DOT output code.

// Per default this is implemented simply using LLVM's basic operator<<(Instruction&). To get an efficient
// implementation see utils/fast-printing.patch which must be applied to VMCore/AsmWriter.cpp and 
// LLVM_EFFICIENT_PRINTING defined to disable the simple implementations below.

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FormattedStream.h"

using namespace llvm;

// Build a mapping from every Instruction in F to its text representation, perhaps the brief version.
DenseMap<const Value*, std::string>& LLPEAnalysisPass::getFunctionCache(const Function* F, bool brief) {

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

// Build a mapping for every GlobalValue to its text representation.
void LLPEAnalysisPass::populateGVCaches(const Module* M) {
  
  getGVText(persistPrinter, M, GVCache, GVCacheBrief);

}

DenseMap<const GlobalVariable*, std::string>& LLPEAnalysisPass::getGVCache(bool brief) {

  return brief ? GVCacheBrief : GVCache;

}

// Use the text-representation cache to describe *V.
void LLPEAnalysisPass::printValue(raw_ostream& ROS, const Value* V, bool brief) {

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

// Similarly, describe a shadow-value.
void LLPEAnalysisPass::printValue(raw_ostream& Stream, ShadowValue V, bool brief) {

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

// This never happens at present. Might be appropriate if you wanted to print Values that do and don't
// occur in the original program interchangably.
void LLPEAnalysisPass::disableValueCache() {

  cacheDisabled = true;
  
}

// Print a dead-store-elimination map entry, which indicates whether or not a particular store instruction
// is needed, has been committed as a concrete instruction, etc.
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

namespace llvm {

  raw_ostream& operator<<(raw_ostream& Stream, const IntegrationAttempt& P) {

    P.describe(Stream);
    return Stream;

  }

}

#ifndef LLVM_EFFICIENT_PRINTING

// Simple implementations of instruction printing if the LLVM core assembly printer
// hasn't been patched to make this much more efficient. This becomes a problem
// once we get beyond hundreds of instructions.

PersistPrinter* llvm::getPersistPrinter(Module*) { return new PersistPrinter(); }

void llvm::getInstructionsText(PersistPrinter*, const Function* IF, DenseMap<const Value*, std::string>& IMap, DenseMap<const Value*, std::string>& BriefMap) {

  for(Function::const_iterator FI = IF->begin(), FE = IF->end(); FI != FE; ++FI) {

    const BasicBlock *BB = &*FI;
    for(BasicBlock::const_iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

      const Instruction* I = &*BI;
      std::string instText;
      {
	raw_string_ostream RSO(instText);
	RSO << *I;
      }

      IMap[I] = instText;
      if(I->getType()->isVoidTy())
	BriefMap[I] = instText;
      else
	BriefMap[I] = instText.substr(0, instText.find("=") - 1);

    }

  }

  for(Function::const_arg_iterator AI = IF->arg_begin(), AE = IF->arg_end(); AI != AE; ++AI) {

    std::string argText;
    {
      raw_string_ostream RSO(argText);
      RSO << *AI;
    }

    IMap[(const Argument*)AI] = argText;
    BriefMap[(const Argument*)AI] = argText;

  }

}

void llvm::getGVText(PersistPrinter*, const Module* M, DenseMap<const GlobalVariable*, std::string>& GVMap, DenseMap<const GlobalVariable*, std::string>& BriefGVMap) {

  for(Module::const_global_iterator it = M->global_begin(), itend = M->global_end(); it != itend; ++it) {

    std::string GVText;
    {
      raw_string_ostream RSO(GVText);
      RSO << *it;
    }

    GVMap[&*it] = GVText;
    BriefGVMap[&*it] = GVText;

  }

}

#endif
