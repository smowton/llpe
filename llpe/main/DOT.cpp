//===-- DOT.cpp -----------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// Functions to describe the hierarchy of peel and inline attempts in DOT format for easy review.
// Used to provide the UI's basic block graph view.

#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"

#include "llvm/Analysis/LLPE.h"

#include <sys/stat.h>
#include <sys/types.h>

#include <string>

using namespace llvm;

std::string IntegrationAttempt::getValueColour(ShadowValue SV, std::string& textColour, bool plain) {

  // How should the instruction be coloured:
  // Bright green: defined here, i.e. it's a loop invariant.
  // Red: killed here or as an invariant (including dead memops)
  // Yellow: Expanded call instruction
  // Pink: Unexpanded call instruction
  // Lime green: Invariant defined above.
  // Dark green: Pointer base known
  // Grey: part of a dead block.

  if(plain)
    return "white";

  InstArgImprovement* IAI = SV.getIAI();
  ShadowInstruction* SI = SV.getInst();
  
  if(!IAI)
    return "#aaaaaa";

  if(SI && SI->readsMemoryDirectly()) {
    if(SI->isThreadLocal == TLS_MUSTCHECK)
      return "orangered";
  }

  if(willBeDeleted(SV))
    return "red";

  if(ShadowInstruction* SI = SV.getInst()) {

    if(GlobalIHP->barrierInstructions.count(SI)) {
      textColour = "white";
      return "black";
    }

  }

  if(val_is<CallInst>(SV) || val_is<InvokeInst>(SV)) {
    if(SV.u.I->typeSpecificData)
      return "yellow";
    else
      return "pink";
  }

  if(IAI->PB) {
    ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IAI->PB);
    if(IVS && IVS->Values.size() == 1)
      return "green";
    if((!IVS) || (IVS->Values.size() != 0 && !IVS->Overdef))
      return "darkgreen";
  }

  return "white";

}

// Helper: shorten str to include at most maxlen characters from the original string,
// plus some suffix.
static std::string TruncStr(std::string str, unsigned maxlen) {

  if(str.size() > maxlen) {

    str.resize(maxlen);
    str.append(" ...");

  }

  return str;

}

// Replace special characters with HTML escapes, and double backslashes (DOT recognises
// both forms of escape sequence)
static std::string escapeHTML(std::string Str) {

  for (unsigned i = 0; i != Str.length(); ++i) {
    switch (Str[i]) {
    case '&':
      Str.replace(i, 1, "&amp;");
      i += 4;
      break;
    case '\\':
      Str.insert(Str.begin()+i, '\\');
      ++i;
      break;
    case '\t':
      Str.insert(Str.begin()+i, ' ');  // Convert to two spaces
      ++i;
      Str[i] = ' ';
      break;
    case '<': 
      Str.replace(i, 1, "&lt;");
      i += 3;
      break;
    case '>':
      Str.replace(i, 1, "&gt;");
      i += 3;
      break;
    case '"':
      Str.replace(i, 1, "&quot;");
      i += 5;
      break;
    }
  }

  return Str;

}

// Stringify V, with abbreviation and escaping.
static std::string escapeHTMLValue(Value* V, IntegrationAttempt* IA, bool brief=false) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  IA->printWithCache(V, RSO, brief);
  return escapeHTML(TruncStr(RSO.str(), 500));

}

// Print any derived result concerning SV (e.g. a constant, or an allocation identifier,
// or a VFS specialisation report. Print nothing if we don't have a concrete result.
void IntegrationAttempt::printRHS(ShadowValue SV, raw_ostream& Out) {
  
  if(SV.isVal())
    return;

  InstArgImprovement* IAI = SV.getIAI();

  ShadowInstruction* SI = SV.getInst();

  uint64_t SVi;
  if(tryGetConstantInt(SV, SVi)) {

    Out << (*SV.getNonPointerType()) << " " << SVi;

  }
  else if(Constant* C = getConstReplacement(SV)) {
    if(isa<Function>(C))
      Out << "@" << C->getName();
    else
      Out << (*C);
    return;
  }
  /*
  if(IAI->dieStatus != INSTSTATUS_ALIVE) {
    if(isInvariant)
      Out << "(invar) ";
    Out << "DEAD";
    return;
  }
  */
  bool PBPrinted = false;
  if(IAI->PB) {
    ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IAI->PB);
    if((!IVS) || (IVS->Values.size() > 0 && !IVS->Overdef)) {
      IAI->PB->print(Out, true);
      PBPrinted = true;
    }
  }

  if(!SI)
    return;

  DenseMap<ShadowInstruction*, std::string>::iterator optit = pass->optimisticForwardStatus.find(SI);
  if(!PBPrinted) {
    if(optit != pass->optimisticForwardStatus.end()) {
      Out << "OPT (" << optit->second << "), ";
    }
  }
  if(inst_is<CallInst>(SI)) {
    DenseMap<ShadowInstruction*, OpenStatus*>::iterator it = pass->forwardableOpenCalls.find(SI);
    if(it != pass->forwardableOpenCalls.end()) {
      Out << it->second->Name << "(" << (it->second->success ? "success" : "not found") << ")";
    }
    else {
      DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(SI);
      if(it != pass->resolvedReadCalls.end())
	Out << it->second.name << " (" << it->second.incomingOffset << "-" << it->second.incomingOffset + (it->second.readSize - 1) << ")";
    }
  }

}

// When we're viewing a loop iteration, we draw target blocks outside this iteration
// as an opaque label, rather than drawing all the instructions as usual. Get such a special
// label if applicable. No edges leave this content for a function...
bool InlineAttempt::getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) {

  return false;

}

// ...but some do for a loop iteration.
bool PeelIteration::getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) {

  if(FromBB->idx == L->latchIdx && ToBB->idx == L->headerIdx) {

    Out << "\"Next iteration header\"";
    return true;

  }
  else if(!L->contains(ToBB->naturalScope)) {

    Out << "\"Exit block " << escapeHTML(ToBB->BB->getName()) << "\"";
    return true;

  }

  return false;

}

// Print an edge from BB -> SB. In brief mode, unreachable blocks / edges and branches to
// unspecialised code are omitted.
void IntegrationAttempt::printOutgoingEdge(ShadowBBInvar* BBI, ShadowBB* BB, ShadowBBInvar* SBI, ShadowBB* SB, uint32_t i, bool useLabels, const ShadowLoopInvar* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief) {

  if(brief && ((!SB) || edgeBranchesToUnspecialisedCode(BBI, SBI)))
    return;

  std::string edgeString;
  raw_string_ostream rso(edgeString);

  rso << "Node" << BBI->BB;
  if(useLabels) {
    rso << ":s" << i;
  }

  rso << " -> ";

  // Handle exits from this loop / this loop's latch specially:
  if(!getSpecialEdgeDescription(BBI, SBI, rso))
    rso << "Node" << SBI->BB;

  if(edgeIsDead(BBI, SBI)) {
    rso << "[color=gray]";
  }
  else if(edgeBranchesToUnspecialisedCode(BBI, SBI)) {
    rso << "[color=red]";
  }

  rso << ";\n";

  if(deferEdgesOutside && !deferEdgesOutside->contains(SBI->naturalScope)) {
    deferredEdges->push_back(rso.str());
  }
  else {
    Out << rso.str();
  }
	
}

// Print path conditions, appearing instruction-like at the top of the relevant block.
void llvm::printPathCondition(PathCondition& PC, PathConditionTypes t, ShadowBB* BB, raw_ostream& Out, bool HTMLEscaped) {

  const char* arrow = HTMLEscaped ? " -&gt; " : " -> ";
  
  switch(t) {
  case PathConditionTypeInt:
    Out << "Int";
    break;
  case PathConditionTypeString:
    Out << "String";
    break;
  case PathConditionTypeIntmem:
    Out << "Intmem";
    break;
  case PathConditionTypeStream:
    Out << "Stream";
    break;
  case PathConditionTypeFptrmem:
    release_assert(0 && "Bad path condition type");
    llvm_unreachable("Bad path condition type");
  }

  Out << " PC: ";

  if(t == PathConditionTypeString) {

    GlobalVariable* GV = cast<GlobalVariable>(PC.u.val);
    ConstantDataArray* CDA = cast<ConstantDataArray>(GV->getInitializer());
    Out << "\"" << CDA->getAsCString() << "\"";

  }
  else if(t == PathConditionTypeStream) {

    Out << PC.u.filename;

  }
  else {

    std::string truncd;

    {
      raw_string_ostream RSO(truncd);
      RSO << itcache(ShadowValue(PC.u.val), true);
    }    

    Out << TruncStr(truncd, 100);
	
  }

  if(!PC.instBB) {

    ShadowGV* GV = &GlobalIHP->shadowGlobals[PC.instIdx];
    Out << arrow << itcache(GV, true);

  }
  else if(PC.instBB == (BasicBlock*)ULONG_MAX) {

    IntegrationAttempt* ArgIA = getIAWithTargetStackDepth(BB->IA->getFunctionRoot(), PC.instStackIdx);

    Function::arg_iterator AI = ArgIA->F.arg_begin();
    std::advance(AI, PC.instIdx);
    Out << arrow << itcache((Argument*)AI, true);

  }
  else {
	
    BasicBlock::iterator BI = PC.instBB->begin();
    std::advance(BI, PC.instIdx);

    Out << arrow << PC.instBB->getName() << " / " << itcache(&*BI, true);

  }

  if(PC.offset != 0)
    Out << " + " << PC.offset;

}

static void printPathConditionList(std::vector<PathCondition>& conds, PathConditionTypes t, raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB) {

  for(std::vector<PathCondition>::iterator it = conds.begin(), itend = conds.end(); it != itend; ++it) {

    if(it->fromBB == BBI->BB) {

      Out << "<tr><td colspan=\"2\" border=\"0\" align=\"left\">  ";

      printPathCondition(*it, t, BB, Out, true);

      Out << "</td></tr>\n";

    }

  }

}

static void printPathConditionsFrom(PathConditions& PC, raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB) {

  // Mention if there are symbolic path conditions or functions here:
  printPathConditionList(PC.IntPathConditions, PathConditionTypeInt, Out, BBI, BB);
  printPathConditionList(PC.AsDefIntPathConditions, PathConditionTypeInt, Out, BBI, BB);
  printPathConditionList(PC.IntmemPathConditions, PathConditionTypeIntmem, Out, BBI, BB);
  printPathConditionList(PC.StringPathConditions, PathConditionTypeString, Out, BBI, BB);

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(),
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(it->BB == BBI->BB) {

      Out << "<tr><td colspan=\"2\" border=\"0\" align=\"left\">  Call PC: ";
      Out << it->F->getName();
      Out << "</td></tr>\n";

    }

  }

}

void IntegrationAttempt::printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB) {

  if(invarInfo->pathConditions)
    printPathConditionsFrom(*invarInfo->pathConditions, Out, BBI, BB);

}

void InlineAttempt::printPathConditions(raw_ostream& Out, ShadowBBInvar* BBI, ShadowBB* BB) {

  if(!BB)
    return;

  if(targetCallInfo)
    printPathConditionsFrom(pass->pathConditions, Out, BBI, BB);

  IntegrationAttempt::printPathConditions(Out, BBI, BB);

}

// Helpers for below:
BasicBlock* InlineAttempt::getEntryBlock() {
  return &F.getEntryBlock();
}

BasicBlock* PeelIteration::getEntryBlock() {
  return getBBInvar(L->headerIdx)->BB;
}

// Draw BB (in brief mode dead blocks are omitted). Yellow highlights indicate blocks that will be
// reached for sure if the specialisation is entered and no implicit checks (e.g. for thread
// interference) fail; green means the same and additionally the block is not in any loop context;
// orange means that explicit checks (e.g. user-specified specialisation conditions) must pass too.
// Light blue means that Clang's vararg code has been special-cased here (a temporary measure
// until the vararg intrinsic work properly).
void IntegrationAttempt::describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const ShadowLoopInvar* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBBInvar*, 4>* forceSuccessors, bool brief, bool plain) {

  if(brief && !BB)
    return;

  Instruction* TI = BBI->BB->getTerminator();
  bool useLabels = false;
  if(!forceSuccessors) {
    if(BranchInst* BI = dyn_cast<BranchInst>(TI))
      useLabels = BI->isConditional();
    else if(isa<SwitchInst>(TI))
      useLabels = true;
  }
  unsigned numSuccessors = 1;
  if(useLabels)
    numSuccessors = TI->getNumSuccessors();

  Out << "Node" << BBI->BB << " [shape=plaintext,fontsize=10,label=<<table cellspacing=\"0\" border=\"0\"><tr><td colspan=\"" << numSuccessors << "\" border=\"1\"><table border=\"0\">\n";

  Out << "<tr><td border=\"0\" align=\"left\" colspan=\"2\"";
  
  if(!plain) {

    if(BB && BB->useSpecialVarargMerge) {
      Out << " bgcolor=\"lightblue\"";
    }
    else if(BB && BB->status == BBSTATUS_CERTAIN) {
      if(!BB->inAnyLoop)
	Out << " bgcolor=\"green\"";
      else
	Out << " bgcolor=\"yellow\"";
    }
    else if(BB && BB->status == BBSTATUS_ASSUMED) {
      Out << " bgcolor=\"orange\"";
    }

  }

  Out << "><font point-size=\"14\">";
  if(BBI->BB == getEntryBlock())
    Out << "Entry block: ";
  Out << escapeHTML(BBI->BB->getName()) << " </font></td></tr>\n";

  bool isFunctionHeader = (!L) && (BBI->BB == &(F.getEntryBlock()));

  printPathConditions(Out, BBI, BB);

  size_t ValSize = BBI->BB->size();
  if(isFunctionHeader)
    ValSize += F.arg_size();

  std::vector<ShadowValue> Vals;
  Vals.reserve(ValSize);

  if(isFunctionHeader) {
    InlineAttempt* self = getFunctionRoot();
    for(uint32_t i = 0; i < F.arg_size(); ++i)
      Vals.push_back(ShadowValue(&(self->argShadows[i])));
  }

  BasicBlock::iterator BI, BE;
  uint32_t i;
  for(BI = BBI->BB->begin(), BE = BBI->BB->end(), i = 0; BI != BE; ++BI, ++i) {
    if(!BB)
      Vals.push_back(ShadowValue(&*BI));
    else
      Vals.push_back(ShadowValue(&(BB->insts[i])));
  }

  for(std::vector<ShadowValue>::iterator VI = Vals.begin(), VE = Vals.end(); VI != VE; ++VI) {

    std::string textColour;
    Out << "<tr><td border=\"0\" align=\"left\" bgcolor=\"" << getValueColour(*VI, textColour, plain) << "\">";
    if(!textColour.empty())
      Out << "<font color=\"" << textColour << "\">";
    Out << escapeHTMLValue(VI->getBareVal(), this);
    if(!textColour.empty())
      Out << "</font>";
    Out << "</td><td>";
    std::string RHSStr;
    raw_string_ostream RSO(RHSStr);
    if(!plain)
      printRHS(*VI, RSO);
    RSO.flush();
    Out << escapeHTML(TruncStr(RSO.str(), 400));
    Out << "</td></tr>\n";

  }

  Out << "</table></td></tr>";

  // Print ports for branch / switch statements, borrowed from the DOT printer.

  if(useLabels) {

    Out << "<tr>\n";
    unsigned i = 0;
    for(succ_const_iterator SI = succ_begin(const_cast<const BasicBlock*>(BBI->BB)), SE = succ_end(const_cast<const BasicBlock*>(BBI->BB)); SI != SE; ++SI, ++i) {
      Out << "<td port=\"s" << i << "\" border=\"1\">" << DOTGraphTraits<const Function*>::getEdgeSourceLabel(BBI->BB, SI) << "</td>\n";
    }
    Out << "</tr>\n";

  }

  Out << "</table>>];\n";

  if(forceSuccessors) {

    for(SmallVector<ShadowBBInvar*, 4>::iterator it = forceSuccessors->begin(), it2 = forceSuccessors->end(); it != it2; ++it) {

      ShadowBBInvar* SuccBBI = getBBInvar((*it)->idx);
      IntegrationAttempt* IA = getIAForScope(SuccBBI->naturalScope);
      ShadowBB* SuccBB = IA->getBB(*SuccBBI);
      printOutgoingEdge(BBI, BB, SuccBBI, SuccBB, 0, false, deferEdgesOutside, deferredEdges, Out, brief);

    }

  }
  else {

    // Print the successor edges *except* any loop exit edges, since those must occur in parent context.
    for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

      ShadowBBInvar* SuccBBI = getBBInvar(BBI->succIdxs[i]);
      IntegrationAttempt* IA = getIAForScope(SuccBBI->naturalScope);
      ShadowBB* SuccBB = IA->getBB(*SuccBBI);

      printOutgoingEdge(BBI, BB, SuccBBI, SuccBB, i, useLabels, deferEdgesOutside, deferredEdges, Out, brief);

    }

  }
 
}

// Is BB live in this context or any child loop?
bool IntegrationAttempt::blockLiveInAnyScope(ShadowBBInvar* BB) {

  if(!getBB(*BB))
    return false;

  if(BB->naturalScope != L) {

    const ShadowLoopInvar* enterL = immediateChildLoop(L, BB->naturalScope);
    if(PeelAttempt* LPA = getPeelAttempt(enterL)) {

      if(LPA->Iterations.back()->iterStatus == IterationStatusFinal) {

	for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	  if(LPA->Iterations[i]->blockLiveInAnyScope(BB))
	    return true;
	  
	}

	return false;

      }

    }

  }

  // Live here and not in a child loop or in an unexpanded or unterminated loop.
  return true;

}

// In brief mode, draw only the entry and live exit blocks of loop DescribeL.
// In normal mode, draw its blocks as per usual but with a grouping frame indicating
// loop structure.
void IntegrationAttempt::describeLoopAsDOT(const ShadowLoopInvar* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief) {

  SmallVector<std::string, 4> deferredEdges;

  if(brief && !BBs[headerIdx])
    return;

  ShadowBBInvar* HeaderBBI = getBBInvar(headerIdx);

  Out << "subgraph \"cluster_" << DOT::EscapeString(HeaderBBI->BB->getName()) << "\" {";
  
  bool loopIsIgnored = pass->shouldIgnoreLoop(&F, getBBInvar(DescribeL->headerIdx)->BB);
  bool loopExplored = false;
  bool loopTerminated = false;

  if(!loopIsIgnored) {

    DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator InlIt = peelChildren.find(DescribeL);
    if(InlIt != peelChildren.end()) {
      loopExplored = true;
      if(InlIt->second->isTerminated())
	loopTerminated = true;
    }

  }

  if(loopIsIgnored) {

    // Print the loop blocks including sub-clustering:
    describeScopeAsDOT(DescribeL, headerIdx, Out, brief, &deferredEdges);

  }
  else if(brief) {

    // Draw the header branching to all exiting blocks, to each exit block.
    const std::vector<uint32_t>& exitingIdxs = DescribeL->exitingBlocks;

    SmallVector<ShadowBBInvar*, 4> liveExitingBlocks;

    for(unsigned i = 0; i < exitingIdxs.size(); ++i) {

      ShadowBBInvar* BBI = getBBInvar(exitingIdxs[i]);
      if(blockLiveInAnyScope(BBI)) {

	liveExitingBlocks.push_back(BBI);

      }

    }

    describeBlockAsDOT(getBBInvar(headerIdx + BBsOffset), getBB(headerIdx + BBsOffset), 0, 0, Out, &liveExitingBlocks, brief, loopTerminated);

    const std::vector<std::pair<uint32_t, uint32_t> >& exitEdges = DescribeL->exitEdges;

    for(SmallVector<ShadowBBInvar*, 4>::iterator it = liveExitingBlocks.begin(), it2 = liveExitingBlocks.end(); it != it2; ++it) {
      
      ShadowBBInvar* BBI = *it;
      SmallVector<ShadowBBInvar*, 4> Targets;

      for(std::vector<std::pair<uint32_t, uint32_t> >::const_iterator it3 = exitEdges.begin(), it4 = exitEdges.end(); it3 != it4; ++it3) {

	if(it3->first == BBI->idx) {

	  Targets.push_back(getBBInvar(it3->second));

	}

      }

      describeBlockAsDOT(BBI, getBB(*BBI), DescribeL, &deferredEdges, Out, &Targets, brief, loopTerminated);      

    }

  }
  else {

    ShadowBBInvar* BBInvar;
    uint32_t idx;

    for(idx = headerIdx, BBInvar = getBBInvar(headerIdx + BBsOffset); DescribeL->contains(BBInvar->naturalScope); ++idx, BBInvar = getBBInvar(idx + BBsOffset)) {

      ShadowBB* BB = getBB(*BBInvar);
      describeBlockAsDOT(BBInvar, BB, DescribeL, &deferredEdges, Out, 0, brief);

    }

  }
						     
  Out << "label = \"Loop " << DOT::EscapeString(HeaderBBI->BB->getName()) << " (";

  if(loopIsIgnored) {

    Out << "Ignored";

  }
  else if(!loopExplored) {

    Out << "Not explored";

  }
  else {

    if(loopTerminated) {
      Out << "Terminated";
    }
    else {
      Out << "Not terminated";
    }

    Out << ", " << peelChildren[DescribeL]->Iterations.size() << " iterations";

  }

  Out << ")\";\n}\n";

  for(SmallVector<std::string, 4>::iterator it = deferredEdges.begin(), it2 = deferredEdges.end(); it != it2; ++it) {

    Out << *it;

  }

}

// Draw the whole scope DescribeL, which starts at block #headerIdx, and may be null to indicate the
// outermost (function) scope (in which case headerIdx == 0).
void IntegrationAttempt::describeScopeAsDOT(const ShadowLoopInvar* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief, SmallVector<std::string, 4>* deferredEdges) {

  ShadowBBInvar* BBI;
  uint32_t i;

  for(i = headerIdx, BBI = getBBInvar(headerIdx + BBsOffset); 
      i < nBBs && ((!DescribeL) || DescribeL->contains(BBI->naturalScope)); 
      ++i, BBI = getBBInvar(i + BBsOffset)) {

    ShadowBBInvar* BBI = getBBInvar(i + BBsOffset);
    ShadowBB* BB = BBs[i];
    
    if(BBI->naturalScope != DescribeL) {

      describeLoopAsDOT(BBI->naturalScope, i, Out, brief);
	
      // Advance past the loop:
      while(i < nBBs && BBI->naturalScope->contains(getBBInvar(i + BBsOffset)->naturalScope))
	++i;
      --i;
      continue;

    }

    describeBlockAsDOT(BBI, BB, deferredEdges ? DescribeL : 0, deferredEdges, Out, 0, brief);

  }

}

// If we'll need DOT files for the user interface they are saved as specialisation proceeds.
void IntegrationAttempt::getSavedDotName(bool brief, std::string& Out) {

  raw_string_ostream RSO(Out);
  RSO << ihp_workdir << "/" << SeqNumber;
  if(brief)
    RSO << "-brief";
  RSO << ".dot";

}

// Save a graph representation of this context.
void IntegrationAttempt::saveDOT2(bool brief) {

  std::string filename;
  getSavedDotName(brief, filename);
  std::error_code error;
  raw_fd_ostream RFO(filename.c_str(), error, sys::fs::F_None);

  if(error) {

    errs() << "Failed to open " << filename << ": " << error.message() << "\n";
    return;

  }

  std::string ignored;
  describeAsDOT(RFO, ignored, brief);

}

// Save both brief and full representations of this context for the UI.
void IntegrationAttempt::saveDOT() {

  if(!IHPSaveDOTFiles)
    return;
  
  if(isCommitted())
    return;

  saveDOT2(true);
  saveDOT2(false);

  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it)
    it->second->saveDOT();

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i)
      it->second->Iterations[i]->saveDOT();

  }

  // Also store a description of the context for the GUI to use.
  if(!L)
    pass->shortHeaders[this] = getShortHeader();

}

void IntegrationAttempt::describeAsDOT(raw_ostream& Out, std::string& othername, bool brief) {

  if(isCommitted()) {

    // Use existing DOT.
    getSavedDotName(brief, othername);
    return;

  }

  std::string escapedName;
  raw_string_ostream RSO(escapedName);
  printHeader(RSO);
  Out << "digraph \"Toplevel\" {\n\tlabel = \"" << DOT::EscapeString(RSO.str()) << "\"\n";

  describeScopeAsDOT(L, 0, Out, brief, 0);

  // Finally terminate the block.
  Out << "}\n";

}

std::string IntegrationAttempt::getGraphPath(std::string prefix) {

  std::string Ret;
  raw_string_ostream RSO(Ret);
  RSO << prefix << "/out.dot";
  return RSO.str();

}

void PeelAttempt::describeTreeAsDOT(std::string path) {

  unsigned i = 0;
  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it, ++i) {

    std::string newPath;
    raw_string_ostream RSO(newPath);
    RSO << path << "/iter_" << i;
    mkdir(RSO.str().c_str(), 0777);
    (*it)->describeTreeAsDOT(RSO.str());

  }

}

void IntegrationAttempt::describeTreeAsDOT(std::string path) {

  std::string graphPath = getGraphPath(path);

  std::error_code error;
  raw_fd_ostream os(graphPath.c_str(), error, sys::fs::F_None);

  if(error) {

    errs() << "Failed to open " << graphPath << ": " << error.message() << "\n";
    return;

  }

  std::string ign;
  describeAsDOT(os, ign, false);

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    std::string newPath;
    raw_string_ostream RSO(newPath);
    RSO << path << "/loop_" << getBBInvar(it->first->headerIdx)->BB->getName();
    mkdir(RSO.str().c_str(), 0777);
    it->second->describeTreeAsDOT(RSO.str());

  }

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {

    std::string newPath;
    raw_string_ostream RSO(newPath);
    RSO << path << "/call_";

    if(it->first->getType()->isVoidTy()) {
      // Name the call after a BB plus offset
      Instruction* I = it->first->invar->I;
      BasicBlock::iterator BI(I);
      int j;
      for(j = 0; BI != I->getParent()->begin(); --BI, ++j) { }
      RSO << I->getParent()->getName() << "+" << j;
    }
    else {
      // Use the call's given name (pull it out of the full call printout)
      std::string callDesc;
      raw_string_ostream callRSO(callDesc);
      callRSO << it->first;
      callRSO.flush();
      RSO << callDesc.substr(2, callDesc.find_first_of('=') - 3);
    }

    mkdir(RSO.str().c_str(), 0777);
    it->second->describeTreeAsDOT(RSO.str());

  }

}
