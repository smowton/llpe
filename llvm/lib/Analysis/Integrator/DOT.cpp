// Functions to describe the hierarchy of peel and inline attempts in DOT format for easy review.

#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"

#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include <sys/stat.h>
#include <sys/types.h>

#include <string>

using namespace llvm;

std::string IntegrationAttempt::getValueColour(ShadowValue SV) {

  // How should the instruction be coloured:
  // Bright green: defined here, i.e. it's a loop invariant.
  // Red: killed here or as an invariant (including dead memops)
  // Yellow: Expanded call instruction
  // Pink: Unexpanded call instruction
  // Lime green: Invariant defined above.
  // Dark green: Pointer base known
  // Grey: part of a dead block.

  Value* V = SV.getBareVal();
  Instruction* I = dyn_cast<Instruction>(V);
  InstArgImprovement* IAI = SV.getIAI();

  if(!IAI)
    return "#aaaaaa";

  if(IAI->dieStatus != INSTSTATUS_ALIVE)
    return "red";

  if(CallInst* CI = dyn_cast_or_null<CallInst>(I)) {
    if(inlineChildren.find(CI) != inlineChildren.end())
      return "yellow";
    else
      return "pink";
  }

  if(getConstReplacement(SV))
    return "green";
  else if(ShadowInstruction* SI = SV.getInst()) {

    const Loop* SVScope = SV.getScope();
    if(L && SVScope != L && ((!SVScope) || SVScope->contains(L))) {
      
      ShadowInstruction* SI2 = getInstFalling(SI->parent->invar, SI->invar->idx);

      if(getConstReplacement(SI2))
	return "limegreen";

    }
    
  }
  else if(IAI->PB.Values.size() != 0 && !IAI->PB.Overdef)
      return "darkgreen";
  
  return "white";

}

static std::string TruncStr(std::string str, unsigned maxlen) {

  if(str.size() > maxlen) {

    str.resize(maxlen);
    str.append(" ...");

  }

  return str;

}

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

static std::string escapeHTMLValue(Value* V, IntegrationAttempt* IA, bool brief=false) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  IA->printWithCache(V, RSO, brief);
  return escapeHTML(TruncStr(RSO.str(), 500));

}

void IntegrationAttempt::printRHS(ShadowValue SV, raw_ostream& Out) {
  
  if(SV.isVal())
    return;

  InstArgImprovement* IAI = SV.getIAI();

  const Loop* MyScope = L;
  const Loop* VScope = SV.getScope();
  bool isInvariant = (MyScope != VScope && ((!VScope) || VScope->contains(MyScope)));
  ShadowInstruction* SI = SV.getInst();
  ShadowInstruction* InvarSI;
  
  if(isInvariant) {
    InvarSI = getInst(SI->invar);
    IAI = &(InvarSI->i);
  }  
  else
    InvarSI = SI;

  if(Constant* C = getConstReplacement(SV)) {
    if(isInvariant)
      Out << "(invar) ";
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
  if(IAI->PB.Values.size() > 0 && !IAI->PB.Overdef) {
    printPB(Out, IAI->PB, true);
    PBPrinted = true;
  }

  if(!SI)
    return;

  DenseMap<Instruction*, std::string>::iterator optit = optimisticForwardStatus.find(SI->invar->I);
  DenseMap<Instruction*, std::string>::iterator pesit = pessimisticForwardStatus.find(SI->invar->I);
  if(!PBPrinted) {
    if(optit != optimisticForwardStatus.end()) {
      Out << "OPT (" << optit->second << "), ";
    }
    if(pesit != pessimisticForwardStatus.end()) {
      Out << "PES (" << pesit->second << "), ";
    }
  }
  if(LoadInst* LI = dyn_cast_inst<LoadInst>(SI)) {

    DenseMap<LoadInst*, std::string>::iterator it = normalLFFailures.find(LI);

    if(it != normalLFFailures.end()) {
      Out << "NORM (" <<  it->second << ")";
    }
  }
  else if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {
    DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.find(CI);
    if(it != forwardableOpenCalls.end()) {
      Out << it->second->Name << "(" << (it->second->success ? "success" : "not found") << ")";
    }
    else {
      DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
      if(it != resolvedReadCalls.end())
	Out << it->second.openArg->Name << " (" << it->second.incomingOffset << "-" << it->second.incomingOffset + (it->second.readSize - 1) << ")";
    }
  }

}

bool InlineAttempt::getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) {

  return false;

}

bool PeelIteration::getSpecialEdgeDescription(ShadowBBInvar* FromBB, ShadowBBInvar* ToBB, raw_ostream& Out) {

  if(FromBB->BB == L->getLoopLatch() && ToBB->BB == L->getHeader()) {

    Out << "\"Next iteration header\"";
    return true;

  }
  else if(!L->contains(ToBB->naturalScope)) {

    Out << "\"Exit block " << escapeHTML(ToBB->BB->getName()) << "\"";
    return true;

  }

  return false;

}

void IntegrationAttempt::printOutgoingEdge(ShadowBBInvar* BBI, ShadowBB* BB, ShadowBBInvar* SBI, ShadowBB* SB, uint32_t i, bool useLabels, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief) {

  if(brief && !SB)
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
    rso << "Node" << SB->invar->BB;

  if(edgeIsDead(BBI, SBI)) {
    rso << "[color=gray]";
  }

  rso << ";\n";

  if(deferEdgesOutside && !deferEdgesOutside->contains(SBI->naturalScope)) {
    deferredEdges->push_back(rso.str());
  }
  else {
    Out << rso.str();
  }
	
}

void IntegrationAttempt::describeBlockAsDOT(ShadowBBInvar* BBI, ShadowBB* BB, const Loop* deferEdgesOutside, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<ShadowBB*, 4>* forceSuccessors, bool brief) {

  if(brief && !BB)
    return;

  TerminatorInst* TI = BBI->BB->getTerminator();
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
  
  if(BB && BB->status == BBSTATUS_CERTAIN) {
    Out << " bgcolor=\"yellow\"";
  }
  else if(BB && BB->status == BBSTATUS_ASSUMED) {
    Out << " bgcolor=\"orange\"";
  }

  Out << "><font point-size=\"14\">";
  if(BBI->BB == getEntryBlock())
    Out << "Entry block: ";
  Out << escapeHTML(BBI->BB->getName()) << "</font></td></tr>\n";

  bool isFunctionHeader = (!L) && (BBI->BB == &(F.getEntryBlock()));

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
      Vals.push_back(ShadowValue(BI));
    else
      Vals.push_back(ShadowValue(&(BB->insts[i])));
  }

  for(std::vector<ShadowValue>::iterator VI = Vals.begin(), VE = Vals.end(); VI != VE; ++VI) {

    Out << "<tr><td border=\"0\" align=\"left\" bgcolor=\"" << getValueColour(*VI) << "\">";
    Out << escapeHTMLValue(VI->getBareVal(), this) << "</td><td>";
    std::string RHSStr;
    raw_string_ostream RSO(RHSStr);
    printRHS(*VI, RSO);
    RSO.flush();
    Out << escapeHTML(TruncStr(RSO.str(), 200));
    Out << "</td></tr>\n";

  }

  Out << "</table></td></tr>";

  // Print ports for branch / switch statements, borrowed from the DOT printer.

  if(useLabels) {

    Out << "<tr>\n";
    unsigned i = 0;
    for(succ_const_iterator SI = succ_begin(const_cast<const BasicBlock*>(BB->invar->BB)), SE = succ_end(const_cast<const BasicBlock*>(BB->invar->BB)); SI != SE; ++SI, ++i) {
      Out << "<td port=\"s" << i << "\" border=\"1\">" << DOTGraphTraits<const Function*>::getEdgeSourceLabel(BB->invar->BB, SI) << "</td>\n";
    }
    Out << "</tr>\n";

  }

  Out << "</table>>];\n";

  if(forceSuccessors) {

    for(SmallVector<ShadowBB*, 4>::const_iterator it = forceSuccessors->begin(), it2 = forceSuccessors->end(); it != it2; ++it) {

      printOutgoingEdge(BBI, BB, (*it)->invar, (*it), 0, false, deferEdgesOutside, deferredEdges, Out, brief);

    }

  }
  else {

    // Print the successor edges *except* any loop exit edges, since those must occur in parent context.
    for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

      ShadowBBInvar* SuccBBI = getBBInvar(BBI->succIdxs[i]);
      ShadowBB* SuccBB = getBB(*SuccBBI);

      printOutgoingEdge(BBI, BB, SuccBBI, SuccBB, i, useLabels, deferEdgesOutside, deferredEdges, Out, brief);

    }

  }
 
}

bool IntegrationAttempt::blockLiveInAnyScope(ShadowBBInvar* BB) {

  if(!getBB(*BB))
    return false;

  if(BB->naturalScope != L) {

    const Loop* enterL = immediateChildLoop(L, BB->naturalScope);
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

void IntegrationAttempt::describeLoopAsDOT(const Loop* DescribeL, uint32_t headerIdx, raw_ostream& Out, bool brief) {

  SmallVector<std::string, 4> deferredEdges;

  if(brief && !BBs[headerIdx])
    return;

  ShadowLoopInvar& LInfo = *(invarInfo->LInfo[DescribeL]);

  Out << "subgraph \"cluster_" << DOT::EscapeString(DescribeL->getHeader()->getName()) << "\" {";

  if(brief) {

    // Draw the header branching to all exiting blocks, to each exit block.
    std::vector<uint32_t>& exitingIdxs = LInfo.exitingBlocks;

    SmallVector<ShadowBB*, 4> liveExitingBlocks;

    for(unsigned i = 0; i < exitingIdxs.size(); ++i) {

      ShadowBBInvar* BBI = getBBInvar(exitingIdxs[i]);
      if(blockLiveInAnyScope(BBI)) {

	liveExitingBlocks.push_back(getBB(*BBI));

      }

    }

    describeBlockAsDOT(getBBInvar(headerIdx + BBsOffset), getBB(headerIdx + BBsOffset), 0, 0, Out, &liveExitingBlocks, brief);

    std::vector<std::pair<uint32_t, uint32_t> >& exitEdges = LInfo.exitEdges;

    for(SmallVector<ShadowBB*, 4>::iterator it = liveExitingBlocks.begin(), it2 = liveExitingBlocks.end(); it != it2; ++it) {
      
      ShadowBB* BB = *it;
      SmallVector<ShadowBB*, 4> Targets;

      for(std::vector<std::pair<uint32_t, uint32_t> >::iterator it3 = exitEdges.begin(), it4 = exitEdges.end(); it3 != it4; ++it3) {

	ShadowBB* TargetBB;
	if(it3->first == BB->invar->idx && (TargetBB = getBB(it3->second))) {

	  Targets.push_back(TargetBB);

	}

      }

      describeBlockAsDOT(BB->invar, BB, DescribeL, &deferredEdges, Out, &Targets, brief);      

    }

  }
  else {

    ShadowBBInvar* BBInvar;
    uint32_t idx;

    for(idx = headerIdx, BBInvar = getBBInvar(headerIdx); DescribeL->contains(BBInvar->naturalScope); ++idx, BBInvar = getBBInvar(idx)) {

      ShadowBB* BB = getBB(*BBInvar);
      describeBlockAsDOT(BBInvar, BB, DescribeL, &deferredEdges, Out, 0, brief);

    }

  }
						     
  Out << "label = \"Loop " << DOT::EscapeString(DescribeL->getHeader()->getName()) << " (";

  DenseMap<const Loop*, PeelAttempt*>::iterator InlIt = peelChildren.find(DescribeL);
  if(InlIt == peelChildren.end()) {

    Out << "Not explored";

  }
  else {

    PeelIteration* LastIter = InlIt->second->Iterations.back();
    if(LastIter->iterStatus == IterationStatusFinal) {
      Out << "Terminated";
    }
    else {
      Out << "Not terminated";
    }

    Out << ", " << InlIt->second->Iterations.size() << " iterations";

  }

  Out << ")\";\n}\n";

  for(SmallVector<std::string, 4>::iterator it = deferredEdges.begin(), it2 = deferredEdges.end(); it != it2; ++it) {

    Out << *it;

  }

}

void IntegrationAttempt::describeAsDOT(raw_ostream& Out, bool brief) {

  std::string escapedName;
  raw_string_ostream RSO(escapedName);
  printHeader(RSO);
  Out << "digraph \"Toplevel\" {\n\tlabel = \"" << DOT::EscapeString(RSO.str()) << "\"\n";

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i + BBsOffset);
    ShadowBB* BB = BBs[i];
    
    if(BBI->naturalScope != L) {

      const Loop* enterL = immediateChildLoop(L, BBI->naturalScope);
      if(!pass->shouldIgnoreLoop(enterL->getHeader()->getParent(), enterL->getHeader())) {

	describeLoopAsDOT(enterL, i, Out, brief);
	
	// Advance past the loop:
	while(i < nBBs && enterL->contains(getBBInvar(i + BBsOffset)->naturalScope))
	  ++i;
	--i;
	continue;

      }

      // Else fall through:

    }

    describeBlockAsDOT(BBI, BB, 0, 0, Out, 0, brief);

  }

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

  std::string error;
  raw_fd_ostream os(graphPath.c_str(), error);

  if(!error.empty()) {

    errs() << "Failed to open " << graphPath << ": " << error << "\n";
    return;

  }

  describeAsDOT(os, false);

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    std::string newPath;
    raw_string_ostream RSO(newPath);
    RSO << path << "/loop_" << it->first->getHeader()->getName();
    mkdir(RSO.str().c_str(), 0777);
    it->second->describeTreeAsDOT(RSO.str());

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    std::string newPath;
    raw_string_ostream RSO(newPath);
    RSO << path << "/call_";

    if(it->first->getType()->isVoidTy()) {
      // Name the call after a BB plus offset
      BasicBlock::iterator BI(it->first);
      int j;
      for(j = 0; BI != it->first->getParent()->begin(); --BI, ++j) { }
      RSO << it->first->getParent()->getName() << "+" << j;
    }
    else {
      // Use the call's given name (pull it out of the full call printout)
      std::string callDesc;
      raw_string_ostream callRSO(callDesc);
      callRSO << *(it->first);
      callRSO.flush();
      RSO << callDesc.substr(2, callDesc.find_first_of('=') - 3);
    }

    mkdir(RSO.str().c_str(), 0777);
    it->second->describeTreeAsDOT(RSO.str());

  }

}
