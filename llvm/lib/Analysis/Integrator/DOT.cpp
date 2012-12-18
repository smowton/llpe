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

class CheckDeadCallback : public Callable {

  Value* V;

public:

  bool isDead;
  
  CheckDeadCallback(Value* _V) : V(_V) { }

  virtual void callback(IntegrationAttempt* Ctx) {

    isDead = Ctx->inDeadValues(V);

  }

};

std::string IntegrationAttempt::getValueColour(Value* V) {

  // How should the instruction be coloured:
  // Bright green: defined here, i.e. it's a loop invariant.
  // Red: killed here or as an invariant (including dead memops)
  // Yellow: Expanded call instruction
  // Pink: Unexpanded call instruction
  // Lime green: Invariant defined above.
  // Dark green: Pointer base known
  // Grey: part of a dead block.

  Instruction* I = dyn_cast<Instruction>(V);

  if(I && blockIsDead(I->getParent()))
    return "#aaaaaa";

  if(I && (deadValues.count(I) || unusedWriters.count(I)))
    return "red";

  if(CallInst* CI = dyn_cast_or_null<CallInst>(I)) {
    if(inlineChildren.find(CI) != inlineChildren.end())
      return "yellow";
    else
      return "pink";
  }

  const Loop* MyScope = getLoopContext();
  const Loop* VScope = getValueScope(V);
  PointerBase PB;

  if(VScope == MyScope) {

    // Defined or killed here:
    if(getReplacement(V) != getDefaultVC(V))
      return "green";

  }
  else if((!VScope) || VScope->contains(MyScope)) {

    if(getReplacement(V) != getDefaultVC(V))
      return "limegreen";
    
    if(I) {
      CheckDeadCallback CDC(I);
      callWithScope(CDC, VScope);
      if(CDC.isDead)
	return "red";
    }

  }
  
  if(getPointerBaseFalling(V, PB)) {

    if(!PB.Overdef)
      return "darkgreen";
    
  }

  if((MyScope != VScope) && ((!MyScope) || MyScope->contains(VScope))) {
    
    // Instruction is a loop variant here.
    return "cyan";

  }

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

// Now unused
/*
static std::string escapeHTMLValue(ValCtx V, IntegrationAttempt* IA, bool brief=false) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  IA->printWithCache(V, RSO, brief);
  return escapeHTML(TruncStr(RSO.str(), 500));

}

static std::string escapeHTMLValue(MemDepResult MDR, IntegrationAttempt* IA, bool brief=false) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  IA->printWithCache(MDR, RSO, brief);
  return escapeHTML(TruncStr(RSO.str(), 500));

}
*/

void IntegrationAttempt::printRHS(Value* V, raw_ostream& Out) {
  
  Instruction* I = dyn_cast<Instruction>(V);

  if(I && blockIsDead(I->getParent()))
    return;

  const Loop* MyScope = getLoopContext();
  const Loop* VScope = getValueScope(V);
  bool isInvariant = (MyScope != VScope && ((!VScope) || VScope->contains(MyScope)));
  PointerBase PB;

  ValCtx Repl = getReplacement(V);  
  if(getDefaultVC(V) != Repl) {
    if(isInvariant)
      Out << "(invar) ";
    if(isa<Function>(Repl.first))
      Out << "@" << Repl.first->getName();
    else
      Out << itcache(Repl, true);
    if(Repl.isVaArg())
      Out << " vararg #" << Repl.va_arg;
    return;
  }
  if(isInvariant && I) {
    CheckDeadCallback CDC(I);
    callWithScope(CDC, VScope);
    if(CDC.isDead)
      Out << "(invar) DEAD";
    return;
  }
  if(I && deadValues.count(I)) {
    Out << "DEAD";
    return;
  }
  bool PBPrinted = false;
  if(getPointerBaseFalling(V, PB) && !PB.Overdef) {
    printPB(Out, PB, true);
    PBPrinted = true;
  }
  DenseMap<Instruction*, std::string>::iterator optit = optimisticForwardStatus.find(I);
  DenseMap<Instruction*, std::string>::iterator pesit = pessimisticForwardStatus.find(I);
  if(!PBPrinted) {
    if(optit != optimisticForwardStatus.end()) {
      Out << "OPT (" << optit->second << "), ";
    }
    if(pesit != pessimisticForwardStatus.end()) {
      Out << "PES (" << pesit->second << "), ";
    }
  }
  if(LoadInst* LI = dyn_cast_or_null<LoadInst>(I)) {

    DenseMap<LoadInst*, MemDepResult>::iterator it = LastLoadFailures.find(LI);

    if(it != LastLoadFailures.end()) {
      Out << "NORM (";
      bool printed = false;
      if(it->second == MemDepResult()) {
	DenseMap<LoadInst*, SmallVector<NonLocalDepResult, 4> >::iterator it2 = LastLoadOverdefs.find(LI);
	if(it2 != LastLoadOverdefs.end()) {
	  Out << "{{ ";
	  int i = 0;
	  for(SmallVector<NonLocalDepResult, 4>::iterator NLI = it2->second.begin(), NLE = it2->second.end(); NLI != NLE && i < 3; ++i, ++NLI) {
	    Out << itcache(NLI->getResult(), true) << ", ";
	  }
	  Out << " }}";
	  printed = true;
	}
      }
      if(!printed)
	Out << itcache(it->second, true);
      Out << ")";
    }
  }
  else if(CallInst* CI = dyn_cast_or_null<CallInst>(I)) {
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

bool InlineAttempt::getSpecialEdgeDescription(BasicBlock* FromBB, BasicBlock* ToBB, raw_ostream& Out) {

  return false;

}

bool PeelIteration::getSpecialEdgeDescription(BasicBlock* FromBB, BasicBlock* ToBB, raw_ostream& Out) {

  if(FromBB == L->getLoopLatch() && ToBB == L->getHeader()) {

    Out << "\"Next iteration header\"";
    return true;

  }
  else if(std::find(parentPA->ExitEdges.begin(), parentPA->ExitEdges.end(), std::make_pair(FromBB, ToBB)) != parentPA->ExitEdges.end()) {

    Out << "\"Exit block " << escapeHTML(ToBB->getName()) << "\"";
    return true;

  }

  return false;

}

void IntegrationAttempt::printOutgoingEdge(BasicBlock* BB, BasicBlock* SB, unsigned i, bool useLabels, SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>* deferEdges, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, bool brief) {

  if(brief && blockIsDead(SB))
    return;

  const Loop* MyLoop = getLoopContext();

  std::string edgeString;
  raw_string_ostream rso(edgeString);

  rso << "Node" << BB;
  if(useLabels) {
    rso << ":s" << i;
  }

  rso << " -> ";

  // Handle exits from this loop / this loop's latch specially:
  if(!getSpecialEdgeDescription(BB, SB, rso))
    rso << "Node" << SB;

  const Loop* edgeLoop = getEdgeScope(BB, SB);

  if(((!edgeLoop) || edgeLoop->contains(MyLoop)) && edgeIsDead(BB, SB)) {
    rso << "[color=gray]";
  }

  rso << ";\n";

  if(deferEdges && std::find(deferEdges->begin(), deferEdges->end(), std::make_pair(BB, const_cast<BasicBlock*>(SB))) != deferEdges->end()) {
    deferredEdges->push_back(rso.str());
  }
  else {
    Out << rso.str();
  }
	
}

void IntegrationAttempt::describeBlockAsDOT(BasicBlock* BB, SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>* deferEdges, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out, SmallVector<BasicBlock*, 4>* forceSuccessors, bool brief) {

  if(brief && blockIsDead(BB))
    return;

  TerminatorInst* TI = BB->getTerminator();
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

  Out << "Node" << BB << " [shape=plaintext,fontsize=10,label=<<table cellspacing=\"0\" border=\"0\"><tr><td colspan=\"" << numSuccessors << "\" border=\"1\"><table border=\"0\">\n";

  Out << "<tr><td border=\"0\" align=\"left\" colspan=\"2\"";
  
  if(blockIsCertain(BB)) {
    Out << " bgcolor=\"yellow\"";
  }

  Out << "><font point-size=\"14\">";
  if(BB == getEntryBlock())
    Out << "Entry block: ";
  Out << escapeHTML(BB->getName()) << "</font></td></tr>\n";

  bool isFunctionHeader = (!getLoopContext()) && (BB == &(F.getEntryBlock()));

  size_t ValSize = BB->size();
  if(isFunctionHeader)
    ValSize += F.arg_size();

  std::vector<Value*> Vals;
  Vals.reserve(ValSize);

  if(isFunctionHeader) {
    for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI)
      Vals.push_back(AI);
  }
  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI)
    Vals.push_back(BI);

  for(std::vector<Value*>::iterator VI = Vals.begin(), VE = Vals.end(); VI != VE; ++VI) {

    Value* V = *VI;
    Out << "<tr><td border=\"0\" align=\"left\" bgcolor=\"" << getValueColour(V) << "\">";
    Out << escapeHTMLValue(V, this) << "</td><td>";
    std::string RHSStr;
    raw_string_ostream RSO(RHSStr);
    printRHS(V, RSO);
    RSO.flush();
    Out << escapeHTML(TruncStr(RSO.str(), 200));
    Out << "</td></tr>\n";

  }

  Out << "</table></td></tr>";

  // Print ports for branch / switch statements, borrowed from the DOT printer.

  if(useLabels) {

    Out << "<tr>\n";
    unsigned i = 0;
    for(succ_const_iterator SI = succ_begin((const BasicBlock*)BB), SE = succ_end((const BasicBlock*)BB); SI != SE; ++SI, ++i) {
      Out << "<td port=\"s" << i << "\" border=\"1\">" << DOTGraphTraits<const Function*>::getEdgeSourceLabel(BB, SI) << "</td>\n";
    }
    Out << "</tr>\n";

  }

  Out << "</table>>];";

  if(forceSuccessors) {

    for(SmallVector<BasicBlock*, 4>::const_iterator it = forceSuccessors->begin(), it2 = forceSuccessors->end(); it != it2; ++it) {

      printOutgoingEdge(BB, *it, 0, false, deferEdges, deferredEdges, Out, brief);

    }

  }
  else {

    // Print the successor edges *except* any loop exit edges, since those must occur in parent context.
    unsigned i = 0;
    for(succ_const_iterator SI = succ_begin((const BasicBlock*)BB), SE = succ_end((const BasicBlock*)BB); SI != SE; ++SI, ++i) {

      printOutgoingEdge(BB, const_cast<BasicBlock*>(*SI), i, useLabels, deferEdges, deferredEdges, Out, brief);

    }

  }
 
}

void IntegrationAttempt::describeLoopAsDOT(const Loop* L, raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted) {

  SmallVector<std::string, 4> deferredEdges;

  if(brief && blockIsDead(L->getHeader()))
    return;

  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> ExitEdges;
  L->getExitEdges(ExitEdges);

  Out << "subgraph \"cluster_" << DOT::EscapeString(L->getHeader()->getName()) << "\" {";

  if(brief) {

    // Draw the header branching to all exiting blocks, to each exit block.
    SmallVector<BasicBlock*, 4> Targets;
    L->getExitingBlocks(Targets);

    describeBlockAsDOT(L->getHeader(), 0, 0, Out, &Targets, brief);

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::const_iterator EI = ExitEdges.begin(), EE = ExitEdges.end(); EI != EE; ++EI) {

      if(blocksPrinted.count(EI->first))
	continue;
      Targets.clear();
      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::const_iterator EI2 = ExitEdges.begin(), EE2 = ExitEdges.end(); EI2 != EE2; ++EI2) {

	if(EI2->first == EI->first)
	  Targets.push_back(EI2->second);

      }
      describeBlockAsDOT(EI->first, &ExitEdges, &deferredEdges, Out, &Targets, brief);
      blocksPrinted.insert(EI->first);

    }

    for(Loop::block_iterator BI = L->block_begin(), BE = L->block_end(); BI != BE; ++BI) {

      BasicBlock* BB = *BI;
      blocksPrinted.insert(BB);

    }

  }
  else {

    for(Loop::block_iterator BI = L->block_begin(), BE = L->block_end(); BI != BE; ++BI) {

      BasicBlock* BB = *BI;
      blocksPrinted.insert(BB);
      describeBlockAsDOT(BB, &ExitEdges, &deferredEdges, Out, 0, brief);

    }

  }
						     
  Out << "label = \"Loop " << DOT::EscapeString(L->getHeader()->getName()) << " (";

  DenseMap<const Loop*, PeelAttempt*>::iterator InlIt = peelChildren.find(L);
  if(InlIt == peelChildren.end()) {

    Out << "Not explored";

  }
  else {

    int numIters = InlIt->second->Iterations.size();
    PeelIteration* LastIter = InlIt->second->Iterations[numIters-1];
    if(LastIter->iterStatus == IterationStatusFinal) {
      Out << "Terminated";
    }
    else {
      Out << "Not terminated";
    }

    Out << ", " << numIters << " iterations";

  }

  Out << ")\";\n}\n";

  for(SmallVector<std::string, 4>::iterator it = deferredEdges.begin(), it2 = deferredEdges.end(); it != it2; ++it) {

    Out << *it;

  }

}

void InlineAttempt::describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted) {

  for(LoopInfo::iterator it = LI[&F]->begin(), it2 = LI[&F]->end(); it != it2; ++it) {

    if(pass->shouldIgnoreLoop(&F, (*it)->getHeader()))
      continue;

    describeLoopAsDOT(*it, Out, brief, blocksPrinted);

  }

}

void PeelIteration::describeLoopsAsDOT(raw_ostream& Out, bool brief, SmallSet<BasicBlock*, 32>& blocksPrinted) {

  for(Loop::iterator it = L->begin(), it2 = L->end(); it != it2; ++it) {

    if(pass->shouldIgnoreLoop(&F, (*it)->getHeader()))
      continue;

    describeLoopAsDOT(*it, Out, brief, blocksPrinted);

  }

}

void IntegrationAttempt::describeAsDOT(raw_ostream& Out, bool brief) {

  std::string escapedName;
  raw_string_ostream RSO(escapedName);
  printHeader(RSO);
  Out << "digraph \"Toplevel\" {\n\tlabel = \"" << DOT::EscapeString(RSO.str()) << "\"\n";

  // First draw all child loops which can be expanded as a sub-cluster.
  SmallSet<BasicBlock*, 32> blocksPrinted;
  
  describeLoopsAsDOT(Out, brief, blocksPrinted);

  // Now print the blocks that belong within our loop but not any child.

  const Loop* myLoop = getLoopContext();

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    bool isMine = (!myLoop) || myLoop->contains(FI);
    if(isMine && !blocksPrinted.count(FI)) {

      describeBlockAsDOT(FI, 0, 0, Out, 0, brief);

    }

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
