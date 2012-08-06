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

std::string IntegrationAttempt::getInstructionColour(Instruction* I) {

  // How should the instruction be coloured:
  // Bright green: defined here, i.e. it's a loop invariant.
  // Red: killed here.
  // Yellow: Call instruction (defined or otherwise)
  // Lime green: Invariant defined above.
  // Grey: part of a dead block.

  if(blockIsDead(I->getParent()))
    return "#aaaaaa";

  if(isa<CallInst>(I))
    return "yellow";

  const Loop* MyScope = getLoopContext();
  const Loop* IScope = getValueScope(I);

  if(IScope == MyScope) {

    // Defined or killed here:
    if(!isUnresolved(I))
      return "green";
    if(deadValues.count(I))
      return "red";

  }
  else if((!IScope) || IScope->contains(MyScope)) {

    if(!isUnresolved(I))
      return "limegreen";

  }

  return "white";

}

static std::string escapeHTML(std::string Str) {

  for (unsigned i = 0; i != Str.length(); ++i) {
    switch (Str[i]) {
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

static std::string escapeHTMLValue(Value* V) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  RSO << *V;
  return escapeHTML(RSO.str());

}

static std::string escapeHTMLValue(ValCtx V) {

  std::string Esc;
  raw_string_ostream RSO(Esc);
  RSO << V;
  return escapeHTML(RSO.str());

}

void IntegrationAttempt::printRHS(Instruction* I, raw_ostream& Out) {
  
  if(blockIsDead(I->getParent()))
    return;
  
  if(!isUnresolved(I))
    Out << escapeHTMLValue(getReplacement(I));
  else if(deadValues.count(I))
    Out << "DEAD";

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

void IntegrationAttempt::describeBlockAsDOT(BasicBlock* BB, SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>* deferEdges, SmallVector<std::string, 4>* deferredEdges, raw_ostream& Out) {

  const Loop* MyLoop = getLoopContext();

  TerminatorInst* TI = BB->getTerminator();
  bool useLabels = false;
  if(BranchInst* BI = dyn_cast<BranchInst>(TI))
    useLabels = BI->isConditional();
  else if(isa<SwitchInst>(TI))
    useLabels = true;
  unsigned numSuccessors = 1;
  if(useLabels)
    numSuccessors = TI->getNumSuccessors();

  Out << "Node" << BB << " [shape=plaintext,label=<<table cellspacing=\"0\" border=\"0\"><tr><td colspan=\"" << numSuccessors << "\" border=\"1\"><table border=\"0\">\n";

  Out << "<tr><td border=\"0\" align=\"left\" colspan=\"2\"";
  
  if(blockIsCertain(BB)) {
    Out << " bgcolor=\"yellow\"";
  }

  Out << "><font point-size=\"18\">";
  if(BB == getEntryBlock())
    Out << "Entry block: ";
  Out << escapeHTML(BB->getName()) << "</font></td></tr>\n";

  for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {

    Out << "<tr><td border=\"0\" align=\"left\" bgcolor=\"" << getInstructionColour(II) << "\">";
    Out << escapeHTMLValue(II) << "</td><td>";
    printRHS(II, Out);
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

  // Print the successor edges *except* any loop exit edges, since those must occur in parent context.
  unsigned i = 0;
  for(succ_const_iterator SI = succ_begin((const BasicBlock*)BB), SE = succ_end((const BasicBlock*)BB); SI != SE; ++SI, ++i) {

    std::string edgeString;
    raw_string_ostream rso(edgeString);

    BasicBlock* SB = const_cast<BasicBlock*>(*SI);
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
 
}

void IntegrationAttempt::describeAsDOT(raw_ostream& Out) {

  std::string escapedName;
  raw_string_ostream RSO(escapedName);
  printHeader(RSO);
  Out << "digraph \"Toplevel\" {\n\tlabel = \"" << DOT::EscapeString(RSO.str()) << "\"\n";

  // First draw all child loops which can be expanded as a sub-cluster.
  SmallSet<BasicBlock*, 32> blocksPrinted;

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    SmallVector<std::string, 4> deferredEdges;

    Out << "subgraph \"cluster_" << DOT::EscapeString(it->first->getHeader()->getName()) << "\" {";

    for(Loop::block_iterator BI = it->first->block_begin(), BE = it->first->block_end(); BI != BE; ++BI) {

      BasicBlock* BB = *BI;
      blocksPrinted.insert(BB);
      describeBlockAsDOT(BB, &it->second->ExitEdges, &deferredEdges, Out);

    }
						     
    Out << "label = \"Loop " << DOT::EscapeString(it->first->getHeader()->getName()) << "\";\n}\n";

    for(SmallVector<std::string, 4>::iterator it = deferredEdges.begin(), it2 = deferredEdges.end(); it != it2; ++it) {

      Out << *it;

    }
						      
  }

  // Now print the blocks that belong within our loop but not any child.

  const Loop* myLoop = getLoopContext();

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    bool isMine = (!myLoop) || myLoop->contains(FI);
    if(isMine && !blocksPrinted.count(FI)) {

      describeBlockAsDOT(FI, 0, 0, Out);

    }

  }
  
  // Finally terminate the block.
  Out << "}\n";

}

std::string InlineAttempt::getGraphPath(std::string prefix) {

  std::string Ret;
  raw_string_ostream RSO(Ret);
  RSO << prefix << "/out.dot";
  return RSO.str();

}

std::string PeelIteration::getGraphPath(std::string prefix) {

  std::string Ret;
  raw_string_ostream RSO(Ret);
  RSO << prefix << "/" << iterationCount << ".dot";
  return RSO.str();

}

void PeelAttempt::describeTreeAsDOT(std::string path) {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->describeTreeAsDOT(path);

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

  describeAsDOT(os);

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
    RSO << path << "/call_" << it->first->getName();
    mkdir(RSO.str().c_str(), 0666);
    it->second->describeTreeAsDOT(RSO.str());

  }

}
