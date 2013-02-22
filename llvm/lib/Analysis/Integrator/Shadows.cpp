// Implement guts of instruction and block shadow structures, as well as utility routines for generating them
// from a function or block.

void IntegrationAttempt::createTopOrderingFrom(BasicBlock* BB, std::vector<BasicBlock*>& Result, SmallSet<BasicBlock*, 8>& Visited, const Loop* MyL, bool enterLoops) {

  if(!Visited.insert(BB))
    return;

  const Loop* BBL = LI[&F]->getLoopFor(BB);
  
  // Drifted out of scope?
  if(MyL != BBL && ((!BBL) || (BBL->contains(MyL))))
    return;

  if(enterLoops && (MyL != BBL)) {

    // Child loop. Use the loop successors rather than the block successors.
    SmallVector<BasicBlock*, 4> ExitBlocks;
    BBL->getExitBlocks(ExitBlocks);
    for(SmallVector<BasicBlock*, 4>::iterator it = ExitBlocks.begin(), it2 = ExitBlocks.end(); it != it2; ++it) {
      
      createTopOrderingFrom(*it, Result, Visited, MyL, enterLoops);
      
    }

  }
  else {

    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {

      createTopOrderingFrom(*SI, Result, Visited, MyL, enterLoops);

    }

  }

  Result.push_back(BB);

}

static void getLoopInfo(DenseMap<const Loop*, uint32_t>& LoopHeaderIndices, DenseMap<const Loop*, uint32_t>& LoopPreheaderIndices, DenseMap<const Loop*, uint32_t>& LoopLatchIndices, DenseMap<const Loop*, std::vector<uint32_t> >& LoopExitingBlocks, std::vector<uint32_t> >& LoopExitBlocks, std::vector<std::pair<uint32_t, uint32_t> >& LoopExitEdges, DenseMap<BasicBlock*, uint32_t>& BBIndices, const Loop* L) {
  
  LoopHeaderIndices[L] = BBIndices[L->getHeader()];
  LoopPreheaderIndices[L] = BBIndices[L->getLoopPreheader()];
  LoopLatchIndices[L] = BBIndices[L->getLoopLatch()];

  {
    SmallVector<BasicBlock*, 4> temp;
    L->getExitingBlocks(temp);
    {
      std::vector<uint32_t>* idxs = LoopExitingBlocks[L] = new std::vector<uint32_t>();
      for(unsigned i = 0; i < temp.size(); ++i)
	idxs->push_back(BBIndices[temp[i]]);
    }

    temp.clear();
    L->getExitBlocks(temp);
    {
      std::vector<uint32_t>* idxs = LoopExitBlocks[L] = new std::vector<uint32_t>();
      for(unsigned i = 0; i < temp.size(); ++i)
	idxs->push_back(BBIndices[temp[i]]);
    }
  }

  {
    SmallVector<std::pair<BasicBlock*, BasicBlock>, 4> exitEdges;
    L->getExitEdges(exitEdges);
    std::vector<std::pair<uint32_t, uint32_t> >* idxs = LoopExitEdges[L] = new std::vector<std::pair<uint32_t, uint32_t> >();
    for(unsigned i = 0; i < exitEdges.size(); ++i)
      idxs->push_back(std::make_pair(BBIndices[exitEdges[i].first], BBIndices[exitEdges[i].second]));
  }

  for(Loop::iterator it = L->begin(), itend = L->end(); it != itend; ++it) {

    getLoopInfo(LoopHeaderIndices, LoopPreheaderIndices, LoopLatchIndices, LoopExitingBlocks, LoopExitBlocks, LoopExitEdges, BBIndices, *it);

  }

}

ShadowFunctionInvar& IntegrationHeuristicsPass::getFunctionInvarInfo(const Function& F) {

  DenseMap<Function*, ShadowFunctionInvar>::iterator findit = functionInfo.find(&F);
  if(findit != functionIndices.end())
    return findit->second;

  LoopInfo* LI = LIs[&F];

  ShadowFunctionInvar& RetInfo = functionInfo[&F];

  std::vector<BasicBlock*> TopOrderedBlocks;
  SmallSet<BasicBlock*, 8> VisitedBlocks;

  createTopOrderingFrom(F.getEntryBlock(), TopOrderedBlocks, VisitedBlocks, /* loop = */ 0, /* enterLoops = */ false);

  std::reverse(TopOrderedBlocks.begin(), TopOrderedBlocks.end());

  // Assign indices to each BB and instruction (IIndices is useful since otherwise we have to walk
  // the instruction list to get from an instruction to its index)

  DenseMap<BasicBlock*, uint32_t> BBIndices;
  DenseMap<Instruction*, uint32_t> IIndices;

  for(uint32_t i = 0; i < TopOrderedBlocks.size(); ++i) {

    BasicBlock* BB = TopOrderedBlocks[i];

    BBIndices[BB] = i;
    
    uint32_t j;
    BasicBlock::iterator it, endit;
    for(j = 0, it = BB->begin(), endit = BB->end(); it != endit; ++it, ++j) {

      IIndices[it] = j;

    }

  }

  ShadowBBInvar* FShadowBlocks = new ShadowBBInvar[TopOrderedBlocks.size()];

  for(uint32_t i = 0; i < TopOrderedBlocks.size(); ++i) {

    BasicBlock* BB = TopOrderedBlocks[i];
    ShadowBBInvar& SBB = FShadowBlocks[i];
    RetInfo.BBMap[BB] = &SBB;
    
    SBB.F = &RetInfo;
    SBB.idx = i;
    SBB.BB = BB;
    SBB.outerScope = getBlockScope(BB);
    SBB.scope = getBlockScopeVariant(BB);
    SBB.naturalScope = LI->getLoopFor(BB);

    // Find successor block indices:

    succ_iterator SI = succ_begin(BB), SE = succ_end(BB);
    SBB.succIdx = new uint32_t[std::distance(SI, SE)];

    for(uint32_t j = 0; SI != SE; ++SI, ++j) {

      SBB.succIdx[j] = BBIndices[*SI];

    }

    // Find predecessor block indices:

    pred_iterator PI = pred_begin(BB), PE = pred_end(BB);
    SBB.predIdx = new uint32_t[std::distance(PI, PE)];
    
    for(uint32_t j = 0; PI != PE; ++PI, ++j) {

      SBB.predIdx[j] = BBIndices[*PI];

    }

    // Find instruction def/use indices:
    ShadowInstructionInvar* insts = new ShadowInstructionInvar[BB->size()];

    BasicBlock::iterator BI = BB->begin(), BE = BB->end();
    for(uint32_t j = 0; BI != BE; ++BI, ++j) {

      Instruction* I = BI;
      ShadowInstructionInvar& SI = insts[j];

      SI.idx = j;
      SI.parent = &SBB;
      SI.I = I;
      SI.scope = getInstructionScope(I);
      
      // Get operands indices:
      ShadowInstIdx* operandIdxs = new ShadowInstIdx[I->getNumOperands()];

      for(unsigned k = 0, kend = I->getNumOperands(); k != kend; ++k) {

	if(Instruction* OpI = dyn_cast<Instruction>(I->getOperand(k))) {

	  operandIdxs[k] = ShadowInstIdx(BBIndices[OpI->getParent()], IIndices[OpI]);

	}
	else {
	  
	  operandIdxs[k] = ShadowInstIdx();

	}

      }

      SI.operandIdxs = ImmutableArray<ShadowInstIdx>(operandIdxs, I->getNumOperands());

      // Get user indices:
      unsigned nUsers = std::distance(I->use_begin(), I->use_end());

      ShadowInstIdx* userIdxs = new ShadowInstIdx[nUsers];

      Instruction::use_iterator UI;
      unsigned k;
      for(k = 0, UI = I->use_begin(); k != nUsers; ++k, ++UI) {

	if(Instruction* UserI = dyn_cast<Instruction>(*UI)) {

	  userIdxs[k] = ShadowInstIdx(BBIndices[UserI->getParent()], IIndices[UserI]);

	}
	else {

	  userIdxs[k] = ShadowInstIdx();
	  
	}

      }

      SI.userIdxs = ImmutableArray<ShadowInstIdx>(userIdxs, nUsers);

    }

    SBB.insts = ImmutableArray<ShadowInstructionInvar>(insts, BB->size());

  }

  RetInfo.BBs = ImmutableArray<ShadowBBInvar>(FShadowBlocks, TopOrderedBlocks.size());

  // Get user info for arguments:

  ShadowArgInvar* Args = new ShadowArgInvar[F.arg_size()];

  Function::arg_iterator AI = F.arg_begin();
  uint32_t i = 0;
  for(; i != F.arg_size(); ++i, ++AI) {

    Argument* A = AI;
    ShadowArgInvar& SArg = Args[i];
    uint32_t nUsers = std::distance(UI, UE);
    ShadowInstIdx* Users = new ShadowInstIdx[nUsers];
      
    unsigned j = 0;
    Argument::use_iterator UI = A->use_begin, UE = A->use_end();
    for(; UI != UE; ++UI, ++j) {

      Value* UsedV = *UI;
      if(Instruction* UsedI = dyn_cast<Instruction>(UsedV)) {

	Users[j] = ShadowInstIdx(BBIndices[UsedI->getParent()], IIndices[UsedI]);

      }
      else {

	Users[j] = ShadowInstIdx();

      }

    }

    SArg.userIdxs = ImmutableArray<ShadowInstIdx>(Users, F.arg_size());

  }

  // Populate map from loop headers to header index. Due to the topological sort,
  // all loops consist of that block + L->getBlocks().size() further, contiguous blocks,
  // making is-in-loop easy to compute.

  for(LoopInfo::iterator it = LI->begin(), it2 = LI->end(); it != it2; ++it)
    getLoopInfo(RetInfo.LoopHeaderIndices, RetInfo.LoopPreheaderIndices, RetInfo.LoopLatchIndices, BBIndices, *it);

  return RetInfo;

}

// Prepare the context-specific data structures, tying them to known invariant information.
// For an inline attempt, create a BB array 

void InlineAttempt::prepareShadows() {

  invarInfo = pass->getFunctionInvarInfo(F);
  nBBs = F.size();
  BBs = new ShadowBB[nBBs];
  for(uint32_t i = 0; i < nBBs; ++i)
    BBs[i] = 0;
  BBsOffset = 0;

  argShadows = new ShadowArg[F.arg_size()];
  uint32_t i = 0;
  Function::arg_iterator it = F.arg_begin();
  for(; i != F.arg_size(); ++i, ++it) {

    argShadows[i].invar = invarInfo->Args[i];

  }

}

void PeelAttempt::getShadowInfo() {

  headerIdx = invarInfo->LoopHeaderIndices[L];
  preheaderIdx = invarInfo->LoopPreheaderIndices[L];
  latchIdx = invarInfo->LoopLatchIndices[L];
  exitBlockIdxs = invarInfo->LoopExitBlocks[L];
  exitingBlockIdxs = invarInfo->LoopExitingBlocks[L];
  exitEdgeIdxs = invarInfo->LoopExitEdges[L];

}

void PeelIteration::prepareShadows() {

  invarInfo = pass->getFunctionInvarInfo(F);
  nBBs = L->getBlocks().size();
  BBsOffset = new ShadowBB[nBBs];
  for(uint32_t i = 0; i < nBBs; ++i)
    BBs[i] = 0;
  BBsOffset = parentPA->headerIdx;

}

ShadowBB* IntegrationAttempt::getBB(ShadowBBInvar& BBI, bool* inScope) {

  return getBB(BBI.idx, inScope);
  
}

ShadowBB* IntegrationAttempt::getBB(uint32_t idx, bool* inScope) {

  if(!(idx >= BBsOffset && idx < (BBsOffset + nBBs))) {
    inScope = false;
    return 0;
  }
  else {
    inScope = true;
    return BBs[idx - BBsOffset];
  }

}

ShadowBBInvar* IntegrationAttempt::getBBInvar(uint32_t idx) {

  return invarInfo->BBs[idx];

}

void IntegrationAttempt::createBB(uint32_t blockIdx) {

  release_assert((!BBs[blockIdx]) && "Creating block for the second time");
  ShadowBB* newBB = new ShadowBB();
  newBB->invar = invarInfo->BBs[blockIdx];
  newBB->succsAlive = new bool[newBB->invar->predIdxs.size()];
  for(unsigned i = 0, ilim = newBB->invar->predIdxs.size(); i != ilim; ++i)
    newBB->succsAlive[i] = true;
  newBB->status = BBSTATUS_UNKNOWN;
  newBB->IA = this;

  ShadowInstruction* insts = new ShadowInstruction[newBB->invar->insts.size()];
  for(uint32_t i = 0, ilim = newBB->invar->insts.size(); i != ilim; ++i) {
    insts[i].idx = i;
    insts[i].invar = newBB->invar->insts[i];
    insts[i].parent = newBB;
  }

}

ShadowInstructionInvar* IntegrationAttempt::getInstInvar(uint32_t blockidx, uint32_t instidx) {

  return invarInfo->BBs[blockidx]->insts[instidx];

}

ShadowInstruction* IntegrationAttempt::getInstFalling(ShadowBBInvar* BB, uint32_t instIdx) {

  if(BB->naturalScope == L) {

    bool inScope;
    ShadowBB* LocalBB = getBB(BB);
    if(!LocalBB)
      return 0;
    return LocalBB->insts[instIdx];

  }
  else {

    return parent->getInstFalling(BB, instIdx);

  }

}

ShadowInstruction* IntegrationAttempt::getInst(uint32_t blockIdx, uint32_t instIdx) {

  bool inScope;
  ShadowBBInvar* OpBBI = invarInfo->BBs[blockIdx];
  ShadowInstructionInvar* OpII = OpBBI->insts[instIdx];

  if(OpII->scope != L)
    return getInstFalling(OpBBI, instIdx);

  ShadowBB* OpBB = getBB(blockIdx, &inScope);
  if(!inScope) {

    // Access to parent context.
    return getInstFalling(OpBBI, instIdx);

  }
  else if(!OpBB) {
    
    return 0;

  }
  else {

    return OpBB->insts[instIdx];

  }

}

ShadowInstruction* IntegrationAttempt::getInst(ShadowInstructionInvar* SII) {

  return getInst(SII->parent->idx, SII->idx);

}

// Get the ShadowValue for this instruction's operand.
// For most kinds of ShadowValue they're just passed through,
// but for ShadowInstructions we must make sure if the operand is
// a loop invariant then we find the right version of the SI.
// Note that due to LCSSA form operands are always in the same context or a parent,
// except for exit PHI operands, which are special cased in HCF's
// getPHINodeValue function.
ShadowValue ShadowInstruction::getOperand(uint32_t i); {

  ShadowInstIdx& SII = invar->operandIdxs[i];
  uint32_t blockOpIdx = SII.blockIdx;
  if(blockOpIdx == INVALID_BLOCK_IDX) {
    Value* ArgV = invar->I->getOperand(i);
    if(Argument* A = dyn_cast<Argument>(ArgV)) {
      return ShadowValue(parent->IA->getFunctionRoot()->args[A->getArgNo()]);
    }
    else {
      return ShadowValue(V);
    }
  }
  else {
    return ShadowValue(parent->IA->getInst(blockOpIdx, SII.instIdx));
  }

}

ShadowInstruction* ShadowInstruction::getUser(uint32_t i) {

  ShadowInstIdx& SII = invar->userIdxs[i];
  return parent->IA->BBs[SII.blockIdx]->insts[SII.instIdx];

}

