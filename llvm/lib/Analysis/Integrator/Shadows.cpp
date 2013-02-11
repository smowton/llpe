// Implement guts of instruction and block shadow structures, as well as utility routines for generating them
// from a function or block.

void getLoopHeaders(DenseMap<const Loop*, uint32_t>& LoopHeaderIndices, DenseMap<const Loop*, uint32_t>& LoopPreheaderIndices, DenseMap<const Loop*, uint32_t>& LoopLatchIndices, DenseMap<BasicBlock*, uint32_t>& BBIndices, const Loop* L) {
  
  LoopHeaderIndices[L->getHeader()] = BBIndices[L->getHeader()];
  LoopPreheaderIndices[L->getLoopPreheader()] = BBIndices[L->getLoopPreheader()];
  LoopLatchIndices[L->getLoopLatch()] = BBIndices[L->getLoopLatch()];

  for(Loop::iterator it = L->begin(), itend = L->end(); it != itend; ++it) {

    getLoopHeaders(LoopHeaderIndices, BBIndices, *it);

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
    getLoopHeaders(RetInfo.LoopHeaderIndices, RetInfo.LoopPreheaderIndices, RetInfo.LoopLatchIndices, BBIndices, *it);

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

}

void PeelIteration::prepareShadows() {

  invarInfo = pass->getFunctionInvarInfo(F);
  nBBs = L->getBlocks().size();
  BBsOffset = new ShadowBB[nBBs];
  for(uint32_t i = 0; i < nBBs; ++i)
    BBs[i] = 0;
  BBsOffset = parentPA->headerIdx;

}

ShadowBB* IntegrationAttempt::getBB(ShadowBBInvar& BBI, bool& inScope) {

  return getBB(BBI.idx, inScope);
  
}

ShadowBB* IntegrationAttempt::getBB(uint32_t idx, bool& inScope) {

  if(!(idx >= BBsOffset && idx < (BBsOffset + nBBs))) {
    inScope = false;
    return 0;
  }
  else {
    inScope = true;
    return BBs[idx - BBsOffset];
  }

}
