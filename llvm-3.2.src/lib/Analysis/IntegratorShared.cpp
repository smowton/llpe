
#include "llvm/ADT/IntervalMap.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/DataLayout.h"
#include "llvm/GlobalValue.h"
#include "llvm/Function.h"
#include "llvm/Operator.h"

using namespace llvm;

namespace llvm {
  class TargetLibraryInfo;
}

// Implement functions called from AA and so which must be linked into core LLVM.

std::pair<ValSetType, ImprovedVal> llvm::getValPB(Value* V) {

  Constant* C = dyn_cast<Constant>(V);
  if(!C)
    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {

    switch(CE->getOpcode()) {

    case Instruction::IntToPtr:
      {
	std::pair<ValSetType, ImprovedVal> CastVal = getValPB(CE->getOperand(0));
	if(CastVal.first == ValSetTypePB)
	  return CastVal;
	else if(CastVal.first == ValSetTypeScalar) {
	  if(ConstantExpr* SubCE = dyn_cast<ConstantExpr>(CastVal.second.V.getVal())) {
	    if(SubCE->getOpcode() == Instruction::PtrToInt)
	      return std::make_pair(ValSetTypeScalar, SubCE->getOperand(0));
	  }
	  return std::make_pair(ValSetTypeScalar, ConstantExpr::getIntToPtr(CE->getOperand(0), CE->getType()));
	}
	else
	  return std::make_pair(ValSetTypeUnknown, ImprovedVal());
      }
    case Instruction::PtrToInt:
      {
	std::pair<ValSetType, ImprovedVal> CastVal = getValPB(CE->getOperand(0));
	if(CastVal.first == ValSetTypePB)
	  return CastVal;
	else if(CastVal.first == ValSetTypeScalar) {
	  if(ConstantExpr* SubCE = dyn_cast<ConstantExpr>(CastVal.second.V.getVal())) {
	    if(SubCE->getOpcode() == Instruction::IntToPtr)
	      return std::make_pair(ValSetTypeScalar, SubCE->getOperand(0));
	  }
	  return std::make_pair(ValSetTypeScalar, ConstantExpr::getPtrToInt(CE->getOperand(0), CE->getType()));
	}
	else
	  return std::make_pair(ValSetTypeUnknown, ImprovedVal());
      }
    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::BitCast:
      return getValPB(CE->getOperand(0));
    case Instruction::GetElementPtr:

      {

	std::pair<ValSetType, ImprovedVal> BasePB = getValPB(CE->getOperand(0));

	if(BasePB.first != ValSetTypePB)
	  return std::make_pair(ValSetTypeUnknown, ImprovedVal());
	if(BasePB.second.Offset == LLONG_MAX)
	  return BasePB;

	int64_t Offset = 0;

	GEPOperator* GEP = cast<GEPOperator>(CE);
	gep_type_iterator GTI = gep_type_begin(GEP);
	for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
	     ++I, ++GTI) {
	  ConstantInt* OpC = cast<ConstantInt>(*I);
	  if (OpC->isZero()) continue;
    
	  // Handle a struct and array indices which add their offset to the pointer.
	  if (StructType *STy = dyn_cast<StructType>(*GTI)) {
	    Offset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
	  } else {
	    uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
	    Offset += OpC->getSExtValue()*Size;
	  }
	}
  
	return std::make_pair(ValSetTypePB, ImprovedVal(BasePB.second.V, BasePB.second.Offset + Offset));

      }
  
    case Instruction::Add:
    case Instruction::Sub:
      {

	std::pair<ValSetType, ImprovedVal> Op1 = getValPB(CE->getOperand(0));
	std::pair<ValSetType, ImprovedVal> Op2 = getValPB(CE->getOperand(1));

	if(Op1.first == ValSetTypeUnknown || Op2.first == ValSetTypeUnknown)
	  return std::make_pair(ValSetTypeUnknown, ShadowValue());

	if(Op1.first == ValSetTypeScalar && Op2.first == ValSetTypeScalar) {

	  if(CE->getOpcode() == Instruction::Add)
	    return std::make_pair(ValSetTypeScalar, (ConstantExpr::getAdd(cast<Constant>(Op1.second.V.getVal()), cast<Constant>(Op2.second.V.getVal()))));
	  else
	    return std::make_pair(ValSetTypeScalar, (ConstantExpr::getSub(cast<Constant>(Op1.second.V.getVal()), cast<Constant>(Op2.second.V.getVal()))));

	}

	if(CE->getOpcode() == Instruction::Add) {

	  if(Op2.first == ValSetTypePB)
	    std::swap(Op1, Op2);

	  if(Op2.first == ValSetTypePB) // Can't add 2 pointers
	    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

	  if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.second.V.getVal()))
	    return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset + Op2C->getLimitedValue()));
	  else
	    return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, LLONG_MAX));

	}
	else {
	
	  if(Op1.first == ValSetTypePB) {
	  
	    if(Op2.first == ValSetTypePB) {
	    
	      if(Op1.second.V == Op2.second.V) {

		if(Op1.second.Offset == LLONG_MAX || Op2.second.Offset == LLONG_MAX)
		  return std::make_pair(ValSetTypeUnknown, ShadowValue());
		else
		  return std::make_pair(ValSetTypeScalar, 
					ImprovedVal(ShadowValue(ConstantInt::get(Type::getInt64Ty(CE->getContext()),
										 Op1.second.Offset - Op2.second.Offset))));
	      
	      }
	      // Else can't subtract 2 pointers with differing bases

	    }
	    else {

	      if(Op1.second.Offset == LLONG_MAX)
		return Op1;
	      if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.second.V.getVal()))
		return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset - Op2C->getLimitedValue()));
	      else
		return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, LLONG_MAX));

	    }
	  
	  }
	
	}

	// Fall through to default

      }	

    default:
      return std::make_pair(ValSetTypeUnknown, ShadowValue());

    }

  }
  else if(isa<GlobalValue>(C)) {

    if(isa<Function>(C))
      return std::make_pair(ValSetTypeScalar, ImprovedVal(ShadowValue(C)));
    
    return std::make_pair(ValSetTypePB, ImprovedVal(ShadowValue(C), 0));

  }
  else if(C->getType()->isPointerTy() && C->isNullValue()) {

    return std::make_pair(ValSetTypePB, ImprovedVal(ShadowValue(C), 0));

  }
  else {

    return std::make_pair(ValSetTypeScalar, ShadowValue(C));

  }

}

static Function* getReplacementFunction(ShadowValue CCalledV) {

  ShadowValue CalledV = CCalledV.stripPointerCasts();

  Constant* C = getConstReplacement(CalledV);

  if(!C) {

    Constant* OnlyVal = 0;
    ImprovedValSetSingle PB;
    if(getImprovedValSetSingle(CalledV, PB)) {
     
      if(!PB.Overdef) {

	for(unsigned i = 0; i < PB.Values.size(); ++i) {

	  Constant* ThisVal = dyn_cast_or_null<Constant>(PB.Values[i].V.getVal());
	  if(!ThisVal) {
	    OnlyVal = 0;
	    break;
	  }
	  if(ThisVal->isNullValue())
	    continue;
	  if(!OnlyVal)
	    OnlyVal = ThisVal;
	  else if(OnlyVal != ThisVal) {
	    OnlyVal = 0;
	    break;
	  }

	}

	if(OnlyVal)
	  C = OnlyVal;

      }

    }

  }

  if(!C)
    return 0;

  return dyn_cast<Function>(C->stripPointerCasts());

}

Function* llvm::getCalledFunction(ShadowInstruction* SI) {

  if(inst_is<CallInst>(SI))
    return getReplacementFunction(SI->getOperandFromEnd(1));
  else if(inst_is<InvokeInst>(SI))
    return getReplacementFunction(SI->getOperandFromEnd(3));
  release_assert(0 && "getCalledFunction called on non-call, non-invoke inst");
  return 0;

}

#define LFV3(x) x

void ImprovedValSetSingle::dropReference() {

  // Singles can never be shared
  LFV3(errs() << "Drop ref on single val: deleted\n");
  delete this;

}

void ImprovedValSetMulti::dropReference() {

  if(!(--MapRefCount)) {

    LFV3(errs() << "Drop ref on multi: deleted\n");
    if(Underlying)
      Underlying->dropReference();
    
    delete this;

  }
  else {

    LFV3(errs() << "Drop ref on multi: new refcount " << MapRefCount << "\n");

  }

}

void ImprovedValSetSingle::replaceRangeWithPB(ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size) {

  *this = NewVal;

}

void ImprovedValSetMulti::replaceRangeWithPB(ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size) {

  if(Size == ULONG_MAX) {

    release_assert(NewVal.Overdef && "Indefinite write with non-clobber value?");

  }

  clearRange(Offset, Size);
  Map.insert(Offset, Offset + Size, NewVal);

  CoveredBytes += Size;
  if(Underlying && CoveredBytes == AllocSize) {

    // This Multi now defines the whole object: drop the underlying object as it never shows through.
    Underlying->dropReference();
    Underlying = 0;

  }

}


void ImprovedValSetSingle::replaceRangeWithPBs(SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  release_assert(NewVals.size() == 1 && Offset == 0);
  *this = NewVals[0].second;

}

void ImprovedValSetMulti::clearRange(uint64_t Offset, uint64_t Size) {

  MapIt found = Map.find(Offset);
  if(found == Map.end())
    return;

  uint64_t LastByte = Offset + Size;

  if(found.start() < Offset) {

    ImprovedValSetSingle RHS;

    if(found.stop() > LastByte) {

      // Punching a hole in a value that wholly covers the range we're clearing:
      ImprovedValSetSingle RHS;
      if(found.val().canTruncate()) {

	RHS = *found;
	RHS.truncateLeft(found.stop() - LastByte);

      }
      else {

	RHS = ImprovedValSetSingle::getOverdef();

      }

    }

    if(found.val().canTruncate()) {
      CoveredBytes -= (found.stop() - Offset);
      found.val().truncateRight(Offset - found.start());
    }
    else {
      found.val().setOverdef();
    }
    uint64_t oldStop = found.stop();
    found.setStopUnchecked(Offset);

    if(RHS.isInitialised()) {

      Map.insert(LastByte, oldStop, RHS);
      CoveredBytes += (oldStop - LastByte);
      return;

    }

    ++found;

  }
  
  while(found != Map.end() && found.start() < LastByte && found.stop() <= LastByte) {

    // Implicitly bumps the iterator forwards:
    CoveredBytes -= (found.stop() - found.start());
    found.erase();

  }

  if(found != Map.end() && found.start() < LastByte) {

    if(found.val().canTruncate()) {
      found.val().truncateLeft(found.stop() - LastByte);
    }
    else {
      found.val().setOverdef();
    }
    CoveredBytes -= (LastByte - found.start());
    found.setStartUnchecked(LastByte);

  }

}

void ImprovedValSetMulti::replaceRangeWithPBs(SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  clearRange(Offset, Size);
  MapIt it = Map.find(Offset);

  for(unsigned i = NewVals.size(); i != 0; --i, --it) {

    IVSRange& RangeVal = NewVals[i-1];
    it.insert(RangeVal.first.first, RangeVal.first.second, RangeVal.second);

  }

  CoveredBytes += Size;
  if(Underlying && CoveredBytes == AllocSize) {

    // This Multi now defines the whole object: drop the underlying object as it never shows through.
    Underlying->dropReference();
    Underlying = 0;

  }  

}

void ImprovedValSetSingle::truncateRight(uint64_t n) {

  // Remove bytes from the RHS, leaving a value of size n bytes.

  if(Overdef)
    return;
  if(SetType == ValSetTypeScalarSplat) {
    release_assert(Values.size() == 1 && "Splat set can't be multivalued");
    Values[0].Offset = (int64_t)n;
    return;
  }

  for(uint32_t i = 0; i < Values.size(); ++i) {

    ConstantInt* CI = cast<ConstantInt>(Values[i].V.getVal());
    llvm::Type* TruncType = Type::getIntNTy(CI->getContext(), n * 8);
    Constant* NewC = ConstantExpr::getTrunc(CI, TruncType);
    release_assert(!isa<ConstantExpr>(NewC));
    Values[i].V = ShadowValue(NewC);

  }

}

void ImprovedValSetSingle::truncateLeft(uint64_t n) {

  // Remove bytes from the LHS, leaving a value of size n bytes.

  if(Overdef)
    return;
  if(SetType == ValSetTypeScalarSplat) {
    release_assert(Values.size() == 1 && "Splat value must be single-valued");
    Values[0].Offset = (int64_t)n;
    return;
  }

  for(uint32_t i = 0; i < Values.size(); ++i) {

    ConstantInt* CI = cast<ConstantInt>(Values[i].V.getVal());
    uint64_t shiftn = CI->getBitWidth() - (n * 8);
    Constant* ShiftAmount = ConstantInt::get(Type::getInt64Ty(CI->getContext()), shiftn);
    Constant* NewC = ConstantExpr::getShl(CI, ShiftAmount);
    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(NewC))
      NewC = ConstantFoldConstantExpression(CE, GlobalTD, GlobalTLI);
    release_assert(!isa<ConstantExpr>(NewC));
    Values[i].V = ShadowValue(NewC);

  }

}

bool ImprovedValSetSingle::canTruncate() {

  return 
    Overdef || 
    (SetType == ValSetTypeScalar && Values[0].V.getType()->isIntegerTy()) || 
    SetType == ValSetTypeScalarSplat;

}

void ImprovedValSetSingle::print(raw_ostream& RSO, bool brief) {

  printPB(RSO, *this, brief);

}

void ImprovedValSetMulti::print(raw_ostream& RSO, bool brief) {

  RSO << "Multi: {\n";
  
  for(MapIt it = Map.begin(), itend = Map.end(); it != itend; ++it) {

    RSO << it.start() << "-" << it.stop() << " -> ";
    it.val().print(RSO, brief);
    RSO << "\n";

  }

  RSO << "}\n";

  if(Underlying) {

    RSO << "With underlying:\n";
    Underlying->print(RSO, brief);

  }

}

void llvm::printPB(raw_ostream& out, ImprovedValSetSingle PB, bool brief) {

  switch(PB.SetType) {
  case ValSetTypeScalar:
    out << "S "; break;
  case ValSetTypeScalarSplat:
    out << "Splat "; break;
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
      if(PB.SetType == ValSetTypePB) {
	if(it->Offset == LLONG_MAX)
	  out << " + ?";
	else
	  out << " + " << it->Offset;
      }
      else if(PB.SetType == ValSetTypeVarArg) {
	out << " #" << it->Offset;
      }
    }
    out << " }";
  }

}



DataLayout* llvm::GlobalTD;
AliasAnalysis* llvm::GlobalAA;
TargetLibraryInfo* llvm::GlobalTLI;
VFSCallAliasAnalysis* llvm::GlobalVFSAA;
IntegrationHeuristicsPass* llvm::GlobalIHP;
