
#include "llvm/ADT/IntervalMap.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/DataLayout.h"
#include "llvm/GlobalValue.h"
#include "llvm/GlobalVariable.h"
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
	  if(ConstantExpr* SubCE = dyn_cast_or_null<ConstantExpr>(getSingleConstant(CastVal.second.V))) {
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
	  if(ConstantExpr* SubCE = dyn_cast_or_null<ConstantExpr>(getSingleConstant(CastVal.second.V))) {
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
	    return std::make_pair(ValSetTypeScalar, (ConstantExpr::getAdd(getSingleConstant(Op1.second.V), getSingleConstant(Op2.second.V))));
	  else
	    return std::make_pair(ValSetTypeScalar, (ConstantExpr::getSub(getSingleConstant(Op1.second.V), getSingleConstant(Op2.second.V))));

	}

	if(CE->getOpcode() == Instruction::Add) {

	  if(Op2.first == ValSetTypePB)
	    std::swap(Op1, Op2);

	  if(Op2.first == ValSetTypePB) // Can't add 2 pointers
	    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

	  uint64_t Op2C;
	  if(tryGetConstantInt(Op2.second.V, Op2C))
	    return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset + Op2C));
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
	      uint64_t Op2C;
	      if(tryGetConstantInt(Op2.second.V, Op2C))
		return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset - Op2C));
	      else
		return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, LLONG_MAX));

	    }
	  
	  }
	
	}

	// Return failure:
	break;

      }

    case Instruction::And:
      {

	std::pair<ValSetType, ImprovedVal> Op1 = getValPB(CE->getOperand(0));
	std::pair<ValSetType, ImprovedVal> Op2 = getValPB(CE->getOperand(1));

	if(Op1.first == ValSetTypeScalar && Op2.first == ValSetTypePB)
	  std::swap(Op1, Op2);

	if(Op1.first != ValSetTypePB || Op2.first != ValSetTypeScalar)
	  break;

	if(!Op1.second.V.isGV())
	  break;

	uint64_t GlobalAlign = Op1.second.V.u.GV->G->getAlignment();
	if(GlobalAlign == 0 || GlobalAlign == 1)
	  break;

	uint64_t AndConst;
	if(!tryGetConstantInt(Op2.second.V, AndConst))
	  break;

	int64_t AndConstSigned = (int64_t)AndConst;

	if(AndConst < GlobalAlign) {
	  
	  // Inspecting offset (pointer bits known zero)
	  uint64_t Result = AndConst & Op1.second.Offset;
	  return std::make_pair(ValSetTypeScalar, ShadowValue::getInt(CE->getType(), Result));

	}
	else if(AndConstSigned < 0 && (-AndConstSigned) <= (int64_t)GlobalAlign) {

	  // Masking offset, pointer bits unaffected
	  return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset & AndConst));

	}
	else
	  break;
	
      }

    default:
      break;

    }

    return std::make_pair(ValSetTypeUnknown, ShadowValue());

  }
  else if(isa<GlobalValue>(C)) {

    if(isa<Function>(C))
      return std::make_pair(ValSetTypeScalar, ImprovedVal(ShadowValue(C)));
    else if(GlobalVariable* GV = dyn_cast<GlobalVariable>(C))
      return std::make_pair(ValSetTypePB,
			    ImprovedVal(&(GlobalIHP->shadowGlobals[GlobalIHP->getShadowGlobalIndex(GV)]), 0));
    else
      return std::make_pair(ValSetTypePB, ImprovedVal(ShadowValue(C), 0));

  }
  else if(C->getType()->isPointerTy() && C->isNullValue()) {

    return std::make_pair(ValSetTypePB, ImprovedVal(ShadowValue(C), 0));

  }
  else if(ConstantInt* CI = dyn_cast<ConstantInt>(C)) {

    return std::make_pair(ValSetTypeScalar, ShadowValue::getInt(CI->getType(), CI->getLimitedValue()));

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

  ShadowValue Op;

  if(inst_is<CallInst>(SI))
    Op = SI->getOperandFromEnd(1);
  else if(inst_is<InvokeInst>(SI))
    Op = SI->getOperandFromEnd(3);
  else
    release_assert(0 && "getCalledFunction called on non-call, non-invoke inst");

  // Shouldn't usually happen, but isCopyInst() called from the DOT printer
  // can run into this situation when drawing in-loop blocks from an outer context.
  if(Op.isInval())
    return 0;

  return getReplacementFunction(Op);

}

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

void ImprovedValSetSingle::print(raw_ostream& RSO, bool brief) {

  printPB(RSO, *this, brief);

}

void ImprovedValSetMulti::print(raw_ostream& RSO, bool brief) {

  RSO << "Multi [" << MapRefCount << "]: {\n";
  
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
  case ValSetTypeDeallocated:
    out << "Deallocated"; return;
  case ValSetTypeOldOverdef:
    out << "Old-overdef"; return;
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
IntegrationHeuristicsPass* llvm::GlobalIHP;
