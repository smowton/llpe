
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Target/TargetData.h"
#include "llvm/GlobalValue.h"

using namespace llvm;

// Implement functions called from AA and so which must be linked into core LLVM.

std::pair<ValSetType, ImprovedVal> llvm::getValPB(Value* V) {

  Constant* C = dyn_cast<Constant>(V);
  if(C)
    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {

    switch(CE->getOpcode()) {

    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::SExt:
    case Instruction::ZExt:
      return getValPB(CE->getOperand(0));
    case Instruction::GetElementPtr:

      {

	std::pair<ValSetType, ImprovedVal> BasePB = getValPB(CE->getOperand(0));

	if(BasePB.first != ValSetTypePB)
	  return std::make_pair(ValSetTypeUnknown, ImprovedVal());
	if(BasePB.second.Offset == LLONG_MAX)
	  return BasePB;

	int64_t Offset;

	GEPOperator* GEP = cast<GEPOperator>(CE);
	gep_type_iterator GTI = gep_type_begin(GEP);
	for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
	     ++I, ++GTI) {
	  ConstantInt* OpC = cast<ConstantInt>(*I);
	  if (OpC->isZero()) continue;
    
	  // Handle a struct and array indices which add their offset to the pointer.
	  if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
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
    
    return std::make_pair(ValSetTypePB, ShadowValue(C));

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
    PointerBase PB;
    if(getPointerBase(CalledV, PB)) {
     
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

TargetData* llvm::GlobalTD;
AliasAnalysis* llvm::GlobalAA;
