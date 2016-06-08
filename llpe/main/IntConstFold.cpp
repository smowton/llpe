//===-- IntConstFold.cpp --------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

// A clone of part of the LLVM base constant folder, specialised to work over ImprovedVals instead of Constants.
bool llvm::IHPFoldIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, SmallVector<uint64_t, 4>& OpInts, ValSetType& ImpType, ImprovedVal& Improved) {

  ImpType = ValSetTypeScalar;

  if(OpInts.size() == 1) {

    // Note that because only integers are handled this way at the moment
    // none of the int <-> FP casts are handled.
    // Bitcast, ptrtoint and inttoptr are all handled on different paths.
    // That only leaves extension and truncation of integers!

    Type* DestTy = SI->getType();
    uint32_t DestBitWidth = cast<IntegerType>(DestTy)->getBitWidth();
    IntegerType* SourceTy = cast<IntegerType>(Ops[0].second.V.getNonPointerType());
    APInt SourceAP(SourceTy->getBitWidth(), OpInts[0]);
      
    switch (SI->invar->I->getOpcode()) {

    default:
      return false;
    case Instruction::ZExt:
      Improved = ImprovedVal(ShadowValue::getInt(DestTy, SourceAP.zext(DestBitWidth).getLimitedValue()));
      break;
    case Instruction::SExt:
      Improved = ImprovedVal(ShadowValue::getInt(DestTy, SourceAP.sext(DestBitWidth).getLimitedValue()));
      break;
    case Instruction::Trunc:
      Improved = ImprovedVal(ShadowValue::getInt(DestTy, SourceAP.trunc(DestBitWidth).getLimitedValue()));
      break;

    }

    return true;

  }
  else if(OpInts.size() == 2) {

    const APInt C1V(cast<IntegerType>(SI->getOperand(0).getNonPointerType())->getBitWidth(), OpInts[0]);
    const APInt C2V(cast<IntegerType>(SI->getOperand(1).getNonPointerType())->getBitWidth(), OpInts[1]);
    switch (SI->invar->I->getOpcode()) {
    default:
      return false;
    case Instruction::Add:     
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V + C2V).getLimitedValue()));
      break;
    case Instruction::Sub:     
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V - C2V).getLimitedValue()));
      break;
    case Instruction::Mul:     
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V * C2V).getLimitedValue()));
      break;
    case Instruction::UDiv:
      assert(C2V != 0 && "Div by zero not handled yet");
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.udiv(C2V).getLimitedValue()));
      break;
    case Instruction::SDiv:
      assert(C2V != 0 && "Div by zero not handled yet");
      if (C2V.isAllOnesValue() && C1V.isMinSignedValue())
	Improved = ImprovedVal(ShadowValue(UndefValue::get(SI->getType())));   // MIN_INT / -1 -> undef
      else
	Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.sdiv(C2V).getLimitedValue()));
      break;
    case Instruction::URem:
      assert(C2V != 0 && "Div by zero not handled yet");
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.urem(C2V).getLimitedValue()));
      break;
    case Instruction::SRem:
      assert(C2V != 0 && "Div by zero not handled yet");
      if (C2V.isAllOnesValue() && C1V.isMinSignedValue())
	Improved = ImprovedVal(ShadowValue(UndefValue::get(SI->getType())));   // MIN_INT % -1 -> undef
      else
	Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.srem(C2V).getLimitedValue()));
      break;
    case Instruction::And:
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V & C2V).getLimitedValue()));
      break;
    case Instruction::Or:
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V | C2V).getLimitedValue()));
      break;
    case Instruction::Xor:
      Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), (C1V ^ C2V).getLimitedValue()));
      break;
    case Instruction::Shl: {
      uint32_t shiftAmt = C2V.getZExtValue();
      if (shiftAmt < C1V.getBitWidth())
	Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.shl(shiftAmt).getLimitedValue()));
      else
	Improved = ImprovedVal(ShadowValue(UndefValue::get(SI->getType()))); // too big shift is undef
      break;
    }
    case Instruction::LShr: {
      uint32_t shiftAmt = C2V.getZExtValue();
      if (shiftAmt < C1V.getBitWidth())
	Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.lshr(shiftAmt).getLimitedValue()));
      else
	Improved = ImprovedVal(ShadowValue(UndefValue::get(SI->getType()))); // too big shift is undef
      break;
    }
    case Instruction::AShr: {
      uint32_t shiftAmt = C2V.getZExtValue();
      if (shiftAmt < C1V.getBitWidth())
	Improved = ImprovedVal(ShadowValue::getInt(SI->getType(), C1V.ashr(shiftAmt).getLimitedValue()));
      else
	Improved = ImprovedVal(ShadowValue(UndefValue::get(SI->getType()))); // too big shift is undef
      break;
    }
    }

    return true;

  }

  return false;

}
