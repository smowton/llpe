// Helper for shadow structures

template<typename T> class ImmutableArray {

  const T* arr;
  size_t n;

 public:

 ImmutableArray() : arr(0), n(0) { }
 ImmutableArray(const T* _arr, size_t _n) : arr(_arr), n(_n) { }

  ImmutableArray(const ImmutableArray& other) {
    arr = other.arr;
    n = other.n;
  }

  ImmutableArray& operator=(const ImmutableArray& other) {
    arr = other.arr;
    n = other.n;
    return *this;
  }

  const T& operator[](size_t n) const {
    return arr[n];
  }

  size_t size() const {
    return n;
  }

  const T& back() {
    return arr[size()-1];
  }

};

// Shadow data structures
class ShadowArg;
class ShadowInstruction;

// Just a tagged union of the types of values that can come out of getReplacement or getOperand.
// This basically replaces ValCtx.
enum ShadowValType {

  SHADOWVAL_ARG,
  SHADOWVAL_INST,
  SHADOWVAL_OTHER,
  SHADOWVAL_INVAL;

};

enum va_arg_type {
  
  va_arg_type_none,
  va_arg_type_baseptr,
  va_arg_type_fp,
  va_arg_type_nonfp

};

struct ShadowValue {

  ShadowValType t;
  union {
    ShadowArg* A;
    ShadowInstruction* I;
    Value* V;
  } u;
  int64_t va_arg;

ShadowValue() : t(SHADOWVAL_INVAL), offset(_o), va_arg(_v), offset(LLONG_MAX), va_arg(-1) { }
ShadowValue(ShadowArg* _A) : t(SHADOWVAL_ARG), u.A(_A), offset(LLONG_MAX), va_arg(-1) { }
ShadowValue(ShadowInstruction* _I, int64_t _v = -1) : t(SHADOWVAL_INST), u.I(_I), va_arg(_v) { }
ShadowValue(Value* _V) : t(SHADOWVAL_OTHER), u.V(_V), offset(LLONG_MAX), va_arg(-1) { }

  bool isInval() {
    return t == SHADOWVAL_INVAL;
  }
  bool isArg() {
    return t == SHADOWVAL_ARG;
  }
  bool isInst() {
    return t == SHADOWVAL_INST;
  }
  bool isVal() {
    return t == SHADOWVAL_OTHER;
  }
  ShadowArg* getArg() {
    return t == SHADOWVAL_ARG ? u.A : 0;
  }
  ShadowInstruction* getInst() {
    return t == SHADOWVAL_INST ? u.I : 0;
  }
  Value* getVal() {
    return t == SHADOWVAL_OTHER ? u.V : 0;
  }

  // Values of va_arg:
  static const int64_t not_va_arg = -1;
  static const int64_t va_baseptr = -2;
  static const int64_t first_nonfp_arg = 0;
  static const int64_t first_fp_arg = 0x00010000;
  static const int64_t max_arg = 0x00020000;

  bool isVaArg() {
    return va_arg != not_va_arg;
  }

  int getVaArgType() {

    if(va_arg == not_va_arg)
      return va_arg_type_none;
    else if(va_arg == va_baseptr)
      return va_arg_type_baseptr;
    else if(va_arg >= first_nonfp_arg && va_arg < first_fp_arg)
      return va_arg_type_nonfp;
    else if(va_arg >= first_fp_arg && va_arg < max_arg)
      return va_arg_type_fp;
    else
      assert(0 && "Bad va_arg value\n");
    return va_arg_type_none;

  }

  int64_t getVaArg() {

    switch(getVaArgType()) {
    case va_arg_type_fp:
      return va_arg - first_fp_arg;
    case va_arg_type_nonfp:
      return va_arg;
    default:
      assert(0);
    }

  }

  const Type* getType() {

    switch(t) {
    case SHADOWVAL_ARG:
      return u.A->getType();
    case SHADOWVAL_INST:
      return u.I->invar->I->getType();
    case SHADOWVAL_VAL:
      return u.V->getType();
    case SHADOWVAL_INVAL:
      return 0;
    }

  }

  ShadowValue stripPointerCasts() {

    if(isArg())
      return *this;
    if(ShadowInstruction* SI = getInst()) {

      if(inst_is<CastInst>()) {
	ShadowValue Op = SI->getOperand(0);
	return Op.stripPointerCasts();
      }
      else {
	return *this;
      }

    }
    else {

      return getVal()->stripPointerCasts();

    }

  }

  IntegrationAttempt* getCtx() {

    switch(t) {
    case SHADOWVAL_ARG:
      return u.A->IA;
    case SHADOWVAL_INST:
      return u.I->parent->IA;
    default:
      return 0;
    }

  }

  Value* getBareVal() {

    switch(t) {
    case SHADOWVAL_ARG:
      return return u.A->invar->A;
    case SHADOWVAL_INST:
      return u.I->invar->I;
    case SHADOWVAL_VAL:
      return u.V;
    default:
      return 0;
    }

  }

  const Loop* getScope() {

    switch(t) {
    case SHADOWVAL_INST:
      return u.I->invar->scope;
    default:
      return 0;
    }

  }

  const Loop* getNaturalScope() {

    switch(t) {
    case SHADOWVAL_INST:
      return u.I->invar->naturalScope;
    default:
      return 0;
    }

  }

  bool isIdentifiedObject() {

    return isIdentifiedObject(getBareVal());

  }

};

template<class X> inline bool val_is(ShadowValue& V) {
  if(Value* V2 = V.getVal())
    return isa<X>(V2);
  else if(ShadowArg* A = V.getArg())
    return isa<X>(A->invar->A);
  else
    return inst_is<X>(V.getInst());
}

template<class X> inline X* dyn_cast_val(ShadowValue& V) {
  if(Value* V2 = V.getVal())
    return dyn_cast<X>(V2);
  else if(ShadowArg* A = V.getArg())
    return dyn_cast<X>(A->invar->A);
  else
    return dyn_cast_inst<X>(V.getInst());
}

template<class X> inline X* cast_val(ShadowValue& V) {
  if(Value* V2 = V.getVal())
    return cast<X>(V2);
  else if(ShadowArg* A = V.getArg())
    return cast<X>(A->invar->A);
  else
    return cast_inst<X>(V.getInst());
}

#define INVALID_BLOCK_IDX 0xffffffff;
#define INVALID_INSTRUCTION_IDX 0xffffffff;

struct ShadowInstIdx {

  uint32_t blockIdx;
  uint32_t instIdx;

ShadowInstIdx() : blockIdx(INVALID_BLOCK_IDX), instIdx(INVALID_INSTRUCTION_IDX) { }
ShadowInstIdx(uint32_t b, uint32_t i) : blockIdx(b), instIdx(i) { }

};

struct ShadowInstructionInvar {
  
  Instruction* I;
  ShadowBBInvar* parent;
  const Loop* scope;
  ImmutableArray<ShadowInstIdx> operandIdxs;
  ImmutableArray<ShadowInstIdx> userIdxs;

};

template<class X> inline bool inst_is(ShadowInstructionInvar* SII) {
   return isa<X>(SII->I);
}

template<class X> inline X* dyn_cast_inst(ShadowInstructionInvar* SII) {
  return dyn_cast<X>(SII->I);
}

template<class X> inline X* cast_inst(ShadowInstructionInvar* SII) {
  return cast<X>(SII->I);
}

enum ShadowInstDIEStatus {

  INSTSTATUS_ALIVE = 0,
  INSTSTATUS_DEAD = 1,
  INSTSTATUS_UNUSED_WRITER = 2

};

struct InstArgImprovement {

  ShadowValue replaceWith;
  ShadowValue baseObject;
  int64_t baseOffset;
  SmallVector<ShadowInstruction*, 1> indirectUsers;
  SmallVector<ShadowInstruction*, 1> PBIndirectUsers; 
  PointerBase PB;
  ShadowInstDIEStatus dieStatus;

InstArgImprovement() : replaceWith(VCNull), baseObject(VCNull), baseOffset(0), dieStatus(INSTSTATUS_ALIVE) { }

};

struct ShadowInstruction {

  uint32_t idx;
  ShadowBB* parent;
  ShadowInstructionInvar* invar;
  InstArgImprovement i;
  SmallVector<ShadowInstruction*, 1> indirectUsers;

  uint32_t getNumOperands() {
    return invar->operandIdxs.size();
  }

  ShadowValue getOperand(uint32_t i);

  ShadowValue getOperandFromEnd(uint32_t i) {
    return getOperand(invar->operandIdxs.size() - i);
  }

  ShadowValue getCallArgOperand(uint32_t i) {
    return getOperand(i);
  }

  uint32_t getNumUsers() {
    return invar->userIdxs.size();
  }

  ShadowInstruction* getUser(uint32_t i);

};

template<class X> inline bool inst_is(ShadowInstruction* SI) {
  return inst_is<X>(SI->invar);
}

template<class X> inline X* dyn_cast_inst(ShadowInstruction* SI) {
  return dyn_cast_inst<X>(SI->invar);
}

template<class X> inline X* cast_inst(ShadowInstruction* SI) {
  return cast_inst<X>(SI->invar);
}

struct ShadowArgInvar {

  Argument* A;
  ImmutableArray<ShadowInstIdx> userIdxs;

};

struct ShadowArg {

  ShadowArgInvar* invar;
  IntegrationAttempt* IA;
  InstArgImprovement i;  

};

enum ShadowBBStatus {

  BBSTATUS_UNKNOWN,
  BBSTATUS_CERTAIN,
  BBSTATUS_ASSUMED

};

struct ShadowFunctionInvar;

struct ShadowBBInvar {

  ShadowFunctionInvar* F;
  uint32_t idx;
  BasicBlock* BB;
  ImmutableArray<uint32_t> succIdxs;
  ImmutableArray<uint32_t> predIdxs;
  ImmutableArray<ShadowInstructionInvar> insts;
  const Loop* outerScope;
  const Loop* scope;
  const Loop* naturalScope;

  inline ShadowBBInvar* getPred(uint32_t i);
  inline uint32_t preds_size();

  inline ShadowBBInvar* getSucc(uint32_t i);  
  inline uint32_t succs_size();

};

struct ShadowBB {

  IntegrationAttempt* IA;
  ShadowBBInvar* invar;
  bool* succsAlive;
  ShadowBBStatus status;
  ImmutableArray<ShadowInstruction> insts;

};

struct ShadowFunctionInvar {

  ImmutableArray<ShadowBBInvar> BBs;
  ImmutableArray<ShadowArgInvar> Args;
  DenseMap<const Loop*, uint32_t> LoopHeaderIndices;
  DenseMap<const Loop*, uint32_t> LoopPreheaderIndices;
  DenseMap<const Loop*, uint32_t> LoopLatchIndices;
  
  // TODO: Remove this map once we never need to map raw BBs onto indices.
  DenseMap<BasicBlock*, ShadowBBInvar*> BBMap;

};

ShadowBBInvar* ShadowBBInvar::getPred(uint32_t i) {
  return F->BBs[predIdxs[i]];
}

uint32_t ShadowBBInvar::preds_size() { 
  return predIdxs.size();
}

ShadowBBInvar* ShadowBBInvar::getSucc(uint32_t i) {
  return F->BBs[succIdxs[i]];
}
  
uint32_t ShadowBBInvar::succs_size() {
  return succIdxs.size();
}

inline ShadowValue getReplacement(ShadowArg* SA, bool mustImprove = false) {
 
  if(SA->i.replaceWith->isInval())
    return mustImprove ? ShadowValue() : ShadowValue(SA);
  else
    return SA->replaceWith;

}

inline ShadowValue getReplacement(ShadowInstruction* SI, bool mustImprove = false) {

  if(SI->i.replaceWith->isInval())
    return mustImprove ? ShadowValue() : ShadowValue(SI);
  else
    return SI->replaceWith;

}

inline ShadowValue getReplacement(ShadowValue& SV, bool mustImprov = false) {

  if(ShadowInstruction* SI = SV.getInst()) {
    return getReplacement(SI);
  }
  else if(ShadowArg* SA = SV.getArg()) {
    return getReplacement(SA);
  
  else {
    return SV;
  }

}

inline Constant* getConstReplacement(ShadowValue& SV) {

  ValCtx VC = getReplacement(SV);
  if(VC.isPtrAsInt())
    return 0;
  return dyn_cast_or_null<Constant>(VC.first);

}

inline bool getBaseAndOffset(ShadowValue& SV, ShadowValue& Base, int64_t& Offset) {

  if(ShadowInstruction* FromSI = SV.getInst()) {
    Base = FromSI->i.baseObject;
    Offset = FromSI->i.baseOffset;
    return !FromSI->i.baseObject.isInval();
  }
  else if(ShadowArg* FromSA = SV.getArg()) {
    Base = FromSA->i.baseObject;
    Offset = FromSA->i.baseOffset;
    return !FromSA->i.baseObject.isInval();
  }
  else if(Constant* C = dyn_cast<Constant>(SV.getVal())) {
    
    Offset = 0;
    Base = ShadowValue(GetBaseWithConstantOffset(C, Offset));
    return isGlobalIdentifiedObject(Base.getVal());

  }

    return false;

}

inline void copyBaseAndOffset(ShadowValue& From, ShadowInstIdx& To) {

  if(ShadowInstruction* FromSI = From.getInst()) {

    To.baseObject = FromSI->i.baseObject;
    To.baseOffset = FromSI->i.baseOffset;

  }
  else if(ShadowArgument* FromSA = From.getArg()) {

    To.baseObject = FromSA->i.baseObject;
    To.baseOffset = FromSA->i.baseOffset;

  }
  else if(Constant* C = dyn_cast<Constant>(From.getVal())) {

    To.baseObject = ShadowValue(GetBaseWithConstantOffset(C, To.baseOffset));
    if(!isGlobalIdentifiedObject(To.baseObject)) {
      To.baseObject = ShadowValue();
      To.baseOffset = 0;
    }

  }

}

inline void copyBaseAndOffset(ShadowValue& From, ShadowInstruction* To) {

  copyBaseAndOffset(From, To->i);

}

inline void copyBaseAndOffset(ShadowValue& From, ShadowArgument* To) {

  copyBaseAndOffset(From, To->i);

}

inline bool isUnresolved(InstArgImprovement& IAI) {
  return !IAI.replaceWith.isInval();
}

inline bool isUnresolved(ShadowInstruction* SI) {
  return isUnresolved(SI->i);
}

inline bool isUnresolved(ShadowArg* SA) {
  return isUnresolved(SA->i);
}
