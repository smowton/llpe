// Helper for shadow structures

template<typename T> class ImmutableArray {

  T* arr;
  size_t n;

 public:

 ImmutableArray() : arr(0), n(0) { }
 ImmutableArray(T* _arr, size_t _n) : arr(_arr), n(_n) { }

  ImmutableArray(const ImmutableArray& other) {
    arr = other.arr;
    n = other.n;
  }

  ImmutableArray& operator=(const ImmutableArray& other) {
    arr = other.arr;
    n = other.n;
    return *this;
  }

  T& operator[](size_t n) const {
    return arr[n];
  }

  size_t size() const {
    return n;
  }

  T& back() {
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

ShadowValue() : t(SHADOWVAL_INVAL) { }
ShadowValue(ShadowArg* _A) : t(SHADOWVAL_ARG), u.A(_A) { }
ShadowValue(ShadowInstruction* _I, int64_t _v = -1) : t(SHADOWVAL_INST), u.I(_I) { }
ShadowValue(Value* _V) : t(SHADOWVAL_OTHER), u.V(_V) { }

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

  InstArgImprovement* getIAI() {

    switch(t) {
    case SHADOWVAL_INST:
      return &(u.I->i);
    case SHADOWVAL_ARG:
      return &(u.A->i);      
    default:
      return 0;
    }

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

  PointerBase PB;
  SmallVector<ShadowInstruction*, 1> indirectUsers; 
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

struct ShadowLoopInvar {

  uint32_t headerIdx;
  uint32_t preheaderIdx;
  uint32_t latchIdx;
  std::vector<uint32_t> exitingBlocks;
  std::vector<uint32_t> exitBlocks;
  std::vector<std::pair<uint32_t, uint32_t> > exitEdges;
  
};

struct ShadowFunctionInvar {

  ImmutableArray<ShadowBBInvar> BBs;
  ImmutableArray<ShadowArgInvar> Args;
  DenseMap<const Loop*, ShadowLoopInvar*> LoopInfo;

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
 
  if(SA->i.PB.Overdef || SA->i.PB.Values.size() != 0)
    return mustImprove ? ShadowValue() : ShadowValue(SA);
  else
    return SA->i.PB.Values[0].V;

}

inline ShadowValue getReplacement(ShadowInstruction* SI, bool mustImprove = false) {

  if(SI->i.PB.Overdef || SI->i.PB.Values.size() != 0)
    return mustImprove ? ShadowValue() : ShadowValue(SI);
  else
    return SI->i.PB.Values[0].V;

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

  ShadowValue V = getReplacement(SV);
  return dyn_cast_or_null<Constant>(V.getVal());

}

inline bool getPointerBase(ShadowValue V, PointerBase& OutPB) {

  if(ShadowInstruction* SI = V.getInst()) {

    OutPB = SI->i.PB;
    return OutPB.isInitialised();

  }
  else if(ShadowArg* SA = V.getArg()) {

    OutPB = SA->i.PB;
    return OutPB.isInitialised();

  }
  else {
    
    std::pair<ValSetType, ImprovedVal> V2PB = getValPB(V2);
    OutPB = PointerBase::get(V2PB.second, V2PB.first);
    return true;

  }

}

inline bool getBaseAndOffset(ShadowValue& SV, ShadowValue& Base, int64_t& Offset) {

  PointerBase SVPB;
  if(!getPointerBase(SV, SVPB))
    return false;

  if(SVPB.type != ValSetTypePB || SVPB.Overdef || SVBP.Values.Size() != 1)
    return false;

  Base = SVPB.Values[0].V;
  Offset = SVPB.Values[0].Offset;
  return true;

}

inline bool getBaseObject(ShadowValue& SV, ShadowValue& Base) {

  int64_t ign;
  return getBaseAndOffset(SV, Base, ign);

}

inline bool getBaseAndConstantOffset(ShadowValue& SV, ShadowValue& Base, int64_t& Offset) {

  bool ret = getBaseAndOffset(SV, Base, Offset);
  if(Offset == LLONG_MAX)
    return false;
  return ret;

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
