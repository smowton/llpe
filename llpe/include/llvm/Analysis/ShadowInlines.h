//===-- ShadowInlines.h ---------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

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

// Just a tagged union of the types of values that can come out of getOperand.
enum ShadowValType {

  SHADOWVAL_ARG,
  SHADOWVAL_INST,
  SHADOWVAL_GV,
  SHADOWVAL_OTHER,
  SHADOWVAL_PTRIDX,
  SHADOWVAL_FDIDX,
  SHADOWVAL_FDIDX64, /* FD stored in an int64 */
  SHADOWVAL_CI8,
  SHADOWVAL_CI16,
  SHADOWVAL_CI32,
  SHADOWVAL_CI64,
  SHADOWVAL_INVAL

};

enum va_arg_type {
  
  va_arg_type_none,
  va_arg_type_baseptr,
  va_arg_type_fp,
  va_arg_type_nonfp,
  va_arg_type_any
  
};

class ShadowArg;
class ShadowInstruction;
class ShadowGV;
class InstArgImprovement;
class LocStore;
class AllocData;

template<class, class> class LocalStoreMap;
template<class, class> class MergeBlockVisitor;
class LocStore;
class DSEMapPointer;
class TLMapPointer;
class OrdinaryStoreExtraState;
class DSEStoreExtraState;
class TLStoreExtraState;

typedef LocalStoreMap<LocStore, OrdinaryStoreExtraState> OrdinaryLocalStore;
typedef LocalStoreMap<DSEMapPointer, DSEStoreExtraState> DSELocalStore;
typedef LocalStoreMap<TLMapPointer, TLStoreExtraState> TLLocalStore;

typedef MergeBlockVisitor<LocStore, OrdinaryStoreExtraState> OrdinaryMerger;
typedef MergeBlockVisitor<DSEMapPointer, DSEStoreExtraState> DSEMerger;
typedef MergeBlockVisitor<TLMapPointer, TLStoreExtraState> TLMerger;

enum ValSetType {

  ValSetTypeUnknown,
  ValSetTypePB, // Pointers; the Offset member is set, and the values must be of idx type.
  ValSetTypeScalar, // Ordinary constants
  ValSetTypeScalarSplat, // Constant splat, used to cheaply express memset(block, size), Offset == size
  ValSetTypeFD, // File descriptors; can only be copied, otherwise opaque. Values are idx type.
  ValSetTypeVarArg, // Special tokens representing a vararg or VA-related cookie. Values are instruction type.
  ValSetTypeOverdef, // Useful for disambiguating empty PB from Overdef; never actually used in PB.
  ValSetTypeDeallocated, // Special single value signifying an object that is deallocted on a given path.
  ValSetTypeOldOverdef // A special case of Overdef where the value is known not to alias objects
                       // created since specialisation started.

};

struct ShadowValue {

  ShadowValType t;
  union {
    ShadowArg* A;
    ShadowInstruction* I;
    ShadowGV* GV;
    Value* V;
    struct {
      int32_t frame;
      uint32_t idx;
    } PtrOrFd;
    uint64_t CI;
  } u;

ShadowValue() : t(SHADOWVAL_INVAL) { u.V = 0; }
ShadowValue(ShadowArg* _A) : t(SHADOWVAL_ARG) { u.A = _A; }
ShadowValue(ShadowInstruction* _I) : t(SHADOWVAL_INST) { u.I = _I; }
ShadowValue(ShadowGV* _GV) : t(SHADOWVAL_GV) { u.GV = _GV; }
ShadowValue(Value* _V) : t(SHADOWVAL_OTHER) { u.V = _V; }
ShadowValue(ShadowValType Ty, int32_t frame, uint32_t idx) : t(Ty) { u.PtrOrFd.frame = frame; u.PtrOrFd.idx = idx; }
ShadowValue(ShadowValType Ty, uint64_t _CI) : t(Ty) { u.CI = _CI; }

  static ShadowValue getPtrIdx(int32_t f, uint32_t i) { return ShadowValue(SHADOWVAL_PTRIDX, f, i); }
  static ShadowValue getFdIdx(uint32_t i) { return ShadowValue(SHADOWVAL_FDIDX, -1, i); }
  static ShadowValue getFdIdx64(uint32_t i) { return ShadowValue(SHADOWVAL_FDIDX64, -1, i); }
  static ShadowValue getInt8(uint8_t i) { return ShadowValue(SHADOWVAL_CI8, i); }
  static ShadowValue getInt16(uint16_t i) { return ShadowValue(SHADOWVAL_CI16, i); }
  static ShadowValue getInt32(uint32_t i) { return ShadowValue(SHADOWVAL_CI32, i); }
  static ShadowValue getInt64(uint64_t i) { return ShadowValue(SHADOWVAL_CI64, i); }
  static ShadowValue getInt(Type*, uint64_t i);

  bool isInval() const {
    return t == SHADOWVAL_INVAL;
  }
  bool isArg() const {
    return t == SHADOWVAL_ARG;
  }
  bool isInst() const {
    return t == SHADOWVAL_INST;
  }
  bool isVal() const {
    return t == SHADOWVAL_OTHER;
  }
  bool isGV() const {
    return t == SHADOWVAL_GV;
  }
  bool isPtrIdx() const {
    return t == SHADOWVAL_PTRIDX;
  }
  bool isFdIdx() const {
    return t == SHADOWVAL_FDIDX || t == SHADOWVAL_FDIDX64;
  }
  bool isConstantInt() const {
    return t == SHADOWVAL_CI8 || t == SHADOWVAL_CI16 || t == SHADOWVAL_CI32 || t == SHADOWVAL_CI64;
  }
  ShadowArg* getArg() const {
    return t == SHADOWVAL_ARG ? u.A : 0;
  }
  ShadowInstruction* getInst() const {
    return t == SHADOWVAL_INST ? u.I : 0;
  }
  Value* getVal() const {
    return t == SHADOWVAL_OTHER ? u.V : 0;
  }
  ShadowGV* getGV() const {
    return t == SHADOWVAL_GV ? u.GV : 0;
  }
  bool getCI(uint64_t& Out) const {
    bool isci = isConstantInt();
    if(isci)
      Out = u.CI;
    return isci;
  }
  bool getSignedCI(int64_t& Out) const {
    bool isci = isConstantInt();
    if(isci) {
      switch(t) {
      case SHADOWVAL_CI8:
	Out = (int8_t)(uint8_t)u.CI;
	break;
      case SHADOWVAL_CI16:
	Out = (int16_t)(uint16_t)u.CI;
	break;
      case SHADOWVAL_CI32:
	Out = (int32_t)(uint32_t)u.CI;
	break;
      case SHADOWVAL_CI64:
	Out = (int64_t)(uint64_t)u.CI;
	break;
      default:
	llvm_unreachable("Bad integer type");
      }
    }
    return isci;
  }

  Type* getNonPointerType() const;
  ShadowValue stripPointerCasts() const;
  IntegrationAttempt* getCtx() const;
  Value* getBareVal() const;
  const ShadowLoopInvar* getScope() const;
  const ShadowLoopInvar* getNaturalScope() const;
  bool isIDObject() const;
  InstArgImprovement* getIAI() const;
  LLVMContext& getLLVMContext() const;
  void setCommittedVal(Value* V);
  bool objectAvailable() const;
  const MDNode* getTBAATag() const;
  uint64_t getAllocSize(OrdinaryLocalStore*) const;
  uint64_t getAllocSize(IntegrationAttempt*) const;
  int32_t getFrameNo() const;
  int32_t getHeapKey() const;
  int32_t getFramePos() const {
    return getHeapKey();
  }
  int32_t getFd() const {
    switch(t) {
    case SHADOWVAL_FDIDX:
    case SHADOWVAL_FDIDX64:
      return getHeapKey();
    default:
      return -1;
    }
  }
  
  AllocData* getAllocData(OrdinaryLocalStore* Map) const;
  bool isNullOrConst() const;
  bool isNullPointer() const;
  uint64_t getValSize() const;

};

inline bool operator==(ShadowValue V1, ShadowValue V2) {
  if(V1.t != V2.t)
    return false;
  switch(V1.t) {
  case SHADOWVAL_INVAL:
    return true;
  case SHADOWVAL_ARG:
    return V1.u.A == V2.u.A;
  case SHADOWVAL_INST:
    return V1.u.I == V2.u.I;
  case SHADOWVAL_GV:
    return V1.u.GV == V2.u.GV;
  case SHADOWVAL_OTHER:
    return V1.u.V == V2.u.V;
  case SHADOWVAL_PTRIDX:
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64:
    return V1.u.PtrOrFd.frame == V2.u.PtrOrFd.frame && V1.u.PtrOrFd.idx == V2.u.PtrOrFd.idx;
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return V1.u.CI == V2.u.CI;
  default:
    release_assert(0 && "Bad SV type");
    return false;
  }
}

inline bool operator!=(ShadowValue V1, ShadowValue V2) {
   return !(V1 == V2);
}

inline bool operator<(ShadowValue V1, ShadowValue V2) {
  if(V1.t != V2.t)
    return V1.t < V2.t;
  switch(V1.t) {
  case SHADOWVAL_INVAL:
    return false;
  case SHADOWVAL_ARG:
    return V1.u.A < V2.u.A;
  case SHADOWVAL_INST:
    return V1.u.I < V2.u.I;
  case SHADOWVAL_GV:
    return V1.u.GV < V2.u.GV;
  case SHADOWVAL_OTHER:
    return V1.u.V < V2.u.V;
  case SHADOWVAL_PTRIDX:
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64:
    if(V1.u.PtrOrFd.frame == V2.u.PtrOrFd.frame)
      return V1.u.PtrOrFd.idx < V2.u.PtrOrFd.idx;
    else
      return V1.u.PtrOrFd.frame < V2.u.PtrOrFd.frame;
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return V1.u.CI < V2.u.CI;
  default:
    release_assert(0 && "Bad SV type");
    return false;
  }
}

inline bool operator<=(ShadowValue V1, ShadowValue V2) {
  return V1 < V2 || V1 == V2;
}

inline bool operator>(ShadowValue V1, ShadowValue V2) {
  return !(V1 <= V2);
}

inline bool operator>=(ShadowValue V1, ShadowValue V2) {
  return !(V1 < V2);
}

// Characteristics for using ShadowValues in hashsets (DenseSet, or as keys in DenseMaps)
template<> struct DenseMapInfo<ShadowValue> {
  
  typedef DenseMapInfo<int> TypeInfo;
  typedef DenseMapInfo<void*> VoidInfo;
  typedef DenseMapInfo<std::pair<int, void*> > PairInfo;

  static inline ShadowValue getEmptyKey() {
    return ShadowValue((Value*)VoidInfo::getEmptyKey());
  }

  static inline ShadowValue getTombstoneKey() {
    return ShadowValue((Value*)VoidInfo::getTombstoneKey());
  }

  static unsigned getHashValue(const ShadowValue& V) {
    void* hashPtr;
    switch(V.t) {
    case SHADOWVAL_INVAL:
      hashPtr = 0; break;
    case SHADOWVAL_ARG:
      hashPtr = V.u.A; break;
    case SHADOWVAL_INST:
      hashPtr = V.u.I; break;
    case SHADOWVAL_GV:
      hashPtr = V.u.GV; break;
    case SHADOWVAL_OTHER:
      hashPtr = V.u.V; break;
    case SHADOWVAL_PTRIDX:
    case SHADOWVAL_FDIDX:
    case SHADOWVAL_FDIDX64:
      // Should work due to the union.
      hashPtr = V.u.V; break;
    case SHADOWVAL_CI8:
    case SHADOWVAL_CI16:
    case SHADOWVAL_CI32:
    case SHADOWVAL_CI64:
      hashPtr = (void*)V.u.CI; break;
    default:
      release_assert(0 && "Bad value type");
      hashPtr = 0;
    }
    return PairInfo::getHashValue(std::make_pair((int)V.t, hashPtr));
  }

  static bool isEqual(const ShadowValue& V1, const ShadowValue& V2) {
    return V1 == V2;
  }

 };

// ImprovedValSetSingle: an SCCP-like value giving candidate constants or pointer base addresses for a value.
// May be: 
// overdefined (overflowed, or defined by an unknown)
// defined (known set of possible values)
// undefined (implied by absence from map)
// Note Value members may be null (signifying a null pointer) without being Overdef.

#define PBMAX 16

bool functionIsBlacklisted(Function*);

struct ImprovedVal {

  ShadowValue V;
  int64_t Offset;

ImprovedVal() : V(), Offset(LLONG_MAX) { }
ImprovedVal(ShadowValue _V, int64_t _O = LLONG_MAX) : V(_V), Offset(_O) { }

  // Values for Offset when this is a VarArg:
  static const int64_t not_va_arg = -1;
  static const int64_t va_baseptr = -2;
  static const int64_t first_nonfp_arg = 0;
  static const int64_t first_fp_arg = 0x00010000;
  static const int64_t first_any_arg = 0x00020000;
  static const int64_t max_arg = 0x00030000;

  int getVaArgType() {

    if(Offset == not_va_arg)
      return va_arg_type_none;
    else if(Offset == va_baseptr)
      return va_arg_type_baseptr;
    else if(Offset >= first_nonfp_arg && Offset < first_fp_arg)
      return va_arg_type_nonfp;
    else if(Offset >= first_fp_arg && Offset < first_any_arg)
      return va_arg_type_fp;
    else if(Offset >= first_any_arg && Offset < max_arg)
      return va_arg_type_any;
    else
      assert(0 && "Bad va_arg value\n");
    return va_arg_type_none;

  }

  int64_t getVaArg() {

    switch(getVaArgType()) {
    case va_arg_type_any:
      return Offset - first_any_arg;
    case va_arg_type_fp:
      return Offset - first_fp_arg;
    case va_arg_type_nonfp:
      return Offset;
    default:
      release_assert(0 && "Bad vaarg type");
      return 0;
    }

  }

  bool isNull() {

    if(Constant* C = dyn_cast_or_null<Constant>(V.getVal()))
      return C->isNullValue();
    else
      return false;

  }

  bool isFunction() {

    return !!dyn_cast_or_null<Function>(V.getVal());

  }

};

inline bool operator==(ImprovedVal V1, ImprovedVal V2) {
  return (V1.V == V2.V && V1.Offset == V2.Offset);
}

inline bool operator!=(ImprovedVal V1, ImprovedVal V2) {
   return !(V1 == V2);
}

inline bool operator<(ImprovedVal V1, ImprovedVal V2) {
  if(V1.V != V2.V)
    return V1.V < V2.V;
  return V1.Offset < V2.Offset;
}

inline bool operator<=(ImprovedVal V1, ImprovedVal V2) {
  return V1 < V2 || V1 == V2;
}

inline bool operator>(ImprovedVal V1, ImprovedVal V2) {
  return !(V1 <= V2);
}

inline bool operator>=(ImprovedVal V1, ImprovedVal V2) {
  return !(V1 < V2);
}

class ImprovedValSetSingle;

typedef std::pair<std::pair<uint64_t, uint64_t>, ImprovedValSetSingle> IVSRange;

#define SAFE_DROP_REF(x) do { if(x->dropReference()) x = 0; } while(0);

struct ImprovedValSet {

  bool isMulti;
ImprovedValSet(bool M) : isMulti(M) { }
  virtual bool dropReference() = 0;
  virtual bool isWritableMulti() = 0;
  virtual ImprovedValSet* getReadableCopy() = 0;
  virtual void print(raw_ostream&, bool brief = false) const = 0;
  virtual ~ImprovedValSet() {}
  virtual bool isWhollyUnknown() const = 0;
  
};

struct ImprovedValSetSingle : public ImprovedValSet {

  static bool classof(const ImprovedValSet* IVS) { return !IVS->isMulti; }

  ValSetType SetType;
  SmallVector<ImprovedVal, 1> Values;
  bool Overdef;

 ImprovedValSetSingle() : ImprovedValSet(false), SetType(ValSetTypeUnknown), Overdef(false) { }
 ImprovedValSetSingle(ValSetType T) : ImprovedValSet(false), SetType(T), Overdef(false) { }
 ImprovedValSetSingle(ValSetType T, bool OD) : ImprovedValSet(false), SetType(T), Overdef(OD) { }
 ImprovedValSetSingle(ImprovedVal V, ValSetType T) : ImprovedValSet(false), SetType(T), Overdef(false) {
    Values.push_back(V);
  }

  virtual ~ImprovedValSetSingle() {}

  virtual bool dropReference();

  bool isInitialised() const {
    return Overdef || SetType == ValSetTypeDeallocated || SetType == ValSetTypeOldOverdef || Values.size() > 0;
  }

  virtual bool isWhollyUnknown() const {
    return Overdef || SetType == ValSetTypeDeallocated || SetType == ValSetTypeOldOverdef || Values.size() == 0;
  }

  bool isOldValue() const {
    return (!Overdef) && SetType == ValSetTypeOldOverdef;
  }
  
  void removeValsWithBase(ShadowValue Base) {

    for(SmallVector<ImprovedVal, 1>::iterator it = Values.end(), endit = Values.begin(); it != endit; --it) {

      ImprovedVal& ThisV = *(it - 1);
      if(ThisV.V == Base)
	Values.erase(it);
      
    }

  }

  bool onlyContainsZeroes() {

    if(Values.size() == 1)
      return Values[0].isNull();
    else
      return false;

  }

  bool onlyContainsNulls() {

    if(SetType == ValSetTypePB)
      return onlyContainsZeroes();
    else
      return false;
    
  }

  bool onlyContainsFunctions() {

    if(SetType != ValSetTypeScalar)
      return false;
    
    for(uint32_t i = 0; i < Values.size(); ++i) {

      if(!Values[i].isFunction())
	return false;
      
    }
    
    return true;

  }

  ImprovedValSetSingle& insert(ImprovedVal V) {

    release_assert(V.V.t != SHADOWVAL_INVAL);

    if(Overdef)
      return *this;

    if(SetType == ValSetTypePB) {

      for(SmallVector<ImprovedVal, 1>::iterator it = Values.begin(), endit = Values.end(); it != endit; ++it) {

	if(it->V == V.V) {

	  if(it->Offset != V.Offset)
	    it->Offset = LLONG_MAX;
	  return *this;

	}

      }

    }
    else {

      if(std::count(Values.begin(), Values.end(), V))
	return *this;

    }

    Values.push_back(V);

    if(Values.size() > PBMAX)
      setOverdef();
    
    return *this;

  }

  ImprovedValSetSingle& mergeOne(ValSetType OtherType, ImprovedVal OtherVal) {

    if(OtherType == ValSetTypeUnknown)
      return *this;

    if(OtherType == ValSetTypeOverdef) {
      setOverdef();
      return *this;
    }

    if(isInitialised() && OtherType != SetType) {

      if(onlyContainsFunctions() && OtherVal.isNull()) {

	insert(OtherVal);
	return *this;

      }
      else if(onlyContainsNulls() && OtherVal.isFunction()) {

	SetType = ValSetTypeScalar;
	insert(OtherVal);
	return *this;

      }
      else {

	if(OtherType == ValSetTypePB)
	  SetType = ValSetTypePB;
	setOverdef();
	
      }

    }
    else {

      SetType = OtherType;
      insert(OtherVal);

    }

    return *this;

  }

  ImprovedValSetSingle& merge(ImprovedValSetSingle& OtherPB) {
    if(!OtherPB.isInitialised())
      return *this;
    if(OtherPB.Overdef) {
      if(OtherPB.SetType == ValSetTypePB)
	SetType = ValSetTypePB;
      setOverdef();
    }
    else if(isInitialised() && OtherPB.SetType != SetType) {

      // Deallocated tags are weak, and are overridden by the other value.
      if(SetType == ValSetTypeDeallocated) {
	*this = OtherPB;
	return *this;
      }
      
      if(OtherPB.SetType == ValSetTypeDeallocated) {

	return *this;

      }

      // Special case: functions may permissibly merge with null pointers. In this case
      // reclassify the null as a scalar.
      if(onlyContainsFunctions() && OtherPB.onlyContainsNulls()) {

	insert(OtherPB.Values[0]);
	return *this;

      }
      else if(onlyContainsNulls() && OtherPB.onlyContainsFunctions()) {

	SetType = ValSetTypeScalar;
	// Try again:
	return merge(OtherPB);

      }

      if(OtherPB.SetType == ValSetTypePB)
	SetType = ValSetTypePB;
      setOverdef();

    }
    else {
      SetType = OtherPB.SetType;
      for(SmallVector<ImprovedVal, 4>::iterator it = OtherPB.Values.begin(), it2 = OtherPB.Values.end(); it != it2 && !Overdef; ++it)
	insert(*it);
    }
    return *this;
  }

  void setOverdef() {

    Values.clear();
    Overdef = true;

  }

  void set(ImprovedVal V, ValSetType T) {

    Values.clear();
    Values.push_back(V);
    SetType = T;
    Overdef = false;

  }

  ImprovedValSet* getReadableCopy() {

    return new ImprovedValSetSingle(*this);

  }

  bool isWritableMulti() {
    return false;
  }

  bool coerceToType(Type* Target, uint64_t TargetSize, std::string* error, bool allowImplicitPtrToInt = true);
  bool canCoerceToType(Type* Target, uint64_t TargetSize, std::string* error, bool allowImplicitPtrToInt = true);
  virtual void print(raw_ostream&, bool brief = false) const;
  
};

// Traits for half-open integers that never coalesce:

struct HalfOpenNoMerge {
  /// startLess - Return true if x is not in [a;b].
  /// This is x < a both for closed intervals and for [a;b) half-open intervals.
  static inline bool startLess(const uint64_t &x, const uint64_t &a) {
    return x < a;
  }

  /// stopLess - Return true if x is not in [a;b].
  /// This is b < x for a closed interval, b <= x for [a;b) half-open intervals.
  static inline bool stopLess(const uint64_t &b, const uint64_t &x) {
    return b <= x;
  }

  /// adjacent - Return true when the intervals [x;a] and [b;y] can coalesce.
  /// This is a+1 == b for closed intervals, a == b for half-open intervals.
  static inline bool adjacent(const uint64_t &a, const uint64_t &b) {
    return false;
  }

};

struct HalfOpenWithMerge {

  static inline bool startLess(const uint64_t &x, const uint64_t &a) {
    return x < a;
  }

  static inline bool stopLess(const uint64_t &b, const uint64_t &x) {
    return b <= x;
  }

  static inline bool adjacent(const uint64_t &a, const uint64_t &b) {
    return a == b;
  }

};

struct ImprovedValSetMulti : public ImprovedValSet {

  typedef IntervalMap<uint64_t, ImprovedValSetSingle, IntervalMapImpl::NodeSizer<uint64_t, ImprovedValSetSingle>::LeafSize, HalfOpenNoMerge> MapTy;
  typedef MapTy::iterator MapIt;
  typedef MapTy::const_iterator ConstMapIt;
  MapTy Map;
  uint32_t MapRefCount;
  ImprovedValSet* Underlying;
  uint64_t CoveredBytes;
  uint64_t AllocSize;

  ImprovedValSetMulti(uint64_t ASize);
  ImprovedValSetMulti(const ImprovedValSetMulti& other);

  virtual ~ImprovedValSetMulti() {}

  static bool classof(const ImprovedValSet* IVS) { return IVS->isMulti; }
  virtual bool dropReference();
  bool isWritableMulti() {
    return MapRefCount == 1;
  }
  ImprovedValSet* getReadableCopy() {
    MapRefCount++;
    return this;
  }

  virtual bool isWhollyUnknown() const {
    return false;
  }

  virtual void print(raw_ostream&, bool brief = false) const;

};

inline bool IVIsInitialised(ImprovedValSet* IV) {

  if(IV->isMulti)
    return true;
  return cast<ImprovedValSetSingle>(IV)->isInitialised();

}

#define INVALID_BLOCK_IDX 0xffffffff
#define INVALID_INSTRUCTION_IDX 0xffffffff

struct ShadowInstIdx {

  uint32_t blockIdx;
  uint32_t instIdx;

ShadowInstIdx() : blockIdx(INVALID_BLOCK_IDX), instIdx(INVALID_INSTRUCTION_IDX) { }
ShadowInstIdx(uint32_t b, uint32_t i) : blockIdx(b), instIdx(i) { }

};

class ShadowBBInvar;

struct ShadowInstructionInvar {
  
  uint32_t idx;
  Instruction* I;
  ShadowBBInvar* parent;
  ImmutableArray<ShadowInstIdx> operandIdxs;
  ImmutableArray<ShadowInstIdx> userIdxs;
  ImmutableArray<uint32_t> operandBBs;

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

#define INSTSTATUS_ALIVE 0
#define INSTSTATUS_DEAD 1
#define INSTSTATUS_UNUSED_WRITER 2

struct InstArgImprovement {

  ImprovedValSet* PB;

InstArgImprovement() : PB(0) { }

};

class ShadowBB;
class OrdinaryStoreExtraState;

template<class, class> class LocalStoreMap;
template<class, class> class MergeBlockVisitor;

class LocStore;
extern LocStore NormalEmptyMapPtr;

struct LocStore {

  ImprovedValSet* store;

LocStore(ImprovedValSet* s) : store(s) {}
LocStore() : store(0) {}
LocStore(const LocStore& other) : store(other.store) {}

  static LocStore& getEmptyStore() {

    return NormalEmptyMapPtr;

  }

  static bool LT(const LocStore* a, const LocStore* b) {

    return a->store < b->store;

  }

  static bool EQ(const LocStore* a, const LocStore* b) {

    return a->store == b->store;
    
  }

  static LocalStoreMap<LocStore, OrdinaryStoreExtraState>* getMapForBlock(ShadowBB*);

  bool isValid() { return !!store; }

  // Insert checkStore here to verify store after each merge:
  void checkMergedResult() {  }

  // Simple forwards:
  LocStore getReadableCopy() { return LocStore(store->getReadableCopy());  }
  bool dropReference() {  return store->dropReference();  }
  void print(raw_ostream& RSO, bool brief) { store->print(RSO, brief); }

  static void mergeStores(LocStore* mergeFrom, LocStore* mergeTo, uint64_t ASize, MergeBlockVisitor<LocStore, OrdinaryStoreExtraState>*);

  static void simplifyStore(LocStore*);

  bool derefWillAllowSimplify() {
    return store && isa<ImprovedValSetMulti>(store) && cast<ImprovedValSetMulti>(store)->MapRefCount == 2;
  }

};

enum AllocTestedState {

  AllocUnchecked,
  AllocTested,
  AllocEscaped

};

struct AllocData {

  uint64_t storeSize;
  int32_t allocIdx;
  bool allocVague;
  AllocTestedState allocTested;
  bool isCommitted;
  ShadowValue allocValue;
  std::vector<std::pair<WeakVH, uint32_t> > PatchRefs;
  Type* allocType;
  Value* committedVal;

  bool isAvailable();

};

enum ThreadLocalState {

  TLS_MUSTCHECK, /* instruction might have been clobbered by other threads; check at runtime */
  TLS_NOCHECK, /* instruction might have been clobbered, but check would be redundant */
  TLS_NEVERCHECK /* instruction cannot possibly be clobbered */

};

#define RUNTIME_CHECK_NONE 0
#define RUNTIME_CHECK_AS_EXPECTED 1
#define RUNTIME_CHECK_READ_LLIOWD 2
#define RUNTIME_CHECK_READ_MEMCMP 3

struct ShadowInstruction {

  ShadowBB* parent;
  ShadowInstructionInvar* invar;
  InstArgImprovement i;
  Value* committedVal;
  // Of a load, memcpy or realloc, is there no need to check for thread interference?
  unsigned char isThreadLocal;
  unsigned char needsRuntimeCheck;
  unsigned char dieStatus;
  void* typeSpecificData;

  void initTypeSpecificData();

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

  uint32_t getNumArgOperands() {
    if(isa<CallInst>(invar->I))
      return getNumOperands() - 1;
    else
      return getNumOperands() - 3;
  }

  uint32_t getNumUsers() {
    return invar->userIdxs.size();
  }

  ShadowInstruction* getUser(uint32_t i);

  Type* getType() {
    return invar->I->getType();
  }

  bool isCopyInst();
  ShadowValue getCopySource();
  ShadowValue getCopyDest();

  bool readsMemoryDirectly();
  bool hasOrderingConstraint();

  uint32_t getNumSuccessors() {
    return invar->I->getNumSuccessors();
  }
  bool isTerminator() {
    return invar->I->isTerminator();
  }

  Instruction* getInstruction() {
    return invar->I;
  }
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

struct ShadowGV {

  GlobalVariable* G;
  uint64_t storeSize;
  int32_t allocIdx;

};

struct ShadowArg {

  ShadowArgInvar* invar;
  InlineAttempt* IA;
  InstArgImprovement i;  
  Value* committedVal;
  unsigned char dieStatus;
  WeakVH patchInst;

  Type* getType() {
    return invar->A->getType();
  }

};

enum ShadowBBStatus {

  BBSTATUS_UNKNOWN,
  BBSTATUS_CERTAIN,
  BBSTATUS_ASSUMED,
  BBSTATUS_IGNORED

};

struct ShadowFunctionInvar;

struct ShadowBBInvar {

  ShadowFunctionInvar* F;
  uint32_t idx;
  BasicBlock* BB;
  ImmutableArray<uint32_t> succIdxs;
  ImmutableArray<uint32_t> predIdxs;
  ImmutableArray<ShadowInstructionInvar> insts;
  const ShadowLoopInvar* outerScope;
  const ShadowLoopInvar* naturalScope;

  inline ShadowBBInvar* getPred(uint32_t i);
  inline uint32_t preds_size();

  inline ShadowBBInvar* getSucc(uint32_t i);  
  inline uint32_t succs_size();

};

struct OrdinaryStoreExtraState {

  // Objects that are certainly not effected by thread yields.
  DenseSet<ShadowValue> threadLocalObjects;
  // Objects that are certainly not reachable from objects older than specialisation start
  DenseSet<ShadowValue> noAliasOldObjects;
  // Objects all of whose pointers are known, and therefore are not aliased by unknown pointers.
  DenseSet<ShadowValue> unescapedObjects;

  void copyFrom(const OrdinaryStoreExtraState& es) { *this = es; }
  static void doMerge(LocalStoreMap<LocStore, OrdinaryStoreExtraState>* toMap, 
		      SmallVector<LocalStoreMap<LocStore, OrdinaryStoreExtraState>*, 4>::iterator fromBegin, 
		      SmallVector<LocalStoreMap<LocStore, OrdinaryStoreExtraState>*, 4>::iterator fromEnd,
		      bool verbose);
  static void dump(LocalStoreMap<LocStore, OrdinaryStoreExtraState>* map);

};

// Define types for DSE stores:

struct TrackedStore {

  ShadowInstruction* I; // Invalid if isCommitted
  bool isCommitted;
  WeakVH* committedInsts; // Valid if the store was live when committed.
  uint64_t nCommittedInsts;
  uint64_t outstandingBytes;
  bool isNeeded;

  TrackedStore(ShadowInstruction* _I, uint64_t ob);
  ~TrackedStore();
  bool canKill() const;
  void kill();
  void derefBytes(uint64_t nBytes);

};

typedef SmallVector<TrackedStore*, 1> DSEMapEntry;

typedef IntervalMap<uint64_t, DSEMapEntry, IntervalMapImpl::NodeSizer<uint64_t, DSEMapEntry>::LeafSize, HalfOpenNoMerge> DSEMapTy;

struct TrackedAlloc {

  ShadowInstruction* SI;
  bool isCommitted;
  uint64_t nRefs;
  bool isNeeded;

  bool dropReference();

  TrackedAlloc(ShadowInstruction* _SI);
  ~TrackedAlloc();

};

class DSEMapPointer;
extern DSEMapPointer DSEEmptyMapPtr;

class DSEStoreExtraState;

struct DSEMapPointer {

  DSEMapTy* M;
  TrackedAlloc* A;
  
DSEMapPointer() : M(0), A(0) {}
DSEMapPointer(DSEMapTy* _M, TrackedAlloc* _A) : M(_M), A(_A) {}
DSEMapPointer(const DSEMapPointer& other) : M(other.M), A(other.A) {}

  static DSEMapPointer& getEmptyStore() {

    return DSEEmptyMapPtr;

  }

  static bool LT(const DSEMapPointer* a, const DSEMapPointer* b) {

    return a->M < b->M;

  }

  static bool EQ(const DSEMapPointer* a, const DSEMapPointer* b) {

    return a->M == b->M;

  }

  static LocalStoreMap<DSEMapPointer, DSEStoreExtraState>* getMapForBlock(ShadowBB* BB);
  bool isValid() { return !!M; }
  void checkMergedResult() { }
  DSEMapPointer getReadableCopy();
  bool dropReference();
  void release();
  void print(raw_ostream& RSO, bool brief);
  static void mergeStores(DSEMapPointer* mergeFrom, DSEMapPointer* mergeTo, 
			  uint64_t ASize, MergeBlockVisitor<DSEMapPointer, DSEStoreExtraState>* Visitor);
  static void simplifyStore(DSEMapPointer*) { }
  bool derefWillAllowSimplify() { return false; }
  void useWriters(int64_t Offset, uint64_t Size);
  void setWriter(int64_t Offset, uint64_t Size, ShadowInstruction* SI);

};

struct DSEStoreExtraState {

  void copyFrom(const DSEStoreExtraState& es) { }
  static void doMerge(LocalStoreMap<DSEMapPointer, DSEStoreExtraState>* toMap, 
		      SmallVector<LocalStoreMap<DSEMapPointer, DSEStoreExtraState>*, 4>::iterator fromBegin, 
		      SmallVector<LocalStoreMap<DSEMapPointer, DSEStoreExtraState>*, 4>::iterator fromEnd,
		      bool verbose) {

  }
  static void dump(LocalStoreMap<DSEMapPointer, DSEStoreExtraState>*) { }

};

// Define types for the TL store:

typedef IntervalMap<uint64_t, bool, IntervalMapImpl::NodeSizer<uint64_t, bool>::LeafSize, HalfOpenWithMerge> TLMapTy;

class TLMapPointer;
extern TLMapPointer TLEmptyMapPtr;
class TLStoreExtraState;

struct TLMapPointer {

  TLMapTy* M;

TLMapPointer() : M(0) {}
TLMapPointer(TLMapTy* _M) : M(_M) {}
TLMapPointer(const TLMapPointer& other) : M(other.M) {}

  static TLMapPointer& getEmptyStore() {

    return TLEmptyMapPtr;

  }

  static bool LT(const TLMapPointer* a, const TLMapPointer* b) {

    return a->M < b->M;

  }

  static bool EQ(const TLMapPointer* a, const TLMapPointer* b) {

    return a->M == b->M;

  }

  static LocalStoreMap<TLMapPointer, TLStoreExtraState>* getMapForBlock(ShadowBB* BB);
  bool isValid() { return !!M; }
  void checkMergedResult() { }
  TLMapPointer getReadableCopy();
  bool dropReference();
  void print(raw_ostream& RSO, bool brief);
  static void mergeStores(TLMapPointer* mergeFrom, TLMapPointer* mergeTo, 
			  uint64_t ASize, MergeBlockVisitor<TLMapPointer, TLStoreExtraState>* Visitor);
  static void simplifyStore(TLMapPointer*) { }
  bool derefWillAllowSimplify() { return false; }
  
};

struct TLStoreExtraState {

  void copyFrom(const TLStoreExtraState& other) {  }

  static void doMerge(LocalStoreMap<TLMapPointer, TLStoreExtraState>* toMap, 
		      SmallVector<LocalStoreMap<TLMapPointer, TLStoreExtraState>*, 4>::iterator fromBegin, 
		      SmallVector<LocalStoreMap<TLMapPointer, TLStoreExtraState>*, 4>::iterator fromEnd,
		      bool verbose) { }

  static void dump(LocalStoreMap<TLMapPointer, TLStoreExtraState>*) { }

};

#include "SharedTree.h"

struct FDState {

  std::string filename;
  uint64_t pos;
  bool clean;

FDState() : filename(""), pos((uint64_t)-1), clean(false) {}
FDState(std::string fn) : filename(fn), pos(0), clean(false) {}
FDState(const FDState& Other) : filename(Other.filename), pos(Other.pos), clean(Other.clean) {}

};

struct FDStore {

  uint32_t refCount;
  std::vector<FDState> fds;

  bool dropReference() {

    bool ret = false;
    if(!(--refCount)) {
      ret = true;
      delete this;
    }
    return ret;

  }

  FDStore* getWritable() {

    if(refCount == 1)
      return this;

    release_assert(refCount);
    refCount--;
    return new FDStore(*this);

  }
  
FDStore() : refCount(1), fds() {}
FDStore(const FDStore& Other) : refCount(1), fds(Other.fds) {}

};

struct FDGlobalState {

  ShadowInstruction* SI;
  bool isCommitted;
  Value* CommittedVal;
  std::vector<std::pair<WeakVH, uint32_t> > PatchRefs;
  bool isFifo;

  FDGlobalState(ShadowInstruction* _SI, bool _isFifo);
  FDGlobalState(bool _isFifo);

  bool isAvailable();

};

struct CommittedBlock {

  BasicBlock* specBlock;
  BasicBlock* breakBlock;
  uint32_t startIndex;

CommittedBlock() : specBlock(0), breakBlock(0), startIndex(UINT_MAX) {}
CommittedBlock(BasicBlock* SB, BasicBlock* BB, uint32_t i) : specBlock(SB), breakBlock(BB), startIndex(i) {}

};

struct ShadowBB {

  IntegrationAttempt* IA;
  ShadowBBInvar* invar;
  bool* succsAlive;
  ShadowBBStatus status;
  ImmutableArray<ShadowInstruction> insts;

  OrdinaryLocalStore* localStore;
  DSELocalStore* dseStore;
  TLLocalStore* tlStore;
  FDStore* fdStore;

  SmallVector<CommittedBlock, 1> committedBlocks;
  
  bool useSpecialVarargMerge;
  bool inAnyLoop;

  ~ShadowBB() {

    delete[] &(insts[0]);
    delete[] succsAlive;

  }

  bool isMarkedCertain() {
    return status == BBSTATUS_CERTAIN;
  }

  bool isMarkedCertainOrAssumed() {
    return status == BBSTATUS_CERTAIN || status == BBSTATUS_ASSUMED;
  }

  bool edgeIsDead(ShadowBBInvar* BB2I) {

    bool foundLiveEdge = false;

    for(uint32_t i = 0; i < invar->succIdxs.size() && !foundLiveEdge; ++i) {

      if(BB2I->idx == invar->succIdxs[i]) {

	if(succsAlive[i])
	  foundLiveEdge = true;
	
      }

    }

    return !foundLiveEdge;

  }

  DenseMap<ShadowValue, LocStore>& getWritableStoreMapFor(ShadowValue&);
  DenseMap<ShadowValue, LocStore>& getReadableStoreMapFor(ShadowValue&);
  LocStore* getWritableStoreFor(ShadowValue&, int64_t Off, uint64_t Size, bool writeSingleObject);
  LocStore* getOrCreateStoreFor(ShadowValue&, bool* isNewStore);
  LocStore* getReadableStoreFor(const ShadowValue& V);
  void pushStackFrame(InlineAttempt*);
  void popStackFrame();
  void setAllObjectsMayAliasOld();
  void setAllObjectsThreadGlobal();
  void clobberMayAliasOldObjects();
  void clobberGlobalObjects();
  void clobberAllExcept(DenseSet<ShadowValue>& Save, bool verbose);
  BasicBlock* getCommittedBreakBlockAt(uint32_t);
  DSEMapPointer* getWritableDSEStore(ShadowValue O);
  TLMapPointer* getWritableTLStore(ShadowValue O);
  uint64_t getAllocSize(ShadowValue);
  FDStore* getWritableFDStore();

  void refStores() {
    ++localStore->refCount;
    ++fdStore->refCount;
    if(tlStore)
      ++tlStore->refCount;
    if(dseStore)
      ++dseStore->refCount;
  }
  void derefStores(std::vector<ShadowValue>* simplify = 0) {
    if(localStore->dropReference(simplify))
      localStore = 0;
    SAFE_DROP_REF(fdStore);
    if(tlStore)
      SAFE_DROP_REF(tlStore);
    if(dseStore)
      SAFE_DROP_REF(dseStore);
  }

  void takeStoresFrom(ShadowBB* Other, bool inLoopAnalyser) {
    localStore = Other->localStore;
    fdStore = Other->fdStore;
    if(!inLoopAnalyser) {
      tlStore = Other->tlStore;
      dseStore = Other->dseStore;
    }
    else {
      tlStore = 0;
      dseStore = 0;
    }
  }

};

struct FDStoreMerger : public ShadowBBVisitor {

  FDStore* newStore;

  SmallVector<ShadowBB*, 4> incomingBlocks;
  void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) { incomingBlocks.push_back(BB); }
  void doMerge();
  void merge2(FDStore* to, FDStore* from);

};

inline LocalStoreMap<LocStore, OrdinaryStoreExtraState>* LocStore::getMapForBlock(ShadowBB* BB) {

  return BB->localStore;

}

struct ShadowLoopInvar {

  uint32_t headerIdx;
  uint32_t preheaderIdx;
  uint32_t latchIdx;
  uint32_t nBlocks;
  std::pair<uint32_t, uint32_t> optimisticEdge;
  std::vector<uint32_t> exitingBlocks;
  std::vector<uint32_t> exitBlocks;
  std::vector<std::pair<uint32_t, uint32_t> > exitEdges;
  bool alwaysIterate;
  struct ShadowLoopInvar* parent;
  SmallVector<ShadowLoopInvar*, 1> childLoops;

  bool contains(const ShadowLoopInvar* Other) const {

    if(!Other)
      return false;
    else if(Other == this)
      return true;
    else
      return contains(Other->parent);

  }
  
};

class PathConditions;

struct ShadowFunctionInvar {

  ImmutableArray<ShadowBBInvar> BBs;
  ImmutableArray<ShadowArgInvar> Args;
  int32_t frameSize;
  
  PathConditions* pathConditions;
  SmallVector<ShadowLoopInvar*, 4> TopLevelLoops;
  
ShadowFunctionInvar() : frameSize(0), pathConditions(0) {}

};

ShadowBBInvar* ShadowBBInvar::getPred(uint32_t i) {
  return &(F->BBs[predIdxs[i]]);
}

uint32_t ShadowBBInvar::preds_size() { 
  return predIdxs.size();
}

ShadowBBInvar* ShadowBBInvar::getSucc(uint32_t i) {
  return &(F->BBs[succIdxs[i]]);
}
  
uint32_t ShadowBBInvar::succs_size() {
  return succIdxs.size();
}

extern Type* GInt8Ptr;
extern Type* GInt8;
extern Type* GInt16;
extern Type* GInt32;
extern Type* GInt64;

inline const MDNode* ShadowValue::getTBAATag() const {

  switch(t) {
  case SHADOWVAL_INST:
    return u.I->invar->I->getMetadata(LLVMContext::MD_tbaa);
  default:
    return 0;
  }

}

inline Value* ShadowValue::getBareVal() const {

  switch(t) {
  case SHADOWVAL_ARG:
    return u.A->invar->A;
  case SHADOWVAL_INST:
    return u.I->invar->I;
  case SHADOWVAL_GV:
    return u.GV->G;
  case SHADOWVAL_OTHER:
    return u.V;
  default:
    release_assert(0 && "Bad value type in getBareVal");
    llvm_unreachable("Bad value type in getBareVal");
  }

}

inline const ShadowLoopInvar* ShadowValue::getScope() const {

  switch(t) {
  case SHADOWVAL_INST:
    return u.I->invar->parent->outerScope;
  default:
    return 0;
  }
  
}

inline const ShadowLoopInvar* ShadowValue::getNaturalScope() const {

  switch(t) {
  case SHADOWVAL_INST:
    return u.I->invar->parent->naturalScope;
  default:
    return 0;
  }

}

extern bool isIdentifiedObject(const Value*);

inline bool ShadowValue::isIDObject() const {

  return isIdentifiedObject(getBareVal());

}

inline InstArgImprovement* ShadowValue::getIAI() const {

  switch(t) {
  case SHADOWVAL_INST:
    return &(u.I->i);
  case SHADOWVAL_ARG:
    return &(u.A->i);      
  default:
    return 0;
  }

}

inline LLVMContext& ShadowValue::getLLVMContext() const {
  switch(t) {
  case SHADOWVAL_INST:
    return u.I->invar->I->getContext();
  case SHADOWVAL_ARG:
    return u.A->invar->A->getContext();
  case SHADOWVAL_GV:
    return u.GV->G->getContext();
  case SHADOWVAL_PTRIDX:
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64:
    return GInt8Ptr->getContext();
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return GInt8->getContext();
  default:
    return u.V->getContext();
  }
}

inline void ShadowValue::setCommittedVal(Value* V) {
  switch(t) {
  case SHADOWVAL_INST:
    u.I->committedVal = V;
    break;
  case SHADOWVAL_ARG:
    u.A->committedVal = V;
    break;
  default:
    release_assert(0 && "Can't replace a value");
  }
}

template<class X> inline bool val_is(ShadowValue V) {
  switch(V.t) {
  case SHADOWVAL_OTHER:
    return isa<X>(V.u.V);
  case SHADOWVAL_GV:
    return isa<X>(V.u.GV->G);
  case SHADOWVAL_INST:
    return inst_is<X>(V.u.I);
  case SHADOWVAL_ARG: {
    if(!V.u.A->invar)
      return false;
    return isa<X>(V.u.A->invar->A);
  }
  default:
    release_assert(0 && "Bad value type in val_is");
    llvm_unreachable("Bad value type in val_is");
  }
}

template<class X> inline X* dyn_cast_val(ShadowValue V) {
  switch(V.t) {
  case SHADOWVAL_OTHER:
    return dyn_cast<X>(V.u.V);
  case SHADOWVAL_GV:
    return dyn_cast<X>(V.u.GV->G);
  case SHADOWVAL_ARG:
    return dyn_cast<X>(V.u.A->invar->A);
  case SHADOWVAL_INST:
    return dyn_cast_inst<X>(V.u.I);
  default:
    release_assert(0 && "Bad value type in dyn_cast_val");
    llvm_unreachable("Bad value type in dyn_cast_val");
  }
}

template<class X> inline X* cast_val(ShadowValue V) {
  switch(V.t) {
  case SHADOWVAL_OTHER:
    return cast<X>(V.u.V);
  case SHADOWVAL_GV:
    return cast<X>(V.u.GV->G);
  case SHADOWVAL_ARG:
    return cast<X>(V.u.A->invar->A);
  case SHADOWVAL_INST:
    return cast_inst<X>(V.u.I);
  default:
    release_assert(0 && "Cast of bad SV");
    llvm_unreachable("Cast of bad SV");
  }
}

static Constant* CIToConst(const ShadowValue V) {

  Type* CITy = V.getNonPointerType();
  return ConstantInt::get(CITy, V.u.CI, true);

}

inline Constant* getSingleConstant(const ShadowValue V) {

  if(V.t == SHADOWVAL_OTHER)
    return cast<Constant>(V.u.V);  
  else if(V.isConstantInt())
    return CIToConst(V);
  else {
    release_assert(0 && "getSingleConstant on non-constant");
    return 0;
  }

}

inline bool hasSingleConstant(const ImprovedValSet* IV) {

  const ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV);
  if(!IVS)
    return false;
  if(IVS->Overdef || IVS->Values.size() != 1 || IVS->SetType != ValSetTypeScalar)
    return false;  
  return true;

}

inline Constant* getSingleConstant(const ImprovedValSet* IV) {
  
  if(!hasSingleConstant(IV))
    return 0;
  return getSingleConstant(cast<ImprovedValSetSingle>(IV)->Values[0].V);

}

inline bool hasConstReplacement(const ShadowArg* SA) {

  if(!SA->i.PB)
    return false;
  return hasSingleConstant(SA->i.PB);

}

inline Constant* getConstReplacement(const ShadowArg* SA) {

  if(!SA->i.PB)
    return 0;
  return getSingleConstant(SA->i.PB);

}

inline bool hasConstReplacement(const ShadowInstruction* SI) {

  if(!SI->i.PB)
    return false;
  return hasSingleConstant(SI->i.PB);

}

inline Constant* getConstReplacement(const ShadowInstruction* SI) {

  if(!SI->i.PB)
    return 0;
  return getSingleConstant(SI->i.PB);

}

inline ImprovedValSet* getIVSRef(ShadowValue V);

inline bool hasConstReplacement(const ShadowValue SV) {

  switch(SV.t) {

  case SHADOWVAL_ARG:
  case SHADOWVAL_INST: 
    {
      ImprovedValSet* IVS = getIVSRef(SV);
      if(!IVS)
	return 0;
      return hasSingleConstant(IVS);
    }
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return true;
  case SHADOWVAL_OTHER:
  case SHADOWVAL_GV:
    return SV.getVal() && isa<Constant>(SV.getVal());
  default:
    release_assert(0 && "Bad SV type in hasConstReplacement");
    llvm_unreachable("Bad SV type in hasConstReplacement");

  }

}

inline Constant* getConstReplacement(ShadowValue SV) {

  switch(SV.t) {

  case SHADOWVAL_ARG:
  case SHADOWVAL_INST: 
    {
      ImprovedValSet* IVS = getIVSRef(SV);
      if(!IVS)
	return 0;
      return getSingleConstant(IVS);
    }
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return getSingleConstant(SV);
  case SHADOWVAL_OTHER:
  case SHADOWVAL_GV:
    return dyn_cast_or_null<Constant>(SV.getVal());
  default:
    release_assert(0 && "Bad SV type in getConstReplacement");
    llvm_unreachable("Bad SV type in getConstReplacement");

  }

}

inline ShadowValue tryGetConstReplacement(ShadowValue SV) {

  if(Constant* C = getConstReplacement(SV))
    return ShadowValue(C);
  else
    return SV;

}

inline bool tryGetConstantSignedInt(ShadowValue SV, int64_t& Out) {

  if(SV.getSignedCI(Out))
    return true;

  ConstantInt* CI;
  if(SV.isVal() && (CI = dyn_cast<ConstantInt>(SV.u.V))) {

    if(CI->getBitWidth() > 64)
      return false;

    Out = CI->getSExtValue();
    return true;
  }
  
  return false;
  
}

inline bool tryGetConstantInt(ShadowValue SV, uint64_t& Out) {

  if(SV.getCI(Out))
    return true;

  ConstantInt* CI;
  if(SV.isVal() && (CI = dyn_cast<ConstantInt>(SV.u.V))) {

    if(CI->getBitWidth() > 64)
      return false;

    Out = CI->getLimitedValue();
    return true;
  }

  return false;

}

inline bool tryGetConstantIntReplacement(ShadowValue SV, uint64_t& Out) {

  if(tryGetConstantInt(SV, Out))
    return true;

  switch(SV.t) {

  case SHADOWVAL_ARG:
  case SHADOWVAL_INST: 
    {
      ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(SV));
      if((!IVS) || IVS->Values.size() != 1)
	return false;
      return tryGetConstantInt(IVS->Values[0].V, Out);
    }
  default:
    return false;

  }

}

std::pair<ValSetType, ImprovedVal> getValPB(Value* V);

inline void getIVOrSingleVal(ShadowValue V, ImprovedValSet*& IVS, std::pair<ValSetType, ImprovedVal>& Single) {

  IVS = 0;

  switch(V.t) {

  case SHADOWVAL_INST:
  case SHADOWVAL_ARG:
    IVS = getIVSRef(V);
    break;
  case SHADOWVAL_GV:
    Single = std::make_pair(ValSetTypePB, ImprovedVal(V, 0));
    break;
  case SHADOWVAL_OTHER:
    Single = getValPB(V.u.V);
    break;
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64: 
    Single.first = ValSetTypeScalar;
    Single.second = V;
    break;
  default:
    release_assert(0 && "Bad value type in getIVOrSingleVal");
    llvm_unreachable("Bad value type in getIVOrSingleVal");
  }

}

inline bool tryGetUniqueIV(ShadowValue V, std::pair<ValSetType, ImprovedVal>& Out) {

  ImprovedValSet* IVS;
  getIVOrSingleVal(V, IVS, Out);
  if(!IVS)
    return true;
  
  ImprovedValSetSingle* IVSingle = dyn_cast<ImprovedValSetSingle>(IVS);
  if(!IVSingle)
    return true;

  if(IVSingle->Values.size() != 1)
    return false;

  Out.first = IVSingle->SetType;
  Out.second = IVSingle->Values[0];

  return true;

}

inline bool IVsEqualShallow(ImprovedValSet*, ImprovedValSet*);

inline bool IVMatchesVal(ShadowValue V, ImprovedValSet* IV) {

  ImprovedValSet* OtherIV = 0;
  std::pair<ValSetType, ImprovedVal> OtherSingle;
  getIVOrSingleVal(V, OtherIV, OtherSingle);

  if(OtherIV)
    return IVsEqualShallow(IV, OtherIV);

  ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV);
  if(!IVS)
    return false;
  
  if(OtherSingle.first == ValSetTypeOverdef)
    return IVS->Overdef;

  if(OtherSingle.first != IVS->SetType)
    return false;

  if(IVS->Values.size() != 1)
    return false;

  return IVS->Values[0] == OtherSingle.second;

}

inline bool getImprovedValSetSingle(ShadowValue V, ImprovedValSetSingle& OutPB) {

  switch(V.t) {

  case SHADOWVAL_INST:
  case SHADOWVAL_ARG:
    {
      ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(V));
      if(!IVS) {
	OutPB.setOverdef();
	return true;
      }
      else {
	OutPB = *IVS;
	return OutPB.isInitialised();
      }	
    }

  case SHADOWVAL_GV:
    OutPB.set(ImprovedVal(V, 0), ValSetTypePB);
    return true;
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64: 
    OutPB.set(V, ValSetTypeScalar);
    return true;
    
  case SHADOWVAL_OTHER:
    {
      std::pair<ValSetType, ImprovedVal> VPB = getValPB(V.getVal());
      if(VPB.first == ValSetTypeUnknown)
	return false;
      OutPB.set(VPB.second, VPB.first);
      return true;
    }



  default:
    release_assert(0 && "Bad value type in getImprovedValSetSingle");
    llvm_unreachable("Bad value type in getImprovedValSetSingle");

  }

}

inline ImprovedValSet* tryGetIVSRef(ShadowValue V) {

  switch(V.t) {
  case SHADOWVAL_INST:
    return V.u.I->i.PB;
  case SHADOWVAL_ARG:
    return V.u.A->i.PB;    
  default:
    return 0;
  }

}

inline ImprovedValSet* getIVSRef(ShadowValue V) {

  release_assert((V.t == SHADOWVAL_INST || V.t == SHADOWVAL_ARG) 
		 && "getIVSRef only applicable to instructions and arguments");
  
  return tryGetIVSRef(V);

}

// V must have an IVS.
inline void addValToPB(ShadowValue& V, ImprovedValSetSingle& ResultPB) {

  switch(V.t) {

  case SHADOWVAL_INST:
  case SHADOWVAL_ARG:
    {
      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(getIVSRef(V));
      if(!IVS->isInitialised())
	ResultPB.setOverdef();
      else
	ResultPB.merge(*IVS);
      return;
    }
  case SHADOWVAL_GV:
    ResultPB.mergeOne(ValSetTypePB, ImprovedVal(V, 0));
    return;
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64: 
    ResultPB.mergeOne(ValSetTypeScalar, V);
    return;
  case SHADOWVAL_OTHER:
    {
      std::pair<ValSetType, ImprovedVal> VPB = getValPB(V.getVal());
      if(VPB.first == ValSetTypeUnknown)
	ResultPB.setOverdef();
      else
	ResultPB.mergeOne(VPB.first, VPB.second);
    }
    return;

  default:
    release_assert(0 && "Bad value type in addValToPB");
    llvm_unreachable("Bad value type in addValToPB");
    
  }

}

inline bool getBaseAndOffset(ShadowValue SV, ShadowValue& Base, int64_t& Offset, bool ignoreNull = false) {

  ImprovedValSetSingle SVPB;
  if(!getImprovedValSetSingle(SV, SVPB))
    return false;

  if(SVPB.SetType != ValSetTypePB || SVPB.Overdef || SVPB.Values.size() == 0)
    return false;

  if(!ignoreNull) {
    if(SVPB.Values.size() != 1)
      return false;

    Base = SVPB.Values[0].V;
    Offset = SVPB.Values[0].Offset;
    return true;
  }
  else {

    bool setAlready = false;

    // Search for a unique non-null value:
    for(uint32_t i = 0, ilim = SVPB.Values.size(); i != ilim; ++i) {

      if(SVPB.Values[i].V.isVal() && isa<ConstantPointerNull>(SVPB.Values[i].V.getVal()))
	continue;

      if(!setAlready) {
	setAlready = true;
	Base = SVPB.Values[i].V;
	Offset = SVPB.Values[i].Offset;
      }
      else {
	Base = ShadowValue();
	return false;
      }

    }

    return setAlready;

  }

}

inline bool getBaseObject(ShadowValue SV, ShadowValue& Base) {

  int64_t ign;
  return getBaseAndOffset(SV, Base, ign);

}

inline bool getBaseAndConstantOffset(ShadowValue SV, ShadowValue& Base, int64_t& Offset, bool ignoreNull = false) {

  Offset = 0;
  bool ret = getBaseAndOffset(SV, Base, Offset, ignoreNull);
  if(Offset == LLONG_MAX)
    return false;
  return ret;

}

inline bool mayBeReplaced(InstArgImprovement& IAI) {

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(IAI.PB);
  if(!IVS)
    return false;
  return IVS->Values.size() == 1 && (IVS->SetType == ValSetTypeScalar ||
				       (IVS->SetType == ValSetTypePB && IVS->Values[0].Offset != LLONG_MAX) ||
				       IVS->SetType == ValSetTypeFD);
}

inline bool mayBeReplaced(ShadowInstruction* SI) {
  return mayBeReplaced(SI->i);
}

inline bool mayBeReplaced(ShadowArg* SA) {
  return mayBeReplaced(SA->i);
}

inline bool mayBeReplaced(ShadowValue SV) {

  switch(SV.t) {
  case SHADOWVAL_INST:
    return mayBeReplaced(SV.u.I);
  case SHADOWVAL_ARG:
    return mayBeReplaced(SV.u.A);
  default:
    return false;
  }

}

inline void deleteIV(ImprovedValSet* I);
inline ImprovedValSetSingle* newIVS();

inline void setReplacement(InstArgImprovement& IAI, Constant* C) {

  if(IAI.PB)
    deleteIV(IAI.PB);

  ImprovedValSetSingle* NewIVS = newIVS();
  IAI.PB = NewIVS;

  std::pair<ValSetType, ImprovedVal> P = getValPB(C);
  NewIVS->Values.push_back(P.second);
  NewIVS->SetType = P.first;

}

inline void setReplacement(ShadowInstruction* SI, Constant* C) {

  setReplacement(SI->i, C);

}

inline void setReplacement(ShadowArg* SA, Constant* C) {

  setReplacement(SA->i, C);

}

inline ShadowValue ShadowValue::stripPointerCasts() const {

  switch(t) {
  case SHADOWVAL_ARG:
  case SHADOWVAL_GV:
    return *this;
  case SHADOWVAL_INST:

    if(inst_is<CastInst>(u.I)) {
      ShadowValue Op = u.I->getOperand(0);
      return Op.stripPointerCasts();
    }
    else {
      return *this;
    }

  case SHADOWVAL_OTHER:
    return u.V->stripPointerCasts();
  default:
    release_assert(0 && "Bad val type in stripPointerCasts");
    llvm_unreachable("Bad val type in stripPointerCasts");
  }

}

inline bool ShadowValue::isNullOrConst() const {

  if(t == SHADOWVAL_GV)
    return u.GV->G->isConstant();
  else if(t == SHADOWVAL_PTRIDX)
    return false;

  return isa<ConstantPointerNull>(getBareVal());

}

inline bool ShadowValue::isNullPointer() const {

  switch(t) {
  case SHADOWVAL_OTHER:
    return isa<ConstantPointerNull>(u.V);
  default:
    return false;
  }

}

// Support functions for AA, which can use bare instructions in a ShadowValue.
// The caller always knows that it's either a bare or a shadowed instruction.

inline ShadowValue getValArgOperand(ShadowValue V, uint32_t i) {

  if(ShadowInstruction* SI = V.getInst())
    return SI->getCallArgOperand(i);
  else {
    CallInst* I = cast<CallInst>(V.getVal());
    return ShadowValue(I->getArgOperand(i));
  }

}


inline ShadowValue getValOperand(ShadowValue V, uint32_t i) {

  if(ShadowInstruction* SI = V.getInst())
    return SI->getOperand(i);
  else {
    Instruction* I = cast<Instruction>(V.getVal());
    return ShadowValue(I->getOperand(i));
  }

}

