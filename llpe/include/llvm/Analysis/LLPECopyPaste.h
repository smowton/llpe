
#ifndef LLPECP_H
#define LLPECP_H

#include <stdint.h>

namespace llvm {

  class Constant;
  class DataLayout;
  class Type;
  template<class> class SmallVectorImpl;
  class Value;

  bool XXXReadDataFromGlobal(Constant *C, uint64_t ByteOffset,
			     unsigned char *CurPtr, unsigned BytesLeft,
			     const DataLayout &TD);

  Type* XXXFindElementAtOffset(Type *Ty, int64_t Offset,
			       SmallVectorImpl<Value*> &NewIndices,
			       const DataLayout* TD);

} // End namespace llvm

#endif
