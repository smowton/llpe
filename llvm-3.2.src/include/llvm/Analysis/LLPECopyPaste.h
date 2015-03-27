
#ifndef LLPECP_H
#define LLPECP_H

#include <stdint.h>

namespace llvm {

  class Constant;
  class DataLayout;

  bool XXXReadDataFromGlobal(Constant *C, uint64_t ByteOffset,
			     unsigned char *CurPtr, unsigned BytesLeft,
			     const DataLayout &TD);

} // End namespace llvm

#endif
