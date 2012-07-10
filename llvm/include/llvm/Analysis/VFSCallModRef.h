
#include <llvm/Analysis/LibCallSemantics.h>
#include <llvm/Analysis/LibCallAliasAnalysis.h>

namespace llvm {

class AliasAnalysis;

class VFSCallModRef : public LibCallInfo {

public:

  VFSCallModRef() { }
 
  virtual unsigned getLocationInfo(const LibCallLocationInfo *&Array) const;
    
  /// getFunctionInfoArray - Return an array of descriptors that describe the
  /// set of libcalls represented by this LibCallInfo object.  This array is
  /// terminated by an entry with a NULL name.
  virtual const LibCallFunctionInfo *getFunctionInfoArray() const; 
 
};

class VFSCallAliasAnalysis : public LibCallAliasAnalysis {

 public:
  static char ID;
 VFSCallAliasAnalysis() : LibCallAliasAnalysis(ID, new VFSCallModRef()) { }

};

} // end namespace llvm
