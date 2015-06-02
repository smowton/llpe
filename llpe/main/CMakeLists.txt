
find_package(OpenSSL REQUIRED)
include_directories(${OPENSSL_INCLUDE_DIR})

add_library(LLVMLLPEMain MODULE ArgSpec.cpp FunctionSharing.cpp MainLoop.cpp Shadows.cpp CFGEval.cpp Eval.cpp NewStats.cpp TentativeLoads.cpp ConditionalSpec.cpp IAWalkers.cpp PartialLoadForward.cpp TLDump.cpp CopyPaste.cpp IntBenefit.cpp PostCommit.cpp VFSCallModRef.cpp DIE.cpp IntConstFold.cpp Print.cpp VFSOps.cpp DOT.cpp IntegratorShared.cpp Save.cpp DSE.cpp LoadForward.cpp SaveSplit.cpp Misc.cpp Selective.cpp)

target_link_libraries(LLVMLLPEMain ${OPENSSL_LIBRARIES})

