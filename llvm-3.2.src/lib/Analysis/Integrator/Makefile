# Path to top level of LLVM hierarchy
LEVEL = ../../..

# Name of the library to build
LIBRARYNAME = IntegratorAnalyses

# Make the shared library become a loadable module so the tools can 
# dlopen/dlsym on the resulting library.
LOADABLE_MODULE = 1

# Include the makefile implementation stuff
include $(LEVEL)/Makefile.common

CFLAGS = $(CFLAGS) -I $(LEVEL)/../release_32/include
LIBS += -lcrypto
