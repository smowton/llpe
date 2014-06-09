# Path to top level of LLVM hierarchy
LEVEL = ../../..

# Name of the library to build
LIBRARYNAME = IntegratorTransforms

# Make the shared library become a loadable module so the tools can 
# dlopen/dlsym on the resulting library.
LOADABLE_MODULE = 1

CPPFLAGS += `wx-config --cppflags`

# Include the makefile implementation stuff
include $(LEVEL)/Makefile.common

LIBS += `wx-config --libs`


