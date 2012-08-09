# Path to top level of LLVM hierarchy
LEVEL = ../../..

# Name of the library to build
LIBRARYNAME = IntegratorTransforms

# Make the shared library become a loadable module so the tools can 
# dlopen/dlsym on the resulting library.
LOADABLE_MODULE = 1

CPPFLAGS += -I/usr/local/lib/wx/include/gtk2-unicode-2.9 -I/usr/local/include/wx-2.9 -D_FILE_OFFSET_BITS=64 -DWXUSINGDLL -D__WXGTK__ -pthread

# Include the makefile implementation stuff
include $(LEVEL)/Makefile.common

LIBS += -L/usr/local/lib -pthread   -lwx_gtk2u_xrc-2.9 -lwx_gtk2u_html-2.9 -lwx_gtk2u_qa-2.9 -lwx_gtk2u_adv-2.9 -lwx_gtk2u_core-2.9 -lwx_baseu_xml-2.9 -lwx_baseu_net-2.9 -lwx_baseu-2.9


