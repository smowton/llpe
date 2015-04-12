---
layout: page
title: Build Instructions
permalink: /build.md
---

This page describes how to build LLPE from source. There are currently two versions: an LLVM 3.2 build that is no longer updated, and the development trunk which currently builds against LLVM 3.6 and will be updated to future LLVM releases as they arise.

Building has only been tested under Linux and using the x86-64 architecture; other operating systems and architectures may work, but specialisation may be incorrect due to assumptions about endian-ness and the kernel API used by subject programs.

Building LLPE Trunk
-------------------

LLPE is distributed as an out-of-tree LLVM module. It builds against at least LLVM 3.6, and possibly earlier or later versions (definitely not 3.2, which has some incompatible changes; however see Building LLPE 3.2 below). It requires LLVM's CMake support files, which are produced when building from source using CMake and may or may not be provided with binary distributions (check for <pre>INSTALL_PREFIX/share/llvm/cmake/LLVMConfig.cmake</pre>)

Build steps:

1. Install dependencies. Right now we need wxWdigets to provide our GUI. Install at least version 2.9, which is routinely included with Linux distros.

2. Checkout from Github:

   git clone https://github.com/smowton/llpe.git

3. Make a build directory; run CMake:

   mkdir llpe/build
   cd llpe/build
   cmake ../llpe

You should give CMake a build type compatible with the LLVM distribution you're compiling against (e.g. a Debug LLPE build will not build against a Release LLVM). For example, pass <pre>-D CMAKE_BUILD_TYPE:STRING=RelWithDebInfo</pre>.

If you're building against an LLVM build that hasn't been installed, or CMake doesn't find the installed distribution in its default search path, you might need to include a parameter like <pre>-D CMAKE_PREFIX_PATH=/path/to/my/llvm-3.6-build

4. Build:

   make

If all works out, you should get build/driver/libLLVMLLPEDriver.so and build/main/libLLVMLLPEMain.so

Building LLPE 3.2
-----------------

This version of LLPE was distributed with a tweaked LLVM 3.2 source tree; this might present you with difficulties if this means concurrently hosting an unmodified LLVM 3.2 and LLPE's modified version. Generally if at all possible you should use trunk instead.

This version of LLPE uses autotools rather that CMake.

Build steps:

1. Install dependencies (as above, just wxWidgets 2.9 +)

2. Checkout from Github:

   git clone https://github.com/smowton/llpe.git
   git checkout 3.2

3. Build LLVM per the LLVM 3.2 [autotools build instructions](http://llvm.org/releases/3.2/docs/GettingStarted.html). Based on experience developing the LLVM 3.6 port there are some errors in debug messages that are usually #ifdef'd out; I recommend building either Release or Release+Asserts, which are better tested; alternatively if you want to build Debug you can just comment out the problematic debug messages.

4. Build the LLPE passes:

   cd /path/to/llpe/llvm-3.2.src