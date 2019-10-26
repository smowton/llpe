---
layout: page
title: Build Instructions
permalink: /build/
---

This page describes how to build LLPE from source. There are currently two versions: an LLVM 3.2 build that is no longer updated, and the development trunk which currently builds against LLVM 6-9 and 3.6-3.8, and will be updated to future LLVM releases as they arise.

Building has only been tested under Linux and using the x86-64 architecture; other operating systems and architectures may work, but specialisation may be incorrect due to assumptions about endian-ness and the kernel API used by subject programs.

Building LLPE Trunk
-------------------

LLPE is distributed as an out-of-tree LLVM module. It builds against at least LLVM 6-9, 3.6-3.8, and possibly earlier or later versions (definitely not 3.2, which has some incompatible changes; however see Building LLPE 3.2 below). It requires LLVM's CMake support files, which are produced when building from source using CMake and may or may not be provided with binary distributions (check for <tt>INSTALL\_PREFIX/share/llvm/cmake/LLVMConfig.cmake</tt>). The LLVM header files are also required, which are likely distributed as a <tt>-dev</tt> or <tt>-devel</tt> package.

Note that LLVM releases are not generally API compatible, which means that LLPE built against LLVM x.y should only be used with the <tt>opt</tt> program belonging to that same version of LLVM. Point releases (x.y.z) are more likely to be compatible, but if problems occur checking for version incompatibility is always a good idea.

Build steps:

1. Install dependencies. Right now we need wxWdigets to provide our GUI and OpenSSL (specifically libcrypto) to compute SHA-1 checksums. Install at least wxWidgets version 2.9, which is routinely included with Linux distros.

2. Checkout from Github:

    ```
    git clone https://github.com/smowton/llpe.git
    ```

3. The current master builds against LLVM 9. If you're using any of the other supported versions (3.6-3.8, 6.0, 7 or 8), run <tt>git checkout 3.7</tt> or similar to check out the appropriate branch (note in keeping with upstream's practices, 6.0 is the last version with two digits; the branches for 7+ are simply named '7', '8' and '9').

4. Make a build directory; run CMake:

    ```
    mkdir llpe/build
    cd llpe/build
    cmake ../llpe
    ```

    You should give CMake a build type compatible with the LLVM distribution you're compiling against (e.g. a Debug LLPE build will not build against a Release LLVM). For example, pass <tt>-D CMAKE\_BUILD\_TYPE:STRING=RelWithDebInfo</tt>.

    If you're building against an LLVM build that hasn't been installed, or CMake doesn't find the installed distribution in its default search path, you might need to include a parameter like <tt>-D CMAKE\_PREFIX\_PATH=/path/to/my/llvm-3.6-build</tt>

5. Build:

    ```
    make
    ```

If all works out, you should get build/driver/libLLVMLLPEDriver.so, build/main/libLLVMLLPEMain.so and build/utils/libLLVMLLPEUtils.so

Next try the [tutorial](/tutorial/)

Building LLPE 3.2
-----------------

This version of LLPE was distributed with a tweaked LLVM 3.2 source tree; this might present you with difficulties if this means concurrently hosting an unmodified LLVM 3.2 and LLPE's modified version. Generally if at all possible you should use trunk instead.

This version of LLPE uses autotools rather that CMake.

Build steps:

1. Install dependencies (as above, just wxWidgets 2.9+ and OpenSSL)

2. Checkout from Github:

    ```
    git clone https://github.com/smowton/llpe.git
    git checkout 3.2
    ```

3. Build LLVM per the LLVM 3.2 [autotools build instructions](http://llvm.org/releases/3.2/docs/GettingStarted.html). Based on experience developing the LLVM 3.6 port there are some errors in debug messages that are usually #ifdef'd out; I recommend building either Release or Release+Asserts, which are better tested; alternatively if you want to build Debug you can just comment out the problematic debug messages.

4. Build the LLPE passes. If you're using an in-tree build:

    ```
    cd /path/to/llpe/llvm-3.2.src
    cd lib/Analysis/Integrator
    make
    cd ../../Transforms/Integrator
    make
    ```

If all goes well you should get (for example) Release+Debug/lib/IntegratorAnalyses.so and IntegratorTransforms.so.

Next try the [tutorial](/tutorial/)
