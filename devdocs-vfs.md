---
layout: page
title: Developer Documentation - Specialising with respect to files and input streams
permalink: /devdocs-vfs/
---

LLPE can specialise programs with respect to the contents of files or the standard input stream. In the former case this permits `open` and other system calls to run at specialisation time and introduces a check against concurrent modification of the target file at runtime. In the latter case it simply uses `memcmp` to check that the stream is as expected. Reads from either input source become copies from global constant data in the final program; `seek` calls are introduced to ensure that file descriptors are positioned appropriately.

This support is not completely safe, as it is possible for an outside program to observe actual I/O operations using mechanisms like `strace` or the `proc` filesystem. However, assuming these can be regarded as private implementation details rather than part of the program's public interface, it should produce a specialised program which is observably equivalent to the original but which doesn't perform actual I/O (or derived computation) at runtime.

This is all implemented by documenting the side-effects of many Linux system calls (see `VFSCallModRef.cpp`) and providing a symbolic implementation for some (see `VFSOps.cpp`). A symbolic file descriptor table is propagated along with the symbolic store used for memory operations; `open` calls insert symbolic file descriptors and `read` operations and similar manipulate them. We determine whether `read` needs to turn into `seek` or can be omitted completely by checking whether the specialised program will contain a subsequent read or other operation that reads the file offset.

Runtime checks against file modification depend on a helper daemon called `lliowd`, which uses `inotify` et al to determine whether we need to branch to unspecialised code to handle a file dependency which is not as expected.

The implementation currently allows the program to consume any file that isn't in a blacklisted location like `/dev`. It should probably be fixed to take explicit permission instead of blacklisting like this.