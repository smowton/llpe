---
layout: page
title: Developer Documentation - Conditional Specialisation
permalink: /devdocs-conditional/
---

Users generating specialised programs commonly want them to check that a particular specialisation is applicable at runtime -- for example, to generate a specialised variant of a particular function for the case that it is given particular arguments, then at runtime dispatch to either the specialised or the general function depending on the actual arguments. LLPE provides this support using *path conditions*, which are assertions about arguments and instruction results. Several different forms of command-line parameter are provided for convenience, but in general the user gets to make an assertion about a particular piece of memory or immediate value as of a particular basic block, or immediately upon definition.

Path conditions have the effect of writing their asserted value to memory (or returning the value as an immediate), while introducing a check and branch to unspecialised code in the resulting program. The code for generating unspecialised code is shared with similar check-failing branches due to the checks against thread interference, and is implemented in `ConditionalSpec.cpp`.

Alternatively, the user can provide an arbitrary function which makes some composite assertion, and another function that checks it holds at runtime. The first will be executed symbolically (so e.g. it should write symbolic memory with the values we want to assume) and the second will be concretely executed at runtime to make sure the specialisation is valid. The symbolic function is represented by an ordinary `InlineAttempt` which is executed as if there was a call at the top of the annotated basic block.

Introducing checks like these has significant implications for the dead store and instruction elimination passes, which need to know that potential branches to unspecialised code may mean that apparently-useless code will actually be needed at runtime after all. Checks also require the structure of the emitted code to be changed, perhaps introducing a mid-block branch.

