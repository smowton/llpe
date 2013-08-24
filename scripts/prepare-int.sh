#!/bin/bash

# Rotate loops so they can be peeled; instcombine and jump thread to eliminate the silly results of loop-rotate (e.g. trivially constant comparisons and jumps).
/usr/bin/opt -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorTransforms.so -strip-debug -functionattrs -mergereturn -loop-rotate -instcombine -jump-threading -simplifycfg -globalopt -loop-simplify -lcssa $@
