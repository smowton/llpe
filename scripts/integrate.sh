#!/bin/bash

# Rotate loops so they can be peeled; instcombine and jump thread to eliminate the silly results of loop-rotate (e.g. trivially constant comparisons and jumps).
# We then jump thread again because the integrator leaves lots of empty blocks lying about and we might as well automate the cleanup process.
opt -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorTransforms.so -loop-rotate -instcombine -jump-threading -loopsimplify -lcssa -integrator -jump-threading $1 -o $2 $3
