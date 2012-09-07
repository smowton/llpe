#!/bin/bash

# Rotate loops so they can be peeled; instcombine and jump thread to eliminate the silly results of loop-rotate (e.g. trivially constant comparisons and jumps).
opt -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorTransforms.so -loop-rotate -instcombine -jump-threading -loopsimplify -lcssa -integrator $1 -o $2 $3
