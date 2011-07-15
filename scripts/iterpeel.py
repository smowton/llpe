#!/usr/bin/python

import sys
import subprocess
import os

peelcount = int(sys.argv[1])
itercount = int(sys.argv[2])
infile = sys.argv[3]
outfile = sys.argv[4]

print "Iteratively peeling", infile, itercount, "times x", peelcount, "peels per run."

devnull = open("/dev/null", "w")

for i in range(itercount):
    subprocess.Popen(["opt", "-loop-peel", "-peel-count", str(peelcount), "-peel-depth-limit", "1", "-std-compile-opts", "-o", outfile, infile]).wait()
    infile = outfile
    if i % 10 == 0:
        print "Progress:", i, "/", itercount
        subprocess.Popen(["stat", "-c", "%s", outfile]).wait()

