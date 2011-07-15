#!/usr/bin/python

import subprocess
import sys
import tempfile
import shutil
import os

if len(sys.argv) < 2:
    print >>sys.stderr, "Usage: vfs_graph.py myprog.c"
    sys.exit(1)

dirname = tempfile.mkdtemp()
opt_args = ["opt"]

if sys.argv[1][-2:] == ".c":
    subprocess.check_call(["llvm-gcc", sys.argv[1], "-std=c99", "-O4", "-c", "-emit-llvm", "-o", "/tmp/vfs_graph_temp.bc"])
    input_file = "/tmp/vfs_graph_temp.bc"
    opt_args.append("-raiseopencalls")
else:
    input_file = sys.argv[1]

opt_args.extend(["-simplevfsgraphs", "-simplevfs-graphout", dirname, input_file])
subprocess.check_call(opt_args)
for dot_filename in os.listdir(dirname):
    subprocess.check_call(["dot", "-Tpdf", "-o", "/tmp/vfs_graph_temp.pdf", os.path.join(dirname, dot_filename)])
    subprocess.check_call(["evince", "/tmp/vfs_graph_temp.pdf"])

shutil.rmtree(dirname)

