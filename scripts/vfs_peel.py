#!/usr/bin/python

import subprocess
import sys

if len(sys.argv) < 2:
    print "Usage: vfs_peel.py filename [args for opt...]"
    sys.exit(1)

opt_args = ["opt", "-loopsimplify", "-simplevfsloops", "-analyze", sys.argv[1]]
opt_proc = subprocess.Popen(opt_args, stdout=subprocess.PIPE)

peels = []

for line in opt_proc.stdout:
    idx = line.find("Should peel")
    if idx != -1:
        peels.append(line[12:-1])
    elif line.find("Could peel") != -1:
        print "Ignoring could-peel", line[11:-1]

ret = opt_proc.wait()
if ret != 0:
    raise Exception("Running %s returned %d" % (opt_args, ret))

if len(peels) == 0:
    print "Nothing to do"
    sys.exit(0)

opt_args = ["opt", "-loop-peel", "-peel-count", "2"]
opt_args.extend(sys.argv[1:])
for peel in peels:
    print "Peeling", peel
    opt_args.extend(["-peel-header", peel])

subprocess.check_call(opt_args)
