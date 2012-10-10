#!/usr/bin/python

import subprocess
import sys
import os

if len(sys.argv) < 2:
	print "Usage: show.py bc-file function1 function2..."
	sys.exit(1)

os.chdir("/tmp")

opt_args = ["opt", "-strip-debug", "-dot-cfg", "-analyze"]
for a in sys.argv[2:]:
	opt_args.extend(["-dot-print-fn", a])
opt_args.append(sys.argv[1])

subprocess.check_call(opt_args)

for a in sys.argv[2:]:
	subprocess.check_call(["dot", "-Tpdf", "-o", "/tmp/cfg.%s.pdf" % a, "/tmp/cfg.%s.dot" % a])
	subprocess.check_call(["evince", "cfg.%s.pdf" % a])

