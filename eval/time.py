#!/usr/bin/python

import subprocess
import sys
import numpy

nul = open("/dev/null", "w")

runtimes = []

for i in range(int(sys.argv[1])):

	with open("/var/run/user/chris/py-runtime", "w") as timesf:
		subprocess.check_call(sys.argv[2:], stdout=nul, stderr=timesf)
	with open("/var/run/user/chris/py-runtime", "r") as timesf:
		lines = timesf.readlines()
		ss = int(lines[0], 16)
		sn = int(lines[1], 16)
		fs = int(lines[2], 16)
		fn = int(lines[3], 16)
		runtime_ns = (((fs * 1000000000) + fn) - ((ss * 1000000000) + sn))
		runtimes.append(runtime_ns)

print "Got", len(runtimes), "results, mean", numpy.mean(runtimes), "sd", numpy.std(runtimes)

