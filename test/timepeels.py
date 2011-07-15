#!/usr/bin/python

import subprocess
from datetime import datetime

trytimes = [(2, 5000), (10, 500), (100, 50), (1000, 5), (5000, 1)]

for (peel, iters) in trytimes:
    start_time = datetime.now()
    subprocess.Popen(["./iterpeel.py", str(peel), str(iters), "wc-test-4.bc", "wc-opt.bc"]).wait()
    elapsed = datetime.now() - start_time
    print "Peeling", peel, "x", iters, "iterations took", elapsed
