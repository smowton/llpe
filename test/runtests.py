#!/usr/bin/python

import subprocess
import os
import os.path

def isinstline(x):

	return x.rstrip() != '' and x[0:2] == '  '

subprocess.check_call(["/usr/bin/make", "-C", "progs"])

find_proc = subprocess.Popen(["/usr/bin/find", "progs", "-type", "f", "-executable"], stdout=subprocess.PIPE)

for prog in find_proc.stdout:

	workingdir = os.path.join(os.getcwd(), "progs")

	prog = "../%s" % prog.strip()
	if prog.endswith("-opt"):
		continue

	progopt = "%s-opt" % prog

	prog_proc = subprocess.Popen(prog, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=workingdir)
	prog_proc.stdin.close()
	progopt_proc = subprocess.Popen(progopt, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=workingdir)
	progopt_proc.stdin.close()

	prog_out = prog_proc.stdout.read()
	progopt_out = progopt_proc.stdout.read()

	if prog_out != progopt_out:
		print prog, "and", progopt, "outputs differ!"

	if prog_proc.wait() != progopt_proc.wait():
		print prog, "and", progopt, "return codes differ!"

	optbc = "%s.bc" % progopt

	disproc = subprocess.Popen(["/usr/bin/llvm-dis", "-o", "-", optbc], stdout=subprocess.PIPE, cwd=workingdir)

	asm = disproc.stdout.read()
	disproc.wait()

	lines = asm.split("\n")

	startidx = None
	endidx = None
	inmain = False
	for i, x in enumerate(lines):
		if x.startswith("define i32 @main"):
			inmain = True
			startidx = i
		elif inmain and x.startswith("}"):
			endidx = i
			break
		
	if startidx is None or endidx is None:
		print "Couldn't count instructions for test", prog
		continue

	lines = lines[startidx:endidx]

	lines = filter(isinstline, lines)

	print "Test", prog, "optimised down to", len(lines), "instructions"
	
