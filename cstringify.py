#!/usr/bin/python

import sys
import re
from optparse import OptionParser

parser = OptionParser()
parser.add_option("-d", "--data-file", dest="datafile", default="data.c",
                  help="Filename to write data strings", metavar="FILE")
parser.add_option("-s", "--syscall-file", dest="syscallfile", default="match.c",
                  help="Filename to write syscall wrappers", metavar="FILE")
parser.add_option("-e", "--header-file", dest="headerfile", default="data.h",
                  help="Filename to write C headers", metavar="FILE")

(options, args) = parser.parse_args()

out_data = open(options.datafile, "w")
out_syscalls = open(options.syscallfile, "w")
out_header = open(options.headerfile, "w")

def print_string_of_file(name, out):

    fd = open(name, "r")
    bytes = 0

    while True:
        nextc = fd.read(1)
        if nextc == "":
            break
        bytes += 1
        out.write("\\x%.2x" % ord(nextc))

    return bytes

def escape_backslashes(fname):
    return re.sub(r"\\", r"\\\\", fname)

def escape_c_identifier(fname):
    return_str = ""
    for c in fname:
        match = re.match(r"[^0-9a-zA-Z]", c)
        if match is None:
            return_str += c
        else:
            return_str += ("_%d_" % ord(c))
    return return_str

out_syscalls.write("#include \"%s\"\n" % options.headerfile)
out_syscalls.write("#include <string.h>\n\n")
out_syscalls.write("char* get_chars_of_file(char* name) {\n")

file_lengths = dict()
c_identifiers = dict()
strings = dict()

for fname in args:
    c_identifiers[fname] = escape_c_identifier(fname)
    strings[fname] = escape_backslashes(fname)

for fname in args:
    out_data.write("char* %s = \"" % c_identifiers[fname])
    file_lengths[fname] = print_string_of_file(fname, out_data)
    out_data.write("\";\n")
    out_header.write("extern char* %s;\n" % c_identifiers[fname])
    out_syscalls.write("\tif(!strcmp(\"%s\", name))\n" % strings[fname])
    out_syscalls.write("\t\treturn %s;\n" % c_identifiers[fname])

out_syscalls.write("\treturn 0;\n")
out_syscalls.write("}\n\n")

out_syscalls.write("int get_length_of_file(char* name) {\n")

for fname in args:
    out_data.write("int %s_len = %d;\n" % (c_identifiers[fname], file_lengths[fname]))
    out_header.write("extern int %s_len;\n" % c_identifiers[fname])
    out_syscalls.write("\tif(!strcmp(\"%s\", name))\n" % strings[fname])
    out_syscalls.write("\t\treturn %s_len;\n" % c_identifiers[fname])

out_syscalls.write("\treturn 0;\n")
out_syscalls.write("}\n\n")




