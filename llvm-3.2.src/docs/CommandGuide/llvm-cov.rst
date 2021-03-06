llvm-cov - emit coverage information
====================================


SYNOPSIS
--------


**llvm-cov** [-gcno=filename] [-gcda=filename] [dump]


DESCRIPTION
-----------


The experimental **llvm-cov** tool reads in description file generated by compiler
and coverage data file generated by instrumented program. This program assumes
that the description and data file uses same format as gcov files.


OPTIONS
-------



**-gcno=filename]**

 This option selects input description file generated by compiler while instrumenting
 program.



**-gcda=filename]**

 This option selects coverage data file generated by instrumented compiler.



**-dump**

 This options enables output dump that is suitable for a developer to help debug
 **llvm-cov** itself.




EXIT STATUS
-----------


**llvm-cov** returns 1 if it cannot read input files. Otherwise, it exits with zero.
