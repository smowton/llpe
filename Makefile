
include Makefile.common

all: fake_fd_table.bc wrappers.bc alias.bc

alias.bc: alias.ll
	llvm-as alias.ll

wrappers.bc: wrappers.c
	$(CC) $(CFLAGS) -g -std=c99 -c wrappers.c -o wrappers.bc

fake_fd_table.bc: fake_fd_table.c
	$(CC) $(CFLAGS) -c -g fake_fd_table.c -o fake_fd_table.bc

clean:
	rm *.bc