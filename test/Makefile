
include ../Makefile.common

all: wc-test wc-plain wc-stdio-plain wc-stdio-test

wc-stdio-test: wc-stdio-test-2.bc
	$(CC) $(CFLAGS) -o wc-stdio-test -Wl,--wrap=open -Wl,--wrap=read -Wl,--wrap=close wc-stdio-test-2.bc -lpthread

wc-stdio-test-2.bc: wc-stdio-test-1.bc ../fake_fd_table.bc ../wrappers.bc
	llvm-ld -o wc-stdio-test-2.bc -link-as-library -export-dynamic wc-stdio-test-1.bc ../fake_fd_table.bc ../wrappers.bc

wc-stdio-test-1.bc: wc-stdio.bc ../fake_fd_table.bc ../wrappers.bc ../alias.bc match.bc data.bc
	llvm-ld -o wc-stdio-test-1.bc -link-as-library ../*.bc match.bc data.bc wc-stdio.bc

wc-stdio-plain: wc-stdio.bc
	$(CC) $(CFLAGS) wc-stdio.bc -o wc-stdio-plain

wc-test: wc-test-4.bc
	$(CC) $(CFLAGS) -o wc-test -Wl,--wrap=open -Wl,--wrap=read -Wl,--wrap=close wc-test-4.bc -lpthread

wc-test-4.bc: wc-test-2.bc
	opt wc-test-2.bc -o wc-test-3.bc -std-compile-opts
	opt wc-test-3.bc -o wc-test-4.bc -std-compile-opts

wc-test-2.bc: wc-test-1.bc ../fake_fd_table.bc ../wrappers.bc
	llvm-ld -o wc-test-2.bc -link-as-library -export-dynamic wc-test-1.bc ../fake_fd_table.bc ../wrappers.bc

wc-test-1.bc: wc.bc ../fake_fd_table.bc ../wrappers.bc ../alias.bc match.bc data.bc
	llvm-ld -o wc-test-1.bc -link-as-library ../*.bc match.bc data.bc wc.bc

wc-plain: wc.bc
	$(CC) $(CFLAGS) wc.bc -o wc-plain 

match.bc: match.c data.h
	$(CC) $(CFLAGS) -o match.bc -c -g match.c

data.bc: data.c data.h
	$(CC) $(CFLAGS) -o data.bc -c -g data.c

data.h: /tmp/chars
	../cstringify.py /tmp/chars

match.c: /tmp/chars
	../cstringify.py /tmp/chars

data.c: /tmp/chars
	../cstringify.py /tmp/chars

wc.bc: wc.c bufsize.h
	$(CC) $(CFLAGS) -o wc.bc -c -g -std=c99 wc.c

wc-stdio.bc: wc-stdio.c
	$(CC) $(CFLAGS) -o wc-stdio.bc -c -g -std=c99 wc-stdio.c

cleanish:
	rm *.bc
	rm wc-plain wc-test wc-stdio-plain wc-stdio-test

clean:
	rm *.bc
	rm data.h
	rm data.c
	rm match.c
	rm wc-plain wc-test wc-stdio-plain wc-stdio-test