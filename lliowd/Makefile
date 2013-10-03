top: lliowd testlib liblliowd.a liblliowd-uclibc.a

%.o: %.cpp
	g++ $^ -c -o $@ -O3 -std=gnu++11 -I. -ggdb3

%.o: %.c
	gcc $^ -c -o $@ -O3 -std=gnu99 -I. -ggdb3

%.uclibc-o: %.c
	/usr/bin/llvm-gcc-uclibc $^ -c -o $@ -O3 -std=gnu99 -I.

lliowd: main.o
	g++ $^ -o $@ -lcrypto

liblliowd.a: clientlib.o
	ar rcs $@ $^

liblliowd-uclibc.a: clientlib.uclibc-o
	ar rcs $@ $^

testlib: testlib.o liblliowd.a
	gcc testlib.o -o $@ -llliowd -L.

clean:
	rm *.a *.o *.uclibc-o
