
wc-stdio-test: wc-stdio.o ../fake_fd_table.o ../wrappers.o match.o data.o data.h
	g++ -o wc-stdio-test -Wl,--wrap=open -Wl,--wrap=read -Wl,--wrap=close ../*.o match.o data.o wc-stdio.o -lpthread

wc-stdio-plain: wc-stdio.o
	gcc wc-stdio.o -o wc-stdio-plain

wc-test: wc.o ../fake_fd_table.o ../wrappers.o match.o data.o data.h
	g++ -o wc-test -Wl,--wrap=open -Wl,--wrap=read -Wl,--wrap=close ../*.o match.o data.o wc.o -lpthread

wc-plain: wc.o
	gcc wc.o -o wc-plain 

match.o: match.c data.h
	gcc -c -g match.c

data.o: data.c data.h
	gcc -c -g data.c

data.h: /tmp/chars
	../cstringify.py /tmp/chars

match.c: /tmp/chars
	../cstringify.py /tmp/chars

data.c: /tmp/chars
	../cstringify.py /tmp/chars

wc.o: wc.c
	gcc -c -g -std=c99 wc.c

wc-stdio.o: wc-stdio.c
	gcc -c -g -std=c99 wc-stdio.c

clean:
	rm *.o
	rm data.h
	rm data.c
	rm match.c