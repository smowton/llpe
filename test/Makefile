
wc-test: wc.o ../fake_fd_table.o ../wrappers.o match.o data.o data.h
	g++ -o wc-test -Wl,--wrap=open -Wl,--wrap=read -Wl,--wrap=close ../*.o *.o -lpthread

match.o: match.c data.h
	gcc -c match.c

data.o: data.c data.h
	gcc -c data.c

data.h: /usr/share/emacs/23.1/etc/compilation.txt
	../cstringify.py /usr/share/emacs/23.1/etc/compilation.txt

match.c: /usr/share/emacs/23.1/etc/compilation.txt
	../cstringify.py /usr/share/emacs/23.1/etc/compilation.txt

data.c: /usr/share/emacs/23.1/etc/compilation.txt
	../cstringify.py /usr/share/emacs/23.1/etc/compilation.txt

wc.o: wc.c
	gcc -c -std=c99 wc.c

clean:
	rm *.o
	rm data.h
	rm data.c
	rm match.c