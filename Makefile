
all: fake_fd_table.o wrappers.o

wrappers.o: wrappers.c
	gcc -g -std=c99 -c wrappers.c -o wrappers.o

fake_fd_table.o: fake_fd_table.cpp
	g++ -c -g fake_fd_table.cpp -o fake_fd_table.o

clean:
	rm *.o