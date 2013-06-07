
#include <stdlib.h>
#include <stdio.h>

#define nallocs 20

int main(int argc, char** argv) {

	if(argc) {

	int* allocs[nallocs];

	for(int i = 0; i < nallocs; ++i)
		allocs[i] = (int*)malloc(sizeof(int));

	for(int i = 0; i < nallocs; ++i) {
		if(argc == 1) 
			*(allocs[i]) = i;
	}

	int acc = 0;
	for(int i = 0; i < nallocs; ++i)
		acc += *(allocs[i]);

	printf("Total is %d\n", acc);

	return acc;

	}

	else {

		return -1;

	}

}
