
#include <stdlib.h>
#include <stdio.h>

#define nallocs 260

int main(int argc, char** argv) {

	int* allocs[nallocs];

	for(int i = 0; i < nallocs; ++i)
		allocs[i] = (int*)malloc(sizeof(int));

	for(int i = 0; i < nallocs; ++i)
		*(allocs[i]) = i;

	int acc = 0;
	for(int i = 0; i < nallocs; ++i)
		acc += *(allocs[i]);

	printf("Total is %d\n", acc);

	return acc;

}
