
#include <stdlib.h>
#include <stdio.h>

int main(int argc, char** argv) {

  char* a = malloc(10);

  for(int i = 0; i < 10; ++i) {

    a[i] = i;

  }

  char* a2 = realloc(a, 20);

  for(int i = 10; i < 20; ++i) {

    a2[i] = i;

  }

  int res1 = *(int*)(a2 + 3);
  int res2 = *(int*)(a2 + 9);
  int res3 = *(int*)(a2 + 12);

  printf("%d %d %d\n", res1, res2, res3);

  return (res1+res2+res3);

}
