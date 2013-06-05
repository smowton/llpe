
#include <stdlib.h>
#include <stdio.h>

void h(int* hx, int* x, int* y, int* z, int i, int argc) {

  if(argc) {

    switch(i) {

    case 1:
      *x = 5;
      break;
    case 2:
      *y = 10;
      break;
    case 3:
      *z = 20;
      break;
    case 4:
      *hx = 500;
      break;

    }

  }

}

void g(int* hx, int* x, int* y, int i, int argc) {

  int z = 0;
  h(hx, x, y, &z, i, argc);

}

void f(int* h, int* x, int i, int argc) {

  int y = 0;
  g(h, x, &y, i, argc);

}

int main(int argc, char** argv) {

  int x = 0;
  int* h = (int*)malloc(sizeof(int));
  *h = 100;

  f(h, &x, 1, argc);
  f(h, &x, 2, argc);
  f(h, &x, 3, argc);
  f(h, &x, 4, argc);

  printf("x = %d, h = %d\n", x, *h);

  return 0;

}
