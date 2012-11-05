
#include <stdio.h>

// Compel x to be stored in memory
int f(int* px) {

  *px &= 0xff;

}

int main(int argc, char** argv) {

  int x = 0;

  f(&x);

  x = getchar();

  return x;

}
