
#include <stdio.h>

int f(int** x, int y) {

  int res = x[y][0];
  printf("%d\n", res);
  return res;

}

int main(int argc, char** argv) {

  int x[2] = {10, 20};
  int* y[2];
  y[1] = &(x[1]);
  return f(y, 1);

}
