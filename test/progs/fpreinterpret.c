
#include <stdio.h>

int main(int argc, char** argv) {

  int x = 5;
  float* f = (float*)&x;

  (*f) += 10;

  x++;

  printf("Result: %d\n", x);

}
