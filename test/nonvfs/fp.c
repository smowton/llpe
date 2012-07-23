
#include <stdio.h>

int main(int argc, char** argv) {

  float w = 0;
  double z = 0;

  for(int i = 0; i < 10; ++i) {
    w += i;
    z += i;
  }

  printf("%lf %f %d\n", z, w, (int)w);
  return 0;

}
