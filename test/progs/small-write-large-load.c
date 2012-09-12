
#include <stdio.h>

int main(int argc, char** argv) {

  char buf[4];

  for(int i = 3; i >= 0; --i) {

    buf[i] = (char)i;

  }

  printf("Buffer contains int value %d\n", *((int*)buf));
  return 0;

}
