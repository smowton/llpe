
#include <stdio.h>
#include <string.h>

const char* test1 = "Hello";
const char* test2 = "World";
const char* test3 = "Arse";

int main(int argc, char** argv) {

  char test1p[5];
  char test2p[5];
  char test3p[4];

  memcpy(test1p, test1, 5);
  memcpy(test2p, test2, 5);
  memcpy(test3p, test3, 4);

  char buf[20];

  for(int i = 0; i < 20; ++i)
    buf[i] = i;

  memcpy(buf + 5, test1p, 3);
  memcpy(buf + 7, test2p, 1);
  memcpy(buf + 9, test3p, 4);

  /* Result definition map:

  0-4: loop
  5-6: test1
  7: test2
  8: loop
  9-12: test3

  */

  int result = *((int*)(buf + 6));
  printf("Result: %d\n", result);
  return result;

}
