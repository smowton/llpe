
#include <string.h>
#include <stdio.h>

const char* source_str = "Hello!";

int main(int argc, char** argv) {

  int testbuf[64];
  long long int total = 0;

  memset(testbuf, 1, 64 * 4);

  for(int i = 0; i < 64; ++i) {

    total += testbuf[i];

  }

  memcpy(testbuf, source_str, 6);

  for(int j = 0; j < 2; ++j) {

    total += testbuf[j];

  }

  printf("Total: %lld\n", total);

  return 0;

}
