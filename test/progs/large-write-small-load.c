
#include <stdio.h>
#include <stdint.h>

int main(int argc, char** argv) {

  uint64_t buf = 0x0102030405060708LL;

  uint32_t total = 0;

  for(int i = 0; i < 8; ++i) {

    total += ((uint8_t*)&buf)[i];

  }

  printf("Total is %u\n", total);

}
