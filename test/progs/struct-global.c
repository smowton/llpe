
#include <stdint.h>

struct test {
  
  uint32_t field1;
  uint64_t field2;

};

struct test g = {1, 2};

int main(int argc, char** argv) {

  struct test l = {3, 4};
  l = g;

  return l.field1;

}
