
#include <stdint.h>

struct test {

  int32_t field1;
  int64_t field2;

};

int main(int argc, char** argv) {

  struct test inst = {1, 2};
  struct test set = {3, 4};

  inst = set;

  return inst.field2;

}
