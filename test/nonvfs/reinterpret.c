
#include <stdio.h>
#include <stdint.h>

struct t {

  char a;
  int b;

};

struct t ts[2] = {
  {1, 2},
  {3, 4}
};

int test[4] = {1, 2, 3, 4};

int main(int argc, char** argv) {

  uint64_t* p = (uint64_t*)test;
  int result1 = ((int)(p[0] + p[1]));

  // Misaligned reinterpret:
  p = (uint64_t*)&(((char*)test)[2]);
  int result2 = (int)(*p);

  // Reinterpret ints as struct
  struct t* ptr = (struct t*)test;
  int result3 = ptr[0].a + ptr[1].b;
  
  // Reinterpret struct as int
  int* ptr2 = (int*)ts;
  int result4 = ptr2[0] + ptr2[2];

  printf("Results: %d, %d, %d, %d\n", result1, result2, result3, result4);

}
