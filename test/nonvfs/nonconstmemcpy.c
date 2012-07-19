
#include <stdio.h>
#include <string.h>

int main(int argc, char** argv) {

  char buf1[4];
  char buf2[6];

  for(int i = 0; i < 4; ++i)
    buf1[i] = (char)i;

  for(int i = 0; i < 6; ++i)
    buf2[i] = (char)(i + 10);

  memcpy(buf1, buf2 + 2, 3);

  int result = *((int*)buf1);
  printf("Result is %d\n", result);
  return result;

}
