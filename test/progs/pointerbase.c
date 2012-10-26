
#include <alloca.h>

int main(int argc, char** argv) {

  char* mem = (char*)alloca(argc);

  for(int i = 0; i < argc; ++i) {

    mem[i] = 0;

  }

  int total = 0;
  for(int i = 0; i < argc; ++i)
    total += mem[i];

  return total;

}
