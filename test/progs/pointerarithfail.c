#include <alloca.h>

int main(int argc, char** argv) {

  char* mem = (char*)alloca(argc);
  char* memend = mem + argc;

  int i = 0;
  for(; mem < memend; ++mem, ++i) {

    *mem = 0;
    if(i == 2) {
      mem = (char*)alloca(10);
      memend = mem;
    }

  }

  mem -= argc;

  int total = 0;
  for(int i = 0; i < argc; ++i)
    total += mem[i];

  return total;

}
