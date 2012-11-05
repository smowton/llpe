
#include <alloca.h>

int main(int argc, char** argv) {

  int total = 0;

  for(int i = 0; i < 10; ++i) {

    char* mem = (char*)alloca(argc);
    char* memend = mem + argc;

    for(; mem < memend; ++mem) {

      *mem = 0;

    }

    mem -= argc;

    for(int i = 0; i < argc; ++i)
      total += mem[i];

  }

  return total;

}
