// A loop that requires the optimistic-loop directive to pursue due to its dynamic exiting edges. Also exercises load forwarding through terminated loops with many exiting edges.

#include <sys/mman.h>

int x;
int y;

int main(int argc, char** argv) {

  const char* fmt = "abcde";

  x = 0;
  y = 0;

  for(const char* p = fmt; *p; ++p) {

    if(argc == *p)
      break;

    x += *p;

    if((p - fmt) == 100) {
      
      // Unhandled syscall, barrier, never actually run
      mmap(0, 0, 0, 0, 0, 0);

    }

  }

  return x + y;

}
