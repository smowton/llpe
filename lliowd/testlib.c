
#include <lliowd.h>
#include <stdio.h>

int main(int argc, char** argv) {

  printf("Connecting...");
  lliowd_init();
  printf("done\n");

  while(1) {

    printf("Press return to check:");
    getchar();

    const char* msg = lliowd_ok() ? "Specialised files ok\n" : "Specialised files bad\n";
    puts(msg);

  }

}
