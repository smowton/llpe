
#include <stdlib.h>

int x;

char* f(int argc) {

  char* origbuf = (char*)malloc(argc);
  char* buf = origbuf;
  char* bufend = buf + argc;

  while(buf < bufend) {

    if(buf) {
      *(buf++) = (char)argc;
    }
    if(argc == 20) {
      return origbuf;
    }

  }

  return 0;

}

int main(int argc, char** argv) {

  x = 0;

  char* freebuf = f(argc);

  if(freebuf)
    free(freebuf);

}
