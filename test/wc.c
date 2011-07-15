
#include <errno.h>
#include <string.h>
#include <stdio.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define BUFSIZE 128

int main(int argc, char** argv) {

  int fd = open("/local/scratch/cs448/integrator/test/wc.c", O_RDONLY);
  int fd2 = open("/local/scratch/cs448/integrator/test/wc.c", O_RDONLY);
  char buf[BUFSIZE];
  int this_read;
  int newlines = 0;
  while((this_read = read(fd, buf, BUFSIZE)) > 0) {
    for(int i = 0; i < this_read; i++)
      if(buf[i] == '\n')
	newlines++;
  }

  while((this_read = read(fd2, buf, BUFSIZE)) > 0) {
    for(int i = 0; i < this_read; i++)
      if(buf[i] == '\n')
	newlines++;
  }

  newlines /= 2;

  if(this_read == -1) {
    printf("Failed to read: %s\n", strerror(errno));
    return 1;
  }
  else {
    printf("%d lines\n", newlines);
    return 0;
  }
 
}
