#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>

int fd;

int main(int argc, char** argv) {

  fd = open("read-input", O_RDONLY);
  if(fd == -1) {

    printf("Epic open fail: %s\n", strerror(errno));
    return 1;

  }

  int total = 0;

  while(1) {

    char buf[4];
    int this_read = read(fd, buf, 4);
    if(this_read <= 0) {
      if(this_read == -1) {
	printf("Epic read fail: %s\n", strerror(errno));
	return 1;
      }
      break;
    }

    for(int i = 0; i < this_read; ++i) {

      total += buf[i];

    }

  }

  printf("File sums to %d\n", total);
  return 0;

}
