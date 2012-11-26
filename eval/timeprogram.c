#include <time.h>
#include <unistd.h>
#include <stdlib.h>

void __uClibc_main (int (*main)(int, char **, char **), int argc,
		   char **argv, void (*app_init)(void), void (*app_fini)(void),
		   void (*rtld_fini)(void),
		   void *stack_end);

const char* hex = "0123456789abcdef";
int backup_stderr;

void write_long(unsigned long n) {
  
  for(int i = 7; i >= 0; --i) {

    char c = ((char*)&n)[i];
    char c1 = (c & 0xf0) >> 4;
    char c2 = c & 0x0f;

    c1 = hex[c1];
    c2 = hex[c2];
    write(backup_stderr, &c1, 1);
    write(backup_stderr, &c2, 1);

  }

  write(backup_stderr, "\n", 1);

}

struct timespec ts;

void write_times() {

  struct timespec tf;
  clock_gettime(CLOCK_MONOTONIC, &tf);

  write_long(ts.tv_sec);
  write_long(ts.tv_nsec);
  write_long(tf.tv_sec);
  write_long(tf.tv_nsec);

}

void __uClibc_main_timed (int (*main)(int, char **, char **), int argc,
			   char **argv, void (*app_init)(void), void (*app_fini)(void),
			   void (*rtld_fini)(void),
			   void *stack_end) {

  backup_stderr = dup(2);
  atexit(write_times);
  clock_gettime(CLOCK_MONOTONIC, &ts);
  __uClibc_main(main, argc, argv, app_init, app_fini, rtld_fini, stack_end);
  close(backup_stderr);

}


