
#include "fake_fd_table.h"

#include <pthread.h>

//pthread_mutex_t fake_fd_mutex = PTHREAD_MUTEX_INITIALIZER;
#define FAKE_FD_OFFSET 0x40000000
int last_fake_fd = 0x40000000;
struct fake_fd fake_fd_array[1024];
int fake_fd_taken[1024];

__attribute__((always_inline)) struct fake_fd* new_fake_fd(int* new_fd) {

  struct fake_fd* ret;

  //  pthread_mutex_lock(&fake_fd_mutex);

  *new_fd = last_fake_fd++;
  int offset = (*new_fd) - FAKE_FD_OFFSET;
  ret = &fake_fd_array[offset];
  fake_fd_taken[offset] = 1;

  //  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

__attribute__((always_inline)) struct fake_fd* get_fake_fd(int fd){ 

  struct fake_fd* ret;

  //  pthread_mutex_lock(&fake_fd_mutex);

  int offset = fd - FAKE_FD_OFFSET;
  if(!fake_fd_taken[offset])
    ret = 0;
  else
    ret = &(fake_fd_array[offset]);

  //  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

__attribute__((always_inline)) void delete_fake_fd(int fd) {

  //  pthread_mutex_lock(&fake_fd_mutex);

  fake_fd_taken[fd - FAKE_FD_OFFSET] = 0;

  //  pthread_mutex_unlock(&fake_fd_mutex);

}

