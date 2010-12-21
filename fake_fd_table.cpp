
#include "fake_fd_table.h"

#include <map>
#include <pthread.h>

pthread_mutex_t fake_fd_mutex = PTHREAD_MUTEX_INITIALIZER;
int last_fake_fd = 0x40000000;
std::map<int, struct fake_fd> fake_fds;

__attribute__((always_inline)) struct fake_fd* new_fake_fd(int* new_fd) {

  struct fake_fd* ret;

  pthread_mutex_lock(&fake_fd_mutex);

  *new_fd = last_fake_fd++;
  ret = &fake_fds[*new_fd];

  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

__attribute__((always_inline)) struct fake_fd* get_fake_fd(int fd){ 

  struct fake_fd* ret;

  pthread_mutex_lock(&fake_fd_mutex);

  std::map<int, struct fake_fd>::iterator it = fake_fds.find(fd);
  if(it != fake_fds.end())
    ret = &(it->second);
  else
    ret = 0;

  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

__attribute__((always_inline)) void delete_fake_fd(int fd) {

  pthread_mutex_lock(&fake_fd_mutex);

  fake_fds.erase(fd);

  pthread_mutex_unlock(&fake_fd_mutex);

}

