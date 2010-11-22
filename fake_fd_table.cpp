
#include "fake_fd_table.h"

#include <map>
#include <pthread.h>

pthread_mutex_t fake_fd_mutex = PTHREAD_MUTEX_INITIALIZER;
int last_fake_fd = 0x40000000;
std::map<int, struct fake_fd> fake_fds;

struct fake_fd* new_fake_fd() {

  struct fake_fd* ret;

  pthread_mutex_lock(&fake_fd_mutex);

  ret = &fake_fds[last_fake_fd++];

  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

struct fake_fd* get_fake_fd(int fd){ 

  struct fake_fd* ret;

  pthread_mutex_lock(&fake_fd_mutex);

  std::map<int, struct fake_fd>::iterator it = fake_fds.find(fd);
  if(it != fake_fds.end())
    ret = &(it->second);

  pthread_mutex_unlock(&fake_fd_mutex);

  return ret;

}

void delete_fake_fd(int fd) {

  pthread_mutex_lock(&fake_fd_mutex);

  fake_fds.erase(fd);

  pthread_mutex_unlock(&fake_fd_mutex);

}

