
#include "match.h"
#include "fake_fd_table.h"

#include <stdlib.h>
#include <fcntl.h>
#include <string.h>

int __real_open(const char* pathname, int flags);

int __wrap_open(const char *pathname, int flags) {

  char* file_chars;
  if((!flags & O_WRONLY) && (file_chars = get_chars_of_file(pathname))) {
    int fd;
    struct fake_fd* new_fd = new_fake_fd(&fd);
    new_fd->file_chars = file_chars;
    new_fd->file_len = get_length_of_file(pathname);
    new_fd->file_pos = 0;
    return fd;
  }
  else {
    return __real_open(pathname, flags);
  }

}

int __real_read(int fd, char* buf, size_t count);

int __fake_read(int fd, char* buf, size_t count) {

  struct fake_fd* ffd;
  if(ffd = get_fake_fd(fd)) {
    size_t len = count;
    if((ffd->file_len - ffd->file_pos) < len)
      len = ffd->file_len - ffd->file_pos;
    memcpy(buf, &(ffd->file_chars[ffd->file_pos]), len);
    ffd->file_pos += len;
    return len;
  }
  else {
    return __real_read(fd, buf, count);
  }

}

int __real_close(int fd);

int __fake_close(int fd) {

  delete_fake_fd(fd);

}
