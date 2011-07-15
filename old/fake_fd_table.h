
#ifdef __cplusplus
extern "C" {
#endif

struct fake_fd {
  char* file_chars;
  int file_len;
  int file_pos;
};

  struct fake_fd* new_fake_fd(int* pfd);

  struct fake_fd* get_fake_fd(int);

  void delete_fake_fd(int);

#ifdef __cplusplus
}
#endif
