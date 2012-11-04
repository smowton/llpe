
int x;

struct fakestream {

  char* bufstart;
  char* bufptr;

};

void fakeinit(struct fakestream* s);
void fakeflush(struct fakestream* s);
void fakewrite(struct fakestream* s, char c, int bytes);

char privbuf[1024];

struct fakestream s = {privbuf, privbuf};

int main(int argc, char** argv) {

  x = 5;
  //  struct fakestream s;
  
  //  fakeinit(&s);

  for(int i = 0; i < 5; ++i) {
    
    fakewrite(&s, 2, argc);

  }

  return x;

}
