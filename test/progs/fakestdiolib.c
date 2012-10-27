
char staticbuf[1024];

struct fakestream {

  char* bufstart;
  char* bufptr;

};

void fakeinit(struct fakestream* s) {

  s->bufstart = staticbuf;
  s->bufptr = staticbuf;

}

void fakeflush(struct fakestream* s) {

  s->bufptr = s->bufstart;

}

void fakewrite(struct fakestream* s, char c, int bytes) {

  if(((s->bufptr - s->bufstart) + bytes) > 1024)
    fakeflush(s);

  for(int i = 0; i < bytes; ++i)
    *s->bufptr++ = c;

}

