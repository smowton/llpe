// Some snippets from uclibc and coreutils that're a tricky challenge for establishing a fixed point amongst lots of mutually feeding loads and stores.

#include <stddef.h> // For wchar_t, size_t, ssize_t.
#include <unistd.h>
#include <limits.h>
#include <alloca.h>
#include <string.h>

int errno_fake;

#define EINTR 1
#define EAGAIN 2

void* memchr_local(const void* buf, int c, size_t size) {

  const char* b = (const char*)buf;

  for(size_t i = 0; i < size; ++i)
    if((b[i]) == (unsigned char)c)
      return &(b[i]);

  return 0;

}

void* memrchr(const void* buf, int c, size_t size) {

  const char* b = (const char*)buf;

  for(size_t i = size - 1; i >= 0; --i)
    if((b[i]) == (unsigned char)c)
      return &(b[i]);

  return 0;

}

#define SSIZE_MAX INT_MAX

#define __STDIO_STREAM_FAKE_VSNPRINTF_FILEDES -1

#define __FLAG_WRITING 1
#define __FLAG_NBF 2
#define __FLAG_LBF 4
#define __FLAG_ERROR 8
#define __FLAG_NARROW 16
#define __FLAG_WRITEONLY 32

#define __STDIO_STREAM_IS_LBF(S)		((S)->__modeflags & __FLAG_LBF)
#define __STDIO_STREAM_IS_NBF(S)		((S)->__modeflags & __FLAG_NBF)
#define __STDIO_STREAM_IS_WRITING(S) ((S)->__modeflags & __FLAG_WRITING)
#define __STDIO_STREAM_IS_FAKE_VSNPRINTF(S) \
  ((S)->__filedes == __STDIO_STREAM_FAKE_VSNPRINTF_FILEDES)
#define __STDIO_STREAM_BUFFER_WAVAIL(S)		((S)->__bufend - (S)->__bufpos)
#define __STDIO_COMMIT_WRITE_BUFFER(S)		__stdio_wcommit((S))
#define __STDIO_STREAM_BUFFER_SIZE(S)		((S)->__bufend - (S)->__bufstart)
#define __STDIO_STREAM_BUFFER_WUSED(S)		((S)->__bufpos - (S)->__bufstart)
#define __STDIO_STREAM_SET_ERROR(S) \
	((void)((S)->__modeflags |= __FLAG_ERROR))

#define __WRITE(STREAMPTR,BUF,SIZE) \
	(write((STREAMPTR)->__filedes,(BUF),(SIZE)))

typedef struct
{
	wchar_t __mask;
	wchar_t __wc;
} __mbstate_t;

struct __STDIO_FILE_STRUCT {

  unsigned short __modeflags;
  unsigned char __ungot_width[2];
  int __filedes;
  unsigned char *__bufstart;
  unsigned char *__bufend;
  unsigned char *__bufpos;
  unsigned char *__bufread;
  unsigned char *__bufgetc_u;
  unsigned char *__bufputc_u;
  struct __STDIO_FILE_STRUCT *__nextopen;
  wchar_t __ungot[2];
  __mbstate_t __state;
  void *__unused;
  int __user_locking;

};

typedef struct __STDIO_FILE_STRUCT FILE;

size_t __stdio_WRITE(register FILE *stream,
		     register const unsigned char *buf, size_t bufsize)
{
  size_t todo;
  int rv, stodo;

  todo = bufsize;

  while (todo != 0) {
    stodo = (todo <= SSIZE_MAX) ? todo : SSIZE_MAX;
    rv = __WRITE(stream, (char *) buf, stodo);
    if (rv >= 0) {
      todo -= rv;
      buf += rv;
    } else {

      __STDIO_STREAM_SET_ERROR(stream);

      /* We buffer data on "transient" errors, but discard it
       * on "hard" ones. Example of a hard error:
       *
       * close(fileno(stdout));
       * printf("Hi there 1\n"); // EBADF
       * dup2(good_fd, fileno(stdout));
       * printf("Hi there 2\n"); // buffers new data
       *
       * This program should not print "Hi there 1" to good_fd.
       * The rationale is that the caller of writing operation
       * should check for error and act on it.
       * If he didn't, then future users of the stream
       * have no idea what to do.
       * It's least confusing to at least not burden them with
       * some hidden buffered crap in the buffer.
       */
      if (errno_fake != EINTR && errno_fake != EAGAIN) {
	/* do we have other "soft" errors? */
	break;
      }
      stodo = __STDIO_STREAM_BUFFER_SIZE(stream);
      if (stodo != 0) {
	unsigned char *s;

	if (stodo > todo) {
	  stodo = todo;
	}

	s = stream->__bufstart;

	do {
	  *s = *buf;
	  if ((*s == '\n')
	      && __STDIO_STREAM_IS_LBF(stream)
	      ) {
	    break;
	  }
	  ++s;
	  ++buf;
	} while (--stodo);

	stream->__bufpos = s;

	todo -= (s - stream->__bufstart);
      }

      bufsize -= todo;
      break;
    }
  }

  return bufsize;
}

size_t __stdio_wcommit(register FILE * __restrict stream)
{
  size_t bufsize;

  if ((bufsize = __STDIO_STREAM_BUFFER_WUSED(stream)) != 0) {
    stream->__bufpos = stream->__bufstart;
    __stdio_WRITE(stream, stream->__bufstart, bufsize);
  }

  return __STDIO_STREAM_BUFFER_WUSED(stream);
}

size_t __stdio_fwrite(const unsigned char * __restrict buffer,
				       size_t bytes,
				       register FILE * __restrict stream)
{
  size_t pending;
  const unsigned char *p;

  if (!__STDIO_STREAM_IS_NBF(stream)) { /* FBF or LBF. */
    if (__STDIO_STREAM_IS_FAKE_VSNPRINTF(stream)) {
      pending = __STDIO_STREAM_BUFFER_WAVAIL(stream);
      if (pending > bytes) {
	pending = bytes;
      }
      memcpy(stream->__bufpos, buffer, pending);
      stream->__bufpos += pending;
      return bytes;
    }

    /* 	RETRY: */
    if (bytes <= __STDIO_STREAM_BUFFER_WAVAIL(stream)) {
      memcpy(stream->__bufpos, buffer, bytes);
      stream->__bufpos += bytes;
      if (__STDIO_STREAM_IS_LBF(stream)
	  && memrchr(buffer, '\n', bytes)	/* Search backwards. */
	  ) {
	if ((pending = __STDIO_COMMIT_WRITE_BUFFER(stream)) > 0) {
	  if (pending > bytes) {
	    pending = bytes;
	  }
	  buffer += (bytes - pending);
	  if ((p = memchr_local(buffer, '\n', pending)) != NULL) {
	    pending = (buffer + pending) - p;
	    bytes -= pending;
	    stream->__bufpos -= pending;
	  }
	}
      }
      return bytes;
    }
    /* FBF or LBF and not enough space in buffer. */
    if (__STDIO_STREAM_BUFFER_WUSED(stream)) { /* Buffered data. */
      if (__STDIO_COMMIT_WRITE_BUFFER(stream)) { /* Commit failed! */
	return 0;
      }
      /* 			goto RETRY; */
    }
  }

  return __stdio_WRITE(stream, buffer, bytes);
}

struct pt_buf {

  void (*fun)(void*);
  void* arg;

};

void thunk(void* v) { return; }

void make_pt_buf(struct pt_buf* p, void (*f)(void*), void* a) {
  
  p->fun = f;
  p->arg = a;

}

void run_pt_buf(struct pt_buf* p) {

  (*(p->fun))(p->arg);

}

size_t fake_fwrite(const unsigned char * __restrict buffer,
		   size_t bytes,
		   register FILE * __restrict stream) 

{

  struct pt_buf b;
  make_pt_buf(&b, thunk, 0);
  __stdio_fwrite(buffer, bytes, stream);
  run_pt_buf(&b);

}

#define _outnstr(stream, string, len)	((len > 0) ? fake_fwrite((const unsigned char *)(string), len, stream) : 0)
#define OUTNSTR _outnstr

size_t _charpad(FILE * __restrict stream, int padchar, size_t numpad)
{
  size_t todo = numpad;
  
  char pad[1];
  
  *pad = padchar;
  while (todo && (OUTNSTR(stream, (const char *) pad, 1) == 1)) {
    --todo;
  }

  return numpad - todo;
}

int x;

#define __INIT_MBSTATE(dest)			((void)((dest)->__mask = 0))
#define __STDIO_STREAM_INIT_BUFREAD_BUFPOS(S)		\
	(S)->__bufread = (S)->__bufpos = (S)->__bufstart
# define __STDIO_STREAM_DISABLE_GETC(S) \
	((void)((S)->__bufgetc_u = (S)->__bufstart))
# define __STDIO_STREAM_ENABLE_PUTC(S) \
	((void)((S)->__bufputc_u = (S)->__bufend))

int main(int argc, char** argv) {

  x = 0;
  
  char* buf = (char*)alloca(argc);
  int size = argc;

  // Stream init copied from vasnprintf:
  FILE f;
  f.__filedes = __STDIO_STREAM_FAKE_VSNPRINTF_FILEDES;
  f.__modeflags = (__FLAG_NARROW|__FLAG_WRITEONLY|__FLAG_WRITING);
  __INIT_MBSTATE(&(f.__state));

  f.__user_locking = 1;		/* Set user locking. */
  //STDIO_INIT_MUTEX(f.__lock);
  f.__nextopen = NULL;

  f.__bufstart = (unsigned char *) buf;
  f.__bufend = (unsigned char *) buf + size;
  __STDIO_STREAM_INIT_BUFREAD_BUFPOS(&f);
  __STDIO_STREAM_DISABLE_GETC(&f);
  __STDIO_STREAM_ENABLE_PUTC(&f);

  _charpad(&f, 0, argc);

  return x;

}
