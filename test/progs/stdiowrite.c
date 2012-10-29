
#include <alloca.h>

int x;

struct ctx {

  char* ptr;

};

void bumpptr(struct ctx* c, int b) {

  char* p = c->ptr;
  
  for(int i = 0; i < b; ++i) {
    *(p++) = 0;
  }

  c->ptr = p;

}
	       
int main(int argc, char** argv) {

  x = 3;
  
  char* mem = alloca(argc * argc);

  struct ctx c;
  c.ptr = mem;

  for(int i = 0; i < argc; ++i)
    bumpptr(&c, argc);

  return x;

}
