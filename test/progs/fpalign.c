
#include <stdio.h>

struct argh {

  int x;
  float y;

};

int main(int argc, char** argv) {

  struct argh s[3];
  struct argh* blimey = (struct argh*)(((char*)s) + 2);

  for(int i = 0; i < 3; ++i) {
    s[i].x = 5;
    s[i].y = 4.0;
  }

  for(int j = 0; j < 2; ++j) {
    blimey[j].y += blimey[j].x;
  }

  int total = 0;

  for(int k = 0; k < 3; ++k) {
    total += s[k].x;
    total += ((int)s[k].y);
  }

  printf("Result: %d\n", total);

}
