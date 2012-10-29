
int x;

int f(int y, int z) {

  x += y;

}

int main(int argc, char** argv) {

  x = 0;

  for(int i = 0; i < argc; ++i) {

    f(5, i);

  }

  return x;

}
