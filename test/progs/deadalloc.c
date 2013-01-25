
void f(int* x, int* y, int z) {

  int* loc = z ? x : y;
  *loc = 5;

}

int main(int argc, char** argv) {

  int x = 0;
  f(&x, &x, 0);
  return x;

}

