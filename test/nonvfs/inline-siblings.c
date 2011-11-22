

int g(int x) {

  return x + 1;

}

int f(int x) {

  return 2 * g(x+1);

}

int main(int argc, char** argv) {

  return f(5) + f(10);

}
