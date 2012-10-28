
int x;

void f(int y) {

  if(y > 3)
    x = 4;

}

int main(int argc, char** argv) {

  x = 0;

  f(argc);
  
  return x;

}
