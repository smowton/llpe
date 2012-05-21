

int main(int argc, char** argv) {

  char a[10];

  a[0] = 0;

  for(int i = 1; i < 5; ++i)
    a[i] = (char)i;

  for(int i = 5; i < 10; ++i)
    a[i] = (char)(i*2);

  int result = 0;

  for(int i = 0; i < 10; ++i)
    result += a[i];

  return result;

}
