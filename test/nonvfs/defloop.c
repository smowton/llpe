

int main(int argc, char** argv) {

  char a[10];

  for(int i = 0; i < 10; ++i)
    a[i] = (char)i;

  int result = 0;

  for(int i = 0; i < 10; ++i)
    result += a[i];

  return result;

}
