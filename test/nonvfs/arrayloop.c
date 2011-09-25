
int main(int argc, char** argv) {

  char* test_str = "Hello world!";
  int result = 0;

  for(int i = 0; i < 12; i++) {

    result += test_str[i];

  }

  return result;

}
