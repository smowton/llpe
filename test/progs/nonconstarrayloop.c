
int main(int argc, char** argv) {

  char test_str[12];
  test_str[0] = 'H';
  test_str[1] = 'e';
  test_str[2] = 'l';
  test_str[3] = 'l';
  test_str[4] = 'o';
  test_str[5] = ' ';
  test_str[6] = 'w';
  test_str[7] = 'o';
  test_str[8] = 'r';
  test_str[9] = 'l';
  test_str[10] = 'd';
  test_str[11] = '!';
  int result = 0;

  for(int i = 0; i < 12; i++) {

    result += test_str[i];

  }

  return result;

}
