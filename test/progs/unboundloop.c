
int x = 0;

int main(int argc, char** argv) {

  for(int i = 0; i < (argc * 2); ++i) {

    x++;
    if(i == argc)
      break;

  }

  return x;

}
