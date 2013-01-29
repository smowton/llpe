
int main(int argc, char** argv) {

  const char* s = "Hello";
  const char* start = &(s[5]);

  int total = 0;

  for(int i = 0;;++i) {

    const char* ptr = &(start[-i]);
    if(ptr < s)
      break;
    total += *ptr;

  }

  return total;

}
