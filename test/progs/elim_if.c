
int main(int argc, char** argv) {

  int total = 0;

  for(int i = 0; i < 100; i++) {
    if(i % 7 == 0)
      total += 10;
    if(i % 3 != 0)
      total += 5;
    total++;
  }

  return total;

}
