
void set1(int* loc, int val) {

  *loc = val;

}

void set2(int* loc, int val) {

  loc[1] = val;

}

int get(int* loc) {

  return *loc;

}

int main(int argc, char** argv) {

  int loc[2];
  loc[0] = 10;
  loc[1] = 20;

  set1(loc, 30);
  set2(loc, 40);

  return get(loc);

}
