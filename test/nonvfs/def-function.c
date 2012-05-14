
void set(int* loc, int val) {

  *loc = val;

}

int get(int* loc) {

  return *loc;

}

int main(int argc, char** argv) {

  int loc = 10;

  set(&loc, 20);

  return get(&loc);

}
