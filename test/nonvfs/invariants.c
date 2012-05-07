
int main(int argc, char** argv) {

  // A short loop that uses a variant branch to sometimes select an invariant and an invariant branch to make a similar choice.

  int seed = 0;
  for(int j = 0; j < 3; ++j)
    seed += 5;

  int total = 0;

  for(int i = 0; i < 3; ++i) {

    int invar = seed + 2;

    if(i == 1)
      total += (i * 3);
    else
      total += seed;

    if(invar == 17)
      total += (i * 3);
    else
      total += seed;

  }

  return total;

}
