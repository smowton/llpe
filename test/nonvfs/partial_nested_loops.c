
// Here we want to test the cast where unrolling the outer improves the inner a bit, but the inner needs unrolling to expose the full opportunity.
// This particular example is a bit silly of course, as all the expressions involving i are loop-invariant and would properly be hoisted.

int main(int argc, char** argv) {

  int total = 0;

  for(int i = 0; i < 100; i++) {
    for(int j = 0; j < 100; j++) {
      int addFactor;
      if(i % 7 == 0) {
	addFactor = i*2;
      }
      else {
	addFactor = i*3;
      }
      total += addFactor;
    }
  }

  return total;

}
