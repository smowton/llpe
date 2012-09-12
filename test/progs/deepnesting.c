

int main(int argc, char** argv) {

  int total = 0;

  for(int i = 0; i < 100; i++) {

    for(int j = i; j < (i+10); j++) {

      for(int k = 0; k < j; k++) {

	total++;

      }

    }

  }

  return total;

}
