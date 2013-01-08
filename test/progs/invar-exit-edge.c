// A loop that exits using an invariant condition.

int main(int argc, char** argv) {

  for(int i = 0; i < 3; ++i) {

    int x = i * 3;

    for(int j = 0; j < 3; ++j) {

      if(x == 7)
	goto break_exit;

    }

  }

  return 0;

 break_exit:

  return 1;

}
