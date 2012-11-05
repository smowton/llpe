
#include <stdarg.h>
#include <stdio.h>

int vf2(int n, va_list l) {

	int ret = 0;

	for(int i = 0; i < n; ++i) {

		ret += va_arg(l, int);

	}

	return ret;

}

int vf(int n, va_list l) {

	int ret = 0;

	for(int i = 0; i < n; ++i) {

		if(i == 2) {

			va_list l2;
			va_copy(l2, l);
			ret += vf2(n - i, l2);

		}

		ret += va_arg(l, int);

	}

	return ret;

}

int f(int n, char crap, char crap2, ...) {

	va_list l;
	va_start(l, crap2);

	int ret = vf(n, l);

	va_end(l);

	return ret;

}

int main(int argc, char** argv) {

	return f(5, 'x', 'y', 1, 2, 3, 4, 5);

}
