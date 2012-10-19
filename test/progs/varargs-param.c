
#include <stdarg.h>
#include <stdio.h>

int vf(int n, va_list l) {

	int ret = 0;

	for(int i = 0; i < n; ++i) {

		ret += va_arg(l, int);

	}

	return ret;

}

int f(int n, ...) {

	va_list l;
	va_start(l, n);

	int ret = vf(n, l);

	va_end(l);

	return ret;

}

int main(int argc, char** argv) {

	return f(5, 1, 2, 3, 4, 5);

}
