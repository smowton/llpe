
#include <stdarg.h>
#include <stdio.h>

int f(int n, ...) {

	va_list l;
	va_start(l, n);

	int ret = 0;

	for(int i = 0; i < n; ++i) {

		ret += va_arg(l, int);

	}

	va_end(l);

	return ret;

}

int main(int argc, char** argv) {

	return f(5, 1, 2, 3, 4, 5);

}
