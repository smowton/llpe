
#include <stdarg.h>
#include <stdio.h>

int f(int n, char c, float f, float f2, ...) {

	va_list l;
	va_start(l, n);

	double ret = 0;

	for(int i = 0; i < n; ++i) {

		ret += va_arg(l, double);

	}

	va_end(l);

	return (int)ret;

}

int main(int argc, char** argv) {

	return f(5, 'a', 5.0, 10.0, 1.0, 2.0, 3.0, 4.0, 5.0);

}
