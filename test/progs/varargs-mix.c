
#include <stdarg.h>
#include <stdio.h>

int vf(int n, va_list l) {

	double ret = 0;

	for(int i = 0; i < n; ++i) {

		if(i % 2 == 1)
			ret += va_arg(l, int);
		else
			ret += va_arg(l, double);

	}

	return (int)ret;

}

int f(int n, char c, float f, float f2, ...) {

	va_list l;
	va_start(l, f2);

	int ret = vf(n, l);

	va_end(l);

	return ret;

}

int main(int argc, char** argv) {

	return f(20, 'x', 5.0, 6.0, 1.0, 2, 3.0, 4, 5.0, 6, 7.0, 8, 9.0, 10, 11.0, 12, 13.0, 14, 15.0, 16, 17.0, 18, 19.0, 20);

}
