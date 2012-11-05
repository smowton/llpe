
#include <stdarg.h>
#include <stdio.h>

int f(void* junk1, char junk2, int n, ...) {

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

	return f(0, 2, 5, argc, argc, argc, argc, argc);

}
