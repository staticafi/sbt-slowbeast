#include <assert.h>

// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = nondet_int();
	if (x < 0) {
		return 0;
	}

	int y = x;

	while (x > 0) {
		if (x > y) {
			--x;
		}
		assert(x == y);
	}

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
