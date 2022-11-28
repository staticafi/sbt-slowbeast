#include <assert.h>

// UNSUPPORTED: bse
// REQUIRES: bounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s


int main() {
	float x = 0.1;//nondet_int();
	if (x < 0) {
		return 0;
	}
	for (int i = 0; i < 1; ++i) {
		++x;
		assert(x > 0);
	}

	assert(x > 1);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

