#include <assert.h>

// UNSUPPORTED: bse
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int x = nondet_int();
	if (x != 0) {
		return 0;
	}

	for (int i = 0; i < 1; ++i) {
		//assert(x == 0);
		//assert(i == 0);
		++x;
	}

	assert(x == 1);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

