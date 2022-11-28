#include <assert.h>

// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = nondet();
	int i = nondet();
	__VERIFIER_assume(x == i);
	for (; i < 5; ++i) {
		++x;
	}

	assert(x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
