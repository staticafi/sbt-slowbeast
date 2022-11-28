#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int a = nondet_int();
	int b = 4;
	assert(a + b == 7);
	// CHECK: Error found.
	// CHECK: Found errors: 1
	return 0;
}
