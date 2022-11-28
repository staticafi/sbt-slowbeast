#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	int n = 7;
	array[n] = 1;
	assert(array[n] == 1);
	// CHECK-NOT: assertion failed!
	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}
