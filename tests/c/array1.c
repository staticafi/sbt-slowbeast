#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	array[0] = 1;
	assert(array[0] == 1);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
