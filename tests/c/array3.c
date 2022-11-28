#include <assert.h>

// We do not handle symbolic pointers in kind yet
// REQUIRES: bounded
//
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	int n = input();
	array[n] = 1;
	assert(array[n] == 1);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
