#include <assert.h>


// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

void __slowbeast_print(int);

int main(void) {
	int a = 3;
	int b = 4;
	__slowbeast_print(a+b);
	assert(a + b == 7);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
	return 0;
}
