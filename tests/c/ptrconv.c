#include <assert.h>

// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
    int array[10];
    array[0] = 1;
    array[1] = 2;
    int *p = array;
    unsigned long pi = (unsigned long)p;
    pi += sizeof(int);
    p = (int *) pi;
    assert(*p == 2);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
