#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int x = 3;
	assert((x ^ (x >> 1u)) == 2);
	// CHECK-NOT: assertion failed!
}
