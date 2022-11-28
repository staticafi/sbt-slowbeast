#include <assert.h>

// REQUIRES: unbounded
//
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



int main() {
    int i;
    for (i = 0; i < 1000000; i += 2)
        ;
    assert(i == 1000000);

	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
    return 0;
}
