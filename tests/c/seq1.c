#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 60 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
    int x = 0;
    int i = 0;

    while (i < 10) { // L3
        ++i;
    }

    // assert((x == i && x >= 10) || (x <= 10 && i == 10));
    while(x < 10) { // L9
        ++x;
        // this we need (we are able to prove it if it is present)
        //assert(i == 10);
    }

    assert(x == i);

	// CHECK-NOT: assertion failed!
	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}
