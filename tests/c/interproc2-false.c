#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



int foo(int y) {
    return y;
}

int main(void) {
    int x = 5;
    int y = foo(x);
    assert(y != 5);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
