#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



int foo2(int y) {
    return y + 1;
}

int foo(int y) {
    return foo2(y);
}

int main(void) {
    int x = 4;
    int y = foo(x);
    assert(y == 5);

	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}
