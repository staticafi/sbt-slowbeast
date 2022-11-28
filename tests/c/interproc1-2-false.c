#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

void foo2(int y) {
    assert(y != 5);
}

void foo(int y) {
    foo2(y);
}

int main(void) {
    int x = 5;
    foo(x);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
