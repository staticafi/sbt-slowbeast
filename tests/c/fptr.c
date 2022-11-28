#include <assert.h>

// REQUIRES: se
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s


int foo(void) {
    assert(0);
}

int main() {
    void (*f)() = foo;
    f();

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
