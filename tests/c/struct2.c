#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

struct A {
    int a;
    int b;
};

struct B {
    struct A a;
    struct A b;
};

int main() {
    struct B s;
    s.a.a = 1;
    s.b.b = 2;
    assert(s.a.a + s.b.b == 3);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
