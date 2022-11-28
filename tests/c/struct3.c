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
    int array[10];
};

int main() {
    struct B s;
    s.a.a = 1;
    s.b.b = 2;
    int *p = s.array + 4;
    *p = 3;
    assert(s.a.a + s.b.b + s.array[4] == 6);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
