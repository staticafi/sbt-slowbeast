#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

#define N 5
#define M 2

void foo(void) {
        int i;
        int x = 0;
        for (i = 0; i < N; ++i) {
                ++x;
        }
        assert (x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

int main(void) {
        foo();
}
