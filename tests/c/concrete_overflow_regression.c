// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

#include <assert.h>

extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int);

int main() {
    int z, k;
    long long x, y;
    z = __VERIFIER_nondet_int();
    k = 1;
    __VERIFIER_assume(z == 1);

    x = 1;
    y = z;

    assert(x*z - x - y + 1 == 0);

    // CHECK-NOT: assertion failed!
    // CHECK: Found errors: 0
}
