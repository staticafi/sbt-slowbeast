// source: sv-benchmarks
#include <assert.h>

// REQUIRES: bself
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s


int main() {
    int k;
    long long y, x, c;
    k = __VERIFIER_nondet_int();

    y = 0;
    x = 0;
    c = 0;

    while (1) {
        assert((y * y) - 2 * x + y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y + x;
    }
    assert((y*y) - 2*x + y == 0);
     
    // CHECK-NOT: assertion failed!
    // CHECK: Found errors: 0
    return 0;
}
