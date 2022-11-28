#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



int main(void) {
    unsigned int x = 0;
    unsigned int y = __VERIFIER_nondet_uint();

    if (y % 2 == 0)
        x += 2;
    else
        x++;

    if (y % 2 == 0)
        x += 2;
    else
        x -= 4;

    assert((x % 2) == (y % 2));

    // CHECK-NOT: assertion failed!
    // CHECK: Found errors: 0
}
