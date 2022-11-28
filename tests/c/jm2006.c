// Source: SV-COMP benchmarks
// Source: Credited to Anubhav Gupta
// appears in Ranjit Jhala, Ken McMillan: "A Practical and Complete Approach
// to Predicate Refinement", TACAS 2006

#include <assert.h>


// REQUIRES: bself
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
    int i, j;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    if (!(i >= 0 && j >= 0)) return 0;
    int x = i;
    int y = j;
    while(x != 0) {
        x--;
        y--;
        //assert(x == y || i != j);
    }

    if (i == j) {
        assert(y == 0);
	    // CHECK-NOT: assertion failed!
	    // CHECK: Found errors: 0
    }
    return 0;
}
