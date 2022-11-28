#include <assert.h>

// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

int main()
{
    int x=__VERIFIER_nondet_int();
    int z=__VERIFIER_nondet_int();
    if (!(x>-100)) return 0;
    if (!(x<200)) return 0;
    if (!(z>100)) return 0;
    if (!(z<200)) return 0;
    while(x<100 && z>100) 
    {
        _Bool tmp=__VERIFIER_nondet_bool();
        if (tmp) {
            x++;
        } else {
            x--;
            z--;
        }
    }                       

    assert(x>=100 || z<=100);

  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0

    return 0;
}


