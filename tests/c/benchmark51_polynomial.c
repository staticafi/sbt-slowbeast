// source: sv-benchmarks
#include <assert.h>

// UNSUPPORTED: se
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
  int x = __VERIFIER_nondet_int();
  
  if (!((x>=0) && (x<=50))) return 0;
  while (1) {
    if (x>50) x++;
    if (x == 0) { x ++;
    } else x--;
    assert((x>=0) && (x<=50));
  }
  // CHECK-NOT: assertion failed!
  // CHECK-NOT: Error found.
  // CHECK: Found errors: 0
  return 0;
}
