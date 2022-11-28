#include <assert.h>

// UNSUPPORTED: bse
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

extern int __VERIFIER_nondet_int(void);

int main() {
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  
  if (!(i==0 && j==0)) return 0;
  while (i<100) {
    j+=2;
    i++;
  }
  assert(j==200);

  // CHECK-NOT: Error found.
  // CHECK: Found errors: 0
  return 0;
}
