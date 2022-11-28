#include <assert.h>

// RUN: rm -rf %t-out
// RUN: timeout 30 sb -se-exit-on-error -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s
//
extern int __VERIFIER_nondet_int();

int main()
{
  int x=__VERIFIER_nondet_int();
  int *p = &x;
 
  while(x<100) {
   (*p)++;
  }                       
  assert(0);    

  // CHECK: Error found.
  // CHECK: Found errors: 1

  return 0;
}

