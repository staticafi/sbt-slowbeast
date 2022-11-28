#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() { 
  int SIZE = 8;
  int i, sn=0;
  for(i=1; i<=SIZE; i++) {
    //assert(sn == 2*i-2);
    sn = sn + 2;
    // assert(sn == 2*i);
  }
  //assert(sn==2*SIZE);
  assert(sn==2*SIZE || sn == 0);

  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0
}

