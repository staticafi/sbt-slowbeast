#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: bself
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



extern float nondet_float(void);
extern unsigned char nondet_uchar(void);
int main()
{
  float f = nondet_float();
  double d;
  unsigned char x = nondet_uchar();

  d=f;
  
  if(f==x)
    assert(d==x);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
