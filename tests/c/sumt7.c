// source: sv-benchmarsk
#include <assert.h>

// REQUIRES: bself
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s


int SIZE = 20000001;
int __VERIFIER_nondet_int();
int main() {
  unsigned int n=0,i=0,k=0,j=0,l=0;
  unsigned int v1=0, v2=0, v3=0, v4=0;
  n = __VERIFIER_nondet_int();
  if (!(n <= SIZE)) return 0;
  while( l < n ) {
	
	  if(!(l%7))
	    v1 = v1 + 1;
	  else if(!(l%6))
	    v2 = v2 + 1;
	  else if(!(l%5))
	    v3 = v3 + 1;
	  else if(!(l%4))
	    v4 = v4 + 1;
	  else if(!(l%3))
	    i = i + 1;
	  else if(!(l%2)) 
		  j = j+1;
	  else 
	    k = k+1;
    l = l+1;
    assert((i+j+k+v1+v2+v3+v4) == l);
  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0
  }
  return 0;
}

