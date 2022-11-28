#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s



#define MAX 2

extern char __VERIFIER_nondet_char();

int main()
{
  unsigned char string_A[MAX], string_B[MAX];
  int nc_A, nc_B;
  
  string_A[0] = 1;
  string_A[1] = 0;
  string_B[0] = 1;
  string_B[1] = 0;
  
  nc_A = 0;
  while(string_A[nc_A]!='\0')
    nc_A++;

  nc_B = 0;
  while(string_B[nc_B]!='\0')
    nc_B++;

  assert(0 >= nc_A || nc_B < nc_A);
  // CHECK: Error found.
  // CHECK: Found errors: 1
  //
  return 0;
}

