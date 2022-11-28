#include <assert.h>


// REQUIRES: unsupported
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


int main() {
    float a = 0.53;
    int i = (int) a;
    assert(i == 0);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
