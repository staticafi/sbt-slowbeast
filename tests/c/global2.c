#include <assert.h>

// REQUIRES: se
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s


int a;

int main() {
	a = nondet_int();
	if (a > 3) {
		a += 1;
	} else {
		a -= 1;
	}

	// CHECK: Executed paths: 2
	// CHECK: Paths that reached exit: 2
	// CHCEK: Number of forks on branches: 1
	// CHECK: Found errors: 0
}
