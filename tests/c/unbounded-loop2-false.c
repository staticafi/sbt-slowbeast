#include <assert.h>

// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

extern unsigned nondet(void);

int main(void) {
	int x = nondet();
	if (x < 0) {
		return 0;
	}

	int n = 0;
	int y = x;
	int old_diff = x - n;
	while (x > 0) {
		--x;
		++n;
		assert(x - n == old_diff - 2);
		//old_diff -= 2;
	}

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
