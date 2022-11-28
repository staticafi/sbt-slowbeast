#include <assert.h>

// REQUIRES: bounded
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
    union {
        int i;
        unsigned short s;
        unsigned char b[sizeof(int)];
    } x;

    x.i = 0xaabbccdd;
    assert(x.b[0] == 0xdd);
    assert(x.b[1] == 0xcc);
    assert(x.b[2] == 0xbb);
    assert(x.b[3] == 0xaa);

    x.b[0] = 0x78;
    x.b[1] = 0x56;
    x.b[2] = 0x34;
    x.b[3] = 0x12;
    assert(x.i == 0x12345678);

    x.s = 0xffff;
    assert(x.i == 0x1234ffff);
    x.b[0] = 0xee;
    assert(x.i == 0x1234ffee);
    assert(x.b[0] == 0xee);
    assert(x.b[1] == 0xff);
    assert(x.b[2] == 0x34);
    assert(x.b[3] == 0x12);

    x.i = nondet();
    __VERIFIER_assume(x.i == 0xaabbccdd);
    assert(x.b[0] == 0xdd);
    assert(x.b[1] == 0xcc);
    assert(x.b[2] == 0xbb);
    assert(x.b[3] == 0xaa);

    x.b[0] = 0x78;
    x.b[2] = 0x34;
    assert(x.i == 0xaa34cc78);

    x.s = 0xffff;
    assert(x.i == 0xaa34ffff);
    x.b[0] = 0xee;
    assert(x.i == 0xaa34ffee);
    assert(x.b[0] == 0xee);
    assert(x.b[1] == 0xff);
    assert(x.b[2] == 0x34);
    assert(x.b[3] == 0xaa);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
