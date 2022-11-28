from slowbeast.domains.symbolic import (
        simplify_polynomial_formula,
        _desimplify_ext,
        BVFormula,
        BVPolynomial
)

from z3 import *

#  FROM uninit_x42*SignExt(32, uninit_x40) ==
#  18446744073709551615 + uninit_x42 + uninit_x43
#  FROM (1 + uninit_x42*SignExt(32, uninit_x40))*
#  SignExt(32, uninit_x40) ==
#  uninit_x42*SignExt(32, uninit_x40) +
#  uninit_x43*SignExt(32, uninit_x40)
#  ORIG Not(SignExt(32, 4294967295 + uninit_x40) +
#      uninit_x42*
#      SignExt(32, uninit_x40)*
#      SignExt(32, 4294967295 + uninit_x40) ==
#      18446744073709551615 +
#      uninit_x43*SignExt(32, uninit_x40))
#  SIMPL Not(uninit_x42*SignExt(32, 4294967295 + uninit_x40) +
#      uninit_x43*SignExt(32, 4294967295 + uninit_x40) ==
#      18446744073709551615 +
#      uninit_x43*SignExt(32, uninit_x40))
#  FINAL Not(uninit_x42*SignExt(32, 4294967295 + uninit_x40) +
#      uninit_x43*SignExt(32, 4294967295 + uninit_x40) ==
#      18446744073709551615 +
#      uninit_x43*SignExt(32, uninit_x40))
#

x42 = BitVec('x42', 64)
x43 = BitVec('x40', 64)
x40 = BitVec('x40', 32)

A = [BVPolynomial.create(x42*SignExt(32, x40) +1 + -1*x42 + -1*x43)]
F = Not(SignExt(32, 4294967295 + x40) +\
        x42*SignExt(32, x40)*SignExt(32, 4294967295 + x40)\
        == 18446744073709551615 + x43*SignExt(32, x40)) 

P = BVFormula.create(F)
print(A)
print(P)
S = simplify_polynomial_formula(P, A)
print(S)
