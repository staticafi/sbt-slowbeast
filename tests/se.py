import sys
from os.path import join, abspath, dirname
pth = join(dirname(__file__), '..')
sys.path.append(abspath(pth))

from slowbeast.ir.program import *
from slowbeast.ir.bblock import *
from slowbeast.ir.instruction import *
from slowbeast.ir.function import *

from slowbeast.interpreter.interpreter import *

if __name__ == "__main__":
    P = Program()

    FOO = Function("foo", 2)

    B0 = BBlock(FOO)

    A = Alloc(Constant(4))
    B0.append(A)
    B0.append(Store(FOO.argument(0), FOO.argument(1)))
    B0.append(Return(None))

    P.add_fun(FOO)

    F = Function("main")

    B0 = BBlock(F)
    B1 = BBlock(F)
    B2 = BBlock(F)
    B3 = BBlock(F)

    A = Alloc(Constant(4))
    B0.append(A)
    B0.append(Store(Constant(0), A))
    B0.append(Branch(Constant(True), B1, B1))

    L1 = Load(A)
    B1.append(L1)
    ADD = Add(L1, Constant(1))
    B1.append(ADD)
    B1.append(Store(ADD, A))
    L2 = Load(A)
    B1.append(L2)
    B1.append(Print(L2, Constant("\n")))
    B1.append(Branch(Constant(True), B2, B2))

    A1 = Alloc(Constant(8))
    B2.append(A1)
    B2.append(Store(A, A1))
    L = Load(A1)
    B2.append(L)
    CALL = Call(FOO, L, A1)
    B2.append(CALL)
    C = Cmp(Cmp.EQ, ADD, L2)
    B2.append(C)
    L = Load(A1)
    C2 = Cmp(Cmp.EQ, A, L)
    B2.append(L)
    B2.append(C2)
    B2.append(Assume(C, C2))
    B2.append(Branch(C, B3, B3))

    B3.append(Return(Constant(0)))


    P.add_fun(F)
    P.set_entry(F)

    I = Interpreter(P)
    I.run()
