from slowbeast.ir.instruction import (
    Alloc,
    Assume,
    Assert,
    Cmp,
    Print,
    Abs,
    FpOp,
    ZExt,
    Cast,
)
from slowbeast.domains.constants import ConstantTrue, ConstantFalse
from ...domains.concrete import ConcreteVal
from slowbeast.ir.types import FloatType, IntType, get_size_type
from .utils import getLLVMOperands, type_size_in_bits, to_float_ty

# FIXME: turn to a dict with separate handlers
special_functions = [
    "llvm.fabs.f32",
    "llvm.fabs.f64",
    "fesetround",
    "nan",
    "__isnan",
    "__isnanf",
    "__isnanl",
    "__isinf",
    "__isinff",
    "__isinfl",
    # NOTE: do we want to implement these as instructions? Probably not...
    "__fpclassify",
    "__fpclassifyf",
    "__fpclassifyl",
    "__signbit",
    "__signbitf",
    "__signbitl",
    "malloc",
    "__assert_fail",
    "__VERIFIER_error",
    "__VERIFIER_assert",
    "__VERIFIER_assume",
    "verifier.assume",
    "assume_abort_if_not",
    "__VERIFIER_assert",
    "__VERIFIER_silent_exit",
    "__INSTR_check_nontermination_header",
    "__INSTR_check_nontermination",
    "__INSTR_check_assume",
    "__INSTR_fail",
    "__slowbeast_print",
]


def create_special_fun(parser, inst, fun, error_funs):
    """
    Return a pair R, S where R is the representant
    used for mapping of instructions and S is the sequence
    of instructions created
    """
    module = parser.llvmmodule
    if fun in error_funs:
        A = Assert(ConstantFalse, "error function called!")
        return A, [A]
    elif fun == "__assert_fail":
        A = Assert(ConstantFalse, "assertion failed!")
        return A, [A]
    elif fun == "__VERIFIER_error":
        A = Assert(ConstantFalse, "__VERIFIER_error called!")
        return A, [A]
    elif fun in ("__VERIFIER_assume", "assume_abort_if_not", "verifier.assume"):
        operands = getLLVMOperands(inst)
        cond = parser.operand(operands[0])
        C = Cmp(
            Cmp.NE,
            cond,
            ConcreteVal(0, IntType(type_size_in_bits(module, operands[0].type))),
        )
        A = Assume(C)
        return A, [C, A]
    elif fun == "__VERIFIER_silent_exit":
        A = Assume(ConstantFalse)
        return A, [A]
    elif fun == "__VERIFIER_assert" or fun == "__INSTR_check_assume":
        operands = getLLVMOperands(inst)
        cond = parser.operand(operands[0])
        C = Cmp(
            Cmp.NE,
            cond,
            ConcreteVal(0, IntType(type_size_in_bits(module, operands[0].type))),
        )
        A = Assert(C)
        return A, [C, A]
    elif fun == "__INSTR_check_nontermination_header":
        return None, []
    elif fun == "__INSTR_fail":
        A = Assert(ConstantFalse)
        return A, [A]
    elif fun == "__INSTR_check_nontermination":
        operands = getLLVMOperands(inst)
        cond = parser.operand(operands[0])
        C = Cmp(Cmp.NE, cond, ConstantTrue)
        A = Assert(C)
        return A, [C, A]
    elif fun == "malloc":
        operands = getLLVMOperands(inst)
        assert (
            len(operands) == 2
        ), "Invalid malloc"  # (call has +1 operand for the function)
        size = parser.operand(operands[0])
        A = Alloc(size, on_heap=True)
        return A, [A]
    elif fun.startswith("llvm.fabs."):
        operands = getLLVMOperands(inst)
        val = parser.operand(operands[0])
        A = Abs(val)
        return A, [A]
    elif fun in ("__isinf", "__isinff", "__isinfl"):
        val = to_float_ty(parser.operand(getLLVMOperands(inst)[0]))
        O = FpOp(FpOp.IS_INF, val)
        P = ZExt(O, ConcreteVal(type_size_in_bits(module, inst.type), get_size_type()))
        return P, [O, P]
    elif fun in "nan":
        I = Cast(ConcreteVal(float("NaN"), FloatType(64)), FloatType(64))
        return I, [I]
    elif fun in ("__isnan", "__isnanf", "__isnanfl"):
        val = to_float_ty(parser.operand(getLLVMOperands(inst)[0]))
        O = FpOp(FpOp.IS_NAN, val)
        # the functions return int
        P = ZExt(O, ConcreteVal(type_size_in_bits(module, inst.type), get_size_type()))
        return P, [O, P]
    elif fun in ("__fpclassify", "__fpclassifyf", "__fpclassifyl"):
        val = to_float_ty(parser.operand(getLLVMOperands(inst)[0]))
        O = FpOp(FpOp.FPCLASSIFY, val)
        # the functions return int
        return O, [O]
    elif fun in ("__signbit", "__signbitf", "__signbitl"):
        val = to_float_ty(parser.operand(getLLVMOperands(inst)[0]))
        O = FpOp(FpOp.SIGNBIT, val)
        # the functions return int
        return O, [O]
    elif fun == "fesetround":
        raise NotImplementedError("fesetround is not supported yet")
    elif fun == "__slowbeast_print":
        P = Print(*[parser.operand(x) for x in getLLVMOperands(inst)[:-1]])
        return P, [P]
    else:
        raise NotImplementedError("Unknown special function: {0}".format(fun))
