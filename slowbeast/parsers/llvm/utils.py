from struct import unpack, pack

from slowbeast.util.debugging import warn
from slowbeast.domains.constants import ConstantTrue, ConstantFalse
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.domains.pointer import get_null_pointer
from slowbeast.ir.types import IntType, FloatType, PointerType


def _getInt(s):
    try:
        if s.startswith("0x"):
            return int(s, 16)
        else:
            if "e" in s:  # scientific notation
                if float(s) > 0 or float(s) < 0:
                    warn("Concretized float number: {0}".format(s))
                    # return None
                return int(float(s))
            else:
                return int(s)
    except ValueError:
        return None


def trunc_to_float(x):
    return unpack("f", pack("f", x))[0]


def to_float_ty(val):
    if isinstance(val, ConcreteVal) and not val.is_float():
        return ConcreteVal(float(val.value()), FloatType(val.bitwidth()))
    return val


def _get_float(s):
    try:
        if s.startswith("0x"):
            # llvm writes the constants as double
            # FIXME: get the byte order from module
            return trunc_to_float(unpack(">d", int(s, 16).to_bytes(8, "big"))[0])
        else:
            return float(s)
    except ValueError:
        return None


def _get_double(s):
    try:
        if s.startswith("0x"):
            # llvm writes the constants as double (even when it is 32 bit)
            return unpack(">d", int(s, 16).to_bytes(8, "big"))[0]
        else:
            return float(s)
    except ValueError:
        return None


def _bitwidth(ty):
    if len(ty) < 2:
        return None
    if ty[0] == "i":
        return _getInt(ty[1:])
    elif ty.startswith("double"):
        # FIXME: get this from program
        return 64
    elif ty.startswith("float"):
        return 32
    else:
        return None


def is_pointer_ty(ty):
    if isinstance(ty, str):
        return ty[-1] == "*"

    assert ty.is_pointer == is_pointer_ty(str(ty))
    return ty.is_pointer


def is_array_ty(ty):
    if isinstance(ty, str):
        if len(ty) < 2:
            return False
        return ty[0] == "[" and ty[-1] == "]"
    assert ty.is_array == is_array_ty(str(ty))
    return ty.is_array


def parseArrayTyByParts(ty):
    print(parts)


def getArrayTySize(m, ty):
    assert is_array_ty(ty)
    sty = str(ty)
    parts = sty.split()
    assert parts[1] == "x", "Invalid array type"
    assert parts[0].startswith("[")
    assert parts[-1].endswith("]")
    return int(parts[0][1:]) * type_size_in_bits(m, " ".join(parts[2:])[:-1])


def type_size_in_bits(m, ty):
    if not isinstance(ty, str) and hasattr(m, "get_type_size"):
        return m.get_type_size(ty)

    # FIXME: get rid of parsing str
    # FIXME: get rid of the magic constants and use the layout from the program
    POINTER_SIZE = 64
    if not isinstance(ty, str):
        if ty.is_pointer:
            return POINTER_SIZE
        if ty.is_struct:
            return None  # unsupported

    sty = str(ty)
    if is_array_ty(ty):
        return getArrayTySize(m, ty)
    elif is_pointer_ty(ty):
        return POINTER_SIZE
    elif sty == "double":
        return 64
    elif sty == "float":
        return 32
    else:
        assert "*" not in sty, "Unsupported type: {0}".format(sty)
        return _bitwidth(sty)
    return None


def type_size(m, ty):
    ts = type_size_in_bits(m, ty)
    if ts is not None:
        if ts == 0:
            return 0
        return int(max(ts / 8, 1))
    return None


def get_sb_type(m, ty):
    if is_pointer_ty(ty):
        return PointerType()

    sty = str(ty)
    if sty in ("void", "metadata"):
        return None

    ts = type_size_in_bits(m, ty)
    if ts is None:
        return None

    if sty in ("float", "double"):
        return FloatType(ts)
    elif sty.startswith("i"):
        return IntType(ts)
    assert False, f"Unsupported type: {ty}"
    return None


def getFloatConstant(sval, isdouble=True):
    if isdouble:
        return _get_double(sval)
    return _get_float(sval)


def get_pointer_constant(val):
    assert is_pointer_ty(val.type)
    parts = str(val).split()
    if parts[-1] == "null":
        return get_null_pointer()
    return None


def getConstant(val):
    # My, this is so ugly... but llvmlite does
    # not provide any other way...
    if is_pointer_ty(val.type):
        return get_pointer_constant(val)

    parts = str(val).split()
    if len(parts) != 2:
        return None

    bw = _bitwidth(parts[0])
    if not bw:
        return None
    isdouble = parts[0] == "double"
    isfloating = parts[0] == "float" or isdouble

    if isfloating:
        c = getFloatConstant(parts[1], isdouble)
    else:
        c = _getInt(parts[1])
    if c is None:
        if bw == 1:
            if parts[1] == "true":
                return ConcreteVal(1, IntType(bw))
                # return ConstantTrue
            elif parts[1] == "false":
                return ConcreteVal(0, IntType(bw))
                # return ConstantFalse
        return None

    return ConcreteVal(c, FloatType(bw) if isfloating else IntType(bw))


def bvToBoolElseId(bv):
    if bv.is_concrete():
        if bv.value() == 0:
            return ConstantFalse
        else:
            return ConstantTrue
    return bv


def getLLVMOperands(inst):
    return [x for x in inst.operands]
