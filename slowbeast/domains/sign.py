from slowbeast.domains.concrete import ConcreteVal, dom_is_concrete
from slowbeast.domains.value import Value
from slowbeast.ir.types import Type, IntType, BoolType


def dom_is_sign(*v):
    return all(map(lambda x: x.KIND == 3, v))


def abstract(v):
    if v < 0:
        v = ZOValue.LT0
    else:
        v = ZOValue.GT0 if v > 0 else ZOValue.ZERO
    return v


class ZOValue(Value):
    """
    Extends concrete domain by -, 0, +  abstractions
    """

    KIND = 3

    # values
    LT0 = -2
    LE0 = -1
    ZERO = 0
    GE0 = 1
    GT0 = 2
    NONZERO = 3
    ANY = 4

    def val_to_str(x):
        if x == ZOValue.LT0:
            return "-"
        if x == ZOValue.LE0:
            return "-0"
        if x == ZOValue.ZERO:
            return "0"
        if x == ZOValue.GE0:
            return "0+"
        if x == ZOValue.GT0:
            return "+"
        if x == ZOValue.NONZERO:
            return "-+"
        if x == ZOValue.ANY:
            return "*"

    __slots__ = "_value"

    def __init__(self, v, t):
        assert isinstance(v, (int, bool, float)), f"Invalid constant: {v} {type(v)}"
        assert isinstance(t, Type), f"Invalid type: {t}"
        assert ZOValue.LT0 <= v <= ZOValue.ANY
        super().__init__(t)
        self._value = v

        assert not self.is_pointer(), "Incorrectly constructed pointer"

    def is_concrete(self):
        return self.value() == ZOValue.ZERO

    def value(self):
        return self._value

    def as_value(self):
        return ZOValue.val_to_str(self.value())

    def __hash__(self):
        return self.value()

    def __eq__(self, rhs):
        return self.value() == rhs.value()

    def __repr__(self):
        return "<{0}:{1}>".format(ZOValue.val_to_str(self.value()), self.type())


def get_unsigned(v):
    if v == ZOValue.LT0:
        return ZOValue.GT0
    if v == ZOValue.LE0:
        return ZOValue.GE0
    if v == ZOValue.NONZERO:
        return ZOValue.GT0
    if v == ZOValue.ANY:
        return ZOValue.GE0
    return v


class ZODomain:
    """
    Takes care of handling symbolic computations
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if a.KIND != 3:
                return False
        return True

    def lift(v):
        if v.KIND == 3:
            return v
        if v.KIND == 1:
            return ZOValue(abstract(v.value()), v.type())

        raise NotImplementedError(f"Invalid value for lifting: {v}")

    def concretize(x):
        assert isinstance(x, ZOValue)
        # the internal values in fact correspond to concrete models
        return x.value()

    def may_be_true(x):
        v = x.value()
        # all other values represent some non-zero values
        return v != ZOValue.ZERO

    def Constant(v, bw):
        return ZOValue(abstract(v), IntType(bw))

    def Var(ty):
        return ZOValue(ZOValue.ANY, ty)

    ##
    # Logic operators
    def conjunction(*args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert dom_is_sign(*args)
        assert all(map(lambda a: a.is_bool(), args))
        # this way it works for abstract values and concrete values too
        return ZOValue(all(map(lambda x: x.value() != 0, args)), BoolType())

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert dom_is_sign(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ZOValue(any(map(lambda x: x.value() != 0, args)), BoolType)

    # def And(a, b):
    #    assert dom_is_sign(a, b)
    #    assert a.type() == b.type()
    #    if a.is_bool():
    #        return ZODomain(1 if (a.value() != 0 and b.value() != 0) else 0)

    #    aval = a.value()
    #    bval = b.value()
    #    # if aval != bval:
    #    #    # aval & bval >= 0
    #    #    return ZODomain(ZODomain.
    #    # if aval >= 0 and bval >= 0:
    #    #    return ZODomain(0, a.type())
    #    return ZODomain(a.value() & b.value(), a.type())

    # def Or(a, b):
    #    assert dom_is_sign(a, b)
    #    assert a.type() == b.type()
    #    if a.is_bool():
    #        return ConcreteBool(a.value() or b.value())
    #    else:
    #        return ConcreteVal(a.value() | b.value(), a.type())

    # def Xor(a, b):
    #    assert dom_is_sign(a, b)
    #    assert a.type() == b.type()
    #    return ConcreteVal(a.value() ^ b.value(), a.type())

    def Not(a):
        assert dom_is_sign(a)
        aval = a.value()
        if a.is_bool():
            if aval == ZOValue.ZERO:
                return ZOValue(ZOValue.GT0, BoolType())
            if aval in (ZOValue.NONZERO, ZOValue.LT0, ZOValue.GT0):
                return ZOValue(ZOValue.ZERO, BoolType())
            return ZOValue(ZOValue.GE0, BoolType())
        else:
            if aval == ZOValue.ZERO:
                return ZOValue(ZOValue.LT0, a.type())
            if aval == ZOValue.LT0:
                return ZOValue(ZOValue.GT0, a.type())
            if aval == ZOValue.GT0:
                return ZOValue(ZOValue.LT0, a.type())
            return ZOValue(ZOValue.ANY, a.type())

    def ZExt(a, b):
        assert dom_is_sign(a)
        assert dom_is_concrete(b)
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        return ZOValue(ZOValue.ANY, IntType(b.value()))  # FIXME

    def SExt(a, b):
        assert dom_is_sign(a)
        assert dom_is_concrete(b)
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        return ZOValue(ZOValue.ANY, IntType(b.value()))  # FIXME

    def Cast(a: ConcreteVal, ty: Type):
        assert dom_is_sign(a, b)
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    #    """
    #    Reinterpret cast
    #    """
    #    assert dom_is_sign(a)
    #    if a.is_int():
    #        if ty.is_float():
    #            return ConcreteVal(float(a.value()), ty)
    #        elif ty.is_int():
    #            return ConcreteVal(a.value(), ty)
    #    elif a.is_float():
    #        if ty.is_float():
    #            return ConcreteVal(a.value(), ty)
    #    # unsupported yet
    #    # elif ty.is_int():
    #    #    return ConcreteVal(int(v), ty)
    #    return None  # unsupported conversion

    def Shl(a, b):
        assert dom_is_sign(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    def AShr(a, b):
        assert dom_is_sign(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    def LShr(a, b):
        assert dom_is_sign(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    #    val = a.value()
    #    return ConcreteVal(
    #        a.value() >> b.value()
    #        if val >= 0
    #        else (val + (1 << a.bitwidth())) >> b.value(),
    #        a.type(),
    #    )

    def Extract(a, start, end):
        assert dom_is_sign(a)
        assert dom_is_concrete(start), start
        assert dom_is_concrete(end), end
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    #    bitsnum = end.value() - start.value() + 1
    #    return ConcreteInt(
    #        (a.value() >> start.value()) & ((1 << (bitsnum)) - 1), bitsnum
    #    )

    def Rem(a, b, unsigned=False):
        assert dom_is_sign(a, b)
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

    #    assert b.value() != 0, "Invalid remainder"
    #    if unsigned:
    #        return ConcreteVal(getUnsigned(a) % getUnsigned(b), a.type())
    #    return ConcreteVal(a.value() % b.value(), a.type())

    ##
    # Relational operators
    def Le(a, b, unsigned=False):
        assert dom_is_sign(a, b)
        if unsigned:
            return ConcreteBool(getUnsigned(a) <= getUnsigned(b))
        return ConcreteBool(a.value() <= b.value())

    def Lt(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_sign(a, b)
        assert a.type() == b.type()
        return ZOValue(ZOValue.ANY, BoolType())
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) < getUnsigned(b))
        # return ConcreteBool(a.value() < b.value())

    def Ge(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_sign(a, b)
        assert a.type() == b.type()
        return ZOValue(ZOValue.ANY, BoolType())
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) >= getUnsigned(b))
        # return ConcreteBool(a.value() >= b.value())

    def Gt(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_sign(a, b)
        assert a.type() == b.type()
        return ZOValue(ZOValue.ANY, BoolType())
        # assert dom_is_sign(a, b)
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) > getUnsigned(b))
        # return ConcreteBool(a.value() > b.value())

    def Eq(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_sign(a, b)
        assert a.type() == b.type()
        return ZOValue(ZOValue.ANY, BoolType())
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) == getUnsigned(b))
        # return ConcreteBool(a.value() == b.value())

    def Ne(a, b, unsigned=False):
        assert dom_is_sign(a, b)
        assert a.type() == b.type(), f"Incompatible types: {a.type()} != {b.type()}"
        aval = a.value()
        bval = b.value()

        if unsigned:
            aval = get_unsigned(aval)
            bval = get_unsigned(bval)

        # the only case when we know they are equal
        if aval == ZOValue.ZERO and bval == ZOValue.ZERO:  # both are ZERO
            return ZOValue(abstract(0), BoolType())

        # when they are surly non-equal?
        noneq = (
            (ZOValue.LT0, ZOValue.ZERO),
            (ZOValue.LT0, ZOValue.GE0),
            (ZOValue.LT0, ZOValue.GT0),
            (ZOValue.LE0, ZOValue.GT0),
            (ZOValue.ZERO, ZOValue.NONZERO),
            (ZOValue.GT0, ZOValue.ZERO),
        )
        if (aval, bval) in noneq or (bval, aval) in noneq:
            return ZOValue(abstract(1), BoolType())

        # the result is 0 or +
        return ZOValue(ZOValue.GE0, BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert dom_is_sign(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float()
        if a.is_float():
            # FIXME
            return ZOValue(
                ZOValue.ANY, a.type()
            )  # ConcreteVal(a.value() + b.value(), a.type())
        # bw = a.type().bitwidth()
        # FIXME
        return ZOValue(
            ZOValue.ANY, a.type()
        )  # ConcreteVal(a.value() + b.value(), a.type())

    def Sub(a, b):
        assert dom_is_sign(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), a.type())
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() - b.value(), bw), a.type())

    def Mul(a, b):
        assert dom_is_sign(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), a.type())
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() * b.value(), bw), a.type())

    def Div(a, b, unsigned=False):
        assert dom_is_sign(a, b)
        return ZOValue(ZOValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        result_ty = a.type()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), result_ty)
        if unsigned:
            return ConcreteVal(getUnsigned(a) / getUnsigned(b), result_ty)
        return ConcreteVal(
            wrap_to_bw(int(a.value() / b.value()), result_ty.bitwidth()), result_ty
        )
