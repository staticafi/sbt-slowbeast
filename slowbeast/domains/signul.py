from slowbeast.domains.concrete import ConcreteVal, dom_is_concrete
from slowbeast.domains.value import Value
from slowbeast.ir.types import Type, IntType, BoolType


def dom_is_signul(*v):
    return all(map(lambda x: x.KIND == 4, v))


def abstract(v):
    if v < 0:
        v = SignULValue.LT0
    else:
        v = SignULValue.GT0 if v > 0 else SignULValue.ZERO
    return v


class SignULValue(Value):
    """
    Extends concrete domain by -, 0, +  abstractions
    """

    KIND = 4

    # values
    LT0 = -2
    LE0 = -1
    ZERO = 0
    GE0 = 1
    GT0 = 2
    NONZERO = 3
    ANY = 4

    def val_to_str(x):
        if x == SignULValue.LT0:
            return "-"
        if x == SignULValue.LE0:
            return "-0"
        if x == SignULValue.ZERO:
            return "0"
        if x == SignULValue.GE0:
            return "0+"
        if x == SignULValue.GT0:
            return "+"
        if x == SignULValue.NONZERO:
            return "-+"
        if x == SignULValue.ANY:
            return "*"

    __slots__ = "_value", "_lower", "_upper"

    def __init__(self, v, t, l=None, u=None):
        assert isinstance(v, (int, bool, float)), f"Invalid constant: {v} {type(v)}"
        assert isinstance(t, Type), f"Invalid type: {t}"
        assert SignULValue.LT0 <= v <= SignULValue.ANY
        super().__init__(t)
        self._value = v
        # lower and upper bound put on this value due to branching
        self._lower = l
        self._upper = u

        assert not self.is_pointer(), "Incorrectly constructed pointer"

    def is_concrete(self):
        return self.value() == SignULValue.ZERO

    def value(self):
        return self._value

    def lower(self):
        return self._lower

    def upper(self):
        return self._upper

    def as_value(self):
        return self.__repr__()

    def __hash__(self):
        return self.value()

    def __eq__(self, rhs):
        return self.value() == rhs.value()

    def __repr__(self):
        return "<{0}[{1},{2}]:{3}>".format(
            SignULValue.val_to_str(self.value()),
            "-\u221e" if self._lower is None else self._lower,
            "\u221e" if self._upper is None else self._upper,
            self.type(),
        )


def get_unsigned(v):
    if v == SignULValue.LT0:
        return SignULValue.GT0
    if v == SignULValue.LE0:
        return SignULValue.GE0
    if v == SignULValue.NONZERO:
        return SignULValue.GT0
    if v == SignULValue.ANY:
        return SignULValue.GE0
    return v


class SignULDomain:
    """
    Takes care of handling symbolic computations
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if a.KIND != 4:
                return False
        return True

    def lift(v):
        if v.KIND == 4:
            return v

        val = v.value()
        if v.KIND == 3:
            return SignULValue(abstract(val), v.type())
        if v.KIND == 1:
            return SignULValue(abstract(val), v.type(), val, val)

        raise NotImplementedError(f"Invalid value for lifting: {v}")

    def concretize(x):
        assert isinstance(x, SignULValue)
        # the internal values in fact correspond to concrete models
        return x.value()

    def Constant(v, bw):
        return SignULValue(abstract(v), IntType(bw))

    def Var(ty):
        return SignULValue(SignULValue.ANY, ty)

    def may_be_true(x):
        v = x.value()
        # all other values represent some non-zero values
        return v != SignULValue.ZERO

    ##
    # Logic operators
    def conjunction(*args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert dom_is_signul(*args)
        assert all(map(lambda a: a.is_bool(), args))
        # this way it works for abstract values and concrete values too
        return SignULValue(all(map(lambda x: x.value() != 0, args)), BoolType())

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert dom_is_signul(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return SignULValue(any(map(lambda x: x.value() != 0, args)), BoolType)

    # def And(a, b):
    #    assert dom_is_signul(a, b)
    #    assert a.type() == b.type()
    #    if a.is_bool():
    #        return SignULDomain(1 if (a.value() != 0 and b.value() != 0) else 0)

    #    aval = a.value()
    #    bval = b.value()
    #    # if aval != bval:
    #    #    # aval & bval >= 0
    #    #    return SignULDomain(SignULDomain.
    #    # if aval >= 0 and bval >= 0:
    #    #    return SignULDomain(0, a.type())
    #    return SignULDomain(a.value() & b.value(), a.type())

    # def Or(a, b):
    #    assert dom_is_signul(a, b)
    #    assert a.type() == b.type()
    #    if a.is_bool():
    #        return ConcreteBool(a.value() or b.value())
    #    else:
    #        return ConcreteVal(a.value() | b.value(), a.type())

    # def Xor(a, b):
    #    assert dom_is_signul(a, b)
    #    assert a.type() == b.type()
    #    return ConcreteVal(a.value() ^ b.value(), a.type())

    def Not(a):
        assert dom_is_signul(a)
        aval = a.value()
        if a.is_bool():
            if aval == SignULValue.ZERO:
                return SignULValue(SignULValue.GT0, BoolType())
            if aval in (SignULValue.NONZERO, SignULValue.LT0, SignULValue.GT0):
                return SignULValue(SignULValue.ZERO, BoolType())
            return SignULValue(SignULValue.GE0, BoolType())
        else:
            if aval == SignULValue.ZERO:
                return SignULValue(SignULValue.LT0, a.type())
            if aval == SignULValue.LT0:
                return SignULValue(SignULValue.GT0, a.type())
            if aval == SignULValue.GT0:
                return SignULValue(SignULValue.LT0, a.type())
            return SignULValue(SignULValue.ANY, a.type())

    def ZExt(a, b):
        assert dom_is_signul(a)
        assert dom_is_concrete(b)
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        return SignULValue(SignULValue.ANY, IntType(b.value()))  # FIXME

    def SExt(a, b):
        assert dom_is_signul(a)
        assert dom_is_concrete(b)
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        return SignULValue(SignULValue.ANY, IntType(b.value()))  # FIXME

    def Cast(a: ConcreteVal, ty: Type):
        assert dom_is_signul(a, b)
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    #    """
    #    Reinterpret cast
    #    """
    #    assert dom_is_signul(a)
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
        assert dom_is_signul(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    def AShr(a, b):
        assert dom_is_signul(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    def LShr(a, b):
        assert dom_is_signul(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    #    val = a.value()
    #    return ConcreteVal(
    #        a.value() >> b.value()
    #        if val >= 0
    #        else (val + (1 << a.bitwidth())) >> b.value(),
    #        a.type(),
    #    )

    def Extract(a, start, end):
        assert dom_is_signul(a)
        assert dom_is_concrete(start), start
        assert dom_is_concrete(end), end
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    #    bitsnum = end.value() - start.value() + 1
    #    return ConcreteInt(
    #        (a.value() >> start.value()) & ((1 << (bitsnum)) - 1), bitsnum
    #    )

    def Rem(a, b, unsigned=False):
        assert dom_is_signul(a, b)
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

    #    assert b.value() != 0, "Invalid remainder"
    #    if unsigned:
    #        return ConcreteVal(getUnsigned(a) % getUnsigned(b), a.type())
    #    return ConcreteVal(a.value() % b.value(), a.type())

    ##
    # Relational operators
    def Le(a, b, unsigned=False):
        assert dom_is_signul(a, b)
        l, u = None, None
        return SignULValue(SignULValue.ANY, BoolType(), l, u)

    def Lt(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_signul(a, b)
        assert a.type() == b.type()
        l, u = None, None
        if b._upper:
            u = b._upper
        return SignULValue(SignULValue.ANY, BoolType(), l, u)
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) < getUnsigned(b))
        # return ConcreteBool(a.value() < b.value())

    def Ge(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_signul(a, b)
        assert a.type() == b.type()
        return SignULValue(SignULValue.ANY, BoolType())
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) >= getUnsigned(b))
        # return ConcreteBool(a.value() >= b.value())

    def Gt(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_signul(a, b)
        assert a.type() == b.type()
        return SignULValue(SignULValue.ANY, BoolType())
        # assert dom_is_signul(a, b)
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) > getUnsigned(b))
        # return ConcreteBool(a.value() > b.value())

    def Eq(a, b, unsigned=False):
        # FIXME FIXME FIXME
        assert dom_is_signul(a, b)
        assert a.type() == b.type()
        return SignULValue(SignULValue.ANY, BoolType())
        # if unsigned:
        #     return ConcreteBool(getUnsigned(a) == getUnsigned(b))
        # return ConcreteBool(a.value() == b.value())

    def Ne(a, b, unsigned=False):
        assert dom_is_signul(a, b)
        assert a.type() == b.type(), f"Incompatible types: {a.type()} != {b.type()}"
        aval = a.value()
        bval = b.value()

        if unsigned:
            aval = get_unsigned(aval)
            bval = get_unsigned(bval)

        # the only case when we know they are equal
        if aval == SignULValue.ZERO and bval == SignULValue.ZERO:  # both are ZERO
            return SignULValue(abstract(0), BoolType())

        # when they are surly non-equal?
        noneq = (
            (SignULValue.LT0, SignULValue.ZERO),
            (SignULValue.LT0, SignULValue.GE0),
            (SignULValue.LT0, SignULValue.GT0),
            (SignULValue.LE0, SignULValue.GT0),
            (SignULValue.ZERO, SignULValue.NONZERO),
            (SignULValue.GT0, SignULValue.ZERO),
        )
        if (aval, bval) in noneq or (bval, aval) in noneq:
            return SignULValue(abstract(1), BoolType())

        # the result is 0 or +
        return SignULValue(SignULValue.GE0, BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert dom_is_signul(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float()
        if a.is_float():
            # FIXME
            return SignULValue(
                SignULValue.ANY, a.type()
            )  # ConcreteVal(a.value() + b.value(), a.type())
        # bw = a.type().bitwidth()
        # FIXME
        return SignULValue(
            SignULValue.ANY, a.type()
        )  # ConcreteVal(a.value() + b.value(), a.type())

    def Sub(a, b):
        assert dom_is_signul(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), a.type())
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() - b.value(), bw), a.type())

    def Mul(a, b):
        assert dom_is_signul(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), a.type())
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() * b.value(), bw), a.type())

    def Div(a, b, unsigned=False):
        assert dom_is_signul(a, b)
        return SignULValue(SignULValue.ANY, a.type())  # FIXME

        assert a.is_int() or a.is_float()
        result_ty = a.type()
        if a.is_float():
            return ConcreteVal(a.value() - b.value(), result_ty)
        if unsigned:
            return ConcreteVal(getUnsigned(a) / getUnsigned(b), result_ty)
        return ConcreteVal(
            wrap_to_bw(int(a.value() / b.value()), result_ty.bitwidth()), result_ty
        )
