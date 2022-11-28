from slowbeast.ir.types import FloatType
from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal


class ConcreteFloat(ConcreteVal):
    def __init__(self, n, bw):
        assert isinstance(n, float), n
        assert isinstance(bw, int), bw
        super().__init__(n, FloatType(bw))


class ConcreteFloatsDomain:
    """
    Takes care of handling concrete float computations.
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            assert isinstance(a, Value), a
            if not (a.is_concrete() and a.is_float()):
                return False
        return True

    def Value(c, bw):
        return ConcreteFloat(float(c), bw)

    ##
    # Relational operators
    def Le(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() <= b.value())

    def Lt(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() < b.value())

    def Ge(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() >= b.value())

    def Gt(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() > b.value())

    def Eq(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        aval, bval = a.value(), b.value()
        return ConcreteBool(aval <= bval and aval >= bval)

    def Ne(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        aval, bval = a.value(), b.value()
        return ConcreteBool(aval < bval and aval > bval)

    ##
    # Arithmetic operations
    def Add(a, b):
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() + b.value(), bw)

    def Sub(a, b):
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() - b.value(), bw)

    def Mul(a, b):
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() * b.value(), bw)

    def Div(a, b, unordered=False):
        assert ConcreteFloatsDomain.belongto(a, b)
        bw = a.bitwidth()
        return ConcreteFloat(a.value() / b.value(), bw)
