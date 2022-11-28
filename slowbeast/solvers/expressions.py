from slowbeast.domains.concrete import ConcreteDomain, ConcreteVal
from slowbeast.domains.symbolic import SymbolicDomain
from slowbeast.ir.types import Type, IntType, BoolType
from slowbeast.domains.value import Value

optimize_exprs = True


def is_symbolic(v):
    return SymbolicDomain.belongto(v)


def is_concrete(v):
    assert not ConcreteDomain.belongto(v) or not is_symbolic(v)
    return ConcreteDomain.belongto(v)


class ExprOptIntf:
    """
    Expressions optimizer interface
    """

    def optimize(expr, *assumptions):
        """Optimize the expression given the assumptions"""
        return expr


class SymbolicExprOpt(ExprOptIntf):
    def optimize(expr, *assumptions):
        if not optimize_exprs:
            return expr

        optexpr = SymbolicDomain.simplify(expr, *assumptions)
        # lower the symbolic expression into a concrete value
        # if possible
        const = SymbolicDomain.pythonConstant(optexpr)
        if const is not None:
            return ConcreteVal(const, optexpr.type())
        return optexpr


def em_optimize_expressions(b=True):
    global optimize_exprs
    optimize_exprs = b


opt = SymbolicExprOpt.optimize


class ExprManager:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    __slots__ = "_names"

    def __init__(self):
        self._names = {}

    def ConcreteVal(self, c, bw):
        return ConcreteDomain.Value(c, bw)

    def Var(self, name, ty):
        assert isinstance(name, str)
        names = self._names
        s = names.get(name)
        if s:
            assert (
                s.type() == ty
            ), f"Creating the same value with different type: {name} ({s.type()} != {ty})"
        else:
            s = SymbolicDomain.Var(name, ty)
            names[name] = s
        assert s, "No var was created"
        return s

    def Bool(self, name):
        return self.Var(name, BoolType())

    # def subexpressions(self, expr):
    #    if expr.is_concrete():
    #        yield expr
    #    else:
    #        yield from SymbolicDomain.subexpressions(expr)

    def simplify(self, expr):
        if expr.is_concrete():
            return expr
        return SymbolicExprOpt.optimize(expr)

    def fresh_value(self, name, ty):
        assert isinstance(name, str)
        names = self._names
        idx = name.rfind("#")
        if idx == -1:
            origname = name
            cnt = 1
        else:
            origname = name[:idx]
            cnt = int(name[idx + 1 :])
        s = names.get(name)
        while s:
            cnt += 1
            name = f"{origname}#{cnt}"
            s = names.get(name)

        s = SymbolicDomain.Var(name, ty)
        names[name] = s
        return s

    def substitute(self, expr, *vals):
        if ConcreteDomain.belongto(expr):
            return expr
        lift = self.lift
        return SymbolicDomain.substitute(expr, *((lift(a), lift(b)) for (a, b) in vals))

    def equals(self, e1, e2):
        """
        Values are syntactically equal
        """
        if ConcreteDomain.belongto(e1, e2):
            return e1 == e2
        lift = self.lift
        return lift(e1) == lift(e2)

    def drop_value(self, name):
        self._names.pop(name)

    def Int1(self, name):
        return self.Var(name, IntType(1))

    def Int8(self, name):
        return self.Var(name, IntType(8))

    def Int16(self, name):
        return self.Var(name, IntType(16))

    def Int32(self, name):
        return self.Var(name, IntType(32))

    def Int64(self, name):
        return self.Var(name, IntType(64))

    def lift(self, v):
        return SymbolicDomain.lift(v)

    def get_true(self):
        return SymbolicDomain.get_true()

    def get_false(self):
        return SymbolicDomain.get_false()

    def conjunction(self, *args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments
        """
        assert all(map(lambda a: a.is_bool(), args))
        if len(args) == 0:
            return ConcreteDomain.get_true()
        if len(args) == 1:
            return args[0]
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.conjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.conjunction(*map(lift, args)))

    def disjunction(self, *args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments.
        """
        assert all(map(lambda a: a.is_bool(), args))
        if len(args) == 0:
            return ConcreteDomain.get_false()
        if len(args) == 1:
            return args[0]
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.disjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.disjunction(*map(lift, args)))

    def Ite(self, c, a, b):
        if ConcreteDomain.belongto(c):
            cval = c.value()
            if cval is True:
                return a
            if cval is False:
                return b
            raise RuntimeError(f"Invalid bool: {cval}")
            # return ConcreteDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Ite(lift(c), lift(a), lift(b)))

    def And(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.And(lift(a), lift(b)))

    def Or(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Or(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Or(lift(a), lift(b)))

    def Xor(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Xor(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Xor(lift(a), lift(b)))

    def Not(self, a):
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Not(a)
        return opt(SymbolicDomain.Not(self.lift(a)))

    def Neg(self, a, isfloat):
        """Return the negated number"""
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Neg(a, isfloat)
        return opt(SymbolicDomain.Neg(self.lift(a), isfloat))

    def Abs(self, a):
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Abs(a)
        return opt(SymbolicDomain.Abs(self.lift(a)))

    def FpOp(self, op, val):
        if ConcreteDomain.belongto(val):
            return ConcreteDomain.FpOp(op, val)
        r = SymbolicDomain.FpOp(op, self.lift(val))
        return opt(r) if r else r  # FpOp may return None

    def ZExt(self, a, b):
        assert ConcreteDomain.belongto(b), "Invalid zext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.ZExt(a, b)
        return opt(SymbolicDomain.ZExt(a, b))

    def SExt(self, a, b):
        assert ConcreteDomain.belongto(b), "Invalid sext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.SExt(a, b)
        return opt(SymbolicDomain.SExt(a, b))

    def Cast(self, a: Value, ty: Type):
        """reinterpret cast"""
        assert isinstance(ty, Type)
        if a.type() == ty:
            return a
        if a.is_pointer():
            # pointer to int or int to pointer (where the int is actually
            # a pointer as we do not change its value)
            return a
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Cast(a, ty)
        return SymbolicDomain.Cast(a, ty)

    def BitCast(self, a: Value, ty: Type):
        """static cast"""
        assert isinstance(ty, Type)
        if a.type() == ty:
            return a
        if a.is_pointer():
            # pointer to int or int to pointer (where the int is actually
            # a pointer as we do not change its value)
            return a
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.BitCast(a, ty)
        return SymbolicDomain.BitCast(a, ty)

    def Extract(self, a, start, end):
        assert ConcreteDomain.belongto(start, end), "Invalid sext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Extract(a, start, end)
        return opt(SymbolicDomain.Extract(a, start, end))

    def Concat(self, *args):
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.Concat(*args)
        lift = self.lift
        return opt(SymbolicDomain.Concat(*map(lift, args)))

    def Shl(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Shl(a, b)
        return opt(SymbolicDomain.Shl(self.lift(a), self.lift(b)))

    def AShr(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.AShr(a, b)
        return opt(SymbolicDomain.AShr(self.lift(a), self.lift(b)))

    def LShr(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.LShr(a, b)
        return opt(SymbolicDomain.LShr(self.lift(a), self.lift(b)))

    ##
    # Relational operators

    def Le(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Le(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Le(lift(a), lift(b), unsigned, isfloat))

    def Lt(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Lt(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Lt(lift(a), lift(b), unsigned, isfloat))

    def Ge(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ge(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Ge(lift(a), lift(b), unsigned, isfloat))

    def Gt(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Gt(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Gt(lift(a), lift(b), unsigned, isfloat))

    def Eq(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Eq(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Eq(lift(a), lift(b), unsigned, isfloat))

    def Ne(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ne(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Ne(lift(a), lift(b), unsigned, isfloat))

    ##
    # Artihmetic operations
    def Add(self, a, b, isfloat=False):
        if ConcreteDomain.belongto(a):
            if a.value() == 0:
                return b
            if ConcreteDomain.belongto(b):
                if b.value() == 0:
                    return a
                return ConcreteDomain.Add(a, b, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Add(lift(a), lift(b), isfloat))

    def Sub(self, a, b, isfloat=False):
        if ConcreteDomain.belongto(b):
            if b.value() == 0:
                return a
            if ConcreteDomain.belongto(a):
                return ConcreteDomain.Sub(a, b, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Sub(lift(a), lift(b), isfloat))

    def Mul(self, a, b, isfloat=False):
        if ConcreteDomain.belongto(a):
            if a.value() == 0:
                return a
            if a.value() == 1:
                return b
            if ConcreteDomain.belongto(b):
                if b.value() == 0:
                    return b
                if b.value() == 1:
                    return a
                return ConcreteDomain.Mul(a, b, isfloat)
        elif ConcreteDomain.belongto(b):
            if b.value() == 1:
                return a
        lift = self.lift
        return opt(SymbolicDomain.Mul(lift(a), lift(b), isfloat))

    def Div(self, a, b, unsigned=False, isfloat=False):
        if ConcreteDomain.belongto(a):
            if a.value() == 0:
                return a
            if ConcreteDomain.belongto(b):
                return ConcreteDomain.Div(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Div(lift(a), lift(b), unsigned, isfloat))

    def Rem(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Rem(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Rem(lift(a), lift(b), unsigned))
