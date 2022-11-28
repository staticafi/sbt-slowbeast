class Monomial:
    """Monomial (power product)"""

    def __init__(self, *variables):
        self.vars = {v: e for v, e in variables if e != 0}

    def __getitem__(self, item):
        return self.vars.get(item)

    def copy(self):
        M = type(self)()
        M.vars = self.vars.copy()
        return M

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def degree(self):
        return sum(self.vars.values())

    def multiplied(self, *rhss):
        """product of self and monomials in rhss. Returns a new object"""

        V = self.vars
        newV = {}
        for m in rhss:
            assert isinstance(m, Monomial), m
            for v, e in m.vars.items():
                # increase exponent
                lv = V.get(v)
                exp = (lv or 0) + e
                if exp != 0:
                    newV[v] = exp
        # fill-in the rest of V
        for v, e in V.items():
            if newV.get(v) is None:
                newV[v] = e

        newMon = type(self)()
        newMon.vars = newV
        return newMon

    def divided(self, *rhss):
        newV = self.vars.copy()
        for m in rhss:
            assert isinstance(m, Monomial), m
            for v, e in m.vars.items():
                lv = newV.get(v)
                # decrease exponent
                if lv is None:
                    newV[v] = -e
                else:
                    # lv - e == 0
                    if lv == e:
                        newV.pop(v)
                    else:
                        newV[v] = lv - e
        newMon = type(self)()
        newMon.vars = newV
        return newMon

    def is_constant(self):
        return not self.vars

    def divides(self, rhs):
        RV = rhs.vars
        for v, e in self.vars.items():
            assert e != 0, self
            re = RV.get(v)
            if re is None:
                return False
            if re < e:
                return False
        return True

    def __eq__(self, rhs):
        return self.vars == rhs.vars

    def __hash__(self):
        # FIXME: we probably want some better hash
        return hash(sum(self.vars.values())) ^ hash(len(self.vars))

    def __repr__(self):
        V = self.vars
        if not V:
            return "[1]"
        return "[{0}]".format(
            "·".join(f"{v}^{e}" if e != 1 else str(v) for v, e in V.items())
        )


class Polynomial:
    def __init__(self, *elems):
        # mapping from monomials to their coefficient
        self.monomials = {}
        self.add(*elems)

    def __getitem__(self, item):
        return self.monomials.get(item)

    def copy(self):
        P = type(self)()
        P.monomials = {m.copy(): c for m, c in self.monomials.items()}
        return P

    def clean_copy(self):
        return type(self)()

    def _create_coefficient(self, c, m):
        """
        Create a coefficient 'c' to monomial 'm'.
        This method can be overriden, e.g., to have the
        coefficients modulo something.
        """
        return c

    def _coefficient_is_zero(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == 0

    def _coefficient_is_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == 1

    def _coefficient_is_minus_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == -1

    def _simplify_coefficient(self, c):
        """
        Simplify the given coefficient.
        This method can be overriden.
        """
        return c

    def __iter__(self):
        return iter(self.monomials.items())

    def _add_monomial(self, r, coef=1):
        M = self.monomials
        cur = M.get(r)
        if cur is None:
            addcoef = self._create_coefficient(coef, r)
            if not self._coefficient_is_zero(addcoef):
                M[r] = addcoef
        else:
            assert not self._coefficient_is_zero(cur)
            newcoef = self._simplify_coefficient(
                cur + self._create_coefficient(coef, r)
            )
            if self._coefficient_is_zero(newcoef):
                M.pop(r)
            else:
                M[r] = newcoef

    def add(self, *elems):
        M = self.monomials
        for r in elems:
            if isinstance(r, Monomial):
                self._add_monomial(r)
            elif isinstance(r, Polynomial):
                for rhsm, rhsc in r:
                    assert not self._coefficient_is_zero(rhsc), r
                    self._add_monomial(rhsm, rhsc)
            elif isinstance(r, tuple):  # tuple of coef and monomial
                self._add_monomial(r[1], r[0])
            else:
                raise NotImplementedError(f"Unhandled polynomial expression: {r}")

    def split(self, mons):
        """
        Put monomials from 'self' that match 'mons' to one polynom
        and the rest to other polynom
        """
        P1 = self.clean_copy()
        P2 = self.clean_copy()
        for m, c in self.monomials.items():
            if m in mons:
                P1.add((c, m))
            else:
                P2.add((c, m))
        return P1, P2

    def _mul_monomials(self, newP, lhsm, lhsc, rhsm, rhsc=None):
        newm = lhsm.multiplied(rhsm)
        newP[newm] = self._simplify_coefficient(
            lhsc * (self._create_coefficient(1, newm) if rhsc is None else rhsc)
        )

    def mul(self, *m):
        newP = {}
        for lhsm, lhsc in self.monomials.items():
            assert not self._coefficient_is_zero(lhsc)
            for r in m:
                if isinstance(r, Monomial):
                    self._mul_monomials(newP, lhsm, lhsc, r)
                elif isinstance(r, Polynomial):
                    for rhsm, rhsc in r:
                        assert not self._coefficient_is_zero(rhsc), r
                        self._mul_monomials(newP, lhsm, lhsc, rhsm, rhsc)
                elif isinstance(r, tuple):
                    self._mul_monomials(newP, lhsm, lhsc, r[1], r[0])
                else:
                    raise NotImplementedError(f"Unhandled polynomial expression: {r}")
        self.monomials = newP

    def change_sign(self):
        newP = {}
        cc = self._create_coefficient
        sc = self._simplify_coefficient
        for m, c in self.monomials.items():
            newP[m] = sc(c * cc(-1, m))
        self.monomials = newP

    def max_degree(self):
        return max(self.monomials.keys())

    def has(self, m):
        return self.monomials.get(m) is not None

    def get_coef(self, m):
        return self.monomials.get(m)

    def coef_is_one(self, m):
        return self._coefficient_is_one(self.monomials.get(m))

    def coef_is_minus_one(self, m):
        return self._coefficient_is_minus_one(self.monomials.get(m))

    def is_normed(self, m):
        x = self.monomials.get(m)
        if x is None:
            return False
        return self._coefficient_is_one(x) or self._coefficient_is_minus_one(x)

    def max_degree_elems(self):
        md = -1
        elems = []
        for m, c in self.monomials.items():
            d = m.degree()
            if d > md:
                elems = [m]
                md = d
            elif d == md:
                elems.append(m)
        return elems

    def pop(self, *ms):
        for m in ms:
            assert isinstance(m, Monomial), m
            self.monomials.pop(m)

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def __repr__(self):
        return str(self.monomials)

    def __str__(self):
        if not self.monomials:
            return "0"
        return " + ".join(map(lambda x: f"{x[1]}·{x[0]}", self.monomials.items()))


class ArithFormula:
    """
    Helper class for representing formulas in LIA or BV theory.
    This class makes it easy to work with commutative expressions
    by merging the operands into sets (if the operation is commutative).
    """

    # commutative operations
    AND = 1
    OR = 2
    EQ = 6

    # non-commutative operations
    MT_NON_COMMUTATIVE = 39
    MT_NON_ASSOCIATIVE = 49
    # non-associative operations
    NOT = 51
    SLE = 52
    SLT = 53
    ULT = 54
    ULE = 55
    SGE = 56
    SGT = 57
    UGT = 58
    UGE = 59

    # variables, constants
    MT_VALUES = 100
    POLYNOM = 101
    BOOLEAN = 102

    def __init__(self, ty, value, *operands):
        assert value is None or ty > ArithFormula.MT_VALUES
        self._ty = ty
        self._value = value
        self._children = []

        # flatter the expression already here
        isac = ArithFormula.op_is_assoc_and_comm(ty)
        for o in operands:
            if isac and o._ty == ty:
                assert o.children(), o
                self.add_child(*o.children())
            else:
                self.add_child(o)

        if len(self._children) == 1 and ty != ArithFormula.NOT:
            elem = self._children.pop()
            self._value = elem._value
            self._ty = elem._ty

    def replace_with(self, F):
        self._ty = F._ty
        self._value = F._value
        self._children = F._children

    def __getitem__(self, item):
        if self._children:
            assert item < len(self._children)
            return self._children[item]
        assert item == 0
        return self._value

    def add_child(self, *args):
        assert self._value is None, "Adding child to var/const"
        self._children.extend(args)

    def op_is_associative(op):
        return op <= ArithFormula.MT_NON_ASSOCIATIVE

    def op_is_commutative(op):
        return op <= ArithFormula.MT_NON_COMMUTATIVE

    def op_is_assoc_and_comm(op):
        return op <= ArithFormula.MT_NON_ASSOCIATIVE

    def __op_to_str(op):
        if op == ArithFormula.AND:
            return "∧"
        if op == ArithFormula.OR:
            return "∨"
        if op == ArithFormula.NOT:
            return "not"
        if op == ArithFormula.EQ:
            return "="
        if op == ArithFormula.SLE:
            return "≤"
        if op == ArithFormula.SLT:
            return "<"
        if op == ArithFormula.ULT:
            return "<u"
        if op == ArithFormula.ULE:
            return "≤u"
        if op == ArithFormula.SGE:
            return "≥"
        if op == ArithFormula.SGT:
            return ">"
        if op == ArithFormula.UGT:
            return ">u"
        if op == ArithFormula.UGE:
            return "≥u"
        return None

    def type(self):
        return self._ty

    def value(self):
        return self._value

    def value_equals(self):
        raise NotImplementedError("Must be overridden")

    def __iter__(self):
        return self._children.__iter__()

    def children(self):
        return self._children

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def expr(self):
        "Convert this object into expression for solver"
        raise NotImplementedError("Must be overridden")

    def is_eq(self):
        return self._ty == ArithFormula.EQ

    def is_not(self):
        return self._ty == ArithFormula.NOT

    def is_poly(self):
        return self._ty == ArithFormula.POLYNOM

    def is_bool(self):
        return self._ty == ArithFormula.BOOLEAN

    def is_value(self):
        return self._ty == ArithFormula.MT_VALUES

    def substitute_inplace(self, *subs):
        """Return True if the formula gets modified"""
        changed = False
        newchldrn = []
        for op in self._children:
            changed |= op.substitute_inplace(*subs)

            for s, to in subs:
                # should substitute?
                if s == op:
                    if self._ty == to._ty and ArithFormula.op_is_assoc_and_comm(to._ty):
                        newchldrn.extend(to.children())
                    else:
                        newchldrn.append(to)
                    changed = True
                else:
                    newchldrn.append(op)
        self._children = newchldrn
        return changed

    def __eq__(self, rhs):
        return (
            isinstance(rhs, ArithFormula)
            and self._ty == rhs._ty
            and self._value == rhs._value
            and self._children == rhs._children
        )

    # FIXME: not efficient
    def __hash__(self):
        v = self._value
        if v is not None:
            return hash(v)
        return hash(
            self._ty
        )  # ^ reduce(lambda a, b: hash(a) ^ hash(b), self._children)

    def __repr__(self):
        ty = self._ty
        if ty == ArithFormula.NOT:
            assert len(self._children) == 1
            return f"¬({self._children[0]})"
        elif ty > ArithFormula.MT_VALUES:
            assert len(self._children) == 0
            return str(self._value)
        op = ArithFormula.__op_to_str(ty)
        assert op
        return "({0})".format(op.join(map(str, self._children)))

    def __str__(self):
        ty = self._ty
        if ty == ArithFormula.NOT:
            assert len(self._children) == 1, self._children
            if self._children[0]._ty == ArithFormula.EQ:
                assert len(self._children[0]._children) >= 2, self._children
                return "({0})".format("≠".join(map(str, self._children[0]._children)))
            return f"¬({self._children[0]})"
        elif ty > ArithFormula.MT_VALUES:
            assert len(self._children) == 0
            return str(self._value)
        op = ArithFormula.__op_to_str(ty)
        assert op
        return "({0})".format(op.join(map(str, self._children)))
