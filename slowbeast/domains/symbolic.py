from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import Type, IntType, BoolType, FloatType
from slowbeast.ir.instruction import FpOp
from slowbeast.solvers.arithformula import Monomial, Polynomial, ArithFormula
from slowbeast.util.debugging import FIXME

_use_z3 = True
if _use_z3:
    from z3 import (
        If,
        Or,
        And,
        Xor,
        Not,
        Bool,
        BoolVal,
        BitVec,
        BitVecVal,
        BitVecSort,
        URem,
        SRem,
        UDiv,
        ULT as BVULT,
        ULE as BVULE,
        UGT as BVUGT,
        UGE as BVUGE,
        ZeroExt as BVZExt,
        SignExt as BVSExt,
        Extract as BVExtract,
        Concat as BVConcat,
        LShR as BVLShR,
    )
    from z3 import is_const, is_bv, is_bv_value, is_bool, is_and, is_or, is_not
    from z3 import is_eq, is_distinct
    from z3 import (
        is_app_of,
        Z3_OP_SLEQ,
        Z3_OP_SLT,
        Z3_OP_SGEQ,
        Z3_OP_SGT,
        Z3_OP_ULT,
        Z3_OP_ULEQ,
        Z3_OP_UGT,
        Z3_OP_UGEQ,
        Z3_OP_EQ,
        Z3_OP_BMUL,
        Z3_OP_BADD,
        Z3_OP_BSUB,
        Z3_OP_ZERO_EXT,
        Z3_OP_SIGN_EXT,
        Z3_OP_CONCAT,
        Z3_OP_EXTRACT,
        Z3_OP_ITE,
    )
    from z3 import is_true, is_false, simplify, substitute
    from z3 import Goal, Tactic, Then, With, Repeat, OrElse
    from z3 import (
        is_fp,
        is_fp_value,
        is_fprm_value,
        FP,
        Float32,
        Float64,
        Float128,
        FPVal,
        fpDiv,
        fpAbs,
        fpNeg,
        fpIsInf,
        fpIsNaN,
        fpIsSubnormal,
        fpIsZero,
        fpIsNegative,
        fpToFP,
        fpFPToFP,
        fpSignedToFP,
        fpUnsignedToFP,
        fpToIEEEBV,
        RNE,
        fpToUBV,
        fpEQ,
        fpNEQ,
        fpGEQ,
        fpGT,
        fpLEQ,
        fpLT,
    )

    def _is_symbol(expr):
        return (
            is_const(expr)
            and not is_bv_value(expr)
            and not is_fp_value(expr)
            and not is_fprm_value(expr)
        )

    def trunc_fp(fexpr, bw):
        return simplify(fpFPToFP(RNE(), fexpr, get_fp_sort(bw)))

    def to_double(x):
        bw = x.bitwidth()
        if x.is_float() and bw == 64:
            return x._expr
        # we first must convert to float and then extend to double
        if x.is_float() and bw == 32:
            r = x._expr
        else:
            assert not x.is_float()
            # bitcast from IEEE
            r = simplify(fpToFP(x._expr, get_fp_sort(bw)))
        r = simplify(fpFPToFP(RNE(), r, Float64()))
        return r

    def to_bv(x):
        if x.is_float():
            r = simplify(fpToIEEEBV(x._expr))
            assert r.sort().size() == x.bitwidth(), f"{r.sort()}, {x.type()}"
            return r
        if x.is_bool():
            return boolToBV(x)
        return x.unwrap()

    def floatToUBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

    def floatToSBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

    def _bv_to_bool(b):
        if is_bool(b):
            return b
        return If(b != bv_const(0, b.sort().size()), TRUE(), FALSE())

    def mk_or(*e):
        if len(e) == 1:
            return e[0]
        return Or(*map(_bv_to_bool, e))

    def mk_and(*e):
        if len(e) == 1:
            return e[0]
        return And(*map(_bv_to_bool, e))

    def mk_add(*e):
        if len(e) < 2:
            return e[0]
        expr = e[0] + e[1]
        for i in range(2, len(e)):
            expr = expr + e[i]
        return expr

    def mk_mul(*e):
        if len(e) < 2:
            return e[0]
        expr = e[0] * e[1]
        for i in range(2, len(e)):
            expr = expr * e[i]
        return expr

    def TRUE():
        return BoolVal(True)

    def FALSE():
        return BoolVal(False)

    def bv(name, bw):
        return BitVec(name, bw)

    def bv_const(v, bw):
        return BitVecVal(v, bw)

    def bool_to_bv(b):
        if not is_bool(b):
            return b
        return If(b, bv_const(1, 1), bv_const(0, 1))

    def boolToBV(b):
        if not b.is_bool():
            return b.unwrap()
        return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))

    def castToFP(b):
        if b.is_float():
            return b.unwrap()
        return fpToFP(b.unwrap(), get_fp_sort(b.type().bitwidth()))

    def castToBool(b):
        if b.is_bool():
            return b.unwrap()
        return If(b.unwrap() != bv_const(0, b.bitwidth()), TRUE(), FALSE())

    def bv_size(bw):
        return bw.sort().size()

    def to_c_expression(expr):
        "An auxiliary method for debugging that converts expr to C expression"

        if is_and(expr):
            return "({0})".format(" && ".join(map(to_c_expression, expr.children())))
        if is_or(expr):
            return "({0})".format(" || ".join(map(to_c_expression, expr.children())))
        if is_not(expr):
            return f"!({to_c_expression(expr.children()[0])})"

        chlds = expr.children()
        if is_app_of(expr, Z3_OP_ITE):
            return f"({to_c_expression(chlds[0])} ? {to_c_expression(chlds[1])} : {to_c_expression(chlds[2])} )"
        if is_app_of(expr, Z3_OP_SLEQ) or is_app_of(expr, Z3_OP_ULEQ):
            return f"({to_c_expression(chlds[0])}) <= ({to_c_expression(chlds[1])})"
        if is_app_of(expr, Z3_OP_SLT) or is_app_of(expr, Z3_OP_ULT):
            return f"({to_c_expression(chlds[0])}) < ({to_c_expression(chlds[1])})"
        if is_app_of(expr, Z3_OP_SGEQ) or is_app_of(expr, Z3_OP_UGEQ):
            return f"({to_c_expression(chlds[0])}) >= ({to_c_expression(chlds[1])})"
        if is_app_of(expr, Z3_OP_SGT) or is_app_of(expr, Z3_OP_UGT):
            return f"({to_c_expression(chlds[0])}) > ({to_c_expression(chlds[1])})"

        return str(expr)

    def _expr_op_to_formula_op(expr):
        if is_and(expr):
            return ArithFormula.AND
        if is_or(expr):
            return ArithFormula.OR
        if is_not(expr):
            return ArithFormula.NOT

        if is_eq(expr):
            return ArithFormula.EQ
        if is_app_of(expr, Z3_OP_SLEQ):
            return ArithFormula.SLE
        if is_app_of(expr, Z3_OP_SLT):
            return ArithFormula.SLT
        if is_app_of(expr, Z3_OP_ULEQ):
            return ArithFormula.ULE
        if is_app_of(expr, Z3_OP_ULT):
            return ArithFormula.ULT
        if is_app_of(expr, Z3_OP_SGEQ):
            return ArithFormula.SGE
        if is_app_of(expr, Z3_OP_SGT):
            return ArithFormula.SGT
        if is_app_of(expr, Z3_OP_UGEQ):
            return ArithFormula.UGE
        if is_app_of(expr, Z3_OP_UGT):
            return ArithFormula.UGT

        # raise NotImplementedError(f"Unhandled operation: {expr}")
        return None

    class BVMonomial(Monomial):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """

        def __init__(self, *variabl):
            super().__init__(*variabl)

        def create(expr):
            raise NotImplementedError("Must be overridden")

        def expr(self):
            "Transform to Z3 expressions"
            V = self.vars
            if not V:
                return None
            it = iter(V.items())
            m, c = next(it)
            expr = m
            while c > 1:
                expr = expr * m
                c -= 1
            for m, c in it:
                while c > 0:
                    expr = expr * m
                    c -= 1
            return simplify(expr)

    class BVPolynomial(Polynomial):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """

        def __init__(self, bw, *elems):
            self._bw = bw  # bitwidth
            super().__init__(*elems)

        def bitwidth(self):
            return self._bw

        def copy(self):
            P = type(self)(self._bw)
            P.monomials = {m.copy(): c for m, c in self.monomials.items()}
            return P

        def clean_copy(self):
            return type(self)(self._bw)

        def _create_coefficient(self, c, m):
            """
            Create a coefficient 'c' to monomial 'm'.
            This method can be overriden, e.g., to have the
            coefficients modulo something.
            """
            if is_bv(c):
                return c
            return bv_const(c, self._bw)

        def _coefficient_is_zero(self, c):
            """
            Check whether the coefficient is zero.
            This method can be overriden.
            """
            assert is_bv(c), c
            val = simplify(c == 0)
            assert is_bool(val), val
            return val.__bool__()

        def _coefficient_is_one(self, c):
            """
            Check whether the coefficient is zero.
            This method can be overriden.
            """
            assert is_bv(c), c
            val = simplify(c == 1)
            assert is_bool(val), val
            return val.__bool__()

        def _coefficient_is_minus_one(self, c):
            """
            Check whether the coefficient is zero.
            This method can be overriden.
            """
            assert is_bv(c), c
            val = simplify(c == -1)
            assert is_bool(val), val
            return val.__bool__()

        def _simplify_coefficient(self, c):
            """
            Check whether the coefficient is zero.
            This method can be overriden.
            """
            return simplify(c)

        def create(expr):
            bw = 1 if is_bool(expr) else expr.size()
            if is_app_of(expr, Z3_OP_BADD):
                return BVPolynomial(
                    bw, *(BVPolynomial.create(e) for e in expr.children())
                )
            elif is_app_of(expr, Z3_OP_BMUL):
                pols = [BVPolynomial.create(e) for e in expr.children()]
                P = pols[0]
                for i in range(1, len(pols)):
                    P.mul(pols[i])
                return P
            # elif is_app_of(expr, Z3_OP_CONCAT) or\
            #        is_app_of(expr, Z3_OP_SIGN_EXT) or\
            #        is_app_of(expr, Z3_OP_ZERO_EXT) or\
            #        is_app_of(expr, Z3_OP_EXTRACT):
            #    # TODO: check that these operations are applied to const?
            #    return BVPolynomial(bw, BVMonomial((expr, 1)))
            # elif is_app_of(expr, Z3_OP_BUREM) or\
            #        is_app_of(expr, Z3_OP_BUREM_I) or\
            #        is_app_of(expr, Z3_OP_BSREM) or\
            #        is_app_of(expr, Z3_OP_BSREM_I) or\
            #        is_app_of(expr, Z3_OP_BUDIV) or\
            #        is_app_of(expr, Z3_OP_BSDIV) or\
            #        is_app_of(expr, Z3_OP_BUDIV_I) or\
            #        is_app_of(expr, Z3_OP_BSDIV_I):
            #    # TODO: check that these operations are applied to const?
            #    return BVPolynomial(bw, BVMonomial((expr, 1)))
            elif is_const(expr):
                if is_bv_value(expr):
                    return BVPolynomial(bw, (expr, BVMonomial()))
                return BVPolynomial(bw, BVMonomial((expr, 1)))

            return BVPolynomial(bw, BVMonomial((expr, 1)))
            # raise NotImplementedError(f"Unhandeld expression: {expr}")

        def expr(self):
            "Transform to Z3 expressions"
            M = self.monomials
            if not M:
                return bv_const(0, self._bw)

            it = iter(M.items())
            m, c = next(it)
            mexpr = bool_to_bv(m.expr())
            expr = c if mexpr is None else c * mexpr
            for m, c in it:
                mexpr = m.expr()
                expr += c if mexpr is None else c * mexpr
            return simplify(expr)

    class BVFormula(ArithFormula):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """

        def __init__(self, ty, *operands):
            super().__init__(ty, *operands)

        def create(expr):
            chlds = expr.children()
            op = _expr_op_to_formula_op(expr)
            if chlds:
                if op is None:
                    # it is a polynomial
                    return BVFormula(ArithFormula.POLYNOM, BVPolynomial.create(expr))
                isac = ArithFormula.op_is_assoc_and_comm(op)
                formula = BVFormula(op, None)
                for c in chlds:
                    f = BVFormula.create(c)
                    if f is None:
                        return None
                    if isac and op == _expr_op_to_formula_op(c):
                        for fc in f.children():
                            formula.add_child(fc)
                    else:
                        formula.add_child(f)
                return formula
            # return BVFormula(_expr_op_to_formula_op(expr), None,
            #                 *(BVFormula.create(c) for c in chlds))
            if not is_bv(expr):
                if is_bool(expr):
                    return BVFormula(ArithFormula.BOOLEAN, expr)
                return None  # it is no bitvector, we cannot do a polynom from it
            return BVFormula(ArithFormula.POLYNOM, BVPolynomial.create(expr))

        def value_equals(self, x):
            v = self._value
            if v is None:
                return False
            return is_bv_value(v) and v.as_long() == x

        def expr(self):
            "Convert this object into expression for solver"
            ty = self._ty
            if ty == ArithFormula.BOOLEAN:
                return self._value
            if ty == ArithFormula.POLYNOM:
                return self._value.expr()
            if ty == ArithFormula.AND:
                return mk_and(*(c.expr() for c in self._children))
            if ty == ArithFormula.OR:
                return mk_or(*(c.expr() for c in self._children))
            if ty == ArithFormula.NOT:
                assert len(self._children) == 1
                return Not(_bv_to_bool(self._children[0].expr()))

            chlds = self._children
            if len(chlds) != 2:
                raise NotImplementedError(f"Not implemented yet: {self}")
                return None
            if ty == ArithFormula.EQ:
                return chlds[0].expr() == chlds[1].expr()
            if ty == ArithFormula.SLE:
                return chlds[0].expr() <= chlds[1].expr()
            if ty == ArithFormula.SLT:
                return chlds[0].expr() < chlds[1].expr()
            if ty == ArithFormula.SGE:
                return chlds[0].expr() >= chlds[1].expr()
            if ty == ArithFormula.SGT:
                return chlds[0].expr() > chlds[1].expr()
            if ty == ArithFormula.ULE:
                return BVULE(chlds[0].expr(), chlds[1].expr())
            if ty == ArithFormula.ULT:
                return BVULT(chlds[0].expr(), chlds[1].expr())
            if ty == ArithFormula.UGE:
                return BVUGE(chlds[0].expr(), chlds[1].expr())
            if ty == ArithFormula.UGT:
                return BVUGT(chlds[0].expr(), chlds[1].expr())

            raise NotImplementedError(f"Not implemented yet: {self}")
            return None

    def subexpressions(expr):
        children = expr.children()
        for c in children:
            yield from subexpressions(c)
        yield expr

    def _symbols(expr, ret: set):
        if _is_symbol(expr):
            ret.add(expr)
        else:
            for c in expr.children():
                _symbols(c, ret)

    def symbols(expr):
        ret = set()
        _symbols(expr, ret)
        return ret

    def is_lit(e):
        return is_const(e) or (
            (
                is_app_of(e, Z3_OP_ZERO_EXT)
                or is_app_of(e, Z3_OP_SIGN_EXT)
                or is_app_of(e, Z3_OP_CONCAT)
                or is_app_of(e, Z3_OP_EXTRACT)
            )
            and is_lit(e.children()[0])
        )

    def _is_const_mul(expr):
        chld = expr.children()
        return is_app_of(expr, Z3_OP_BMUL) and is_lit(chld[0]) and is_lit(chld[1])

    def _get_replacable(expr, atoms):
        chld = expr.children()
        if _is_const_mul(expr):
            v = atoms.setdefault(expr, 0)
            atoms[expr] = v + 1
            return
        for c in chld:
            _get_replacable(c, atoms)

    def _desimplify_ext(expr):
        "replace concat with singext if possible -- due to debugging"
        if is_app_of(expr, Z3_OP_CONCAT):
            chld = expr.children()
            c0 = chld[0]
            if is_app_of(c0, Z3_OP_EXTRACT):
                params = c0.params()
                if (
                    params[0] == params[1] == (chld[-1].size() - 1)
                    and c0.children()[0] == chld[-1]
                ):
                    if all(map(lambda e: e == c0, chld[1:-1])):
                        return BVSExt(expr.size() - chld[-1].size(), chld[-1])
            des = [_desimplify_ext(c) for c in chld]
            assert len(des) == len(chld)
            assert len(des) > 1
            return BVConcat(des)
        else:
            if is_and(expr):
                return mk_and(*(_desimplify_ext(c) for c in expr.children()))
            elif is_or(expr):
                return mk_or(*(_desimplify_ext(c) for c in expr.children()))
            elif is_not(expr):
                return Not(*(_desimplify_ext(c) for c in expr.children()))
            elif is_app_of(expr, Z3_OP_BADD):
                return mk_add(*(_desimplify_ext(c) for c in expr.children()))
            elif is_app_of(expr, Z3_OP_BMUL):
                return mk_mul(*(_desimplify_ext(c) for c in expr.children()))
            elif is_app_of(expr, Z3_OP_CONCAT):
                return BVConcat(*(_desimplify_ext(c) for c in expr.children()))
            elif is_eq(expr):
                dc = (_desimplify_ext(c) for c in expr.children())
                return next(dc) == next(dc)
            elif is_distinct(expr):
                dc = (_desimplify_ext(c) for c in expr.children())
                return next(dc) != next(dc)
            else:
                assert not is_app_of(expr, Z3_OP_CONCAT), expr
                return expr.decl()(*(_desimplify_ext(c) for c in expr.children()))
                return expr

    def _rewrite_sext(expr):
        "replace sext(x + c) with sext(x) + c if possible"
        if is_const(expr):
            return expr
        chld = expr.children()
        # Do we want to recurse also into operands of == and !=?
        if is_app_of(expr, Z3_OP_SIGN_EXT):
            c0 = chld[0]
            if is_app_of(c0, Z3_OP_BADD):
                c0chld = c0.children()
                if len(c0chld) == 2:
                    c, x = c0chld[0], c0chld[1]
                    if not is_bv_value(c):
                        c, x = x, c
                    if is_bv_value(c) and is_const(x):
                        # expr = sext(x + c)
                        bw = c.size()
                        ebw = expr.size()
                        # expr = sext(x + 1)
                        if simplify(c == 1).__bool__():
                            return If(
                                x != 2 ** (bw - 1) - 1,
                                # BVSExt(ebw - bw, x) + BVZExt(ebw - bw, c),
                                # expr)
                                BVSExt(ebw - bw, x) + bv_const(1, ebw),
                                simplify(
                                    BVSExt(ebw - bw, bv_const(2 ** bw - 1, bw) + 1)
                                ),
                            )
                        # expr = sext(x + (-1))
                        elif simplify(c == -1).__bool__():
                            return If(
                                x != 2 ** (bw - 1),
                                # BVSExt(ebw - bw, x) + BVSExt(ebw - bw, c),
                                # expr)
                                BVSExt(ebw - bw, x) + bv_const(-1, ebw),
                                simplify(
                                    BVSExt(ebw - bw, bv_const(2 ** bw - 1, bw) - 1)
                                ),
                            )
                        # FIXME: do this for generic values
            return expr
        else:
            red = (_rewrite_sext(c) for c in chld)
            if is_and(expr):
                return mk_and(*red)
            elif is_or(expr):
                return mk_or(*red)
            elif is_not(expr):
                return Not(*red)
            elif is_app_of(expr, Z3_OP_CONCAT):
                return BVConcat(*red)
            elif is_app_of(expr, Z3_OP_BADD):
                return mk_add(*red)
            elif is_app_of(expr, Z3_OP_BMUL):
                return mk_mul(*red)
            elif is_eq(expr):
                return next(red) == next(red)
            elif is_distinct(expr):
                return next(red) != next(red)
            else:
                return expr

    def _get_common_monomials(P1, P2, same_coef=False):
        monomials = []
        for p1m, c1 in P1.monomials.items():
            c2 = P2.get_coef(p1m)
            if c2 is None:
                continue
            if not same_coef or (
                c1.size() == c2.size() and simplify(c1 == c2).__bool__()
            ):
                monomials.append(p1m)
        return monomials

    class PolynomialSimplifier:
        def __init__(self, *args):
            # these polynomials we'll use to simplify the given formula
            self.polynomials = [*args]
            # index of a polynomial and polynomials that we substitued into other polynomials -- to prevent cycles
            # FIXME: we do not use it right now...
            self.used = {}

        def add_poly(self, *ps):
            self.polynomials.extend(*ps)

        def _simplify_polynomial_formula(self, formula):
            # print("> SIMPLIFY", formula)
            # print("> WITH")
            # for p in self.polynomials:
            #    print('  ', p)
            # print('---')
            polynoms = self.polynomials
            assert formula.is_poly(), formula
            P = formula[0]
            for p in polynoms:
                me = p.max_degree_elems()
                if len(me) != 1:
                    # FIXME: we should keep track of polynomials that we substitued
                    # to not to get into a cycle
                    common = _get_common_monomials(p, P, same_coef=True)
                    if common:  # and all(map(lambda c: c in common, me)):
                        p1, p2 = p.split(common)
                        p1.change_sign()
                        P.add(p1)
                        P.add(p2)
                        continue
                    mP = P.copy()
                    mP.change_sign()
                    common = _get_common_monomials(p, mP, same_coef=True)
                    if common:  # and all(map(lambda c: c in common, me)):
                        p1, p2 = p.split(common)
                        p2.change_sign()
                        P.add(p1)
                        P.add(p2)
                        continue
                    continue
                # the rest of the polynomial must have a lesser degree now
                # so perform the substitution of the monomial with the maximal
                # degree
                mme = me[0]
                for monomial, coef in P:
                    # mc = P.get_coef(monomial)
                    # mec = p.get_coef(mme)
                    if not P.is_normed(monomial):
                        continue  # FOR NOW
                    if mme.divides(monomial):
                        # FIXME: multiply with the coefficient!
                        r = BVPolynomial(P.bitwidth(), monomial.divided(mme))
                        p1, p2 = p.split([mme])
                        p2.change_sign()
                        r.mul(p2)  # do the substitution
                        P.pop(monomial)
                        P.add(r)
                        # we changed the polynomial, we cannot iterate any further.
                        # just return and we can simplify again
                        return True
            return False

        def simplify_formula(self, formula):
            changed = False
            # flatten equalities
            if formula.is_eq():
                chld = formula.children()
                if len(chld) == 2 and chld[0].is_poly() and chld[1].is_poly():
                    chld[1][0].change_sign()
                    chld[0][0].add(chld[1][0])
                    changed |= self._simplify_polynomial_formula(chld[0])
                    formula.replace_with(
                        BVFormula(
                            ArithFormula.EQ,
                            None,
                            chld[0],
                            BVFormula.create(bv_const(0, chld[0][0].bitwidth())),
                        )
                    )
                else:
                    for c in formula.children():
                        changed |= self.simplify_formula(c)
            elif formula.is_poly():
                changed |= self._simplify_polynomial_formula(formula)
            else:
                for c in formula.children():
                    changed |= self.simplify_formula(c)
            return changed

    def simplify_polynomial_formula(formula, polynoms):
        simplifier = PolynomialSimplifier(*polynoms)
        while simplifier.simplify_formula(formula):
            pass

    def rewrite_polynomials(expr_to, exprs_from):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        exprs_from = exprs_from or []
        try:
            re = Tactic("elim-term-ite")(_rewrite_sext(_desimplify_ext(expr_to)))
            assert len(re) == 1, re
            expr_to = _desimplify_ext(simplify(mk_and(*re[0])))
            to_formula = BVFormula.create(expr_to)
            if to_formula is None:
                return expr_to
            simple_poly = []
            for e in exprs_from:
                e_formula = BVFormula.create(_desimplify_ext(e))
                if e_formula is None:
                    continue
                if e_formula.is_eq():
                    chlds = list(e_formula.children())
                    if len(chlds) == 2 and chlds[0].is_poly() and chlds[1].is_poly():
                        P1 = chlds[0][0]
                        P2 = chlds[1][0]
                        P2.change_sign()
                        P1.add(P2)
                        simple_poly.append(P1)

            # print('--------')
            # for p in simple_poly:
            #    print('  > ASSUM', _desimplify_ext(simplify(p.expr())))
            # print('>ORIG', _desimplify_ext(simplify(to_formula.expr())))
            # print('--------')
            simplify_polynomial_formula(to_formula, simple_poly)
            #     print('>SIMPL', _desimplify_ext(simplify(to_formula.expr())))
            e = _desimplify_ext(simplify(to_formula.expr()))
            # print('   --   ')
            # print('>FINAL', e)
            # print('--------')
            return e
        except ValueError:
            return None

    def get_eqs_from_ineqs(expr):
        ###
        # check for equalities from inequalities:
        # Not(1 + x <= c) && x <= c  ==> x=c

        # NOTE: requires expr in CNF
        clauses = set(expr.children())
        eqs = []
        for clause in clauses:
            # FIXME: Add greate-equal and check also for other patters
            # (a <= b & 1 + a > b), ...
            if is_app_of(clause, Z3_OP_SLEQ):
                chld = clause.children()
                nc = Not(1 + chld[0] <= chld[1])
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = Not(chld[0] + 1 <= chld[1])
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = chld[1] <= chld[0]
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = chld[0] >= chld[1]
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue

            if is_app_of(clause, Z3_OP_ULEQ):
                chld = clause.children()
                nc = Not(BVULE(1 + chld[0], chld[1]))
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = Not(BVULE(chld[0] + 1, chld[1]))
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = BVUGE(chld[0], chld[1])
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
                nc = BVULE(chld[1], chld[0])
                if nc in clauses:
                    eqs.append((clause, nc, chld[0] == chld[1]))
                    continue
        return eqs

    def eqs_from_ineqs(expr):
        ###
        # check for equalities from inequalities:
        # Not(1 + x <= c) && x <= c  ==> x=c
        eqs = get_eqs_from_ineqs(expr)
        if eqs:
            clauses = set(expr.children())
            for c, nc, e in eqs:
                clauses.remove(c)
                clauses.remove(nc)
                clauses.add(e)
            return And(*clauses)
        return None

    def replace_arith_ops(expr):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        try:
            atoms = {}
            expr = mk_and(*Then("tseitin-cnf", With("simplify", som=True))(expr)[0])
            # assert len(expr_mod) == 1, expr_mod
            # expr = And(*expr_mod[0])
            _get_replacable(expr, atoms)
            subs = {}
            for e, num in atoms.items():
                if num < 1:
                    continue
                subs[e] = BitVec(f"r_{hash(e)}", e.size())
            return substitute(expr, *subs.items()), subs
        except ValueError:
            return None, None

    def _reduce_eq_bitwidth(expr, bw):
        if is_const(expr):
            return expr
        chld = expr.children()
        # Do we want to recurse also into operands of == and !=?
        if is_eq(expr):
            return BVExtract(bw - 1, 0, chld[0]) == BVExtract(bw - 1, 0, chld[1])
        elif is_not(expr):
            # do not dive into negations - negation of overapproximation
            # is underapproximation
            return expr
        else:
            red = [_reduce_eq_bitwidth(c, bw) for c in chld]
            if is_and(expr):
                return mk_and(*red)
            elif is_or(expr):
                return mk_or(*red)
            else:
                return expr.decl()(*red)

    def reduce_eq_bitwidth(expr, bw):
        # return _reduce_eq_bitwidth(expr, bw, variables)
        try:
            # we need the expr in NNF
            expr_nnf = Tactic("nnf")(expr)
            assert len(expr_nnf) == 1, expr_nnf
            return _reduce_eq_bitwidth(mk_and(*expr_nnf[0]), bw)
        except ValueError:
            return None

    def _rdw(expr, bw):
        oldbw = expr.size()
        if oldbw <= bw:
            return expr
        return BVZExt(oldbw - bw, BVExtract(bw - 1, 0, expr))

    def _reduce_arith_bitwidth(expr, bw):
        if is_bv(expr):
            return _rdw(expr, bw)
        # oldbw = expr.size()
        # return BVExtract(bw-1, 0, expr) if oldbw > bw else expr
        else:
            red = (_reduce_arith_bitwidth(c, bw) for c in expr.children())
            if is_and(expr):
                return And(*red)
            elif is_or(expr):
                return Or(*red)
            return expr.decl()(*red)

    def reduce_arith_bitwidth(expr, bw):
        # return _reduce_arith_bitwidth(expr, bw, variables)
        try:
            return _reduce_arith_bitwidth(expr, bw)
        except ValueError:
            return None

    def to_cnf(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Tactic("tseitin-cnf")
        goal = t(g)
        assert len(goal) == 1
        return goal[0]

    def to_nnf(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Tactic("nnf")
        goal = t(g)
        assert len(goal) == 1
        return goal[0]

    def rewrite_simplify(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Then(
            With("simplify", arith_lhs=True, som=True),
            Tactic("propagate-ineqs"),
            Tactic("normalize-bounds"),
            Tactic("propagate-values"),
            Tactic("simplify"),
        )
        return t(g)

    def split_clauses(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Repeat(OrElse(Tactic("split-clause"), Tactic("skip")))
        return t(g)

    def solver_to_sb_type(s):
        if is_bv(s):
            return IntType(s.sort().size())
        if is_fp(s):
            srt = s.sort()
            return FloatType(srt.ebits() + srt.sbits())
        assert is_bool(s), f"Unhandled expression: {s}"
        return BoolType()

    def get_fp_sort(bw):
        if bw == 32:
            return Float32()
        if bw == 64:
            return Float64()
        elif bw == 128:
            return Float128()
        raise NotImplementedError("Invalid FP type")

else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.shortcuts import BVULT, BVULE, BVUGT, BVUGE
    from pysmt.typing import BVType

    def bv(name, bw):
        return Symbol(name, BVType(bw))

    def bv_const(v, bw):
        return BV(v, bw)


def dom_is_symbolic(v):
    return v.KIND == 2


class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """

    # FIXME: get rid of the magic constant
    KIND = 2

    __slots__ = "_expr"

    def __init__(self, e, t):
        assert not isinstance(e, int), e
        assert isinstance(t, Type), t
        Value.__init__(self, t)
        self._expr = e

    def unwrap(self):
        return self._expr

    def is_nondet_load(self):
        return False

    def is_nondet_instr_result(self):
        return False

    def is_future(self):
        return False

    def name(self):
        return str(self._expr)

    def is_concrete(self):
        return False

    def as_value(self):
        return str(self)

    def subexpressions(self):
        """Traverse the expression and return its all subexpressions"""
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in subexpressions(self.unwrap())
        )

    def children(self):
        """
        Get the children (1st-level subexpressions) of this expression.
        E.g. for And(a, b) this method returns [a, b].
        """
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in self.unwrap().children()
        )

    def symbols(self):
        """
        Get the symbols used in this expression.
        E.g. for And(a, 3*b) this method returns [a, b].
        """
        return (Expr(s, solver_to_sb_type(s)) for s in symbols(self.unwrap()))

    def is_symbol(self):
        return _is_symbol(self._expr)

    def to_cnf(self):
        """
        Get the expression in CNF form.
        """
        return Expr(And(*to_cnf(self.unwrap())), self.type())

    def rewrite_and_simplify(self):
        """
        Get the expression in CNF form.
        """
        return Expr(
            mk_or(*(And(*c) for c in rewrite_simplify(self._expr))), self.type()
        )

    def split_clauses(self):
        """
        Get the expression in CNF form.
        """
        return Expr(mk_or(*(And(*c) for c in split_clauses(self._expr))), self.type())

    def reduce_eq_bitwidth(self, bw):
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr = reduce_eq_bitwidth(self.unwrap(), bw)
        if expr is None:
            return None
        ty = solver_to_sb_type(expr)
        assert ty.bitwidth() <= bw
        return Expr(expr, ty)

    def reduce_arith_bitwidth(self, bw):
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr = reduce_arith_bitwidth(self.unwrap(), bw)
        if expr is None:
            return None
        ty = solver_to_sb_type(expr)
        assert ty.bitwidth() <= bw
        return Expr(expr, ty)

    def rewrite_polynomials(self, from_exprs):
        expr = rewrite_polynomials(
            self.unwrap(), map(lambda x: x.unwrap(), from_exprs) if from_exprs else None
        )
        if expr is None:
            return self
        return Expr(expr, self.type())

    def infer_equalities(self):
        cnf = self.to_cnf().unwrap()  # we need clauses
        # get equalities  from comparison
        eqs = set(e for c1, c2, e in get_eqs_from_ineqs(cnf))
        # get equalities right from the formula
        eqs.update(e for e in cnf.children() if is_eq(e))
        return [Expr(expr, solver_to_sb_type(expr)) for expr in eqs]

    def eqs_from_ineqs(self):
        expr = eqs_from_ineqs(self.to_cnf().unwrap())
        if expr is None:
            return self
        return Expr(expr, self.type())

    def replace_arith_ops(self):
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr, subs = replace_arith_ops(self.unwrap())
        if expr is None:
            return None, None
        return Expr(expr, self.type()), {
            Expr(k, solver_to_sb_type(k)): Expr(v, solver_to_sb_type(v))
            for k, v in subs.items()
        }

    def isAnd(self):
        return is_and(self.unwrap())

    def isOr(self):
        return is_or(self.unwrap())

    def isNot(self):
        return is_not(self.unwrap())

    def isEq(self):
        return is_app_of(self._expr, Z3_OP_EQ)

    def isLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ) or is_app_of(self._expr, Z3_OP_ULEQ)

    def isGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ) or is_app_of(self._expr, Z3_OP_UGEQ)

    def isLt(self):
        return is_app_of(self._expr, Z3_OP_SLT) or is_app_of(self._expr, Z3_OP_ULT)

    def isGt(self):
        return is_app_of(self._expr, Z3_OP_SGT) or is_app_of(self._expr, Z3_OP_UGT)

    def isSLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ)

    def isSGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ)

    def isSLt(self):
        return is_app_of(self._expr, Z3_OP_SLT)

    def isSGt(self):
        return is_app_of(self._expr, Z3_OP_SGT)

    def isULe(self):
        return is_app_of(self._expr, Z3_OP_ULEQ)

    def isUGe(self):
        return is_app_of(self._expr, Z3_OP_UGEQ)

    def isULt(self):
        return is_app_of(self._expr, Z3_OP_ULT)

    def isUGt(self):
        return is_app_of(self._expr, Z3_OP_UGT)

    def isMul(self):
        return is_app_of(self._expr, Z3_OP_BMUL)  # or is_app_of(self._expr, Z3_OP_MUL)

    def __hash__(self):
        return self._expr.__hash__()

    def __eq__(self, rhs):
        return self._expr == rhs._expr if isinstance(rhs, Expr) else False

    def __repr__(self):
        return "<{0}:{1}>".format(self._expr, self.type())


class NondetInstrResult(Expr):
    """Expression representing a result of instruction that is unknown - non-deterministic"""

    __slots__ = "_instr"

    def __init__(self, e, t, instr):
        super().__init__(e, t)
        self._instr = instr

    def is_nondet_instr_result(self):
        return True

    def instruction(self):
        return self._instr

    def fromExpr(expr, instr):
        assert isinstance(expr, Expr)
        return NondetInstrResult(expr.unwrap(), expr.type(), instr)

    def __repr__(self):
        return f"{self._instr.as_value()}={Expr.__repr__(self)}"


class NondetLoad(NondetInstrResult):
    __slots__ = "alloc"

    def __init__(self, e, t, load, alloc):
        super().__init__(e, t, load)
        self.alloc = alloc

    def is_nondet_load(self):
        return True

    def load(self):
        return self._instr

    def fromExpr(expr, load, alloc):
        assert isinstance(expr, Expr)
        return NondetLoad(expr.unwrap(), expr.type(), load, alloc)

    def rhs_repr(self):
        return Expr.__repr__(self)

    def __repr__(self):
        return f"L({self.alloc.as_value()})={Expr.__repr__(self)}"


class Future(Expr):
    """
    Represents a value of non-executed operation (instruction)
    (that is going to be executed as a feedback to the developement of the search
    """

    __slots__ = "_instr", "_state"

    def __init__(self, e, t, instr, state):
        super().__init__(e, t)
        # to which instr we assigned the nondet value
        self._instr = instr
        # stored state
        self._state = state

    def is_future(self):
        return True

    def state(self):
        return self._state

    def from_expr(expr, instr, state):
        assert isinstance(expr, Expr)
        return Future(expr.unwrap(), expr.type(), instr)

    def __repr__(self):
        return f"future({self._instr.as_value()})={super().__repr__()}"


def zext_expr(a, bw):
    return BVZExt(bw - a.bitwidth(), boolToBV(a))


def sext_expr(a, bw):
    return BVSExt(bw - a.bitwidth(), boolToBV(a))


def python_constant(val):
    """
    Take a symbolic constant and get a python constant for it.
    Return None if the given expression is not a constant number
    or boolean
    """
    if is_bv_value(val):
        return val.as_long()
    elif is_true(val):
        return True
    elif is_false(val):
        return False
    return None


def python_to_sb_type(val, bw):
    if isinstance(val, bool):
        assert bw == 1
        return BoolType()
    if isinstance(val, int):
        return IntType(bw)
    if isinstance(val, float):
        return FloatType(bw)
    return None


class BVSymbolicDomain:
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if a.KIND != 2:
                return False
        return True

    def lift(v):
        assert isinstance(v, Value), "Invalid value for lifting: {0}".format(v)
        if isinstance(v, Expr):
            return v

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), BoolType())
            ty = v.type()
            if v.is_float():
                return Expr(FPVal(v.value(), get_fp_sort(ty.bitwidth())), ty)
            return Expr(bv_const(v.value(), ty.bitwidth()), ty)

        raise NotImplementedError("Invalid value for lifting: {0}".format(v))

    def simplify(expr):
        return Expr(
            simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.type()
        )

    def pythonConstant(expr):
        return python_constant(expr.unwrap())

    def substitute(expr, *what):
        e = simplify(
            substitute(expr.unwrap(), *((a.unwrap(), b.unwrap()) for (a, b) in what))
        )
        c = python_constant(e)
        if c is not None:
            return ConcreteVal(c, python_to_sb_type(c, expr.type().bitwidth()))
        return Expr(e, expr.type())

    def Constant(c, ty):
        bw = ty.bitwidth()
        if ty.is_float():
            return Expr(FPVal(c, fps=get_fp_sort(bw)), ty)
        elif ty.is_int():
            return Expr(bv_const(c, bw), ty)
        else:
            raise NotImplementedError(f"Invalid type: {ty}")

    ##
    # variables
    def Var(name: str, ty):
        if ty.is_float():
            return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)
        elif ty.is_bool():
            return Expr(Bool(name), ty)
        else:
            assert ty.is_int() or ty.is_pointer(), ty
            return Expr(bv(name, ty.bitwidth()), ty)

    def BVVar(name, bw):
        return Expr(bv(name, bw), IntType(bw))

    def Bool(name):
        return Expr(Bool(name), BoolType())

    def Int1(name, ty):
        return BVSymbolicDomain.BVVar(name, 1)

    def Int8(name):
        return BVSymbolicDomain.BVVar(name, 8)

    def Int16(name):
        return BVSymbolicDomain.BVVar(name, 16)

    def Int32(name):
        return BVSymbolicDomain.BVVar(name, 32)

    def Int64(name):
        return BVSymbolicDomain.BVVar(name, 64)

    ##
    # Logic operators
    def conjunction(*args):
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(And(*map(lambda x: _bv_to_bool(x.unwrap()), args)), BoolType())

    def disjunction(*args):
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(Or(*map(lambda x: _bv_to_bool(x.unwrap()), args)), BoolType())

    def Ite(c, a, b):
        assert BVSymbolicDomain.belongto(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return Expr(If(_bv_to_bool(c.unwrap()), a.unwrap(), b.unwrap()), a.type())

    def And(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) & to_bv(b), IntType(a.bitwidth()))

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) | to_bv(b), IntType(a.bitwidth()))

    def Xor(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) ^ to_bv(b), IntType(a.bitwidth()))

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_bool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~to_bv(a), IntType(a.bitwidth()))

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        bw = b.value()
        assert a.bitwidth() <= bw, "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVZExt(bw - a.bitwidth(), ae), IntType(bw))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a), a
        assert b.is_concrete(), b
        assert b.is_int(), b
        bw = b.value()
        assert a.bitwidth() <= bw, f"Invalid sext argument: {a} to {bw} bits"

        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVSExt(bw - a.bitwidth(), ae), IntType(bw))

    def BitCast(a: Value, ty: Type):
        """Static cast"""
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float() and a.is_bytes():
            # from IEEE bitvector
            expr = fpToFP(a._expr, get_fp_sort(tybw))
            return Expr(expr, ty)
        if ty.is_float():
            if a.is_int():
                # from IEEE bitvector
                expr = fpToFP(a._expr, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        elif a.is_float() and ty.is_int():
            ae = fpToIEEEBV(a._expr)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), IntType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    def Cast(a: Value, ty: Type, signed: bool = True):
        """Reinterpret cast"""
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float():
            if a.is_int():
                abw = a.bitwidth()
                if signed:  # from signed bitvector
                    expr = fpSignedToFP(RNE(), a._expr, get_fp_sort(tybw))
                else:
                    expr = fpUnsignedToFP(RNE(), a._expr, get_fp_sort(tybw))
                    # from IEEE bitvector
                    # expr = fpToFP(a._expr, get_fp_sort(tybw))
                # expr = fpToFP(a._expr, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
            if a.is_bytes():
                # from IEEE bitvector
                expr = fpToFP(a._expr, get_fp_sort(a.bitwidth()))
                expr = fpFPToFP(RNE(), expr, get_fp_sort(tybw))
                return Expr(expr, ty)
        elif a.is_float() and ty.is_int():
            if signed:
                ae = floatToSBV(a, ty)
            else:
                ae = floatToUBV(a, ty)
            # ae = fpToIEEEBV(a._expr)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), IntType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    def Extract(a, start, end):
        assert BVSymbolicDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        return Expr(
            BVExtract(end.value(), start.value(), a.unwrap()),
            IntType(end.value() - start.value() + 1),
        )

    def Concat(*args):
        l = len(args)
        assert l > 0, args
        assert BVSymbolicDomain.belongto(*args), args
        if l == 1:
            return args[0]
        return Expr(
            BVConcat(*(e.unwrap() for e in args)),
            IntType(sum(e.bitwidth() for e in args)),
        )

    def Shl(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) << b.unwrap(), IntType(a.bitwidth()))

    def AShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) >> b.unwrap(), IntType(a.bitwidth()))

    def LShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(BVLShR(to_bv(a), b.unwrap()), IntType(a.bitwidth()))

    def get_true():
        return Expr(TRUE(), BoolType())

    def get_false():
        return Expr(FALSE(), BoolType())

    ##
    # Relational operators

    def Le(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) <= to_bv(b), BoolType())

    def Lt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) < to_bv(b), BoolType())

    def Ge(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) >= to_bv(b), BoolType())

    def Gt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) > to_bv(b), BoolType())

    def Eq(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} != {b}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if a.is_bool() and b.is_bool():
            return Expr(a == b, BoolType())
        return Expr(to_bv(a) == to_bv(b), BoolType())

    def Ne(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpNEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if a.is_bool() and b.is_bool():
            return Expr(a != b, BoolType())
        return Expr(to_bv(a) != to_bv(b), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} + {b}"
        bw = a.bitwidth()
        if isfloat:
            # the operations on CPU work on doubles( well, 80-bits...)
            # and then truncate to float if needed
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae + be, bw), FloatType(bw))
        return Expr(to_bv(a) + to_bv(b), IntType(bw))

    def Sub(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} - {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae - be, bw), FloatType(bw))
        return Expr(to_bv(a) - to_bv(b), IntType(bw))

    def Mul(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} * {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae * be, bw), FloatType(bw))
        return Expr(to_bv(a) * to_bv(b), IntType(bw))

    def Div(a, b, unsigned=False, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} / {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(fpDiv(RNE(), ae, be), bw), FloatType(bw))
        if unsigned:
            return Expr(UDiv(to_bv(a), to_bv(b)), IntType(bw))
        return Expr(to_bv(a) / to_bv(b), IntType(bw))

    def Rem(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)

    def Abs(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_float():
            return Expr(fpAbs(a.unwrap()), a.type())
        expr = a.unwrap()
        return Expr(If(expr < 0, -expr, expr), a.type())

    def Neg(a, isfloat):
        """Return the negated number"""
        assert BVSymbolicDomain.belongto(a)
        bw = a.bitwidth()
        if isfloat:
            return Expr(trunc_fp(fpNeg(to_double(a)), bw), FloatType(bw))
        expr = a.unwrap()
        return Expr(-expr, a.type())

    def FpOp(op, val):
        assert BVSymbolicDomain.belongto(val)
        # FIXME: do not use the enum from instruction
        assert val.is_float()

        if op == FpOp.IS_INF:
            return Expr(fpIsInf(val.unwrap()), BoolType())
        if op == FpOp.IS_NAN:
            return Expr(fpIsNaN(val.unwrap()), BoolType())
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.unwrap()
            expr = If(
                fpIsNaN(v),
                bv_const(0, 32),
                If(
                    fpIsInf(v),
                    bv_const(1, 32),
                    If(
                        fpIsZero(v),
                        bv_const(2, 32),
                        If(fpIsSubnormal(v), bv_const(3, 32), bv_const(4, 32)),
                    ),
                ),
            )
            return Expr(expr, IntType(32))
            if op == FpOp.SIGNBIT:
                return Expr(
                    If(fpIsNegative(bv_const(1, 32), bv_const(0, 32))), IntType(32)
                )

        return None


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
