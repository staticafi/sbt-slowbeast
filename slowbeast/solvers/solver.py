from slowbeast.domains.symbolic import _use_z3
from slowbeast.domains.concrete import ConcreteVal
from .expressions import ExprManager

if _use_z3:
    from z3 import Solver as Z3Solver
    from z3 import sat, unsat, unknown
    from z3 import BitVecVal, BoolVal, BitVecNumRef, FPNumRef, is_false

    def models(assumpt, *args):
        s = Z3Solver()
        for a in assumpt:
            assert a.is_bool()
            s.add(a.unwrap())
        r = s.check()
        if r != sat:
            return None

        m = s.model()
        vals = []
        for a in args:
            c = m[a.unwrap()]
            if c is None:
                # m does not have a value for this variable
                # use 0
                c = BoolVal(False) if a.is_bool() else BitVecVal(0, a.type().bitwidth())
            vals.append(c)

        return vals

    def models_inc(solver, assumpt, *args):
        solver.push()
        for a in assumpt:
            assert a.is_bool()
            if a.is_concrete():
                solver.add(a.value())
            else:
                solver.add(a.unwrap())
        r = solver.check()
        if r != sat:
            solver.pop()
            return None

        m = solver.model()
        vals = []
        for a in args:
            c = m[a.unwrap()]
            if c is None:
                # m does not have a value for this variable
                # use 0
                c = BoolVal(False) if a.is_bool() else BitVecVal(0, a.type().bitwidth())
            vals.append(c)

        solver.pop()
        return vals

    def _is_sat(solver, timeout, *args):
        if solver is None:
            solver = Z3Solver()

        if timeout:
            solver.set("timeout", timeout)
            r = solver.check(*args)
            solver.set("timeout", 4294967295)  # default value
        else:
            r = solver.check(*args)

        if r == sat:
            return True
        if r == unsat:
            return False
        if r == unknown:
            reason = solver.reason_unknown()
            if reason == "interrupted from keyboard":
                # If the user interrupted the computation,
                # re-raise the interrupt if it was consumed
                # in the solver so that the rest of the code
                # can react on it
                raise KeyboardInterrupt
        return None

else:
    from pysmt.shortcuts import is_sat


# FIXME add support for incremental solving

global_expr_manager = ExprManager()


def global_expr_mgr():
    global global_expr_manager
    return global_expr_manager


class SolverIntf:
    """Interface of solvers"""

    __slots__ = "_exprmanager"

    def __init__(self, em=global_expr_manager):
        # for now we use a global expr manager
        self._exprmanager = em

    def expr_manager(self):
        return self._exprmanager

    def is_sat(self, *e):
        raise NotImplementedError("Must be overriden")

    def try_is_sat(self, timeout, *e):
        raise NotImplementedError("Must be overriden")

    def fresh_value(self, name, ty):
        """ty = type"""
        return self._exprmanager.fresh_value(name, ty)

    def Var(self, name, ty):
        """ty = type"""
        return self._exprmanager.Var(name, ty)


class ConcreteSolver(SolverIntf):
    """
    Just check for True/False values of concrete computation
    wrapped to the interface solver.
    """

    def __init__(self, em=ExprManager()):
        super().__init__(em)

    def is_sat(self, *e):
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))

    # for x in e:
    #    assert x.is_bool()
    #    assert isinstance(x.value(), bool)
    #    if x.value() is False:
    #        return False
    # return True

    def try_is_sat(self, timeout, *e):
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))


def map_model(m, e):
    if m is None:  # unsat
        return None
    ret = []
    for n, v in enumerate(e):
        if m[n] is None:
            ret.append(None)
        else:
            if v.is_float():
                val = m[n]
                if isinstance(val, BitVecNumRef):
                    f = val.as_long()
                elif isinstance(val, FPNumRef):
                    if val.isNaN():
                        f = float("NaN")
                    elif val.isInf():
                        if val.isNegative():
                            f = float("-inf")
                        else:
                            f = float("inf")
                    else:
                        f = float(eval(str(val)))
                else:
                    raise RuntimeError(f"Invalid model type: {v}")
                ret.append(ConcreteVal(f, v.type()))
            else:
                ret.append(ConcreteVal(m[n].as_long(), v.type()))
    return ret


class SymbolicSolver(SolverIntf):
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self, em=global_expr_manager):
        super().__init__(em)

    def is_sat(self, *e):
        if any(
            map(lambda x: is_false(x) or (x.is_concrete() and x.value() is False), e)
        ):
            return False
        return _is_sat(
            Z3Solver(), None, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def try_is_sat(self, timeout, *e):
        if any(
            map(lambda x: is_false(x) or (x.is_concrete() and x.value() is False), e)
        ):
            return False
        return _is_sat(
            Z3Solver(), timeout, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def concretize(self, assumpt, *e):
        assert all(
            map(lambda x: not x.is_concrete(), e)
        ), "ConcreteVal instead of symbolic value"
        if any(map(lambda x: x.is_concrete() and x.value() is False, assumpt)):
            return None
        m = models(assumpt, *e)
        return map_model(m, e)


class IncrementalSolver(SymbolicSolver):
    def __init__(self, em=global_expr_manager):
        # FIXME: add local expr manager
        super().__init__(em)
        self._solver = Z3Solver()

    def add(self, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            self._solver.add(BoolVal(False))
        self._solver.add(*(x.unwrap() for x in e if not x.is_concrete()))

    def push(self):
        self._solver.push()

    def pop(self, num: int = 1):
        self._solver.pop(num)

    def is_sat(self, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return _is_sat(
            self._solver, None, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def try_is_sat(self, timeout, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return _is_sat(
            self._solver, timeout, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def copy(self):
        s = IncrementalSolver()
        s._solver = self._solver.translate(self._solver.ctx)
        return s

    def concretize(self, assumpt, *e):
        assert all(
            map(lambda x: not x.is_concrete(), e)
        ), "ConcreteVal instead of symbolic value"
        if any(map(lambda x: x.is_concrete() and x.value() is False, assumpt)):
            return None
        m = models_inc(self._solver, assumpt, *e)
        return map_model(m, e)

    def _model(self):
        """Debugging feature atm. Must follow is_sat() that is True"""
        return self._solver.model()

    def __repr__(self):
        return f"IncrementalSolver: {self._solver}"


Solver = SymbolicSolver


def _sort_subs(subs):
    """
    Return multiplication of two variables later than other expressions
    """
    # FIXME: not very efficient
    V = []
    for k, v in subs.items():
        s = sum(map(lambda c: not c.is_concrete(), k.children()))
        if s > 1:
            V.append((k, v))
        else:
            yield (k, v)
    for k, v in V:
        yield (k, v)


def _rewrite_poly(em, exprs, assumptions=None):
    expr = em.conjunction(*exprs)
    if expr.is_concrete():
        return expr
    expr1 = expr.rewrite_polynomials(assumptions)
    if assumptions:
        A = []
        for i in range(len(assumptions)):
            a = assumptions[i]
            A.append(a.rewrite_polynomials(assumptions))
        return em.conjunction(*A, expr1)
    return expr1


def solve_incrementally(assumptions, exprs, em, to1=3000, to2=500):
    # check if we can evaluate some expression syntactically
    for a in assumptions:
        exprs = [em.substitute(e, (a, em.get_true())) for e in exprs]
    # filter out expressions that are 'true'
    exprs = [e for e in exprs if not (e.is_concrete() and bool(e.value()))]

    if assumptions:
        exprs, r = _remove_implied(assumptions, em, exprs)
        if r is not None:
            return r

    # First try to rewrite the formula into a simpler form
    expr = _rewrite_poly(em, exprs, assumptions)
    if expr.is_concrete():
        return bool(expr.value())
    exprcnf = expr.to_cnf()
    eqs = exprcnf.infer_equalities()
    if eqs:
        expr = _rewrite_poly(em, list(exprcnf.children()), eqs)
        if not expr.is_concrete():
            exprs, r = _remove_implied(eqs, em, expr.to_cnf().children())
            if r is not None:
                return r
            expr = em.conjunction(*exprs, *eqs)
    # else: keep the last expr that we had

    if expr.is_concrete():
        return bool(expr.value())

    # FIXME: transfer state from _remove_implied
    solver = IncrementalSolver()

    # FIXME try reduced bitwidth with propagating back models instead of this
    # for bw in (1, 2, 4, 8, 16):
    #    # FIXME: handle signed/unsinged and negations correctly in
    #    # reduce_arith_bitwidth and use that
    #    solver.add(expr.reduce_eq_bitwidth(bw).rewrite_and_simplify())
    #    r = solver.try_is_sat(bw*500)
    #    if r is False: return False
    #    elif r is None:
    #        break
    #    assert r is True
    #    # the reduced subformulas are sat. Try to check the original formula
    #    # with the knowledge about the reduced formulas stored in the solver
    #    r = solver.try_is_sat(bw*500, expr)
    #    if r is not None:
    #        return r
    ###
    # Now try abstractions
    #
    rexpr, subs = expr.replace_arith_ops()
    if rexpr:
        solver.push()
        solver.add(rexpr.rewrite_and_simplify())
        n = 0
        for placeholder, e in _sort_subs(subs):
            n += 1
            if solver.try_is_sat(n * to2) is False:
                return False
            solver.add(em.Eq(e, placeholder))
        solver.pop()
    # fall-back to solving the un-abstracted expression
    return solver.is_sat(expr)


def _remove_implied(assumptions, em, exprs):
    solver = IncrementalSolver()
    solver.add(*assumptions)
    # check the assumpitons - if we are able to check them on their own,
    r = solver.try_is_sat(1000)
    if r is False:
        return [em.get_false()], False
    # we're good and can continue -- the solver has built a state for faster solving now

    # try to subsume the implied expressions
    # assert solver.is_sat() is True # otherwise we'll subsume everything
    exprs = [e for e in exprs if solver.try_is_sat(500, em.Not(e)) is not False]
    r = solver.try_is_sat(1000, *exprs)
    return exprs, r
