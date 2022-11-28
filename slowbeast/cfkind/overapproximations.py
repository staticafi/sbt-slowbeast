from functools import partial
from slowbeast.domains.concrete import ConcreteInt
from slowbeast.util.debugging import dbg, dbgv
from slowbeast.solvers.expressions import em_optimize_expressions
from slowbeast.solvers.solver import global_expr_mgr, IncrementalSolver
from slowbeast.symexe.statesset import union, intersection, complement
from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.annotations import (
    AssertAnnotation,
    execute_annotation_substitutions,
)

from .inductivesequence import InductiveSequence


def remove_implied_literals(clauses):
    """
    Returns an equivalent but possibly smaller formula
    """

    solver = IncrementalSolver()

    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in clauses:
        if c.is_concrete() and c.value() is True:
            continue
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)
            solver.add(c)

    EM = global_expr_mgr()
    Not = EM.Not
    newclauses = []
    # NOTE: we could do this until a fixpoint, but...
    for r in rest:
        changed = False
        drop = False
        newc = []
        for l in r.children():
            if solver.is_sat(l) is False:
                # dbg(f"Dropping {l}, it's False")
                changed = True
            elif solver.is_sat(Not(l)) is False:
                # XXX: is it worth querying the solver for this one?
                drop = True
                break
            else:
                newc.append(l)
        if drop:
            # dbg(f"Dropping {r}, it's True")
            continue
        if changed:
            if len(newc) == 1:
                singletons.append(newc[0])
                solver.add(newc[0])
            else:
                newclauses.append(EM.disjunction(*newc))
        else:
            newclauses.append(r)

    return singletons + newclauses


def poststates(executor, paths, prestate):
    """
    Return states after executing paths with precondition 'pre'
    extended by the postcondition 'post'. We do not evaluate the
    validity of the postcondition, so that we can get the path condition
    and manipulate with it (it can be unsat and evaluating it could
    simplify it to false, which is undesired here
    """
    result = PathExecutionResult()
    indexecutor = executor.ind_executor()
    for path in paths:
        # p = path.copy()
        # the post-condition is the whole frame
        # if pre:
        #    p.add_annot_before(pre.as_assume_annotation())

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = indexecutor.execute_annotated_path([prestate.copy()], path)
        result.merge(r)

    assert result.errors is None
    if not result.ready:
        return None

    ready = result.ready
    return ready


def literals(c):
    if c.isOr():
        yield from c.children()
    else:
        yield c


def get_predicate(l):
    EM = global_expr_mgr()
    if l.isSLe():
        return EM.Le
    if l.isSGe():
        return EM.Ge
    if l.isSLt():
        return EM.Lt
    if l.isSGt():
        return EM.Gt
    if l.isULe():
        return partial(EM.Le, unsigned=True)
    if l.isUGe():
        return partial(EM.Ge, unsigned=True)
    if l.isULt():
        return partial(EM.Lt, unsigned=True)
    if l.isUGt():
        return partial(EM.Gt, unsigned=True)

    raise NotImplementedError(f"Unhandled predicate in expr {l}")


def _decompose_literal(l):
    isnot = False
    if l.isNot():
        isnot = True
        l = list(l.children())[0]

    if l.isLt() or l.isLe():
        addtoleft = False
    elif l.isGt() or l.isGe():
        addtoleft = True
    else:
        return None, None, None, None

    chld = list(l.children())
    assert len(chld) == 2
    left, P, right = chld[0], get_predicate(l), chld[1]

    if isnot:
        addtoleft = not addtoleft
        EM = global_expr_mgr()
        binop = P
        P = lambda a, b: EM.Not(binop(a, b))

    return left, right, P, addtoleft


class DecomposedLiteral:
    __slots__ = "left", "right", "pred", "addtoleft"

    def __init__(self, lit):
        self.left, self.right, self.pred, self.addtoleft = _decompose_literal(lit)

    def __bool__(self):
        assert self.left is None or self.right and self.pred
        return self.left is not None

    def toformula(self):
        return self.pred(self.left, self.right)

    def bitwidth(self):
        left = self.left
        if left:
            return left.type().bitwidth()
        return None

    def extended(self, num):
        EM = global_expr_mgr()
        left, right = self.left, self.right
        if self.addtoleft:
            left = EM.Add(left, num)
        else:
            right = EM.Add(right, num)

        # try pushing further
        return self.pred(left, right)


def get_left_right(l):
    if l.isNot():
        l = list(l.children())[0]

    chld = list(l.children())
    assert len(chld) == 2, "Invalid literal (we assume binop or not(binop)"
    return chld[0], chld[1]


def check_literal(EM, lit, ldata):
    if lit is None or lit.is_concrete():
        return False

    # safety check
    if (
        not ldata.safety_solver.try_is_sat(500, EM.disjunction(lit, *ldata.clause))
        is False
    ):
        return False

    have_feasible = False
    substitute = EM.substitute

    I = ldata.indset_with_placeholder
    placeholder = ldata.placeholder
    solver = ldata.solver
    A = AssertAnnotation(
        substitute(I.expr(), (placeholder, lit)), I.substitutions(), EM
    )
    for s in ldata.loop_poststates:
        # feasability check
        solver.push()
        pathcond = substitute(s.path_condition(), (placeholder, lit))
        solver.add(pathcond)
        feasible = solver.try_is_sat(500)
        if feasible is not True:
            solver.pop()
            if feasible is None:  # solver t-outed/failed
                return False
            continue
        # feasible means ok, but we want at least one feasible path
        # FIXME: do we?
        have_feasible = True

        # inductivity check
        hasnocti = A.do_substitutions(s)
        # we have got pathcond in solver already
        if solver.try_is_sat(500, EM.Not(hasnocti)) is not False:  # there exist CTI
            solver.pop()
            return False
        solver.pop()
    return have_feasible


def extend_with_num(dliteral, constadd, num, maxnum, ldata, EM):
    """
    Add 'num' as many times as possible to the literal that is created from dliteral and constadd

    constadd - this number is always added to the literal (that is the current
               value of extending
    num - number to keep adding
    maxnum - maximal number to try (the sum of added 'num' cannot exceed this)

    \return the maximal added number which is multiple of 'num' + constadd,
            i.e., the new value that is safe to add to the literal
    """
    numval = num.value()
    retval = constadd
    Add = EM.Add

    # keep the retval also in python int, so that we can check it agains
    # maxnum (expressions are counted modulo, so we cannot check that
    # on expressions)
    acc = retval.value() + numval
    if acc > maxnum:
        return retval

    newretval = Add(retval, num)
    newl = dliteral.extended(newretval)

    ### push as far as we can with this num
    while check_literal(EM, newl, ldata):
        # the tried value is ok, so set it as the new final value
        retval = newretval
        assert retval.value() <= maxnum

        newretval = Add(newretval, num)
        acc += numval

        # do not try to shift the number beyond maxnum
        if acc > maxnum:
            break
        newl = dliteral.extended(newretval)

    return retval


def extend_literal(ldata, EM):
    dliteral = ldata.decomposed_literal

    bw = dliteral.bitwidth()
    two = ConcreteInt(2, bw)
    # adding 2 ** bw would be like adding 0, stop before that
    maxnum = 2 ** bw - 1

    # a fast path where we try shift just by one.  If we cant, we can give up
    # FIXME: try more low values (e.g., to 10)
    num = ConcreteInt(1, bw)
    l = dliteral.extended(num)
    if not check_literal(EM, l, ldata):
        return ldata.literal

    # this is the final number that we are going to add to one side of the
    # literal
    finalnum = ConcreteInt(1, bw)  # we know we can add 1 now
    num = ConcreteInt(2 ** (bw - 1) - 1, bw)  # this num we'll try to add
    while finalnum.value() <= maxnum:
        finalnum = extend_with_num(dliteral, finalnum, num, maxnum, ldata, EM)

        if num.value() <= 1:
            # we have added also as many 1 as we could, finish
            return dliteral.extended(finalnum)
        num = EM.Div(num, two)
    raise RuntimeError("Unreachable")


class LoopStateOverapproximation:
    """
    Structure taking care for over-approximations of states
    """

    # __slots__ = "executor", "clauses", "target", "unsafe", "loop", "expr_mgr"

    def __init__(self, S, executor, target, unsafe, loop, expr_mgr):
        self.executor = executor
        self.target = target
        self.unsafe = unsafe
        self.loop = loop
        self.expr_mgr = expr_mgr

        self.goal = S
        # clauses are our internal working structure. Any change that we do is not visible until we do commit().
        # Note: break equalities to <= && >= so that we can overapproximate them
        self.clauses = list(S.as_expr().rewrite_and_simplify().to_cnf().children())

        safesolver = IncrementalSolver()
        safesolver.add(unsafe.as_expr())
        self.safesolver = safesolver

    def drop_disjuncts(self):
        solver = IncrementalSolver()
        solver.add(*self.clauses)
        assert solver.is_sat(), "The clauses are unsat!"
        em = self.expr_mgr
        disjunction, conjunction, Not = em.disjunction, em.conjunction, em.Not
        false, true = em.get_false(), em.get_true()
        substitute = em.substitute

        subs = []
        newclauses = []
        for c in self.clauses:
            c = substitute(c, *subs)
            newd = []
            if c.is_concrete():
                val = c.value()
                if val is True:
                    continue
                elif val is False:
                    raise RuntimeError(
                        "BUG in dropping disjuncts! Made the expression unsat"
                    )
                raise RuntimeError(f"Invalid boolean value: {val}")
            if not c.isOr():
                newclauses.append(c)
                continue

            for d in c.children():
                nd = Not(d)
                if solver.try_is_sat(100, nd) is False:
                    if nd.isNot():
                        subs.append((d, true))
                        newd.append(true)
                        continue
                    subs.append((nd, false))
                if solver.try_is_sat(100, d) is False:
                    if d.isNot():
                        subs.append((next(d.children()), true))
                    subs.append((d, false))
                else:
                    newd.append(d)
            if newd:
                newclauses.append(disjunction(*newd))
            else:
                raise RuntimeError(
                    "BUG in dropping disjuncts! Made the expression unsat"
                )
        self.clauses = [em.substitute(c, *subs) for c in newclauses]

    def _drop_clauses(self, clauses, assumptions):
        """
        assumptions are clauses that we do not try to drop
        """
        target = self.target

        # we start with all clauses
        em = self.expr_mgr
        conjunction = em.conjunction
        expressions = set()
        for c in clauses:
            if c.is_concrete():
                if c.value() is False:
                    dbg("  ... got FALSE in clauses, returning FALSE")
                    return [em.get_false()]
                dbg("  ... dropping True clause")
            else:
                expressions.add(c)

        newclauses = list(expressions)
        # newS = S.copy()
        safesolver = self.safesolver
        S = self.goal
        loop = self.loop
        for c in expressions:
            assert not c.is_concrete(), c
            # create a temporary formula without the given clause
            tmp = newclauses.copy()
            tmp.remove(c)

            # check whether we can get rid of the clause
            if assumptions:
                tmpexpr = conjunction(*tmp, assumptions.as_expr())
            else:
                tmpexpr = conjunction(*tmp)
            if tmpexpr.is_concrete():
                continue  # either False or True are bad for us

            # == safety check
            if safesolver.is_sat(tmpexpr) is not False:
                continue  # unsafe overapprox

            X = S.copy()
            X.reset_expr(tmpexpr)
            if loop.set_is_inductive_towards(X, target):
                newclauses = tmp
                dbg(f"  dropped {c}...")

        return newclauses

    def _drop_clauses_fixpoint(self, assumptions):
        """Drop clauses until fixpoint"""
        newclauses = self.clauses
        _drop_clauses = self._drop_clauses
        while True:
            dbgv(" ... droping clauses (starting iteration)")
            oldlen = len(newclauses)
            newclauses = _drop_clauses(newclauses, assumptions)
            if oldlen == len(newclauses):
                break
        dbgv(" ... done droping clauses")
        return newclauses

    def drop_clauses(self, assumptions=None):
        newclauses = self._drop_clauses_fixpoint(assumptions)
        # new add the assumptions (without them the formula is not equivalent to expr now)
        if assumptions:
            newclauses.extend(list(assumptions.as_expr().to_cnf().children()))
        clauses = remove_implied_literals(newclauses)

        assert intersection(
            self.unsafe, self.executor.create_set(self.expr_mgr.conjunction(*clauses))
        ).is_empty(), f"Dropping clauses made the set unsafe:\n{self.clauses}\nvvv new clauses vvv\n{clauses}\nvvv with unsafe vvv:\n{self.unsafe}"
        self.clauses = clauses

    def commit(self):
        S = self.goal
        expr = self.expr_mgr.conjunction(*self.clauses)
        if not expr.is_concrete():
            expr = expr.rewrite_and_simplify()
        S.reset_expr(expr)
        return S

    def overapproximate(self):
        conjunction = self.expr_mgr.conjunction
        overapprox_clause = self.overapprox_clause
        clauses, newclauses = self.clauses, []
        target = self.target
        S = self.goal
        em = self.expr_mgr
        Le, Ge = em.Le, em.Ge
        Lt, Gt = em.Lt, em.Gt
        # Now take every clause c and try to overapproximate it
        for n in range(len(clauses)):
            c = clauses[n]
            # R is the rest of the actual formula without the clause c
            R = S.copy()  # copy the substitutions
            R.reset_expr(conjunction(*newclauses, *clauses[n + 1 :]))

            # try breaking equalities into inequalities. We do it here so that we preserve the equality
            # if we fail overapproximating. This is because when we later derive relations from path condition,
            # we want the equalities there.
            if c.isEq():
                chld = list(c.children())
                assert len(chld) == 2, c
                le = Le(chld[0], chld[1])
                ge = Ge(chld[0], chld[1])
                new_le = overapprox_clause(le, intersection(R, ge))
                new_ge = overapprox_clause(ge, intersection(R, le))
                if (
                    new_le
                    and new_ge
                    and (new_le != le or new_ge != ge)
                    and is_overapprox_of(S, intersection(R, new_le, new_ge))
                ):
                    newclauses.append(new_le)
                    newclauses.append(new_ge)
                    continue
                if (
                    new_le
                    and new_le != le
                    and is_overapprox_of(S, intersection(R, new_le, ge))
                ):
                    newclauses.append(new_le)
                    newclauses.append(ge)
                    continue
                if (
                    new_ge
                    and new_ge != ge
                    and is_overapprox_of(S, intersection(R, new_ge, le))
                ):
                    newclauses.append(new_ge)
                    newclauses.append(le)
                    continue
                newclauses.append(c)
            elif c.isNot() and next(c.children()).isEq():
                chld = list(next(c.children()).children())
                assert len(chld) == 2, c
                lt = Lt(chld[0], chld[1])
                gt = Gt(chld[0], chld[1])
                new_lt = (
                    overapprox_clause(lt, R)
                    if self.loop.set_is_inductive_towards(
                        intersection(R, lt), target, allow_infeasible_only=True
                    )
                    else em.get_false()
                )
                new_gt = (
                    overapprox_clause(gt, R)
                    if self.loop.set_is_inductive_towards(
                        intersection(R, gt), target, allow_infeasible_only=True
                    )
                    else em.get_false()
                )
                if (
                    new_lt
                    and new_gt
                    and (new_lt != lt or new_gt != gt)
                    and is_overapprox_of(S, intersection(R, em.Or(new_lt, new_gt)))
                ):
                    newclauses.append(em.Or(new_lt, new_gt))
                    continue
                if (
                    new_lt
                    and new_lt != lt
                    and is_overapprox_of(S, intersection(R, em.Or(new_lt, gt)))
                ):
                    newclauses.append(em.Or(new_lt, gt))
                    continue
                if (
                    new_gt
                    and new_gt != gt
                    and is_overapprox_of(S, intersection(R, em.Or(new_gt, lt)))
                ):
                    newclauses.append(em.Or(new_gt, lt))
                    continue
                newclauses.append(c)
            else:
                newclause = overapprox_clause(c, R)
                if newclause:
                    # newclauses.append(newclause)
                    # FIXME: this check should be
                    # assertion, overapprox_clause should not give us such clauses
                    # assert intersection(tmp, S).is_empty()
                    if is_overapprox_of(S, intersection(R, newclause)):
                        # new clause makes S to be an overapproximation, good
                        newclauses.append(newclause)
                    else:
                        newclauses.append(c)
                else:
                    newclauses.append(c)

            if __debug__:
                R.intersect(newclauses[-1])
                assert not R.is_empty()
                R.intersect(self.unsafe)
                assert R.is_empty(), f"Overapproxmating clause made the set unsafe: {c}"

        if __debug__:
            S.reset_expr(self.expr_mgr.conjunction(*newclauses))
            assert not S.is_empty()
            assert intersection(
                self.unsafe, S
            ).is_empty(), "Overapproxmating clauses made the set unsafe"

        self.clauses = newclauses

    def overapprox_clause(self, c, R):
        """
        c - the clause
        R - rest of clauses of the formula
        """
        if c.is_concrete():
            return c

        assert intersection(R, c, self.unsafe).is_empty(), f"{R} & {c} & {self.unsafe}"
        if __debug__:
            X = R.copy()
            X.intersect(c)
            assert self.loop.set_is_inductive_towards(
                X, self.target, allow_infeasible_only=True
            ), X

        newc = []
        lits = list(literals(c))
        simplify = self.expr_mgr.simplify

        overapprox_lit = self.overapprox_literal
        for l in lits:
            newl = simplify(overapprox_lit(l, lits, R))
            newc.append(newl)
            if __debug__:
                if l != newl:
                    dbg(
                        f"  Overapproximated {l} --> {newl}",
                        color="gray",
                    )
                    X = R.copy()
                    X.intersect(
                        self.expr_mgr.disjunction(
                            *(
                                newc[i] if i < len(newc) else lits[i]
                                for i in range(len(lits))
                            )
                        )
                    )
                    assert self.loop.set_is_inductive_towards(
                        X, self.target, allow_infeasible_only=True
                    ), f"X: {X}, target: {self.target}"

        if len(newc) == 1:
            return newc[0]

        return self.expr_mgr.disjunction(*newc)

    def overapprox_literal(self, l, rl, S):
        """
        l - literal
        rl - list of all literals in the clause
        S - rest of clauses of the formula except for 'rl'
        unsafe - set of unsafe states
        target - set of safe states that we want to keep reachable
        """
        assert not l.isAnd() and not l.isOr(), f"Input is not a literal: {l}"
        assert intersection(S, l, self.unsafe).is_empty(), "Unsafe states in input"

        EM = self.expr_mgr
        executor = self.executor

        # create a fresh literal that we use as a placeholder instead of our literal during extending
        placeholder = EM.Bool("litext")
        # X is the original formula with 'placeholder' instead of 'l'
        clause_without_lit = list(x for x in rl if x != l)
        X = intersection(S, EM.disjunction(placeholder, *clause_without_lit))
        assert not X.is_empty(), f"S: {S}, l: {l}, rl: {rl}"
        post = poststates(executor, self.loop.paths(), X.get_se_state())
        if not post:
            return l

        # U is allowed reachable set of states
        U = union(self.target, X)
        indset_with_placeholder = U.as_assume_annotation()
        # execute the instructions from annotations, so that the substitutions have up-to-date value
        poststates_with_placeholder, nonr = execute_annotation_substitutions(
            executor.ind_executor(), post, indset_with_placeholder
        )
        assert not nonr, f"Got errors while processing annotations: {nonr}"

        dliteral = DecomposedLiteral(l)
        if not dliteral:
            return l
        assert dliteral.toformula() == l

        # we always check S && unsafe && new_clause, so we can keep S  and unsafe
        # in the solver all the time
        safety_solver = self.safesolver
        safety_solver.push()
        safety_solver.add(S.as_expr())
        # induction solver
        solver = IncrementalSolver()

        ldata = LiteralOverapproximationData(
            l,
            dliteral,
            rl,
            clause_without_lit,
            indset_with_placeholder,
            placeholder,
            safety_solver,
            solver,
            poststates_with_placeholder,
        )
        assert isinstance(ldata.decomposed_literal, DecomposedLiteral)

        em_optimize_expressions(False)
        # the optimizer could make And or Or from the literal, we do not want that...
        l = extend_literal(ldata, EM)
        em_optimize_expressions(True)

        safety_solver.pop()
        return l


class LiteralOverapproximationData:
    __slots__ = (
        "literal",
        "decomposed_literal",
        "clause",
        "clause_without_literal",
        "indset_with_placeholder",
        "placeholder",
        "safety_solver",
        "solver",
        "loop_poststates",
    )

    def __init__(
        self,
        literal,
        dliteral: DecomposedLiteral,
        clause,
        clause_without_literal,
        indset_with_placeholder,
        placeholder,
        safety_solver,
        solver,
        loop_poststates,
    ):
        assert isinstance(dliteral, DecomposedLiteral)
        assert isinstance(clause, list)
        assert isinstance(clause_without_literal, list)
        assert isinstance(solver, IncrementalSolver)
        assert isinstance(safety_solver, IncrementalSolver)

        self.literal = literal
        self.decomposed_literal = dliteral
        self.clause = clause
        self.clause_without_literal = clause_without_literal
        self.indset_with_placeholder = indset_with_placeholder
        self.placeholder = placeholder
        self.safety_solver = safety_solver
        self.solver = solver
        # also with placeholder
        self.loop_poststates = loop_poststates


def break_eqs(expr):
    EM = global_expr_mgr()
    clauses = []

    def break_eq(c):
        l, r = c.children()
        ret = []
        # if not const_only or (dom_is_concrete(l) or dom_is_concrete(r)):
        for x in EM.Le(l, r), EM.Le(r, l):
            if not x.is_concrete():
                ret.append(x)
        return ret
        # return [c]

    # break equalities that have a constant on one side,
    # so that we can generalize them
    for c in expr.children():
        if c.isNot():
            d = next(c.children())
            if d.isEq():
                cls = break_eq(d)
                clauses.append(EM.disjunction(*(EM.Not(x) for x in cls)) if cls else c)
            else:
                clauses.append(c)
        elif c.isEq():
            clauses.extend(break_eq(c))
        else:
            clauses.append(c)

    return clauses


def is_overapprox_of(A, B):
    """Return true if B is overapproximation of A"""
    return intersection(complement(B), A).is_empty()


def overapprox_set(
    executor, EM, goal, unsafe, indtarget, assumptions, L, drop_only=False
):
    """
    goal - the set to be overapproxiamted
    drop_only - only try to drop clauses, not to extend them
    """
    create_set = executor.create_set
    # unify variables in goal, target, and unsafe
    S = goal.translated(unsafe)
    target = indtarget.translated(unsafe)
    if assumptions:
        assumptions = assumptions.translated(unsafe)

    # assert not S.is_empty(), "Overapproximating empty set"
    assert intersection(
        S, unsafe
    ).is_empty(), f"Whata? Unsafe states among one-step reachable safe states:\nS = {S},\nunsafe = {unsafe}"
    if __debug__:
        # r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
        # assert (
        #    r.errors is None
        # ), f"Input set is not inductive (CTI: {r.errors[0].model()})"
        assert L.set_is_inductive_towards(
            S, target, allow_infeasible_only=True
        ), f"{S} -> {target}"

    dbg(f"Overapproximating {S}", color="dark_blue")
    dbg(f"  with unsafe states: {unsafe}", color="dark_blue")

    expr = S.as_expr()
    if expr.is_concrete():
        return S

    overapprox = LoopStateOverapproximation(S, executor, target, unsafe, L, EM)
    # overapprox.drop_disjuncts()
    overapprox.drop_clauses(assumptions)

    # NOTE: this works good alone sometimes
    if drop_only:
        S = overapprox.commit()
        return S

    overapprox.overapproximate()

    # drop clauses once more
    overapprox.drop_clauses(None)
    S = overapprox.commit()

    assert intersection(
        unsafe, create_set(S)
    ).is_empty(), "Dropping clauses second time made the set unsafe"

    dbg(f"Overapproximated to {S}", color="orange")

    return S
