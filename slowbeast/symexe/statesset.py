from slowbeast.symexe.statedescription import (
    StateDescription,
    state_to_description,
    unify_state_descriptions,
    eval_state_description,
)
from slowbeast.symexe.constraints import ConstraintsSet
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.annotations import (
    ExprAnnotation,
    AssertAnnotation,
    AssumeAnnotation,
)
from slowbeast.domains.symbolic import Expr
from slowbeast.domains.concrete import ConcreteVal

from slowbeast.solvers.solver import global_expr_mgr


class StatesSet:
    """
    A symbolic execution state represents a set of concrete states.
    This class is a wrapper that makes it convenient to treat
    SE state as a set of concrete states (i.e., it allows to
    use set operations, etc.
    NOTE that the state given to ctor is stored as a reference,
    i.e. the operations modify the state and it is intentional.
    To avoid this, pass a fresh copy of the state into the ctor
    (state.copy()).
    """

    __slots__ = "_state"

    def __init__(self, state: SEState):
        """Create new states set from the given states"""

        assert state is not None and isinstance(state, SEState)
        # assert state.is_feasible(), "Infeasible state given"
        # NOTE: we want to be able to create infeasible states
        # (empty sets)
        self._state = state

    def copy(self):
        return StatesSet(self.get_se_state().copy())

    def expr_manager(self):
        return global_expr_mgr()

    def get_se_state(self):
        return self._state

    def as_description(self):
        return state_to_description(self.get_se_state())

    def as_expr(self):
        """NOTE: use carefully, only when you know what you do..."""
        return self._state.constraints_obj().as_formula(self.expr_manager())

    def rewrite_and_simplify(self):
        self.reset_expr(self.as_expr().rewrite_and_simplify())
        return self

    def as_assume_annotation(self):
        sd = state_to_description(self._state)
        return AssumeAnnotation(
            sd.expr(), sd.substitutions(), self._state.expr_manager()
        )

    def as_assert_annotation(self):
        sd = state_to_description(self._state)
        return AssertAnnotation(
            sd.expr(), sd.substitutions(), self._state.expr_manager()
        )

    def reset_expr(self, expr=None):
        """NOTE: use carefully, only when you know what you do..."""
        C = ConstraintsSet()
        if expr is not None:
            C.add(expr)
        self._state.set_constraints(C)
        return self

    def _unite(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)

        if not state.constraints():
            # the state is clean, just add the first constraints
            state.add_constraint(expr)
            return

        EM = state.expr_manager()
        C = ConstraintsSet()
        newexpr = EM.Or(expr, state.constraints_obj().as_formula(EM))
        if not newexpr.is_concrete():
            C.add(newexpr)
        # else:
        #    # if newexpr is concrete, it must be True. And adding True is useless,
        #    # its the same as empty constraints
        #    assert newexpr.value() is True  # this is Or expr...
        state.set_constraints(C)

    def model(self):
        return self._state.model()

    def unite(self, *S):
        for s in S:
            self._unite(s)
        return self

    def add(self, *S):
        return self.unite(S)

    def intersect(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)
        state.add_constraint(expr)
        return self

    def translate(self, S):
        """
        Make the set use internally the same variables as 'S'
        """
        selfsd = state_to_description(self._state)

        if isinstance(S, SEState):
            state = S.copy()
        else:
            state = S._state.copy()
        self._state = state
        newexpr = eval_state_description(state.executor(), state, selfsd)
        state.set_constraints(ConstraintsSet((newexpr,)))
        return self

    def translated(self, S):
        """
        Make the set use internally the same variables as 'S'
        """
        selfsd = state_to_description(self._state)
        if isinstance(S, SEState):
            state = S.copy()
        else:
            state = S._state.copy()
        newexpr = eval_state_description(state.executor(), state, selfsd)
        state.set_constraints(ConstraintsSet((newexpr,)))
        return StatesSet(state)

    def complement(self):
        state = self._state
        EM = state.expr_manager()
        expr = EM.Not(state.constraints_obj().as_formula(EM))
        C = ConstraintsSet()
        C.add(expr)
        state.set_constraints(C)
        return self

    def minus(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)
        EM = state.expr_manager()
        state.add_constraint(EM.Not(expr))
        return self

    def is_empty(self):
        """Check whether the set is empty. Involves a solver call"""
        return not self._state.is_feasible()

    def contains(self, S):
        X = self.copy()
        X.complement()
        X.intersect(S)
        return X.is_empty()

    def contains_any(self, *Ss):
        X = self.copy()
        X.complement()
        for s in Ss:
            if intersection(X, s).is_empty():
                return True
        return False

    def __repr__(self):
        return f"{{{self.as_description().__repr__()}}}"

    def dump(self):
        print(f"StateSet{{{self.as_description().__repr__()}}}")


def to_states_descr(S) -> StateDescription:
    EM = global_expr_mgr()

    if isinstance(S, StatesSet):
        return S.as_description()
    if isinstance(S, SEState):
        return state_to_description(S)
    elif isinstance(S, StateDescription):
        return S
    elif isinstance(S, ExprAnnotation):
        return S.descr()
    elif isinstance(S, Expr):
        # NOTE: maybe we should have a special method for Expr,
        # because Expr does not fully describe the state (unlike the others)
        # and therefore can break things... For this reason, it would
        # be reasonable to have explicit method conserning adding Expr
        # so that the user is aware of this problem...
        return StateDescription(S, {})
    elif isinstance(S, ConcreteVal) and S.is_bool():
        return StateDescription(S, {})
    elif hasattr(S, "__iter__"):
        R = None
        for s in S:
            if R is None:
                R = to_states_descr(s)
            else:
                expr1, expr2, subs = unify_state_descriptions(EM, R, to_states_descr(s))
                R = StateDescription(EM.Or(expr1, expr2), subs)
        return R

    raise NotImplementedError(f"Unhandled states representation: {type(S)}")


def union(S1, *Ss) -> StatesSet:
    assert isinstance(S1, StatesSet), S1
    X = S1.copy()
    for S in Ss:
        X.add(S)
    return X


def intersection(S1, *Ss) -> StatesSet:
    assert isinstance(S1, StatesSet), S1
    X = S1.copy()
    for S in Ss:
        X.intersect(S)
    return X


def complement(S) -> StatesSet:
    assert isinstance(S, StatesSet), S
    X = S.copy()
    X.complement()
    return X


#
# class StatesSet:
#     """
#     A unified way how to represent a set of states in symbolic execution.
#     Once we have a StateSet, we can unify or intersect it with other StatesSet,
#     Annotation (StateDescription) or symbolic execution state or with just
#     a formula.
#     """
#     __slots__ = ["_descr"]
#
#     def __init__(self, s):
#         self._descr = none
#         self.add(s)
#
#     def getexprmanager(self):
#         return getglobalexprmanager()
#
#     def descr(self):
#         return self._descr
#
#     def _adjoin(self, s, op):
#         em = self.getexprmanager()
#         d = to_states_descr(s)
#         descr = self._descr
#         if descr:
#             e1, e2, subs = unify_state_descriptions(em, d, descr)
#             self._descr = statedescription(op(e1, e2), subs)
#         else:
#             self._descr = d
#
#     def add(self, S):
#         self._adjoin(S, self.expr_manager().Or)
#
#     def intersect(self, S):
#         self._adjoin(S, self.expr_manager().And)
#
#     def union(self, S):
#         self.add(S)
#
#     def negate(self):
#         """ Complement this set in-place """
#         descr = self._descr
#         if descr:
#             descr.setExpr(self.expr_manager().Not(descr.expr()))
#
#     def complement(self):
#         """ Returns the complement of this set without modifying it """
#         d = self._descr
#         if d:
#             EM = self.expr_manager()
#             return StatesSet(StateDescription(EM.Not(d), d.substitutions()))
#         return StatesSet()
#
#     def __repr__(self):
#         d = self._descr
#         if d is None:
#             return "{empty}"
#         return f"{{{d.cannonical(self.expr_manager())}}}"
#
#     def dump(self):
#         d = self._descr
#         if d is None:
#             print("{empty}")
#             return
#         print("StatesSet -->:")
#         print(f"Expr:\n{{{d}}}\n")
#         print(f"Cannonical:\n{{{d.cannonical(self.expr_manager())}}}")
#         print("<--:")
#
#
# def to_states_descr(S) -> StateDescription:
#     EM = global_expr_mgr()
#
#     if isinstance(S, StatesSet):
#         return S.descr()
#     if isinstance(S, SEState):
#         return state_to_description(S)
#     elif isinstance(S, StateDescription):
#         return S
#     elif isinstance(S, ExprAnnotation):
#         return S.descr()
#     elif isinstance(S, Expr):
#         return StateDescription(S, {})
#     elif S is None and hasattr(S, "__iter__"):
#         R = None
#         for s in S:
#             if R is None:
#                 R = to_states_descr(s)
#             else:
#                 R = unify_state_descriptions(EM, R, to_states_set(s))
#         return R
#
#     raise NotImplementedError("Unhandled states representation")
