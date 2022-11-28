from copy import copy
from slowbeast.util.debugging import dbgv_sec, ldbgv
from slowbeast.core.executor import split_ready_states
from slowbeast.symexe.executionstate import ExecutionState
from .statedescription import StateDescription, unify_state_descriptions


def get_subs(state):
    return {nd.value: nd.instruction for nd in state.nondet_loads()}


class Annotation:
    """
    Object representing what to do/assume/assert in a state.
    """

    ASSUME = 1
    ASSERT = 2
    INSTRS = 3

    __slots__ = "type"

    def __init__(self, ty):
        assert ty >= Annotation.ASSUME and ty <= Annotation.INSTRS
        self.type = ty

    def is_instrs(self):
        return self.type == Annotation.INSTRS

    def is_assume(self):
        return self.type == Annotation.ASSUME

    def is_assert(self):
        return self.type == Annotation.ASSERT


class InstrsAnnotation(Annotation):
    """
    Annotation that is barely a sequence of instructions
    that should be executed
    """

    __slots__ = "instrs"

    def __init__(self, instrs):
        super().__init__(Annotation.INSTRS)
        self.instrs = instrs

    def instructions(self):
        return self.instrs

    def __iter__(self):
        return self.instrs.__iter__()

    def __repr__(self):
        return "[{0}]".format(", ".join(map(lambda i: i.as_value(), self.instrs)))

    def dump(self):
        print("InstrsAnnotation[")
        for i in self.instrs:
            print(f"  {i}")
        print("]")


class ExprAnnotation(Annotation):

    __slots__ = "_sd", "cannonical"

    def __init__(self, ty, expr, subs, EM):
        super().__init__(ty)

        # state description
        self._sd = StateDescription(expr, subs)

        # cannonical form of the annotation (so that we can compare
        # annotations)
        self.cannonical = self._sd.cannonical(EM)

    def descr(self):
        return self._sd

    def expr(self):
        return self._sd.expr()

    # NOTE: use carefully...
    def set_expr(self, expr):
        self._sd.set_expr(expr)

    def substitutions(self):
        return self._sd.substitutions()

    def get_cannonical(self):
        return self.cannonical

    def Not(self, EM):
        n = copy(self)  # to copy the type and methods
        n._sd = StateDescription(EM.Not(self.expr()), self.substitutions())
        n.cannonical = n._sd.cannonical(EM)
        return n

    def do_substitutions(self, state):
        return self._sd.do_substitutions(state)

    def do_input_substitutions(self, state):
        return self._sd.do_input_substitutions(state)

    def has_all_substitutions(self, state):
        return self._sd.has_all_substitutions(state)

    def eval_subs(self, state):
        return self._sd.eval_subs(state)

    def eval_input_subs(self, state):
        return self._sd.eval_input_subs(state)

    def __eq__(self, rhs):
        return self.cannonical == rhs.cannonical

    def __hash__(self):
        assert self.cannonical
        return self.cannonical.__hash__()

    def __repr__(self):
        assert self.cannonical
        return f"{self.cannonical}"
        # return "{0}[{1}]".format(self._expr, ",
        # ".join(f"{x.as_value()}/{val.unwrap()}" for (x, val) in
        # self.subs.items()))

    def dump(self):
        print(
            "ExprAnnotation[{0}]:".format(
                "assert" if self.type == Annotation.ASSERT else "assume"
            )
        )
        print(f"> expr: {self.expr()}")
        print(f"> cannonical: {self.get_cannonical()}")
        print(
            "> substitutions: {0}".format(
                ", ".join(
                    f"{x.as_value()}/{val.unwrap()}"
                    for (val, x) in self.substitutions().items()
                )
            )
        )


class AssertAnnotation(ExprAnnotation):
    def __init__(self, expr, arg1, em=None):
        if isinstance(arg1, ExecutionState):
            subs = get_subs(arg1)
            em = arg1.expr_manager()
        else:
            subs = arg1
        assert isinstance(subs, dict), subs
        assert em is not None
        super().__init__(Annotation.ASSERT, expr, subs, em)

    def to_assume(self, EM):
        return AssumeAnnotation(self.expr(), self.substitutions(), EM)

    def assume_not(self, EM):
        return AssumeAnnotation(EM.Not(self.expr()), self.substitutions(), EM)

    def __repr__(self):
        return f"@[assert {ExprAnnotation.__repr__(self)}]"


class AssumeAnnotation(ExprAnnotation):
    def __init__(self, expr, subs, EM):
        super().__init__(Annotation.ASSUME, expr, subs, EM)

    def to_assume(self, EM):
        return self

    def assume_not(self, EM):
        return AssumeAnnotation(EM.Not(self.expr()), self.substitutions(), EM)

    def __repr__(self):
        return f"@[assume {ExprAnnotation.__repr__(self)}]"


class DummyInst:
    """
    Dummy instruction that serves as a place-holder for the
    pc in a state. The execute methods call get_next_inst()
    and if the state has no pc set, it crashes.
    FIXME: this is a hack, rather make the execute() not to call get_next_inst()
    (add a new method execute_with_pc or something like that)
    """

    def get_next_inst(self):
        return self


def _execute_instr(executor, states, instr):
    newstates = []
    dummypc = DummyInst()
    for state in states:
        # FIXME: get rid of this -- make a version of execute() that does not mess with pc
        oldpc = state.pc
        state.pc = dummypc
        assert state.is_ready()
        tmp = executor.execute(state, instr)
        for t in tmp:
            t.pc = oldpc
        newstates += tmp

    ready, nonready = [], []
    for x in newstates:
        (ready, nonready)[0 if x.is_ready() else 1].append(x)
    return ready, nonready


def _execute_instr_annotation(executor, states, annot):
    nonready = []
    for instr in annot:
        states, u = _execute_instr(executor, states, instr)
        nonready += u
    return states, nonready


def execute_annotation_substitutions(executor, states, annot):
    """
    Execute instructions from substitutions of an annotation
    """
    subs = annot.substitutions()
    nonready = []
    for i in set(subs.values()):
        states, nr = _execute_instr(executor, states, i)
        nonready += nr
    return states, nonready


def _execute_expr_annotation(executor, states, annot):
    states, nonready = execute_annotation_substitutions(executor, states, annot)

    isassume = annot.is_assume()
    ready = states
    states = []
    for s in ready:
        expr = annot.do_substitutions(s)
        ldbgv("Executing annotation\n{0}\n==>\n{1}", (annot, expr), verbose_lvl=3)
        if isassume:
            s = executor.assume(s, expr)
            if s:
                states.append(s)
        else:
            assert annot.is_assert()
            tmp = executor.exec_assert_expr(s, expr)
            tr, tu = split_ready_states(tmp)
            states += tr
            nonready += tu

    return states, nonready


def execute_annotation(executor, states, annot):
    """Execute the given annotation on states"""

    assert isinstance(annot, Annotation), annot
    assert all(map(lambda s: s.is_ready(), states))

    ldbgv("{0}", (annot,), verbose_lvl=3)
    # dbgv_sec(f"executing annotation:\n{annot}")

    if annot.is_instrs():
        states, nonready = _execute_instr_annotation(executor, states, annot)
    else:
        assert annot.is_assume() or annot.is_assert()
        states, nonready = _execute_expr_annotation(executor, states, annot)

    # dbgv_sec()
    return states, nonready


def execute_annotations(executor, s, annots):
    assert s.is_ready(), "Cannot execute non-ready state"
    oldpc = s.pc

    dbgv_sec(f"executing annotations on state {s.get_id()}", verbose_lvl=3)

    ready, nonready = [s], []
    for annot in annots:
        ready, nr = execute_annotation(executor, ready, annot)
        nonready += nr

    assert all(map(lambda s: s.pc is oldpc, ready))

    dbgv_sec()
    return ready, nonready


def _join_annotations(EM, Ctor, op, annots):
    assert len(annots) > 0
    if len(annots) == 1:
        return Ctor(annots[0].expr(), annots[0].substitutions(), EM)

    simplify = EM.simplify
    subs = {}
    S = None
    for a in annots:
        expr1, expr2, subs = unify_state_descriptions(EM, S, a)
        if expr1 and expr2:
            S = Ctor(simplify(op(expr1, expr2)), subs, EM)
        else:
            S = Ctor(expr1 or expr2, subs, EM)
    return S


def unify_annotations(EM, a1, a2):
    return unify_state_descriptions(EM, a1.descr(), a2.descr())


def or_annotations(EM, toassert, *annots):
    assert isinstance(toassert, bool)
    assert all(map(lambda x: isinstance(x, ExprAnnotation), annots))

    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    return _join_annotations(EM, Ctor, EM.Or, annots)


def and_annotations(EM, toassert, *annots):
    assert isinstance(toassert, bool)
    assert all(map(lambda x: isinstance(x, ExprAnnotation), annots))

    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    return _join_annotations(EM, Ctor, EM.And, annots)


def state_to_annotation(state, toassert=False):
    EM = state.expr_manager()
    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    return Ctor(
        state.constraints_obj().as_formula(EM),
        get_subs(state),
        EM,
    )


def states_to_annotation(states):
    a = None
    for s in states:
        EM = s.expr_manager()
        a = or_annotations(
            EM,
            False,
            a or AssumeAnnotation(EM.get_false(), {}, EM),
            state_to_annotation(s),
        )
    return a
