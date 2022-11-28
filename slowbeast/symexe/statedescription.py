from slowbeast.domains.symbolic import Expr
from slowbeast.domains.pointer import Pointer
from slowbeast.ir.instruction import Instruction, Load
from slowbeast.domains.concrete import ConcreteVal


def _get_cannonic_var(val, x, EM):
    if isinstance(x, Load):
        name = f"{x.operand(0).as_value()}"
    else:
        name = x.as_value()
    return EM.Var(name, val.type())


def _createCannonical(expr, subs, EM):
    get_cannonic_var = _get_cannonic_var
    return EM.substitute(
        expr,
        *(
            (val, get_cannonic_var(val, x, EM))
            for (val, x) in subs.items()
            if not val.is_pointer()
        ),
    )


class StateDescription:
    """
    A description of a symbolic execution state
    as a formula + substitutions from results
    of instructions. That is, an StateDescription
    object describes the symbolic execution state
    in which holds the expression after substituing
    the results of instructions according to
    the substitutions.
    """

    __slots__ = "_expr", "_subs"

    def __init__(self, expr, subs):
        assert expr.is_bool(), expr
        assert expr is not None and isinstance(expr, (Expr, ConcreteVal))
        assert subs is not None and isinstance(subs, dict)

        # the expression to evaluate
        self._expr = expr

        # substitution for the expression -
        # a mapping expr -> instruction meaning that
        # state.eval(instruction) should be put on the
        # place of the key expression
        assert isinstance(subs, dict)
        assert all(map(lambda k: isinstance(k, (Expr, Pointer)), subs.keys())), subs
        assert all(map(lambda k: isinstance(k, Instruction), subs.values())), subs
        self._subs = subs

    def cannonical(self, EM):
        return _createCannonical(self._expr, self._subs, EM)

    def expr(self):
        return self._expr

    def set_expr(self, expr):
        """Set expression in this states decriptior. Use responsibly!"""
        self._expr = expr

    def substitutions(self):
        return self._subs

    def has_all_substitutions(self, state):
        get = state.get
        for v, x in self._subs.items():
            assert v, (v, x)
            xx = get(x)
            if xx is None:
                return False
        return True

    def eval_subs(self, state):
        get = state.get
        for v, x in self._subs.items():
            assert v, (v, x)
            xx = get(x)
            if xx is None or v == xx:
                continue  # cannot or don't need to substitute
            assert xx.type() == v.type(), (xx, v)
            if xx.is_pointer():
                assert v.is_pointer(), v
                yield (v.object(), xx.object())
                yield (v.offset(), xx.offset())
            else:
                yield (v, xx)

    def do_substitutions(self, state):
        """
        Return the expression after substitutions
        in the given state.
        """
        EM = state.expr_manager()
        subs = self.eval_subs(state)

        # we must do all the substitution at once!
        assert all(
            map(lambda x: x[0].type() == x[1].type(), self.eval_subs(state))
        ), self._subs
        return EM.simplify(
            EM.substitute(
                self._expr, *((val, curval) for (val, curval) in subs if curval)
            )
        )

    def eval_input_subs(self, state):
        ndts = {nd.instruction: nd.value for nd in state.nondets()}
        get = ndts.get
        return ((v, get(x)) for (v, x) in self._subs.items() if get(x) is not None)

    def do_input_substitutions(self, state):
        """
        Return the expression after substitutions of nondeterministic (input) values
        in the given state. The difference is that do_substitutions takes the output
        values (registers) and this method takes the input values (nondets).
        """
        assert all(
            map(lambda x: x[0].type() == x[1].type(), self.eval_input_subs(state))
        )

        EM = state.expr_manager()
        return EM.simplify(
            EM.substitute(
                self._expr,
                *(
                    (val, curval)
                    for (val, curval) in self.eval_input_subs(state)
                    if curval
                ),
            )
        )

    def __repr__(self):
        return "{0}[{1}]".format(
            self._expr,
            ", ".join(f"{x.as_value()}->{val}" for (val, x) in self._subs.items()),
        )

    def dump(self):
        print("StateDescription:")
        print(f"> expr: {self._expr}")
        print(
            "> substitutions: {0}".format(
                ", ".join(
                    f"{x.as_value()} -> {val.unwrap()}"
                    for (val, x) in self._subs.items()
                )
            )
        )


def unify_state_descriptions(EM, sd1, sd2):
    """
    Take two annotations, unify their variables and substitutions.
    Return the new expressions and the substitutions
    """
    if sd1 is None:
        return None, sd2.expr(), sd2.substitutions()
    if sd2 is None:
        return sd1.expr(), None, sd1.substitutions()

    # perform less substitutions if possible
    subs1 = sd1.substitutions()
    subs2 = sd2.substitutions()
    expr1 = sd1.expr()
    expr2 = sd2.expr()
    if 0 < len(subs2) < len(subs1) or len(subs1) == 0:
        subs1, subs2 = subs2, subs1
        expr1, expr2 = expr2, expr1

    if len(subs1) == 0:
        assert len(subs2) == 0
        return EM.simplify(expr1), EM.simplify(expr2), {}

    subs = {}
    col = False
    for (val, instr) in subs1.items():
        instr2 = subs2.get(val)
        if instr2 and instr2 != instr:
            # collision
            freshval = EM.fresh_value(val.name(), val.type())
            expr2 = EM.substitute(expr2, (val, freshval))
            subs[freshval] = instr2

        # always add this one
        subs[val] = instr

    # add the rest of subs2
    for (val, instr) in subs2.items():
        if not subs.get(val):
            subs[val] = instr

    return EM.simplify(expr1), EM.simplify(expr2), subs


def state_to_description(state):
    EM = state.expr_manager()
    return StateDescription(
        state.constraints_obj().as_formula(EM),
        {
            l.value: l.instruction
            for l in state.nondets()
            if isinstance(l.instruction, Load)
        },
    )


def states_to_description(states) -> StateDescription:
    a = None
    for s in states:
        # FIXME: this can break things in the future
        EM = s.expr_manager()
        if a is None:
            a = state_to_description(s)
        else:
            e1, e2, subs = unify_state_descriptions(
                EM,
                a,
                state_to_description(s),
            )
            a = StateDescription(EM.Or(e1, e2), subs)
    return a


def _execute_instr(executor, state, instr):
    class DummyInstr:
        """
        Dummy class that returns self as the next instruction.
        Needed to execute the instructions from substitutions.
        """

        def get_next_inst(self):
            return self

    assert state.is_ready()
    # FIXME: get rid of this -- make a version of execute() that does not mess with pc
    oldpc, state.pc = state.pc, DummyInstr()
    newstates = executor.execute(state, instr)
    assert newstates, "Executing instruction resulted in no state"
    if len(newstates) != 1:
        raise NotImplementedError("Executing forking instructions not supported")
    state = newstates[0]
    assert state.is_ready(), "Executing instruction resulted in non-ready state"
    state.pc = oldpc
    return state


def eval_state_description(executor, state, sd):
    subs = sd.substitutions()
    # execute those instructions whose value we are going to substitute
    for i in set(subs.values()):
        if state.get(i) is not None:
            continue  # we already got this value, do not execute again
        state = _execute_instr(executor, state, i)

    return sd.do_substitutions(state)
