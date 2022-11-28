from .executor import Executor as SExecutor
from ..util.debugging import print_stderr, print_stdout, dbg

from .symbolicexecution import SEOptions, SymbolicExecutor


def subsumed_memory(s, state):
    # every value in the state must be included in the corresponding value of s
    # FIXME: accessing protected attrs
    meml, memr = state.memory, s.memory

    if len(meml._cs) != len(memr._cs):
        return False

    # cs, objects, globalobjects
    for reg, lo in meml._objects.items():
        # if two MO with same ID in two states correspond to the same allocation during runtime, so we can just compare
        # them
        ro = memr.get_obj(reg)
        if ro is None:
            return False
        for lval in lo.values().items():
            s.is_sat()
    return True


class StatefulSymbolicExecutor(SymbolicExecutor):
    def __init__(
        self, P, ohandler=None, opts=SEOptions(), executor=None, ExecutorClass=SExecutor
    ):
        super().__init__(
            P,
            ohandler,
            opts,
            executor,
            ExecutorClass,
        )
        self.explored_states = {}

    def handle_new_state(self, state):
        if self.is_subsumed(state):
            return
        if state.is_ready():
            self.states.append(state)
        else:
            super().handle_new_state(state)

    def is_subsumed(self, state):
        """
        Return true if we have a state that was implied by this state
        """
        pc = state.pc
        # FIXME use approximate hasing to get a small set of states for subsumption checking
        # for s in self.explored_states.setdefault(pc, set()):
        EM = state.expr_manager()
        for s in self.explored_states.setdefault(pc, []):
            # FIXME: will not work with incremental solving, there may be a symbol collision
            # every value in the state must be included in the corresponding value of s
            assert state.pc is s.pc
            if s.status != state.status:
                continue
            if subsumed_memory(s, state):
                return True

        # if s.is_sat(EM.Not(state.constraints_obj().asFormula(EM))) is False:
        #    dbg(f"Subsumed {state.constraints()} by {s.constraints()} at {pc}", color="white")
        #    return True
        # self.explored_states[pc].add(state)
        self.explored_states[pc].append(state)
        return False
