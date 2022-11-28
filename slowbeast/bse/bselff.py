from slowbeast.symexe.executionstate import SEState as ExecutionState
from slowbeast.symexe.symbolicexecution import SymbolicExecutor, SEOptions, SExecutor
from slowbeast.symexe.annotations import execute_annotation
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.bse.bse import report_state
from slowbeast.bse.bself import BSELF, BSELFOptions, BSELFChecker as BSELFCheckerVanilla
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.util.debugging import (
    print_stdout,
    inc_print_indent,
    dec_print_indent,
    dbg,
)

from slowbeast.cfkind.relations import get_var_cmp_relations


#####################################################################
# Forward execution
#####################################################################
class SEState(ExecutionState):
    """
    Execution state of forward symbolic execution in BSELFF.
    It is exactly the same as the parent class, but it also
    computes the number of hits to a particular loop headers.
    """

    __slots__ = "_loc_visits"

    def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)
        self._loc_visits = {}

    def _copy_to(self, new):
        super()._copy_to(new)
        # FIXME: use COW
        new._loc_visits = self._loc_visits.copy()

    def visited(self, inst):
        n = self._loc_visits.setdefault(inst, 0)
        self._loc_visits[inst] = n + 1

    def num_visits(self, inst=None):
        if inst is None:
            inst = self.pc
        return self._loc_visits.get(inst)


class Executor(SExecutor):
    def create_state(self, pc=None, m=None):
        if m is None:
            m = self.get_memory_model().create_memory()
        s = SEState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s


class BSELFFSymbolicExecutor(SymbolicExecutor):
    def __init__(
        self,
        P,
        ohandler=None,
        opts=SEOptions(),
        executor=None,
        ExecutorClass=Executor,
        programstructure=None,
        fwdstates=None,
    ):
        super().__init__(P, ohandler, opts, executor, ExecutorClass)
        self.programstructure = programstructure
        self._loop_headers = {
            loc.elem()[0]: loc for loc in self.programstructure.get_loop_headers()
        }
        self._covered_insts = set()
        self.forward_states = fwdstates

    def is_loop_header(self, inst):
        return inst in self._loop_headers

    def get_next_state(self):
        states = self.states
        if not states:
            return None

        none_num = 0
        state_idx = None
        some_state_idx = None
        covered = self._covered_insts
        for idx in range(len(states)):
            state = states[idx]
            if state is None:
                none_num += 1
                continue
            if some_state_idx is None:
                some_state_idx = idx
            if state.pc not in covered:
                state_idx = idx
                break

        if state_idx is None:
            state_idx = some_state_idx
        if state_idx is None:
            assert all(map(lambda x: x is None, states))
            self.states = None
            return None

        assert state_idx is not None
        state = states[state_idx]
        states[state_idx] = None

        # don't care about the +1 from prev line...
        if state is None or (none_num > 20 and (none_num / len(states)) >= 0.5):
            self.states = [s for s in states if s is not None]
        return state

    def handle_new_state(self, s):
        pc = s.pc
        self._covered_insts.add(pc)

        if s.is_ready() and self.is_loop_header(pc):
            s.visited(pc)
            self._register_loop_states(s)
        super().handle_new_state(s)

    def _register_loop_states(self, state):
        n = state.num_visits()
        assert n > 0, "Bug in counting visits"
        states = self.forward_states.setdefault(state.pc, [])
        # if we have a state that visited state.pc n times,
        # we must have visited it also k times for all k < n
        assert len(states) != 0 or n == 1, self.forward_states
        assert len(states) >= n - 1, self.forward_states
        if len(states) == n - 1:
            states.append([state.copy()])
        else:
            assert len(states) >= n
            states[n - 1].append(state.copy())

    # S = self.executor().create_states_set(state)
    # loc = self._loop_headers[state.pc]
    # A, rels, states = self.forward_states.setdefault(loc, (self.executor().create_states_set(), set(), []))
    # cur_rels = set()
    # for rel in (r for r in get_var_cmp_relations(state, A) if r not in rels):
    #    if rel.get_cannonical().is_concrete(): # True
    #        continue
    #    rels.add(rel)
    #    cur_rels.add(rel)
    #    print('rel', rel)
    #    A.add(S)
    # states.append((state, rels))
    # print(states)
    # print(A)


#####################################################################
# Backward execution
#####################################################################


class BSELFChecker(BSELFCheckerVanilla):
    def __init__(
        self,
        loc,
        A,
        program,
        programstructure,
        opts,
        invariants=None,
        indsets=None,
        max_loop_hits=None,
        forward_states=None,
    ):
        super().__init__(
            loc, A, program, programstructure, opts, invariants, indsets, max_loop_hits
        )
        self.forward_states = forward_states
        memorymodel = LazySymbolicMemoryModel(opts)
        pathexecutor = PathExecutor(program, self.solver(), opts, memorymodel)
        # forbid defined calls...
        # pathexecutor.forbid_calls()
        self._pathexecutor = pathexecutor

    def check_loop_precondition(self, L, A):
        loc = L.header()
        print_stdout(f"Checking if {str(A)} holds on {loc}", color="purple")

        # "fast" path -- check with the forward states that we have
        fstates = self.forward_states.get(L.header().elem()[0])
        if fstates:
            # use only the states from entering the loop -- those are most likely to work
            states = [s.copy() for s in fstates[0]]
            r, n = execute_annotation(self._pathexecutor, states, A)
            if n and any(map(lambda s: s.has_error(), n)):
                return Result.UNKNOWN, None
        inc_print_indent()
        # run recursively BSELFChecker with already computed inductive sets
        checker = BSELFChecker(
            loc,
            A,
            self.program,
            self.programstructure,
            self.options,
            indsets=self.inductive_sets,
            invariants=self.invariant_sets,
            max_loop_hits=1,
            forward_states=self.forward_states,
        )
        result, states = checker.check(L.entries())

        dec_print_indent()
        dbg(f"Checking if {A} holds on {loc} finished")
        return result, states

    def fold_loop(self, loc, L, unsafe, loop_hit_no):
        fstates = self.forward_states.get(L.header().elem()[0])
        if fstates is None:
            self.max_seq_len = 2
        else:
            self.max_seq_len = 2  # * len(L.paths())
        return super().fold_loop(loc, L, unsafe, loop_hit_no)

    def do_step(self):
        bsectx = self.get_next_state()
        if bsectx is None:
            return (
                Result.UNKNOWN if self.problematic_states else Result.SAFE
            ), self.problematic_paths_as_result()
        return self._do_step(bsectx)


class BSELFF(BSELF):
    """
    The main class for BSELFF (BSELF with forward analysis)
    """

    def __init__(self, prog, ohandler=None, opts=BSELFOptions()):
        print("BSELF^2")
        super().__init__(prog, ohandler, opts)
        self.forward_states = {}
        # self.create_set = self.ind_executor().create_states_set

    def run(self):
        se = BSELFFSymbolicExecutor(
            self.program,
            self.ohandler,
            self.options,
            programstructure=self.programstructure,
            fwdstates=self.forward_states,
        )
        se.prepare()
        se_checkers = [se]

        bself_checkers = []
        for loc, A in self._get_possible_errors():
            print_stdout(f"Checking possible error: {A.expr()} @ {loc}", color="white")
            checker = BSELFChecker(
                loc,
                A,
                self.program,
                self.programstructure,
                self.options,
                invariants=self.invariants,
                forward_states=self.forward_states,
            )
            checker.init_checker()
            bself_checkers.append(checker)

        while True:
            remove_checkers = set()
            for checker in se_checkers:
                for i in range(7):
                    # print("... forward step")
                    checker.do_step()

                    # forward SE found an error
                    if checker.stats.errors > 0:
                        return Result.UNSAFE
                    # forward SE searched whole program and found no error
                    if not checker.states:
                        if checker.stats.killed_paths == 0:
                            return Result.SAFE
                        else:
                            # BSELF can still prove the program correct if we failed here,
                            # just remove this checker
                            remove_checkers.add(checker)
            for c in remove_checkers:
                se_checkers.remove(c)

            bself_has_unknown = False
            remove_checkers = set()
            for checker in bself_checkers:
                # print("... backward step")
                result, states = checker.do_step()
                if result is None:
                    continue
                self.stats.add(checker.stats)
                if result is Result.UNSAFE:
                    # FIXME: report the error from bsecontext
                    print_stdout(
                        f"{states.get_id()}: [assertion error]: {loc} reachable.",
                        color="redul",
                    )
                    print_stdout(str(states), color="wine")
                    print_stdout("Error found.", color="redul")
                    self.stats.errors += 1
                    return result
                if result is Result.SAFE:
                    print_stdout(
                        f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                    )
                    remove_checkers.add(checker)
                elif result is Result.UNKNOWN:
                    print_stdout(
                        f"Checking {A} at {loc} was unsuccessful.", color="yellow"
                    )
                    bself_has_unknown = True
                    assert (
                        checker.problematic_states
                    ), "Unknown with no problematic paths?"
                    for p in checker.problematic_states:
                        report_state(self.stats, p)

            for c in remove_checkers:
                bself_checkers.remove(c)
            if not bself_checkers:
                if bself_has_unknown:
                    print_stdout("Failed deciding the result.", color="orangeul")
                    return Result.UNKNOWN

                print_stdout("No error found.", color="greenul")
                ohandler = self.ohandler
                if ohandler:
                    ohandler.testgen.generate_proof(self)
                return Result.SAFE
