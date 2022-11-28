from slowbeast.interpreter.interpreter import Interpreter, ExecutionOptions
from slowbeast.solvers.solver import Solver
from slowbeast.domains.symbolic import Future
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from slowbeast.core.errors import AssertFailError
from slowbeast.ir.instruction import Call

from .executor import Executor as SExecutor


class FutureExecutor(SExecutor):
    def exec_call(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.called_function()
        if self.is_error_fn(fun):
            state.set_error(AssertFailError(f"Called '{fun.name()}'"))
            return [state]

        if fun.is_undefined():
            return self.exec_undef_fun(state, instr, fun)

        if self.calls_forbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.set_killed(
                "calling '{0}', but calls are forbidden".format(fun.name())
            )
            return [state]

        nexti = instr.get_next_inst()
        # if we have no next instr, execute normally
        if False or nexti is None:  # execute normally
            # map values to arguments
            assert len(instr.operands()) == len(fun.arguments())
            mapping = {
                x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
            }
            state.push_call(instr, fun, mapping)
            return [state]
        else:
            retTy = fun.return_type()
            futureval = state.expr_manager().fresh_value("future", retTy)
            future = Future(futureval.unwrap(), futureval.type(), instr, state)
            newstate = state.copy()
            newstate.set(instr, future)
            newstate.add_nondet(future)
            newstate.pc = nexti  # continue executing the next instruction
            newstate.dump()
            # FIXME: clear the state (the function may modify globals)
            return [newstate]


class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super(SEOptions, self).__init__(opts)
        if opts:
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
            self.error_funs = opts.error_funs
        else:
            self.concretize_nondets = False
            self.uninit_is_nondet = False
            self.exit_on_error = False
            self.error_funs = []


class SEStats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0


class FutureSymbolicExecutor(Interpreter):
    def __init__(
        self,
        P,
        ohandler=None,
        opts=SEOptions(),
        executor=None,
        ExecutorClass=FutureExecutor,
    ):
        self.solver = Solver()
        super().__init__(P, opts, executor or ExecutorClass(self.solver, opts))
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler

    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

    def solver(self):
        return self.solver

    def get_next_state(self):
        states = self.states
        if not states:
            return None

        # DFS for now
        return states.pop()

    def handle_new_states(self, newstates):
        hs = self.handle_new_state
        for s in newstates:
            hs(s)

    def handle_new_state(self, s):
        testgen = self.ohandler.testgen if self.ohandler else None
        stats = self.stats
        if s.is_ready():
            self.states.append(s)
        elif s.has_error():
            print_stderr(
                "{0}: {1}, {2}".format(s.get_id(), s.pc, s.get_error()), color="RED"
            )
            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.process_state(s)
            if self.get_options().exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return
        elif s.is_terminated():
            print_stderr(s.get_error(), color="BROWN")
            stats.paths += 1
            stats.terminated_paths += 1
            if testgen:
                testgen.process_state(s)
        elif s.was_killed():
            stats.paths += 1
            stats.killed_paths += 1
            print_stderr(s.status_detail(), prefix="KILLED STATE: ", color="WINE")
            if testgen:
                testgen.process_state(s)
        else:
            assert s.exited()
            dbg("state exited with exitcode {0}".format(s.get_exit_code()))
            stats.paths += 1
            stats.exited_paths += 1
            if testgen:
                testgen.process_state(s)
