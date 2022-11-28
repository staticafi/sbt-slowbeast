from ..core.executor import Executor

from ..util.debugging import print_stderr, dbg
from .interactive import InteractiveHandler


class ExecutionOptions:
    INSTR_STEP = 1
    BLOCK_STEP = 2

    def __init__(self, opts=None):
        if opts:
            self.step = opts.step
            self.interactive = opts.interactive
            self.no_calls = opts.no_calls
            self.lazy_mem_access = opts.lazy_mem_access
        else:
            self.step = ExecutionOptions.INSTR_STEP
            self.interactive = False
            self.no_calls = False
            self.lazy_mem_access = False

    def setBlockStep(self):
        self.step = ExecutionOptions.BLOCK_STEP
        return self

    def __str__(self):
        return f"{self.__repr__()}\n" + "\n".join(
            f"  {k} = {v}" for k, v in self.__dict__.items()
        )


# dummy class used as a program counter during initialization
# of global variables
class GlobalInit:
    def get_next_inst(self):
        return self


class Interpreter:
    def __init__(self, program, opts=ExecutionOptions(), executor=None):
        self._program = program
        self._options = opts
        self._executor = Executor(opts) if executor is None else executor
        self._interactive = InteractiveHandler(self) if opts.interactive else None

        self.states = []
        self.error_states = []
        # self.states_num = 0

    def getProgram(self):
        return self._program

    def get_options(self):
        return self._options

    def executor(self):
        return self._executor

    def getStates(self):
        return self.states

    def initialStates(self):
        """
        Get state(s) from which to start execution.
        May be overriden by child classes
        """
        return [self._executor.create_state()]

    def get_next_state(self):
        if not self.states:
            return None

        # this is concrete execution
        assert len(self.states) == 1
        s = self.states.pop()
        assert len(self.states) == 0
        return s

    def handle_new_state(self, state):
        if state.is_ready():
            assert len(self.states) == 0
            self.states.append(state)
        elif state.has_error():
            print_stderr("Error while executing '{0}'".format(state), color="RED")
            print_stderr(state.get_error(), color="BROWN")
            self.error_states.append(state)
            state.dump()
        elif state.is_terminated():
            print_stderr(state.get_error(), color="BROWN")
        elif state.was_killed():
            print_stderr(state.status_detail(), prefix="KILLED STATE: ", color="WINE")
        else:
            assert state.exited()
            dbg(f"state exited with exitcode {state.get_exit_code()}")

        raise RuntimeError("This line should be unreachable")

    def handle_new_states(self, newstates):
        assert len(newstates) == 1, "Concrete execution returned more than one state"
        self.handle_new_state(newstates[0])

    def interact_if_needed(self, s):
        if self._interactive is None:
            return

        self._interactive.prompt(s)

    def run_static(self):
        """Run static ctors (e.g. initialize globals)"""
        # fake the program counter for the executor
        ginit = GlobalInit()
        states = self.states

        for s in states:
            s.pc = ginit

        globs = self._program.globals()
        for G in globs:
            # bind the global to the state
            for s in states:
                s.memory.allocate_global(G, zeroed=G.is_zeroed())

            if not G.has_init():
                continue
            for i in G.init():
                for s in states:
                    ret = self._executor.execute(s, i)
                    assert len(ret) == 1, "Unhandled initialization"
                    assert ret[0] is s, "Unhandled initialization instruction"
                    assert ret[
                        0
                    ].is_ready(), (
                        "Generated errorneous state during initialization of globals"
                    )

    def _main_args(self, state):
        """
        Initialize argc and argv (if needed) for the main function
        """
        fun = self.getProgram().entry()
        args = fun.arguments()
        if len(args) == 0:
            return None
        argc = state.solver().fresh_value("argc", args[0].type())
        argv_size = state.solver().fresh_value("argv_size", args[0].type())
        # FIXME: this is only approximation...
        # FIXME: argv should be terminated with 0, but our memory model does not handle
        # symbolic writes yet
        argv = state.memory.allocate(argv_size, nm="argv")
        return {args[0]: argc, args[1]: argv}

    def prepare(self):
        """
        Prepare the interpreter for execution.
        I.e. initialize static memory and push the call to
        the main function to call stack.
        Result is a set of states before starting executing
        the entry function.
        """
        self.states = self.initialStates()
        self.run_static()

        # push call to main to call stack
        for s in self.states:
            main_args = self._main_args(s)
            s.push_call(None, self.getProgram().entry(), argsMapping=main_args)

    def report(self):
        pass

    def do_step(self):
        state = self.get_next_state()
        if state is None:
            return
        self.interact_if_needed(state)
        if self._options.step == ExecutionOptions.INSTR_STEP:
            newstates = self._executor.execute(state, state.pc)
        elif self._options.step == ExecutionOptions.BLOCK_STEP:
            newstates = self._executor.executeTillBranch(state)
        else:
            raise NotImplementedError("Invalid step: {0}".format(self._options.step))

        # self.states_num += len(newstates)
        # if self.states_num % 100 == 0:
        #    print("Searched states: {0}".format(self.states_num))
        self.handle_new_states(newstates)

    def run(self):
        self.prepare()

        # we're ready to go!
        do_step = self.do_step
        while self.states:
            do_step()

        self.report()

        return 0
