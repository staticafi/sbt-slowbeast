import sys
from itertools import chain

from slowbeast.domains.pointer import Pointer
from slowbeast.util.debugging import ldbgv
from slowbeast.ir.instruction import *
from slowbeast.domains.concrete import ConcreteInt
from .errors import GenericError
from .memorymodel import MemoryModel
from .executionstate import ExecutionState


def split_ready_states(states):
    ready, notready = [], []
    for x in states:
        (ready, notready)[0 if x.is_ready() else 1].append(x)
    return ready, notready


def split_nonready_states(states):
    errs, oth = [], []
    for x in states:
        (errs, oth)[0 if x.has_error() else 1].append(x)
    return errs or None, oth or None


class PathExecutionResult:
    __slots__ = ["ready", "errors", "early", "other"]

    def __init__(self, ready=None, errors=None, early=None, other=None):
        # states that can be further executed
        self.ready = ready
        # error states that were hit during the execution
        # of the last point on the path
        self.errors = errors
        # non-ready states that were hit during the execution
        # of the path up to the last point
        # (these include error, terminated and killed states)
        self.early = early
        # other states --  these can be only the
        # killed and terminated states hit during the execution
        # of the last point on the path
        self.other = other

    def errorsToEarly(self):
        errs = self.errors
        earl = self.early
        if earl and errs:
            earl += errs
        elif errs:
            self.early = errs
        self.errors = None

    def otherToEarly(self):
        oth = self.other
        earl = self.early
        if earl and oth:
            earl += oth
        elif oth:
            self.early = oth
        self.other = None

    def add(self, states):
        ready = self.ready or []
        errs = self.errors or []
        oth = self.other or []
        for s in states:
            if s.is_ready():
                ready.append(s)
            elif s.has_error():
                errs.append(s)
            else:
                oth.append(s)
        self.ready = ready
        self.errors = errs
        self.other = oth

    def merge(self, r):
        if r.ready:
            ready = self.ready or []
            ready += r.ready
            self.ready = ready
        if r.errors:
            errs = self.errors or []
            errs += r.errors
            self.errors = errs
        if r.early:
            erl = self.early or []
            erl += r.early
            self.early = erl
        if r.other:
            oth = self.other or []
            oth += r.other
            self.other = oth

    def killed(self):
        other = self.other
        early = self.early
        killed1 = (s for s in other if s.was_killed()) if other else ()
        killed2 = (s for s in early if s.was_killed()) if early else ()
        return chain(killed1, killed2)

    def check(self):
        assert not self.ready or all(map(lambda x: x.is_ready(), self.ready))
        assert not self.errors or all(map(lambda x: x.has_error(), self.errors))
        assert not self.early or all(map(lambda x: not x.is_ready(), self.early))
        assert not self.other or all(
            map(lambda x: x.is_terminated() or x.was_killed() or x.exited(), self.other)
        )
        return True

    def __repr__(self):
        haveany = False
        msg = "PathExecutionResult: {"
        if self.ready:
            haveany = True
            msg += f"\n  ready: {[x.get_id() for x in self.ready]}"
        if self.errors:
            haveany = True
            msg += f"\n  errors: {[x.get_id() for x in self.errors]}"
        if self.early:
            haveany = True
            msg += f"\n  early: {[x.get_id() for x in self.early]}"
        if self.other:
            haveany = True
            msg += f"\n  other: {[x.get_id() for x in self.other]}"
        if haveany:
            msg += "\n}"
        else:
            msg += "}"

        return msg


class Executor:
    """
    Class that takes care of executing single instructions.
    That is, the executor takes a state, executes one instruction
    and generates new states.
    """

    def __init__(self, program, opts, memorymodel=None):
        self.memorymodel = memorymodel or MemoryModel(opts)

        self._program = program
        self._opts = opts
        self._executed_instrs = 0
        self._executed_blks = 0

    # def setMemoryModel(self, mm):
    #    self.memorymodel = mm

    def get_memory_model(self):
        assert self.memorymodel is not None
        return self.memorymodel

    def create_state(self, pc=None, m=None):
        """
        Create a state that can be processed by this executor.
        """
        if m is None:
            m = self.memorymodel.create_memory()
        return ExecutionState(pc, m)

    def getExecInstrNum(self):
        return self._executed_instrs

    def getExecStepNum(self):
        return self._executed_blks

    def get_options(self):
        return self._opts

    def forbid_calls(self):
        self._opts.no_calls = True

    def calls_forbidden(self):
        return self._opts.no_calls

    def execStore(self, state, instr):
        assert isinstance(instr, Store)

        states = self.memorymodel.write(
            state, instr, instr.value_operand(), instr.pointer_operand()
        )

        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def execLoad(self, state, instr):
        assert isinstance(instr, Load)

        states = self.memorymodel.read(
            state, instr, instr.pointer_operand(), instr.bytewidth(), instr.bitwidth()
        )

        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def execAlloc(self, state, instr):
        states = self.memorymodel.allocate(state, instr)
        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def exec_cmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.operand(0))
        op2 = state.eval(instr.operand(1))
        if op1.is_pointer():
            if not op2.is_pointer():
                raise RuntimeError("Comparison of pointer to a constant")
            if op1.object.get_id() != op2.object.get_id():
                raise RuntimeError("Comparison of unrelated pointers")
            op1 = op1.offset
            op2 = op2.offset
        else:
            op1 = op1.value()
            op2 = op2.value()
        x = None
        p = instr.predicate()
        if p == Cmp.LE:
            x = op1 <= op2
        elif p == Cmp.LT:
            x = op1 < op2
        elif p == Cmp.GE:
            x = op1 >= op2
        elif p == Cmp.GT:
            x = op1 > op2
        elif p == Cmp.EQ:
            x = op1 == op2
        elif p == Cmp.NE:
            x = op1 != op2

        state.set(instr, ConcreteInt(x, 1))
        state.pc = state.pc.get_next_inst()

        return [state]

    def execPrint(self, state, instr):
        assert isinstance(instr, Print)
        for x in instr.operands():
            v = state.eval(x)
            if v.is_concrete():
                v = v.value()
            sys.stdout.write(str(v))
        sys.stdout.write("\n")
        sys.stdout.flush()

        state.pc = state.pc.get_next_inst()

        return [state]

    def exec_branch(self, state, instr):
        assert isinstance(instr, Branch)
        c = instr.condition()
        assert isinstance(c, ValueInstruction) or c.is_concrete()
        cv = state.eval(instr.condition()).value()

        if cv:
            succ = instr.true_successor()
        elif cv == False:
            succ = instr.false_successor()
        else:
            raise RuntimeError("Indeterminite condition")

        assert succ
        if not succ.empty():
            state.pc = succ.instruction(0)
        else:
            state.pc = None

        return [state]

    def exec_assert(self, state, instr):
        assert isinstance(instr, Assert)
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_concrete()
            if v.value() != True:
                state.set_error(
                    AssertFailError(
                        "Assertion failed: {0} is {1} (!= True)".format(o, v)
                    )
                )
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assume(self, state, instr):
        assert isinstance(instr, Assume)
        state.pc = state.pc.get_next_inst()
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_concrete()
            assert v.is_bool()
            if v.value() != True:
                print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                state.dump()
                break

        return [state]

    def exec_unary_op(self, state, instr):
        raise NotImplementedError("Concrete executor does not implement unary op yet")

    def exec_binary_op(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1c = state.eval(instr.operand(0))
        op2c = state.eval(instr.operand(1))
        op1 = None
        op2 = None
        bw = max(op1c.bytewidth(), op2c.bytewidth())
        # if one of the operands is a pointer,
        # lift the other to pointer too
        if op1c.is_pointer():
            if not op2c.is_pointer():
                assert op2c.is_concrete()
                # adding a constant -- create a pointer
                # to the object with the right offset
                op2c = Pointer(op1c.object, op2c.value())
        elif op2c.is_pointer():
            if not op1c.is_pointer():
                assert op1c.is_concrete()
                # adding a constant -- create a pointer
                # to the object with the right offset
                op1c = Pointer(op2c.object, op1c.value())
        else:
            op1 = op1c.value()
            op2 = op2c.value()

        if op1c.is_pointer() and op1c.object != op2c.object:
            raise RuntimeError("Pointer arithmetic on unrelated pointers")

        r = None
        if instr.operation() == BinaryOperation.ADD:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset + op2c.offset)
            else:
                r = ConcreteInt(op1 + op2, bw)
        elif instr.operation() == BinaryOperation.SUB:
            if isinstance(op1c, Pointer):
                assert isinstance(op2c, Pointer)
                r = Pointer(op1c.object, op1c.offset - op2c.offset)
            else:
                r = ConcreteInt(op1 - op2, bw)
        elif instr.operation() == BinaryOperation.MUL:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset * op2c.offset)
            else:
                r = ConcreteInt(op1 * op2, bw)
        elif instr.operation() == BinaryOperation.DIV:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset / op2c.offset)
            else:
                r = ConcreteInt(op1 / op2, bw)
        else:
            raise NotImplementedError("Binary operation: " + str(instr))

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_ite(self, state, instr):
        raise NotImplementedError("Ite not implemented in core")

    def exec_call(self, state, instr):
        assert isinstance(instr, Call)

        if self.calls_forbidden():
            state.set_killed("Calls are forbidden")
            return [state]

        fun = instr.called_function()
        ldbgv("-- CALL {0} --", (fun.name()))
        if fun.is_undefined():
            state.set_error(
                GenericError("Called undefined function: {0}".format(fun.name()))
            )
            return [state]
        # map values to arguments
        assert len(instr.operands()) == len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        state.push_call(instr, fun, mapping)
        return [state]

    def exec_ret(self, state, instr):
        assert isinstance(instr, Return)

        # obtain the return value (if any)
        ret = None
        if len(instr.operands()) != 0:  # returns something
            ret = state.eval(instr.operand(0))
            assert (
                ret is not None
            ), f"No return value even though there should be: {instr}"

        # pop the call frame and get the return site
        rs = state.pop_call()
        if rs is None:  # popped the last frame
            if ret is not None and ret.is_pointer():
                state.set_error(GenericError("Returning a pointer from main function"))
                return [state]
            # elif not ret.is_concrete():
            #    state.add_warning(
            #        "Returning a non-constant value from the main function"
            #    )

            state.set_exited(ret)
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.get_next_inst()
        return [state]

    def execute(self, state, instr):
        """
        Execute the next instruction in the state and modify the state accordingly.
        """
        # debug print
        ldbgv(
            "({2}) {0}: {1}",
            (
                "--" if not instr.bblock() else instr.fun().name(),
                instr,
                state.get_id(),
            ),
            verbose_lvl=3,
        )

        self._executed_instrs += 1

        # TODO: add an opcode to instruction and check only the opcode
        states = None
        if isinstance(instr, Store):
            states = self.execStore(state, instr)
        elif isinstance(instr, Load):
            states = self.execLoad(state, instr)
        elif isinstance(instr, Alloc):
            states = self.execAlloc(state, instr)
        elif isinstance(instr, Cmp):
            states = self.exec_cmp(state, instr)
        elif isinstance(instr, Print):
            states = self.execPrint(state, instr)
        elif isinstance(instr, Branch):
            states = self.exec_branch(state, instr)
        elif isinstance(instr, Assert):
            states = self.exec_assert(state, instr)
        elif isinstance(instr, Assume):
            states = self.exec_assume(state, instr)
        elif isinstance(instr, UnaryOperation):
            states = self.exec_unary_op(state, instr)
        elif isinstance(instr, BinaryOperation):
            states = self.exec_binary_op(state, instr)
        elif isinstance(instr, Ite):
            states = self.exec_ite(state, instr)
        elif isinstance(instr, (Thread, ThreadExit, ThreadJoin)):
            # XXX: must be before Call and Return
            state.set_killed(f"Threads are not implemented by this executor: {instr}")
            return [state]
        elif isinstance(instr, Call):
            states = self.exec_call(state, instr)
        elif isinstance(instr, Return):
            states = self.exec_ret(state, instr)
        else:
            state.set_killed("Not implemented instruction: {0}".format(instr))
            return [state]

        return states

    def execute_seq(self, state, instrs):
        """
        Execute instructions 'instrs' from state(s) 'state'. The instructions
        must not contain Branch instruction. \return two list, the first
        contains READY states and the other contains not READY states.
        """
        nonreadystates = []
        if isinstance(state, list):
            readystates = state
        else:
            readystates = [state]

        execute = self.execute
        nonreadystatesappend = nonreadystates.append
        for i in instrs:
            assert not isinstance(i, Branch), "Branch instruction in execute_seq"

            newst = []
            newstappend = newst.append
            for s in readystates:
                s.pc = i
                nxt = execute(s, i)
                for n in nxt:
                    if n.is_ready():
                        newstappend(n)
                    else:
                        nonreadystatesappend(n)

            readystates = newst
            if not readystates:
                break

        return readystates, nonreadystates

    def executeTillBranch(self, state, stopBefore=False):
        """
        Start executing from 'state' and stop execution after executing a
        branch instruction.  This will typically execute exactly one basic block
        of the code.
        If 'stopBefore' is True, stop the execution before executing the
        branch instruction.
        """
        self._executed_blks += 1

        finalstates = []
        if isinstance(state, list):
            readystates = state
        else:
            readystates = [state]

        execute = self.execute
        finalstatesappend = finalstates.append
        while readystates:
            newst = []
            newstappend = newst.append
            for s in readystates:
                pc = s.pc
                # remember that it is a branch now,
                # because execute() will change pc
                isbranch = isinstance(pc, Branch)
                if stopBefore and isbranch:
                    finalstatesappend(s)
                    continue

                nxt = execute(s, pc)
                if isbranch:
                    # we stop here
                    finalstates += nxt
                else:
                    for n in nxt:
                        if n.is_ready():
                            newstappend(n)
                        else:
                            finalstatesappend(n)

            readystates = newst

        assert not readystates
        return finalstates

    def execute_path(self, state, path):
        """
        Execute the given path through CFG. Return two lists of states.
        The first list contains the resulting states that reaches the
        end of the path, the other list contains all other states, i.e.,
        the error, killed or exited states reached during the execution of the CFG.
        """

        if isinstance(state, list):
            states = state
        else:
            states = [state]

        earlytermstates = []
        idx = 0

        locs = path.locations()
        # set the pc of the states to be the first instruction of the path
        for s in states:
            assert s.is_ready()
            s.pc = locs[0].bblock().first()

        for idx in range(0, len(locs)):
            # execute the block till branch
            newstates = self.executeTillBranch(states, stopBefore=True)

            # get the ready states
            states = []
            for n in newstates:
                (states, earlytermstates)[0 if n.is_ready() else 1].append(n)

            # now execute the branch following the edge on the path
            if idx + 1 < len(locs):
                curbb = locs[idx].bblock()
                succbb = locs[idx + 1].bblock()
                followsucc = curbb.last().true_successor() == succbb
                newstates = []
                assert followsucc or curbb.last().false_successor() == succbb
                for s in states:
                    assert s.is_ready()
                    newstates += self.exec_branch_to(s, s.pc, followsucc)
            else:  # this is the last location on path,
                # so just normally execute the block instructions
                newstates = self.executeTillBranch(states)
            states = newstates

        assert all(map(lambda x: not x.is_ready(), earlytermstates))

        return states, earlytermstates
