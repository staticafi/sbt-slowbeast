from slowbeast.ir.instruction import *
from slowbeast.ir.function import Function
from slowbeast.ir.types import get_offset_type
from slowbeast.domains.value import Value
from slowbeast.domains.constants import ConcreteBool
from slowbeast.domains.concrete import ConcreteVal, dom_is_concrete
from slowbeast.domains.pointer import Pointer
from slowbeast.core.executor import Executor as ConcreteExecutor
from slowbeast.solvers.expressions import is_symbolic
from slowbeast.util.debugging import dbgv, ldbgv
from slowbeast.core.errors import AssertFailError, GenericError

from .memorymodel import SymbolicMemoryModel
from .executionstate import SEState, IncrementalSEState, ThreadedSEState
from .statesset import StatesSet

from random import getrandbits

unsupported_funs = [
    "memmove",
    "memcpy",
    "llvm.memmove.p0i8.p0i8.i32",
    "llvm.memmove.p0i8.p0i8.i64",
    "llvm.memcpy.p0i8.p0i8.i32",
    "llvm.memcpy.p0i8.p0i8.i64",
]


class SEStats:
    def __init__(self):
        # number of branch instructions
        self.branchings = 0
        # number of branch instructions where we forked
        self.branch_forks = 0
        # number of times we called fork()
        self.fork_calls = 0
        # number of times when the call to fork() forked the execution
        self.forks = 0


def add_pointer_with_constant(E, op1, op2):
    return Pointer(op1.object(), E.Add(op1.offset(), op2))


def condition_to_bool(cond, EM):
    if cond.type().is_bool():
        return cond

    if cond.is_concrete():
        cval = EM.Ne(cond, ConcreteVal(0, cond.type()))
    else:
        assert is_symbolic(cond)
        assert not cond.type().is_bool()
        assert cond.type().bitwidth() == 1, f"Invalid condition in branching: {cond}"
        cval = EM.Ne(cond, ConcreteVal(0, cond.type()))

    assert cval.is_bool()
    return cval


def eval_condition(state, cond):
    assert isinstance(cond, ValueInstruction) or cond.is_concrete()
    c = state.eval(cond)
    assert isinstance(c, Value)
    # solvers make difference between bitvectors and booleans, so we must
    # take care of it here: if it is a bitvector, compare it to 0 (C
    # semantics)
    return condition_to_bool(c, state.expr_manager())


class Executor(ConcreteExecutor):
    def __init__(self, program, solver, opts, memorymodel=None):
        if memorymodel is None:
            memorymodel = SymbolicMemoryModel(opts)
        super().__init__(program, opts, memorymodel)
        self.solver = solver
        self.stats = SEStats()
        # use these values in place of nondet values
        self._input_vector = None

    def is_error_fn(self, fun):
        if isinstance(fun, str):
            return fun in self.get_options().error_funs
        return fun.name() in self.get_options().error_funs

    def error_funs(self):
        return self._error_funs

    def set_input_vector(self, ivec):
        self._input_vector = ivec.copy()
        # reverse the vector so that we can pop from it
        self._input_vector.reverse()

    def create_state(self, pc=None, m=None):
        if m is None:
            m = self.get_memory_model().create_memory()
        if self.get_options().incremental_solving:
            s = IncrementalSEState(self, pc, m)
        else:
            # FIXME: we do not use the solver...
            s = SEState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s

    def create_clean_state(self, pc=None, m=None):
        s = self.create_state(pc, m)
        s.push_call(None)
        return s

    def create_states_set(self, S=None):
        ss = StatesSet(self.create_clean_state())
        if S:
            # set the set to be S
            ss.intersect(S)
        return ss

    def fork(self, state, cond):
        self.stats.fork_calls += 1

        T, F = None, None

        # fast path + do not add True/False to constraints
        if cond.is_concrete():
            assert cond.is_bool(), "Invalid constant"
            if cond.value():
                return state, None
            elif not cond.value():
                return None, state
            else:
                raise RuntimeError("Invalid condition: {0}".format(cond.value()))

        # check SAT of cond and its negation
        csat = state.is_sat(cond)
        if csat is None:
            T = state.copy()
            T.set_killed("Solver failure: {0}".format(csat))

        ncond = state.expr_manager().Not(cond)
        ncsat = state.is_sat(ncond)
        if ncsat is None:
            F = state.copy()
            F.set_killed("Solver failure: {0}".format(ncsat))

        # is one of the conditions implied?
        # in that case we do not need to add any constraint
        if csat is True and ncsat is False:
            return state, None
        elif ncsat is True and csat is False:
            return None, state
        else:
            if csat is True:
                T = state.copy()
                T.add_constraint(cond)

            if ncsat is True:
                F = state.copy()
                F.add_constraint(ncond)

            if T and F:
                self.stats.forks += 1

        return T, F

    # FIXME: make this a method of State?
    def assume(self, state, cond):
        """Put an assumption _into_ the given state.
        Return the state or None if that situation cannot happen
        (the assumption is inconsistent with the state).
        """
        if cond.is_concrete():
            assert cond.is_bool(), "Invalid constant"
            if cond.value():
                return state
            else:
                return None

        r = state.is_sat(cond)
        if r is None:
            return None
        elif r:
            state.add_constraint(cond)
            return state
        return None

    def exec_branch_to(self, state, instr, to):
        """
        Execute a branch instruction and follow the given successor
        (True or False successor).
        """
        assert isinstance(instr, Branch)
        assert isinstance(to, bool)
        ldbgv("branching to {0} succ of {1}", (to, instr))
        self.stats.branchings += 1

        cond = instr.condition()
        cval = eval_condition(state, cond)

        succ = None
        if to is True:
            s = self.assume(state, cval)
            succ = instr.true_successor()
        elif to is False:
            s = self.assume(state, state.expr_manager().Not(cval))
            succ = instr.false_successor()
        else:
            raise RuntimeError("Invalid branch successor: {0}".format(to))

        if s is None:
            dbgv("branching is not feasible!")
            return []
        else:
            assert succ
            s.pc = succ.instruction(0)

        return [s]

    def exec_branch(self, state, instr):
        assert isinstance(instr, Branch)
        self.stats.branchings += 1

        cond = instr.condition()
        cval = eval_condition(state, cond)

        trueBranch, falseBranch = self.fork(state, cval)
        # at least one must be feasable...
        assert trueBranch or falseBranch, "Fatal Error: failed forking condition"

        states = []
        if trueBranch:
            trueBranch.pc = instr.true_successor().instruction(0)
            states.append(trueBranch)
        if falseBranch:
            falseBranch.pc = instr.false_successor().instruction(0)
            states.append(falseBranch)

        if trueBranch and falseBranch:
            self.stats.branch_forks += 1

        return states

    def compare_values(self, E, p, op1, op2, unsgn, flt=False):
        if p == Cmp.LE:
            return E.Le(op1, op2, unsgn, flt)
        elif p == Cmp.LT:
            return E.Lt(op1, op2, unsgn, flt)
        elif p == Cmp.GE:
            return E.Ge(op1, op2, unsgn, flt)
        elif p == Cmp.GT:
            return E.Gt(op1, op2, unsgn, flt)
        elif p == Cmp.EQ:
            return E.Eq(op1, op2, unsgn, flt)
        elif p == Cmp.NE:
            return E.Ne(op1, op2, unsgn, flt)
        else:
            raise RuntimeError("Invalid comparison")

    def compare_pointers(self, state, instr, p1, p2):
        mo1id = p1.object()
        mo2id = p2.object()
        if is_symbolic(mo1id) or is_symbolic(mo2id):
            state.set_killed(
                "Comparison of symbolic pointers unimplemented: {0}".format(instr)
            )
            return [state]

        E = state.expr_manager()
        p = instr.predicate()
        if mo1id == mo2id:
            state.set(
                instr,
                self.compare_values(
                    E, p, p1.offset(), p2.offset(), instr.is_unsigned()
                ),
            )
            state.pc = state.pc.get_next_inst()
            return [state]
        else:
            if p != Cmp.EQ and p != Cmp.NE:
                state.set_killed(
                    "Comparison of pointers implemented only for "
                    "(non-)equality or into the same object"
                )
            else:
                state.set(instr, ConcreteBool(p == Cmp.NE))
                state.pc = state.pc.get_next_inst()
            return [state]

        state.set_killed("Invalid pointer comparison")
        return [state]

    def compare_ptr_and_nonptr(self, em, pred, op1, op2):
        if pred not in (Cmp.EQ, Cmp.NE):
            return None  # we cannot handle that yet
        if dom_is_concrete(op1):
            op1, op2 = op2, op1
        assert op1.is_pointer()
        assert dom_is_concrete(op2)
        if op2.is_zero():
            obj, off = op1.object(), op1.offset()
            expr = em.And(
                em.Eq(obj, em.ConcreteVal(0, obj.bitwidth())),
                em.Eq(off, em.ConcreteVal(0, off.bitwidth())),
            )
            return expr if pred == Cmp.EQ else em.Not(expr)
        return None

    def exec_cmp(self, state, instr):
        assert isinstance(instr, Cmp)
        seval = state.eval
        getop = instr.operand
        op1 = seval(getop(0))
        op2 = seval(getop(1))

        op1isptr = op1.is_pointer()
        op2isptr = op2.is_pointer()
        if op1isptr or op2isptr:
            if op1isptr and op2isptr:
                return self.compare_pointers(state, instr, op1, op2)
            else:
                # we handle only comparison of symbolic constant (pointer) to null
                E = state.expr_manager()
                if op1isptr and op1.is_null():
                    state.set(
                        instr,
                        self.compare_values(
                            E,
                            instr.predicate(),
                            E.ConcreteVal(0, op1.bitwidth()),
                            op2,
                            instr.is_unsigned(),
                        ),
                    )
                elif op2isptr and op2.is_null():
                    state.set(
                        instr,
                        self.compare_values(
                            E,
                            instr.predicate(),
                            op1,
                            E.ConcreteVal(0, op1.bitwidth()),
                            instr.is_unsigned(),
                        ),
                    )
                else:
                    expr = self.compare_ptr_and_nonptr(E, instr.predicate(), op1, op2)
                    if expr is None:
                        state.set_killed(
                            f"Comparison of pointer to this constant not implemented: {op1} cmp {op2}"
                        )
                        return [state]
                    state.set(instr, expr)
                state.pc = state.pc.get_next_inst()
                return [state]

        x = self.compare_values(
            state.expr_manager(),
            instr.predicate(),
            op1,
            op2,
            instr.is_unsigned(),
            instr.is_float(),
        )
        state.set(instr, x)
        state.pc = state.pc.get_next_inst()

        return [state]

    def _resolve_function_pointer(self, state, funptr):
        ptr = state.try_eval(funptr)
        if ptr is None:
            return None
        # FIXME: should we use a pointer instead of funs id?
        if not isinstance(ptr, ConcreteVal):
            return None

        for f in self._program:
            if f.get_id() == ptr.value():
                return f
        return None

    def exec_call(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.called_function()
        if not isinstance(fun, Function):
            fun = self._resolve_function_pointer(state, fun)
            if fun is None:
                state.set_killed(
                    f"Failed resolving function pointer: {instr.called_function()}"
                )
                return [state]
            assert isinstance(fun, Function)

        if self.is_error_fn(fun):
            state.set_error(AssertFailError(f"Called '{fun.name()}'"))
            return [state]

        if fun.is_undefined():
            name = fun.name()
            if name == "abort":
                state.set_terminated("Aborted via an abort() call")
                return [state]
            if name in ("exit", "_exit"):
                state.set_exited(state.eval(instr.operand(0)))
                return [state]
            if name in unsupported_funs:
                state.set_killed(f"Called unsupported function: {name}")
                return [state]
            # NOTE: this may be overridden by child classes
            return self.exec_undef_fun(state, instr, fun)

        if self.calls_forbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.set_killed(
                "calling '{0}', but calls are forbidden".format(fun.name())
            )
            return [state]

        return self.call_fun(state, instr, fun)

    def call_fun(self, state, instr, fun):
        # map values to arguments
        assert len(instr.operands()) == len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        state.push_call(instr, fun, mapping)
        return [state]

    def exec_undef_fun(self, state, instr, fun):
        retTy = fun.return_type()
        if retTy:
            if self.get_options().concretize_nondets:
                val = ConcreteVal(getrandbits(32), retTy)
            elif self._input_vector:
                val = self._input_vector.pop()
                ldbgv(f"Using value from input vector: {0}", (val,))
                assert val.type() == retTy, f"{val.type()} != {retTy}"
                # if assertions are turned off, just return nondet-value
                if val.type() != retTy:
                    dbg(
                        f"Input value type does not match ({val.type()} != {retTy}). "
                        "Using nondet value"
                    )
                    val = state.solver().fresh_value(fun.name(), retTy)
            else:
                val = state.solver().fresh_value(fun.name(), retTy)
                state.create_nondet(instr, val)
            state.set(instr, val)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_binary_op(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        seval = state.eval
        getop = instr.operand
        op1 = seval(getop(0))
        op2 = seval(getop(1))
        states = []
        # if one of the operands is a pointer,
        # lift the other to pointer too
        r = None
        E = state.expr_manager()
        op1ptr = op1.is_pointer()
        op2ptr = op2.is_pointer()
        if op1ptr:
            if not op2ptr:
                r = add_pointer_with_constant(E, op1, op2)
            else:
                state.set_killed(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr)
                )
                return [state]
        elif op2ptr:
            if not op1ptr:
                r = add_pointer_with_constant(E, op2, op1)
            else:
                state.set_killed(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr)
                )
                return [state]
        else:
            opcode = instr.operation()
            if opcode == BinaryOperation.ADD:
                r = E.Add(op1, op2, instr.is_fp())
            elif opcode == BinaryOperation.SUB:
                r = E.Sub(op1, op2, instr.is_fp())
            elif opcode == BinaryOperation.MUL:
                r = E.Mul(op1, op2, instr.is_fp())
            elif opcode == BinaryOperation.DIV:
                if instr.is_fp():
                    # compilers allow division by FP 0
                    r = E.Div(op1, op2, instr.is_unsigned(), isfloat=True)
                else:
                    good, bad = self.fork(state, E.Ne(op2, ConcreteVal(0, op2.type())))
                    if good:
                        state = good
                        assert not instr.is_fp()
                        r = E.Div(op1, op2, instr.is_unsigned())
                    if bad:
                        bad.set_killed("Division by 0")
                        states.append(bad)
                        if good is None:
                            return states
            elif opcode == BinaryOperation.SHL:
                r = E.Shl(op1, op2)
            elif opcode == BinaryOperation.LSHR:
                r = E.LShr(op1, op2)
            elif opcode == BinaryOperation.ASHR:
                r = E.AShr(op1, op2)
            elif opcode == BinaryOperation.REM:
                r = E.Rem(op1, op2, instr.is_unsigned())
            elif opcode == BinaryOperation.AND:
                r = E.And(op1, op2)
            elif opcode == BinaryOperation.OR:
                r = E.Or(op1, op2)
            elif opcode == BinaryOperation.XOR:
                r = E.Xor(op1, op2)
            else:
                state.set_killed("Not implemented binary operation: {0}".format(instr))
                return [state]

        assert r, "Bug in creating a binary op expression"

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        states.append(state)
        return states

    def exec_ite(self, state, instr):
        cond = condition_to_bool(state.eval(instr.condition()), state.expr_manager())
        if cond.is_concrete():
            cval = cond.value()
            if cval is True:
                state.set(instr, state.eval(instr.operand(0)))
            elif cval is False:
                state.set(instr, state.eval(instr.operand(0)))
            else:
                raise RuntimeError(f"Invalid value of boolean condition: {cval}")
        else:
            op1 = state.eval(instr.operand(0))
            op2 = state.eval(instr.operand(1))
            expr = state.expr_manager().Ite(cond, op1, op2)
            state.set(instr, expr)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_unary_op(self, state, instr: UnaryOperation):
        assert isinstance(instr, UnaryOperation)
        op1 = state.eval(instr.operand(0))
        opcode = instr.operation()
        E = state.expr_manager()
        if opcode == UnaryOperation.ZEXT:
            bw = instr.bitwidth()
            r = E.ZExt(op1, bw)
        elif opcode == UnaryOperation.SEXT:
            bw = instr.bitwidth()
            r = E.SExt(op1, bw)
        elif opcode == UnaryOperation.CAST:
            r = E.Cast(op1, instr.casttype())
            if r is None:
                state.set_killed("Unsupported/invalid cast: {0}".format(instr))
                return [state]
        elif opcode == UnaryOperation.EXTRACT:
            start, end = instr.range()
            r = E.Extract(op1, start, end)
        elif opcode == UnaryOperation.NEG:
            r = E.Neg(op1, instr.is_fp())
        elif opcode == UnaryOperation.ABS:
            r = E.Abs(op1)
        elif opcode == UnaryOperation.FP_OP:
            r = E.FpOp(instr.fp_operation(), op1)
            if r is None:
                state.set_killed(f"Unsupported FP operation: {instr}")
                return [state]
        else:
            state.set_killed("Unary instruction not implemented: {0}".format(instr))
            return [state]

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assume_expr(self, state, v):
        v = condition_to_bool(v, state.expr_manager())
        assert v.is_bool(), v
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            isunsat = not v.value()
        else:
            tmp = self.assume(state, v)
            isunsat = tmp is None

        if isunsat:
            state.set_terminated(f"Assumption unsat: {v} (!= True)")

        return [state]

    def exec_assume(self, state, instr):
        assert isinstance(instr, Assume)
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_bool()
            if v.is_concrete():
                assert isinstance(v.value(), bool)
                isunsat = not v.value()
            else:
                tmp = self.assume(state, v)
                isunsat = tmp is None

            if isunsat:
                state.set_terminated(
                    "Assumption unsat: {0} == {1} (!= True)".format(o, v)
                )
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assert_expr(self, state, v, msg=""):
        states = []
        assert v.is_bool()
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            if not v.value():
                state.set_error(AssertFailError(msg))
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                states.append(okBranch)
            if errBranch:
                errBranch.set_error(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def exec_assert(self, state, instr):
        assert isinstance(instr, Assert)
        o = instr.condition()
        msg = instr.msg()
        if not msg:
            msg = str(o)
        v = state.eval(o)
        states = []
        assert v.is_bool()
        if v.is_concrete():
            if v.value() != True:
                state.set_error(AssertFailError(msg))
            else:
                state.pc = state.pc.get_next_inst()
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                okBranch.pc = okBranch.pc.get_next_inst()
                states.append(okBranch)
            if errBranch:
                errBranch.set_error(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def concretize(self, state, val):
        if val.is_concrete():
            return val

        return state.solver().concretize(val, *state.constraints())


class ThreadedExecutor(Executor):
    def __init__(self, program, solver, opts, memorymodel=None):
        super().__init__(program, solver, opts, memorymodel)

    def create_state(self, pc=None, m=None):
        if m is None:
            m = self.get_memory_model().create_memory()
        # if self.get_options().incremental_solving:
        #    return IncrementalSEState(self, pc, m)
        return ThreadedSEState(self, pc, m, self.solver)

    def exec_undef_fun(self, state, instr, fun):
        fnname = fun.name()
        if fnname == "__VERIFIER_atomic_begin":
            state.start_atomic()
            state.pc = state.pc.get_next_inst()
            return [state]
        elif fnname == "__VERIFIER_atomic_end":
            state.end_atomic()
            state.pc = state.pc.get_next_inst()
            return [state]
        if fnname == "pthread_mutex_init":
            state.mutex_init(state.eval(instr.operand(0)))
            # return non-det value for the init
            # TODO: we should connect the returned value with the
            # effect of init...
            return super().exec_undef_fun(state, instr, fun)
        if fnname == "pthread_mutex_destroy":
            state.mutex_destroy(state.eval(instr.operand(0)))
            # the same as for init...
            return super().exec_undef_fun(state, instr, fun)
        if fnname == "pthread_mutex_lock":
            mtx = state.eval(instr.operand(0))
            # TODO: This does not work with mutexes initialized via assignment...
            # if not state.has_mutex(mtx):
            #    state.set_killed("Locking unknown mutex")
            #    return [state]
            lckd = state.mutex_locked_by(mtx)
            if lckd is not None:
                if lckd == state.thread().get_id():
                    state.set_killed("Double lock")
                else:
                    state.mutex_wait(mtx)
            else:
                state.mutex_lock(mtx)
                state.pc = state.pc.get_next_inst()
            return [state]
        if fnname == "pthread_mutex_unlock":
            mtx = state.eval(instr.operand(0))
            if not state.has_mutex(mtx):
                state.set_killed("Unlocking unknown mutex")
                return [state]
            lckd = state.mutex_locked_by(mtx)
            if lckd is None:
                state.set_killed("Unlocking unlocked lock")
            else:
                if lckd != state.thread().get_id():
                    state.set_killed("Unlocking un-owned mutex")
                else:
                    state.mutex_unlock(mtx)
                    state.pc = state.pc.get_next_inst()
            return [state]
        if fnname.startswith("pthread_"):
            state.set_killed(f"Unsupported pthread_* API: {fnname}")
            return [state]
        return super().exec_undef_fun(state, instr, fun)

    def call_fun(self, state, instr, fun):
        if fun.name().startswith("__VERIFIER_atomic_"):
            state.start_atomic()
        return super().call_fun(state, instr, fun)

    def exec_thread(self, state, instr):
        fun = instr.called_function()
        ldbgv("-- THREAD {0} --", (fun.name(),))
        if fun.is_undefined():
            state.set_error(
                GenericError(
                    "Spawning thread with undefined function: {0}".format(fun.name())
                )
            )
            return [state]
        # map values to arguments
        # TODO: do we want to allow this? Less actual parameters than formal parameters?
        # assert len(instr.operands()) == len(fun.arguments())
        if len(instr.operands()) > len(fun.arguments()):
            dbgv(
                "Thread created with less actual arguments than with formal arguments..."
            )
        assert len(instr.operands()) >= len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        t = state.add_thread(fun.bblock(0).instruction(0))
        t.cs.push_call(None, fun, mapping or {})

        # we executed the thread inst, so move
        state.pc = state.pc.get_next_inst()
        state.set(instr, ConcreteVal(t.get_id(), get_offset_type()))
        return [state]

    def exec_thread_exit(self, state, instr):
        assert isinstance(instr, ThreadExit)

        # obtain the return value (if any)
        ret = None
        if len(instr.operands()) != 0:  # returns something
            ret = state.eval(instr.operand(0))
            assert (
                ret is not None
            ), f"No return value even though there should be: {instr}"

        state.exit_thread(ret)
        return [state]

    def exec_thread_join(self, state, instr):
        assert isinstance(instr, ThreadJoin)
        assert len(instr.operands()) == 1
        tid = state.eval(instr.operand(0))
        if not tid.is_concrete():
            state.set_killed("Symbolic thread values are unsupported yet")
        else:
            state.join_threads(tid.value())
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

        if state.frame().function.name().startswith("__VERIFIER_atomic_"):
            state.end_atomic()
        # pop the call frame and get the return site
        rs = state.pop_call()
        if rs is None:  # popped the last frame
            # if ret is not None and ret.is_pointer():
            #    state.set_error(GenericError("Returning a pointer from main function"))
            #    return [state]

            # if state.thread().get_id() == 0:
            #    # this is the main thread exiting, exit the whole program
            #    # FIXME: we should call dtors and so on...
            #    state.set_exited(0)
            # else:
            #    # this is the same as calling pthread_exit
            #    # FIXME: set the retval to 'ret'
            #    state.exit_thread()
            state.exit_thread(ret)
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.get_next_inst()
        return [state]

    def execute(self, state, instr):
        # state._trace.append(
        #    "({2}) {0}: {1}".format(
        #        "--" if not instr.bblock() else instr.fun().name(),
        #        instr,
        #        state.thread().get_id(),
        #    ),
        # )

        if isinstance(instr, Thread):
            return self.exec_thread(state, instr)
        elif isinstance(instr, ThreadExit):
            return self.exec_thread_exit(state, instr)
        elif isinstance(instr, ThreadJoin):
            return self.exec_thread_join(state, instr)
        return super().execute(state, instr)
