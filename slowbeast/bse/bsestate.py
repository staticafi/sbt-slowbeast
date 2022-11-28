from sys import stdout

from slowbeast.bse.memorymodel import _nondet_value
from slowbeast.domains.concrete import ConcreteInt
from slowbeast.domains.pointer import Pointer
from slowbeast.symexe.annotations import ExprAnnotation, execute_annotation
from slowbeast.symexe.executionstate import LazySEState, Nondet
from slowbeast.util.debugging import ldbgv, print_stdout
from slowbeast.solvers.solver import solve_incrementally


def _subst_val(substitute, val, subs):
    assert isinstance(subs, tuple), subs
    assert len(subs) == 2, subs
    if subs[0].is_pointer():
        assert subs[1].is_pointer(), subs
        subs = (
            (subs[0].object(), subs[1].object()),
            (subs[0].offset(), subs[1].offset()),
        )
    else:
        assert not subs[1].is_pointer(), subs
        subs = (subs,)
    if val.is_pointer():
        return Pointer(substitute(val.object(), *subs), substitute(val.offset(), *subs))
    return substitute(val, *subs)


def _iter_read_pairs(reads):
    for idx1, r1 in enumerate(reads):
        ptr1, val1 = r1
        for idx2 in range(idx1 + 1, len(reads)):
            ptr2, val2 = reads[idx2]
            yield (ptr1, val1), (ptr2, val2)


def _same_ptrs(em, ptr1, ptr2):
    Eq, And = em.Eq, em.And
    # pointers are equal?
    return em.simplify(
        And(
            Eq(ptr1.object(), ptr2.object()),
            Eq(ptr1.offset(), ptr2.offset()),
        )
    )


def _same_values(em, val1, val2):
    """Create an expression that says: if the pointers are the same, the values must be the same"""
    Eq, And, Or, Not = em.Eq, em.And, em.Or, em.Not

    val1ptr, val2ptr = val1.is_pointer(), val2.is_pointer()

    if val1ptr and val2ptr:
        return And(
            Eq(val1.object(), val2.object()),
            Eq(val1.offset(), val2.offset()),
        )
    elif val1ptr and not val2ptr:
        if val2.is_concrete() and val2.value() == 0:  # comparison to null
            return And(Eq(val1.object(), val2), Eq(val1.offset(), val2))
        else:
            raise NotImplementedError("Comparison of symbolic addreses not implemented")
    elif val2ptr and not val1ptr:
        if val1.is_concrete() and val1.value() == 0:  # comparison to null
            return And(Eq(val2.object(), val1), Eq(val2.offset(), val1))
        else:
            raise NotImplementedError("Comparison of symbolic addreses not implemented")
    else:  # non is are pointer
        return Eq(val1, val2)

    raise NotImplementedError(f"Cannot compare values {val1} {val2}")


class BSEState(LazySEState):
    def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)
        # inputs are the subset of nondet values that we search for in pre-states
        # when joining states
        self._inputs = []

    def _copy_to(self, new):
        super()._copy_to(new)
        new._inputs = self._inputs.copy()

    def add_input(self, nd):
        self._inputs.append(nd)

    def inputs(self):
        return self._inputs

    def input(self, x):
        for nd in self._inputs:
            if nd.instruction == x:
                return nd
        return None

    def eval(self, v):
        value = self.try_eval(v)
        if value is None:
            value = _nondet_value(self.solver().fresh_value, v, v.type().bitwidth())
            ldbgv(
                "Created new input value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.create_nondet(v, value)
            self.add_input(Nondet(v, value))
        assert value
        return value

    def _init_memory_constraints(self, initstate):
        """
        Add constraints from matching input reads of zeroed globals.
        """
        M, em = self.memory, self.expr_manager()
        IM = initstate.memory
        R, get_obj = M._input_reads, IM.get_obj
        constraints = []
        # FIXME: we target globals, but we could in fact just try reading from initstate
        # to get, e.g., values of bytes from objects.
        # However, the problem is that symbolic offsets are not supported, so...
        for ptr, val in R.items():
            obj = ptr.object()
            # this can happen if we execute a path that does not contain all information
            # to match all inputs. It is not a bug.
            # assert obj.is_concrete(), f"Initial state has symbolic object:\n{self}"
            if obj.is_concrete():
                mo = get_obj(obj)
                if mo is None:
                    continue
                # we found zeroed global from which we read
                if mo.is_global() and mo.is_zeroed():
                    constraints.append(em.Eq(val[0], ConcreteInt(0, val[0].bitwidth())))
            else:
                for g, ptr in (
                    (g, ptr) for (g, ptr) in IM.bound_globals() if g.is_zeroed()
                ):
                    constraints.append(
                        em.Or(
                            em.Ne(obj, ptr.object()),
                            em.Eq(val[0], ConcreteInt(0, val[0].bitwidth())),
                        )
                    )
        return constraints

    def _memory_constraints(self):
        constraints = []
        em = self.expr_manager()
        for iptr, ipair in self.memory._input_reads.items():
            ival, isize = ipair
            # set of reads that may be the same read ordered from the
            # oldest to the newest
            matches = []
            for ptr, val in reversed(self.memory._reads):
                # we assume that such reads do not read the same memory
                # TODO: this assumption may not be right
                if ival is val or val.bytewidth() != isize:
                    continue
                # if pointers are surely the same, we may bail out
                if ptr == iptr:
                    matches.append((ptr, iptr, val, ival))
                    break
                # else if the pointers may be the same, add them to match
                if self.is_sat(_same_ptrs(em, ptr, iptr)) is True:
                    matches.append((ptr, iptr, val, ival))

            # go from the newest read to the oldest -- every older read
            # overwrites the newer read, which we must build into an expression
            expr = None
            Ite = em.Ite
            for ptr, iptr, val, ival in reversed(matches):
                if expr is None:
                    expr = em.Or(
                        em.Not(_same_ptrs(em, ptr, iptr)), _same_values(em, val, ival)
                    )
                else:
                    expr = Ite(
                        _same_ptrs(em, ptr, iptr), _same_values(em, val, ival), expr
                    )

            if expr:
                if expr.is_concrete() and bool(expr.value()):
                    continue
                constraints.append(expr)
        return constraints

    def apply_postcondition(self, postcondition):
        if isinstance(postcondition, ExprAnnotation):
            good, _ = execute_annotation(self.executor(), [self], postcondition)
            return good
        raise NotImplementedError(f"Invalid post-condition: {postcondition}")

    def _replace_value(self, val, newval):
        em = self.expr_manager()
        # print_stdout(f'REPLACING {val} WITH {newval}', color="red")

        # coerce the values
        if not val.is_bool() and newval.is_bool():
            bw = val.bitwidth()
            assert bw <= 8, f"{val} -> {newval}"
            newval = em.Ite(newval, ConcreteInt(1, bw), ConcreteInt(0, bw))
        elif not val.is_float() and newval.is_float():
            assert val.bitwidth() == newval.bitwidth(), f"{val} -> {newval}"
            newval = em.Cast(newval, val.type())
        elif newval.bitwidth() == 1 and val.bitwidth() == 8:
            newval = em.Cast(newval, val.type())
        elif val.bitwidth() == 1 and newval.bitwidth() == 8:
            assert not val.is_bool(), f"{val} -> {newval}"
            z = ConcreteInt(0, 8)
            newval = em.Extract(newval, z, z)

        assert val.type() == newval.type(), f"{val} -- {newval}"
        # FIXME: use incremental solver
        substitute = em.substitute
        new_repl = []
        pc = self.path_condition()
        if val.is_pointer():
            assert (
                val.object().is_concrete() or val.object().is_symbol()
            ), f"Cannot replace {val} with {newval}"
            assert (
                val.offset().is_concrete() or val.offset().is_symbol()
            ), f"Cannot replace {val} with {newval}"
            # if the value is pointer, we must substitute it also in the state of the memory
            assert newval.is_pointer(), newval
            pc = substitute(
                pc, (val.object(), newval.object()), (val.offset(), newval.offset())
            )
        else:
            assert (
                val.is_concrete() or val.is_symbol()
            ), f"Cannot replace {val} with {newval}"
            pc = substitute(pc, (val, newval))
        self._replace_value_in_memory(new_repl, newval, substitute, val)
        self.set_constraints(pc)

        return new_repl

    def replace_input_value(self, val, newval):
        """
        Replace an input value with a new values and consume it.
        NOTE: the argument 'val' must be the very same object (not only equal expression),
        e.g., obtained by the input() method.
        """
        mtch_input = None
        for inp in self._inputs:
            if inp.value is val:
                mtch_input = inp
                break
        if mtch_input:
            self.replace_value(val, newval)
            self._inputs.remove(mtch_input)
            return True
        return False

    def replace_value(self, val, newval):
        # recursively handle the implied equalities
        replace_value = self._replace_value
        new_repl = replace_value(val, newval)
        while new_repl:
            tmp = []
            for r in new_repl:
                tmp += replace_value(r[0], r[1])
            new_repl = tmp

    def _replace_value_in_memory(self, new_repl, newval, substitute, val):
        # FIXME: remove reads that are for sure overwritten
        # to not to carry them with us all the time
        self.memory._reads = [
            (
                _subst_val(substitute, cptr, (val, newval)),
                _subst_val(substitute, cval, (val, newval)),
            )
            for cptr, cval in self.memory._reads
        ]

        UP = self.memory._input_reads
        nUP = {}
        # replace pointers in input reads, but not the values
        # we will need the values in substitutions
        for cptr, cval in UP.items():
            nptr = _subst_val(substitute, cptr, (val, newval))
            curval = nUP.get(nptr)
            if curval is not None:
                new_repl.append((curval[0], cval[0]))
            nUP[nptr] = cval
        self.memory._input_reads = nUP

    def _get_symbols(self):
        symbols = set(
            s for e in self.constraints() for s in e.symbols() if not e.is_concrete()
        )
        for ptr, val in self.memory._reads:
            symbols.update(ptr.symbols())
            symbols.update(val.symbols())
        for ptr, val in self.memory._input_reads.items():
            symbols.update(ptr.symbols())
            symbols.update(val[0].symbols())
        return symbols

    def join_prestate(self, prestate, is_init):
        self._join_prestate(prestate)
        if is_init:
            # we have feasible state in init, we must check whether it is really feasible
            # by adding the omitted memory constraints
            # FIXME: can we somehow easily check that we do not have to do this?
            self.add_constraint(*self._memory_constraints())
            self.add_constraint(*self._init_memory_constraints(prestate))

        if not self.is_feasible():
            return []
        return [self]

    def _join_prestate(self, prestate):
        """
        Update this state with information from prestate. That is, simulate
        that this state is executed after prestate.
        # FIXME: do not touch the internal attributes of memory
        """
        assert isinstance(prestate, BSEState), type(prestate)
        # print("==================== Pre-state ========================")
        # print_stdout(str(prestate), color="green")
        # print("==================== Join into ========================")
        # print_stdout(str(self), color='cyan')
        # print("====================           ========================")
        try_eval = prestate.try_eval
        add_input = self.add_input

        ### modify the state according to the pre-state
        replace_value = self.replace_value
        new_inputs = []
        for inp in self.inputs():
            preval = try_eval(inp.instruction)
            if preval:
                # print('REPL from reg', inp.value, preval)
                replace_value(inp.value, preval)
            else:
                new_inputs.append(inp)
        self._inputs = new_inputs  # new inputs are those that we didn't match

        changed = True
        while changed:
            changed = False
            for ptr, inpval in self.memory._input_reads.items():
                # try read the memory if it is written in the state
                val, _ = prestate.memory.read(ptr, inpval[1])
                if val:
                    replace_value(inpval[0], val)
                    changed = True
                    # we matched the input read, so remove it
                    self.memory._input_reads.pop(ptr)

        ### copy the data from pre-state
        self.memory._reads = prestate.memory._reads + self.memory._reads
        ireads = self.memory._input_reads
        self.memory._input_reads = prestate.memory._input_reads.copy()
        for k, v in ireads.items():
            assert k not in self.memory._input_reads
            self.memory._input_reads[k] = v

        # filter the nondets that are still used
        symbols = set(self._get_symbols())
        assert len(self._inputs) <= len(symbols), f"{{{self._inputs}}} not in {symbols}"
        assert len(set(inp.instruction for inp in self._inputs)) == len(
            self._inputs
        ), f"Repeated value for an instruction: {self._inputs}"
        self._nondets = [
            inp for inp in self.nondets() if not symbols.isdisjoint(inp.value.symbols())
        ]
        assert len(self._nondets) <= len(symbols)

        # add new inputs from pre-state
        for inp in prestate.nondets():
            self.add_nondet(inp)
        for inp in prestate.inputs():
            add_input(inp)
        self.add_constraint(*prestate.constraints())

    # print("==================== Joined st ========================")
    # print_stdout(str(self), color="orange")
    # print("====================           ========================")

    def maybe_sat(self, *e):
        """
        This is a copy of sestate.is_sat() but we bail out after some timeout
        assuming that 'sat'.
        """
        # XXX: check whether this kind of preprocessing is not too costly
        symb = []
        for x in e:
            if x.is_concrete():
                assert isinstance(x.value(), bool)
                if not x.value():
                    return False
                else:
                    continue
            else:
                symb.append(x)
        if not symb:
            return True

        r = self._solver.try_is_sat(500, *self.constraints(), *e)
        if r is not None:
            return r
        return solve_incrementally(
            self.constraints(), e, self.expr_manager(), 2000, 500
        )

    def __repr__(self):
        s = f"BSEState [{self.get_id()}]"
        if self.memory._input_reads:
            s += "\n" + "\n".join(
                f"-> L({p.as_value()})={x}" for p, x in self.memory._input_reads.items()
            )
        if self.memory._reads:
            s += "\n" + "\n".join(
                f"<- L({p.as_value()})={x}" for p, x in self.memory._reads
            )
        if self._inputs:
            s += "\n" + "\n".join(
                f"?  {nd.instruction.as_value()}={nd.value}" for nd in self._inputs
            )
        s += f"\nconstraints: {self.constraints()}"
        return s

    def dump(self, stream=stdout):
        super().dump(stream)
        write = stream.write
        write(" -- inputs --\n")
        for n in self._inputs:
            write(str(n))
            write("\n")
