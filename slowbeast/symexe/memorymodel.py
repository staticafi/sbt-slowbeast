from slowbeast.util.debugging import dbgv
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import Alloc, GlobalVariable, Load
from slowbeast.ir.types import IntType
from slowbeast.domains.symbolic import NondetLoad
from slowbeast.symexe.memory import Memory
from slowbeast.core.memorymodel import MemoryModel as CoreMM
from slowbeast.ir.types import get_size_type


class SymbolicMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)

    def create_memory(self):
        """Create a memory object that is going to be a part of a state."""
        return Memory()


# LazySymbolicMemoryModel inherints from CoreMM intentionally (SymbolicMemoryModel
# to use core.Memory. symexe.Memory overrides uninitialized reads in the Memory() object
# in a way that is not suitable for lazy memory
class LazySymbolicMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)
        # over-approximate unsupported operations
        self._overapprox_unsupported = True

    def lazy_allocate(self, state, op):
        assert isinstance(op, (Alloc, GlobalVariable)), op
        s = self.allocate(state, op)
        assert len(s) == 1 and s[0] is state
        dbgv("Lazily allocated {0}".format(op), color="white", verbose_lvl=3)
        assert state.get(op), "Did not bind an allocated value"

    def allocate(self, state, instr):
        """
        Perform the allocation by the instruction
        "inst" and return the new states (there may be
        several new states, e.g., one where the allocation succeeds,
        one where it fails, etc.).
        """
        if isinstance(instr, (Alloc, GlobalVariable)):
            size = instr.size()
        elif self._overapprox_unsupported:
            size = state.solver().Var(f"ndt_size_{instr.as_value()}", get_size_type())
        size = state.try_eval(size)
        if instr.is_global():
            ptr = state.memory.allocate_global(instr, instr.is_zeroed())
        else:
            ptr = state.memory.allocate(size, instr)
        state.set(instr, ptr)
        return [state]

    def _havoc_ptr_target(self, state, ptr, without=None):
        """Havoc memory possibly pointed by ptr"""
        # we do not know what we write where, so just clear all the information if possible
        mo = None
        if ptr.is_pointer():
            mo = state.memory.get_obj(ptr.object())
        if mo:
            state.havoc((mo,))
        else:
            state.havoc()
        return None

    def write(self, state, instr, valueOp, toOp):
        to = state.get(toOp)
        if to is None:
            self.lazy_allocate(state, toOp)
            to = state.get(
                toOp
            )  # FIXME "We're calling get() method but we could return the value..."
            assert to
        if not to.is_pointer():
            if self._overapprox_unsupported:
                self._havoc_ptr_target(
                    state, to
                )  # symbolic pointers are unsupported atm
            else:
                state.set_killed(f"Invalid pointer to write to: {to}")
            return [state]
        if (
            not to.offset().is_concrete()
        ):  # FIXME: move this check to memory.write() object
            if self._overapprox_unsupported:
                self._havoc_ptr_target(state, to)
            else:
                state.set_killed("Write with non-constant offset not supported yet")
            return [state]

        value = state.try_eval(valueOp)
        if value is None:
            value = state.solver().Var(
                f"uninit_{valueOp.as_value()}", IntType(8 * instr.bytewidth())
            )
        assert isinstance(value, Value)

        err = state.memory.write(to, value)
        if err:
            assert err.is_memory_error()
            if err.is_unsupported() and self._overapprox_unsupported:
                self._havoc_ptr_target(state, to)
            else:
                state.set_error(err)
        return [state]

    def uninitialized_read(self, state, frm, ptr, bitsnum):
        dbgv(
            "Reading nondet for uninitialized value: {0}".format(ptr),
            color="white",
            verbose_lvl=3,
        )
        # NOTE: this name identifier is reserved for value representing
        # uninitialized read from this allocation, so it is unique and
        # we can recycle its name
        # val = self.solver().fresh_value(f"uninit_{frm.as_value()}", 8 * bytesNum)
        val = state.solver().Var(f"uninit_{frm.as_value()}", IntType(bitsnum))
        # write the fresh value into memory, so that
        # later reads see the same value.
        # If an error occurs, just propagate it up
        assert ptr.is_pointer() and ptr.offset().is_concrete(), ptr
        err = state.memory.write(ptr, val)
        return val, err

    def _nondet_value(self, state, frm, ptr, bitsnum):
        if ptr.is_pointer() and ptr.offset().is_concrete():
            return self.uninitialized_read(state, frm, ptr, bitsnum)
        # return val, err
        # FIXME: it is not always int type... we should at least use bytes type
        return (
            state.solver().fresh_value(f"uninit_{frm.as_value()}", IntType(bitsnum)),
            None,
        )

    def read(self, state, toOp, fromOp, bytesNum, bitsnum=None):
        """
        We want to read 'bitsnum' of bits and in order to do that
        we read 'bytesNum' of bytes
        """
        assert (
            bitsnum is None or max(1, int(bitsnum / 8)) == bytesNum
        ), f"{bytesNum} {bitsnum}"
        assert isinstance(bytesNum, int), f"Invalid number of bytes: {bytesNum}"

        frm = state.get(fromOp)
        if frm is None:
            if (
                not isinstance(fromOp, (Alloc, GlobalVariable))
                and self._overapprox_unsupported
            ):
                val = state.solver().Var(
                    f"unknown_ptr_{fromOp.as_value()}",
                    IntType(bitsnum or 8 * bytesNum()),
                )
                state.set(toOp, val)
                return [state]
            else:
                self.lazy_allocate(state, fromOp)
                frm = state.get(fromOp)

        if not frm.is_pointer() and self._overapprox_unsupported:
            val, err = self._nondet_value(state, fromOp, frm, bitsnum or bytesNum * 8)
            if err:
                state.set_error(err)
            else:
                state.set(toOp, val)
            return [state]
        else:
            assert frm.is_pointer(), frm
        if not frm.offset().is_concrete():
            if self._overapprox_unsupported:
                val, err = self._nondet_value(
                    state, fromOp, frm, bitsnum or bytesNum * 8
                )
                if err:
                    state.set_error(err)
                else:
                    state.set(toOp, val)
                return [state]
            else:
                state.set_killed("Read with non-constant offset not supported yet")
            return [state]
        val, err = state.memory.read(frm, bytesNum)
        if err:
            assert err.is_memory_error(), err
            if err.is_uninit_read():
                val, err = self.uninitialized_read(
                    state, fromOp, frm, bitsnum or bytesNum * 8
                )
                assert isinstance(toOp, Load)
                state.create_nondet(toOp, NondetLoad.fromExpr(val, toOp, fromOp))
            elif err.is_unsupported() and self._overapprox_unsupported:
                val, err = self._nondet_value(
                    state, fromOp, frm, bitsnum or bytesNum * 8
                )
        if err:
            state.set_error(err)
        else:
            state.set(toOp, val)
        return [state]
