from ..ir.instruction import Alloc, GlobalVariable
from slowbeast.domains.value import Value
from .memory import Memory


class MemoryModel:
    """
    Class that takes care of performing memory operations
    (without knowing what is the real memory implementation)
    """

    def __init__(self, opts):
        self._opts = opts

    def create_memory(self):
        """
        Create a memory object that is going to be a part
        of a state.
        """
        return Memory()

    def allocate(self, state, instr):
        """
        Perform the allocation by the instruction
        "inst" and return the new states (there may be
        several new states, e.g., one where the allocation succeeds,
        one where it fails, etc.).
        """
        assert isinstance(instr, Alloc) or isinstance(instr, GlobalVariable)
        size = state.try_eval(instr.size())
        if instr.is_global():
            ptr = state.memory.allocate_global(instr, zeroed=instr.is_zeroed())
        else:
            ptr = state.memory.allocate(size, instr)
        state.set(instr, ptr)
        return [state]

    def write(self, state, instr, valueOp, toOp):
        value = state.eval(valueOp)
        to = state.get(toOp)
        if to is None:
            state.set_killed("Use of unknown variable: {0}".format(toOp))
            return [state]

        assert isinstance(value, Value)
        assert to.is_pointer()
        try:
            err = state.memory.write(to, value)
        except NotImplementedError as e:
            state.set_killed(str(e))
            return [state]
        if err:
            if err.is_memory_error() and err.is_unsupported():
                state.set_killed(str(err))
            else:
                state.set_error(err)
        return [state]

    def read(self, state, toOp, fromOp, bytesNum, bitsnum=None):
        frm = state.get(fromOp)
        if frm is None:
            state.set_killed("Use of unknown variable: {0}".format(fromOp))
            return [state]

        assert frm.is_pointer()
        try:
            val, err = state.memory.read(frm, bytesNum)
        except NotImplementedError as e:
            state.set_killed(str(e))
            return [state]
        if err:
            if err.is_memory_error() and err.is_unsupported():
                state.set_killed(str(err))
            else:
                state.set_error(err)
        else:
            state.set(toOp, val)
        return [state]
