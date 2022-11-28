from sys import stdout
from copy import copy
from functools import reduce
from operator import xor

from slowbeast.util.debugging import dbgv
from slowbeast.core.memorymodel import MemoryModel
from slowbeast.core.memory import Memory as CoreMemory
from slowbeast.core.errors import MemError
from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.instruction import Alloc, GlobalVariable, Load
from slowbeast.ir.types import OffsetType, IntType

from slowbeast.domains.symbolic import NondetLoad


class AIMemoryObject:
    __slots__ = "_id", "_values", "_size", "_name", "_allocation", "_ro"
    ids = 0

    def __init__(self, size, nm="unnamed", objid=None):
        if objid:
            self._id = objid
        else:
            AIMemoryObject.ids += 1  # shift the objects counter for the next object
            self._id = AIMemoryObject.ids

        self._values = {}
        self._size = size
        self._name = nm  # for debugging
        self._allocation = None  # which allocation allocated this memory
        self._ro = False  # COW support

    def _set_ro(self):
        self._ro = True

    def _is_ro(self):
        return self._ro

    def writable_copy(self):
        new = copy(self)
        new._values = copy(self._values)
        new._ro = False
        return new

    def get_id(self):
        return self._id

    def get_size(self):
        return self._size

    def set_allocation(self, a):
        self._allocation = a

    def write(self, x, off=None):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        offval = 0 if off is None else off.value()
        # self._values.setdefault(offval, set()).add(x)
        self._values[offval] = x
        return None

    def read(self, bts, off=None):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """

        offval = 0 if off is None else off.value()
        val = self._values.get(offval)
        if val is None:
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read from uninitialized memory (or unaligned read (not supp.  yet)).\n"
                f"Reading bytes {offval}-{offval}+{bts-1} from obj {self._id} with contents:\n"
                f"{self._values}",
            )

        return val, None

    def __str__(self):
        s = "ai-mo{0} ({1}, alloc'd by {2}, ro:{3}), size: {4}".format(
            self._id,
            self._name if self._name else "no name",
            self._allocation.as_value() if self._allocation else "unknown",
            self._ro,
            self._size,
        )
        for k, v in self._values.items():
            s += "\n  {0} -> {1}".format(k, v)
        return s

    def as_value(self):
        return "ai-mo{0}".format(self._id)

    def dump(self, stream=stdout):
        stream.write(str(self))
        stream.write("\n")

    def __eq__(self, rhs):
        return self._id == rhs._id

    def __hash__(self):
        return self._id  # FIXME: is this a good hashing method for comparing states?


class AIMemory(CoreMemory):
    def create_memory_object(self, size, nm=None, objid=None, is_global=False):
        """
        Create a new memory object -- may be overriden
        by child classes to create a different type of
        memory objects.
        """
        assert not is_global, "Not supported atm"
        return AIMemoryObject(size, nm, objid)

    def __eq__(self, rhs):
        return (
            self._objects == rhs._objects
            and self._glob_objects == rhs._glob_objects
            and self._cs == rhs._cs
        )

    def __hash__(self):
        return (
            reduce(xor, map(hash, self._objects.items()), 0)
            ^ reduce(lambda a, b: a ^ b, map(hash, self._glob_objects.items()), 0)
            ^ self._cs.__hash__()
        )


class AIMemoryModel(MemoryModel):
    def __init__(self, opts, solver):
        super().__init__(opts)

    def create_memory(self):
        return AIMemory()


class AIMemoryModel(MemoryModel):
    def __init__(self, opts):
        super().__init__(opts)

    def create_memory(self):
        return AIMemory()

    def lazy_allocate(self, state, op):
        assert isinstance(op, Alloc) or isinstance(op, GlobalVariable)
        s = self.allocate(state, op)
        assert len(s) == 1 and s[0] is state
        dbgv("Lazily allocated {0}".format(op), color="WHITE")
        assert state.get(op), "Did not bind an allocated value"

    def write(self, state, valueOp, toOp):
        value = state.eval(valueOp)
        to = state.get(toOp)
        if to is None:
            self.lazy_allocate(state, toOp)
            # FIXME "We're calling get() method but we could return the value..."
            to = state.get(toOp)

        assert isinstance(value, Value)
        assert to.is_pointer()
        if not to.offset().is_concrete():
            # FIXME: move this check to memory.write() object
            state.set_killed("Write with non-constant offset not supported yet")
            return [state]
        try:
            err = state.memory.write(to, value)
        except NotImplementedError as e:
            state.set_killed(str(e))
            return [state]
        if err:
            state.set_error(err)
        return [state]

    def uninitialized_read(self, state, frm, ptr, bytesNum):
        dbgv("Reading nondet for uninitialized value: {0}".format(ptr), color="WHITE")
        # NOTE: this name identifier is reserved for value representing
        # uninitialized read from this allocation, so it is unique and
        # we can recycle its name
        val = self.solver().Var(f"load_of_{frm.as_value()}", IntType(8 * bytesNum))
        # write the fresh value into memory, so that
        # later reads see the same value.
        # If an error occurs, just propagate it up
        err = state.memory.write(ptr, val)

        return val, err

    def read(self, state, toOp, fromOp, bytesNum):
        assert isinstance(bytesNum, int), f"Invalid number of bytes: {bytesNum}"
        frm = state.get(fromOp)
        if frm is None:
            self.lazy_allocate(state, fromOp)
            frm = state.get(fromOp)

        assert frm.is_pointer()
        if not frm.offset().is_concrete():
            state.set_killed("Read with non-constant offset not supported yet")
            return [state]
        try:
            val, err = state.memory.read(frm, bytesNum)
            if err:
                assert err.is_memory_error()
                if err.is_uninit_read():
                    val, err = self.uninitialized_read(state, fromOp, frm, bytesNum)
                    assert isinstance(toOp, Load)
                    state.add_nondet(NondetLoad.fromExpr(val, toOp, fromOp))

        except NotImplementedError as e:
            state.set_killed(str(e))
            return [state]
        if err:
            state.set_error(err)
        else:
            state.set(toOp, val)
        return [state]
