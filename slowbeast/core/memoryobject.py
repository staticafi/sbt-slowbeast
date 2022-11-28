from sys import stdout
from copy import copy

from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal, ConcreteInt
from slowbeast.ir.types import get_offset_type
from slowbeast.core.errors import MemError


class MemoryObject:
    ids = 0

    __slots__ = (
        "_id",
        "_values",
        "_size",
        "_name",
        "_allocation",
        "_ro",
        "_is_global",
        "_zeroed",
    )

    def __init__(self, size, nm="unnamed", objid=None, is_global=False):
        if objid:
            self._id = objid
        else:
            MemoryObject.ids += 1  # shift the objects counter for the next object
            self._id = MemoryObject.ids

        self._values = {}  # until we support composite objects, use just 'value'
        self._size = size
        self._name = nm  # for debugging
        self._allocation = None  # which allocation allocated this memory
        self._is_global = is_global
        self._zeroed = False

        self._ro = False  # COW support

    def _set_ro(self):
        self._ro = True

    def _is_ro(self):
        return self._ro

    def set_zeroed(self):
        self._zeroed = True

    def is_zeroed(self):
        return self._zeroed

    def is_global(self):
        return self._is_global

    def clear(self):
        assert not self._ro
        self._values.clear()

    def writable_copy(self):
        new = copy(self)
        new._values = copy(self._values)
        new._ro = False
        return new

    def clean_copy(self):
        new = copy(self)
        new._values = {}
        new._ro = False
        return new

    def __eq__(self, rhs):
        return self._id == rhs._id

    def get_id(self):
        return self._id

    def size(self):
        return self._size

    def set_allocation(self, a):
        self._allocation = a

    def allocation(self):
        return self._allocation

    def _has_concrete_size(self):
        sz = self._size
        return sz is not None and sz.is_concrete()

    def _is_oob(self, bytesnum, offval=0):
        sz = self._size
        return sz is None or bytesnum > sz.value() + offval

    def write(self, x, off=None):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if not off.is_concrete():
            return MemError(
                MemError.UNSUPPORTED, "Write to non-constant offset not supported"
            )

        if not self._has_concrete_size():
            return MemError(
                MemError.UNSUPPORTED, "Write to symbolic-sized objects not implemented"
            )
        offval = 0 if off is None else off.value()
        if offval != 0:
            # FIXME: not efficient...
            bw = x.bytewidth()
            for o, val in self._values.items():
                if offval < o + val.bytewidth() and offval + bw > o:
                    return MemError(
                        MemError.UNSUPPORTED,
                        "Writing overlapping values to an object is not supported yet",
                    )
        if self._is_oob(x.bytewidth(), offval):
            return MemError(
                MemError.OOB_ACCESS,
                "Written value too big for the object. "
                "Writing {0}B to offset {1} of {2}B object".format(
                    x.bytewidth(), off, self._size
                ),
            )
        self._values[offval] = x
        return None

    def read(self, bts, off=None):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"
        if off is None:
            off = ConcreteVal(0, get_offset_type())

        if not off.is_concrete():
            raise NotImplementedError("Read from non-constant offset not supported")

        if not self._has_concrete_size():
            return None, MemError(
                MemError.UNSUPPORTED,
                "Read from symbolic-sized objects not implemented yet",
            )

        offval = off.value()

        if self._is_oob(bts):
            return None, MemError(
                MemError.OOB_ACCESS,
                "Read {0}B from object of size {1}B".format(bts, self._size),
            )

        val = self._values.get(offval)
        if val is None:
            if self._is_global and self._allocation.is_zeroed():
                return ConcreteInt(0, bts * 8), None
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read from uninitialized memory (or unaligned read (not supp.  yet)).\n"
                f"Reading bytes {offval}-{offval+bts-1} from obj {self._id} with contents:\n"
                f"{self._values}",
            )

        # we would need to obtain overlapping offsets
        if val.bytewidth() != bts:
            return None, MemError(
                MemError.UNSUPPORTED,
                f"Reading bytes from object defined by parts is unsupported atm: "
                f"reading {bts} bytes from off {offval} where is value with "
                f"{val.bytewidth()} bytes",
            )

        # FIXME: make me return Bytes objects (a sequence of bytes)
        return val, None

    def offsets(self):
        """Get offsets on which something is written"""
        return self._values.keys()

    def __repr__(self):
        s = "mo{0} ({1}, alloc'd by {2}, ro:{3}), 0-ed: {4}, size: {5}".format(
            self._id,
            self._name if self._name else "no name",
            self._allocation.as_value() if self._allocation else "unknown",
            self._ro,
            self._zeroed,
            self._size,
        )
        for k, v in self._values.items():
            s += "\n  {0} -> {1}".format(k, v)
        return s

    def as_value(self):
        return "mo{0}".format(self._id)

    def dump(self, stream=stdout):
        stream.write(str(self))
        stream.write("\n")
