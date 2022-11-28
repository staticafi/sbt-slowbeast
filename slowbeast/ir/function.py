from sys import stdout
from .argument import Argument
from .program import ProgramElement
from .instruction import Return


class Function(ProgramElement):

    __slots__ = "_name", "_bblocks", "_arguments", "_retty"

    def __init__(self, name, args, retty=None):
        super().__init__()
        self._name = name
        self._bblocks = []
        self._arguments = args or []
        self._retty = retty

        assert all(map(lambda a: isinstance(a, Argument), args))

    def __eq__(self, other):
        assert self._name != other._name or self.get_id() == other.get_id()
        return self._name == other._name

    __hash__ = ProgramElement.__hash__

    def is_undefined(self):
        return self._bblocks == []

    def name(self):
        return self._name

    def argument(self, idx):
        assert idx < len(self._arguments)
        return self._arguments[idx]

    def arguments(self):
        return self._arguments

    def return_type(self):
        return self._retty

    def type(self):
        return self._retty

    def add_bblock(self, bb):
        self._bblocks.append(bb)
        bb.set_fun(self)

    def bblock(self, idx):
        assert idx < len(self._bblocks)
        return self._bblocks[idx]

    def bblocks(self):
        return self._bblocks

    def ret_bblocks(self):
        return [b for b in self._bblocks if isinstance(b[-1], Return)]

    def __iter__(self):
        return self._bblocks.__iter__()

    def dump(self, ind=0, stream=stdout, color=True):
        super().dump(ind, stream, color)
        stream.write(
            "fun {0}({1})\n".format(
                self._name, ", ".join(map(lambda x: x.as_value(), self._arguments))
            )
        )

        for b in self._bblocks:
            b.dump(2, stream=stream)
            stream.write("\n")

        if len(self._bblocks) > 0:
            stream.write("nuf\n")

    def as_value(self):
        return self._name
