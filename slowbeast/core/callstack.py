from copy import copy
from sys import stdout
from functools import reduce
from operator import xor


class CallStack:
    class Frame:
        def __init__(self, fun, returnsite=None, v={}):
            self.function = fun
            self.returnsite = returnsite
            self.values = copy(v)
            self._ro = False

        def __eq__(self, rhs):
            return (
                self.function == rhs.function
                and self.values == rhs.values
                and self.returnsite == rhs.returnsite
            )

        def __hash__(self):
            r = reduce(xor, map(hash, self.values), 0) ^ hash(self.function)
            rets = self.returnsite
            return r ^ hash(rets) if rets else r

        def _set_ro(self):
            self._ro = True

        def _is_ro(self):
            return self._ro

        def _cow_reown(self):
            if self._values_ro:
                self.values = copy(self.values)
                self._values_ro = False

        def writable_copy(self):
            new = copy(self)
            new.values = copy(self.values)
            new._ro = False
            return new

        def clear(self):
            self.values = {}

        def set(self, what, v):
            assert self._ro is False, "COW bug"
            self.values[what] = v

        def get(self, v):
            return self.values.get(v)

        def values_list(self):
            return self.values.keys()

        def dump(self, stream=stdout):
            for x, v in self.values.items():
                stream.write("{0} -> {1}\n".format(x.as_value(), v.as_value()))

    def __init__(self):
        self._cs = []
        self._cs_ro = False

    def copy(self):
        new = copy(self)
        new._cs_ro = True
        self._cs_ro = True
        for f in self._cs:
            f._set_ro()
        return new

    def _cow_reown(self):
        if self._cs_ro:
            assert all([x._is_ro() for x in self._cs])
            self._cs = copy(self._cs)
            self._cs_ro = False

    def __len__(self):
        return len(self._cs)

    def __eq__(self, rhs):
        return self._cs == rhs._cs

    def __hash__(self):
        # FIXME: make more efficient
        if not self._cs:
            return 0
        ret = 0
        for c in self._cs:
            ret ^= c.__hash__()
        return ret

    def __iter__(self):
        return self._cs.__iter__()

    def frame(self, idx=-1):
        return self._cs[idx]

    def set(self, what, v):
        """Set a value in the current frame"""
        self._cow_reown()
        if self.frame()._is_ro():
            self._cs[-1] = self.frame().writable_copy()
            assert not self.frame()._is_ro()
        self.frame().set(what, v)

    def get(self, v):
        """Set a value from the current frame"""
        return self.frame().get(v)

    def values_list(self, frameidx=-1):
        """Set a value from the current frame"""
        return self.frame(frameidx).values_list()

    def push_call(self, callsite, fun, argsMap):
        self._cow_reown()
        self._cs.append(CallStack.Frame(fun, callsite, argsMap))
        assert not self.frame()._is_ro()

    def pop_call(self):
        assert len(self._cs) > 0
        self._cow_reown()
        rs = self.frame().returnsite
        del self._cs[-1]
        return rs

    def dump(self, stream=stdout):
        for n, f in enumerate(self._cs):
            name = f.function.name() if f.function else None
            stream.write(f" -- {n}: {name} --\n")
            f.dump(stream)
