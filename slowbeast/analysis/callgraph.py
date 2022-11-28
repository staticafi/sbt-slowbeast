from sys import stdout

from slowbeast.ir.function import Function
from slowbeast.ir.instruction import Call


class CallGraph:
    class Node:
        __slots__ = "_fun", "_callsites", "_callers"

        def __init__(self, F):
            self._fun = F
            self._callers = []
            self._callsites = {}

        def fun(self):
            return self._fun

        def callsites(self):
            return self._callsites

        def callers(self):
            return self._callers

        def add_callsite(self, callsite, funs):
            """
            This node contains a call-site 'callsite'
            that calls funs
            """
            self._callsites[callsite] = funs
            for f in funs:
                f._callers.append((self, callsite))

        def predecessors(self):
            """
            Simple predecessors (over functios)
            """
            return (f for (f, cs) in self._callers)

        def successors(self):
            """
            Simple successors (over functios)
            """
            return set(
                (v for funs in self._callsites.values() for v in funs)
            ).__iter__()

    __slots__ = "_program", "_nodes"

    def __init__(self, P):
        self._program = P
        self._nodes = {}

        self._build()

    def create_node(self, *args):
        """Override this method in child classes
        to get nodes with more data
        """
        assert len(args) == 1
        return CallGraph.Node(*args)

    def get_node(self, B):
        return self._nodes.get(B)

    def get_nodes(self):
        return self._nodes.values()

    def funs(self):
        return (f.fun() for f in self._nodes.values())

    def _build(self):
        for F in self._program.funs():
            self._nodes[F] = self.create_node(F)

        for _fun, node in self._nodes.items():
            self._build_fun(_fun, node)

    def _build_fun(self, _fun, node):
        for block in _fun.bblocks():
            for I in block.instructions():
                if not isinstance(I, Call):
                    continue

                # this function (node) contains call I that calls ...
                node.add_callsite(I, [self._nodes[I.called_function()]])

    def get_reachable(self, node):
        if isinstance(node, Function):
            node = self.get_node(node)
        assert isinstance(node, CallGraph.Node)

        queue = [node]
        reachable = set()
        while queue:
            n = queue.pop()
            reachable.add(n)
            for s in n.successors():
                if s not in reachable:
                    queue.append(s)

        return reachable

    def prune_unreachable(self, frm):
        reach = self.get_reachable(frm)
        nonreach = [(k, n) for (k, n) in self._nodes.items() if n not in reach]
        for (k, n) in nonreach:
            self._nodes.pop(k)

    def dump(self, stream=stdout):
        for f, node in self._nodes.items():
            stream.write("Fun '{0}' calls\n".format(f.name()))
            for cs, funs in node.callsites().items():
                for n, cf in enumerate(funs):
                    if n == 0:
                        stream.write(
                            "  {0} -> {1}\n".format(cs.get_id(), cf.fun().name())
                        )
                    else:
                        stream.write("     -> {0}\n".format(cf.fun().name()))
