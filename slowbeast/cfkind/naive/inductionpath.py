from slowbeast.cfkind.annotatedcfg import CFGPath
from sys import stdout
from copy import copy


class InductionPath:
    """
    An object that consists of a state and a CFG path.
    It is a helper class for performing efficient checks
    for reachable errors
    """

    def __init__(self, cfg, state, blocks=[]):
        self.cfg = cfg
        self.state = state
        self.path = CFGPath(blocks)

    def copy(self):
        return InductionPath(self.cfg, self.state.copy(), copy(self.path.locations()))

    def getState(self):
        return self.state

    def getPath(self):
        return self.path

    def appendLoc(self, loc):
        self.path.append(loc)
        return self

    def reaches_assert(self):
        return self.path.reaches_assert()

    def extend(self):
        last = self.path.last()
        if last:
            succs = last.successors()
        else:
            succs = [self.cfg.get_node(self.state.pc.bblock())]

        if len(succs) == 1:
            self.path.append(succs[0])
            return [self]
        else:
            return [self.copy().appendLoc(s) for s in succs]

    def successorsWithAssert(self):
        last = self.path.last()
        if last:
            succs = last.successors()
        else:
            succs = [self.cfg.get_node(self.state.pc.bblock())]

        return [s for s in succs if s.has_assert()]

    def dump(self, stream=stdout):
        stream.write("state: {0}\n".format(self.state.get_id()))
        stream.write("path: ")
        self.path.dump(stream)

    def __repr__(self):
        return "({0}):: {1}".format(self.state.get_id(), self.path)
