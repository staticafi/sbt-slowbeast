from slowbeast.util.debugging import dbg
from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.scc import strongly_connected_components_iterative
from slowbeast.cfkind.annotatedcfa import AnnotatedCFAPath


class Loop:
    """
    Represents a set of _paths _header --> _header
    such that all these _paths are acyclic
    """

    def __init__(self, loc, parent, paths, locs, entries, exits, inedges, backedges):
        # parent loops
        self._parent = parent
        # header of the loop (the target of backedges)
        self._header = loc
        # header-header _paths
        self._paths = paths
        self._locs = locs
        self._exits = exits  # edges leaving the loop
        self._entries = entries  # edges from outside to the loop header
        self._inedges = inedges  # edges from header into loop
        self._backedges = backedges  # edges from loop into header
        self._edges = set(e for path in paths for e in path)

    def cfa(self):
        return self._header.cfa()

    def header(self):
        return self._header

    def locs(self):
        return self._locs

    def has_loc(self, l):
        return l in self._locs

    def __contains__(self, item: CFA.Edge):
        assert isinstance(item, CFA.Edge)
        return item in self._edges

    def paths(self):
        return self._paths

    def last_iteration_paths(self):
        """
        Take all paths in the loop and prolong them such that they end with an exit edge.
        """
        result = []
        queue = self._paths.copy()
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    if succedge in self._exits:
                        result.append(path.copyandappend(succedge))
                    elif succedge not in self._backedges:
                        newqueue.append(path.copyandappend(succedge))
                    # else drop the path
            queue = newqueue
        return result

    def paths_to_header(self, frm):
        """
        All paths from the given node to header
        """
        result = []
        queue = [AnnotatedCFAPath([e]) for e in frm.successors()]
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    if succedge in self._exits:
                        pass  # drop
                    elif succedge in self._backedges:
                        result.append(path.copyandappend(succedge))
                    else:
                        newqueue.append(path.copyandappend(succedge))
            queue = newqueue
        return result

    def get_exit_paths(self):
        """
        All paths from header to exit edge
        """
        result = []
        queue = [AnnotatedCFAPath([e]) for e in self._header.successors()]
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    if succedge in self._exits:
                        result.append(path.copyandappend(succedge))
                    elif succedge not in self._backedges:
                        newqueue.append(path.copyandappend(succedge))
                    # else drop the path
            queue = newqueue
        return result

    def exits(self):
        return self._exits

    def entries(self):
        return self._entries

    def inedges(self):
        return self._inedges

    def has_inedge(self, *args):
        if len(args) == 1:
            assert isinstance(args[0], CFA.Edge)
            s, t = args[0].source(), args[0].target()
        elif len(args) == 2:
            s, t = args[0], args[1]
        else:
            raise RuntimeError("Invalid arguments to has_inedge")

        assert isinstance(s, CFA.Location)
        assert isinstance(t, CFA.Location)
        for edge in self._inedges:
            if edge.source() == s and edge.target() == t:
                return True
        return False


def _construct_simple_loop(vertices, parent, loc):
    """
    Construct a loop that has no nested loops. Fail if a nested loop is found.
    """
    backedges = set()
    locs = set()
    locs.add(loc)

    def processedge(edge, dfstype):
        start, end = edge.source(), edge.target()
        if dfstype == DFSEdgeType.BACK:
            if end == loc:
                backedges.add(edge)
            else:
                raise ValueError("Nested loop")
        if dfstype != DFSEdgeType.TREE and end in locs:
            # backtrack is not called for non-tree edges...
            locs.add(start)

    def backtrack(edge):
        if edge is not None and edge.target() in locs:
            locs.add(edge.source())

    try:
        DFSVisitor(vertices).foreachedge(loc, processedge, backtrack)
    except ValueError:  # nested loop
        return None

    entries = set()
    inedges = set()
    exits = set()
    # FIXME: do not store this, just return generators from getters (except for exits, those need to be precomputed)
    for edge in loc.successors():
        if edge.target() in locs:
            inedges.add(edge)
        else:
            exits.add(edge)
    for edge in loc.predecessors():
        if edge.source() not in locs:
            entries.add(edge)

    # fixme: not efficient at all...
    paths = []
    queue = [[e] for e in inedges]
    while queue:
        newqueue = []
        for path in queue:
            for succedge in path[-1].successors():
                succloc = succedge.target()
                if succloc not in locs:
                    exits.add(succedge)
                    continue
                np = path + [succedge]
                if succloc != loc:
                    newqueue.append(np)
                else:
                    paths.append(np)
        queue = newqueue

    return Loop(
        loc,
        parent,
        [AnnotatedCFAPath(p) for p in paths],
        locs,
        entries,
        exits,
        inedges,
        backedges,
    )


def _compute_loops(vertices, edges, result):
    """Compute loops in the graph given by vertices and edges"""
    for C in strongly_connected_components_iterative(vertices, edges):
        if len(C) <= 1:
            continue

        subvertices = list(C)
        # entries to the SCC
        entries = set(
            l
            for l in subvertices
            if any(p.source() not in subvertices for p in l.predecessors())
        )
        if len(entries) != 1:
            dbg(f"SCC with multiple entries: {C}")
            continue
        entry = next(iter(entries))
        # FIXME: handle nested loops by removing backedges to entry from the SCC and recursing into the SCC
        loop = _construct_simple_loop(list(C), None, entry)
        result[entry] = loop


def compute_loops(cfa):
    result = {}
    locations = cfa.locations()
    edges = {l: [succ.target() for succ in l.successors()] for l in locations}
    _compute_loops(locations, edges, result)
    return result


class SimpleLoop:
    """
    Represents a set of _paths _header --> _header
    such that all these _paths are acyclic
    """

    def __init__(self, loc, paths, locs, entries, exits, inedges, backedges):
        self._header = loc
        # header-header _paths
        self._paths = paths
        # _paths inside the loop that do not return to the header
        # the last edge from each path is also an exit (but one that does
        # not go through the loop header)
        self._locs = locs
        self._exits = exits  # edges leaving the loop
        self._entries = entries  # edges from outside to loop header
        self._inedges = inedges  # edges from header into loop
        self._backedges = backedges  # edges from loop into header
        self._edges = set(e for path in paths for e in path)

        # the state after executing the given path
        self.states = None
        self.vars = None

    def header(self):
        return self._header

    def locs(self):
        return self._locs

    def has_loc(self, l):
        return l in self._locs

    def __contains__(self, item: CFA.Edge):
        assert isinstance(item, CFA.Edge)
        return item in self._edges

    def paths(self):
        return self._paths

    def get_exit_paths(self):
        """
        Take all paths in the loop and prolong them such that they end with an exit edge.
        """
        result = []
        queue = self._paths.copy()
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    if succedge in self._exits:
                        result.append(path.copyandappend(succedge))
                    elif succedge not in self._backedges:
                        newqueue.append(path.copyandappend(succedge))
                    # else drop the path
            queue = newqueue
        return result

    def exits(self):
        return self._exits

    def entries(self):
        return self._entries

    def inedges(self):
        return self._inedges

    def has_inedge(self, *args):
        if len(args) == 1:
            assert isinstance(args[0], CFA.Edge)
            s, t = args[0].source(), args[0].target()
        elif len(args) == 2:
            s, t = args[0], args[1]
        else:
            raise RuntimeError("Invalid arguments to has_inedge")

        assert isinstance(s, CFA.Location)
        assert isinstance(t, CFA.Location)
        for edge in self._inedges:
            if edge.source() == s and edge.target() == t:
                return True
        return False

    def construct(loc):
        """
        Construct the SimpleLoop obj for _header.
        Returns None if that cannot be done
        """

        backedges = set()
        locs = set()
        locs.add(loc)

        def processedge(edge, dfstype):
            start, end = edge.source(), edge.target()
            if dfstype == DFSEdgeType.BACK:
                if end == loc:
                    backedges.add(edge)
                else:
                    raise ValueError("Nested loop")
            if dfstype != DFSEdgeType.TREE and end in locs:
                # backtrack is not called for non-tree edges...
                locs.add(start)

        def backtrack(edge):
            if edge is not None and edge.target() in locs:
                locs.add(edge.source())

        try:
            DFSVisitor().foreachedge(loc, processedge, backtrack)
        except ValueError:  # nested loop
            return None

        entries = set()
        inedges = set()
        exits = set()
        # FIXME: do not store this, just return generators from getters (except for exits, those need to be precomputed)
        for edge in loc.successors():
            if edge.target() in locs:
                inedges.add(edge)
            else:
                exits.add(edge)
        for edge in loc.predecessors():
            if edge.source() not in locs:
                entries.add(edge)

        # fixme: not efficient at all...
        paths = []
        queue = [[e] for e in inedges]
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    succloc = succedge.target()
                    if succloc not in locs:
                        exits.add(succedge)
                        continue
                    np = path + [succedge]
                    if succloc != loc:
                        newqueue.append(np)
                    else:
                        paths.append(np)
            queue = newqueue

        return SimpleLoop(
            loc,
            [AnnotatedCFAPath(p) for p in paths],
            locs,
            entries,
            exits,
            inedges,
            backedges,
        )
