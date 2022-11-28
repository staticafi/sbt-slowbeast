from .cfa import CFA


class DFSEdgeType:
    TREE = 1
    FORWARD = 2
    BACK = 3
    CROSS = 4

    def tostr(val):
        if val == DFSEdgeType.TREE:
            return "tree"
        elif val == DFSEdgeType.FORWARD:
            return "forward"
        elif val == DFSEdgeType.BACK:
            return "back"
        elif val == DFSEdgeType.CROSS:
            return "cross"


class DFSData:
    def __init__(self):
        self.visited = False
        self.innum = None
        self.outnum = None


class DFSCounter:
    def __init__(self):
        self.counter = 0


def _get_id(x):
    if isinstance(x, CFA.Location):
        return x.id()
    return (x.bblock().get_id(),)


class DFSVisitor:
    """
    Visit edges in the DFS order and run a user-specified function on them.
    """

    def __init__(self, vertices=None, stop_vertices=None):
        self._data = {}
        self._dfscounter = 0
        # traverse only these vertices
        self._vertices = vertices
        self._stop_vertices = stop_vertices

    def _getdata(self, node):
        return self._data.setdefault(node, DFSData())

    def foreachedge(self, startnode, fun, backtrackfun=None):
        assert self._vertices is None or startnode in self._vertices
        assert self._stop_vertices is None or startnode not in self._stop_vertices

        counter = DFSCounter()
        if isinstance(startnode, CFA.Location):
            self._foreachedge_cfa(fun, backtrackfun, None, startnode, counter)
        else:
            self._foreachedge_cfg(fun, backtrackfun, None, startnode, counter)

    def _foreachedge_cfg(self, fun, backtrackfun, prevnode, node, counter):
        getdata = self._getdata
        counter.counter += 1

        nddata = getdata(node)
        nddata.visited = True
        nddata.innum = counter.counter

        only_vertices = self._vertices
        stop_verts = self._stop_vertices
        for succ in node.successors():
            if only_vertices and succ not in only_vertices:
                continue

            succdata = getdata(succ)
            if succdata.visited:
                sin = succdata.innum
                din = nddata.innum
                assert sin is not None

                if sin < din:
                    sout = succdata.outnum
                    if sout is None:
                        fun(node, succ, DFSEdgeType.BACK)
                    elif sout < din:
                        fun(node, succ, DFSEdgeType.CROSS)
                else:
                    fun(node, succ, DFSEdgeType.FORWARD)
            else:
                fun(node, succ, DFSEdgeType.TREE)
                if not (stop_verts and succ in stop_verts):
                    self._foreachedge_cfg(fun, backtrackfun, node, succ, counter)

        counter.counter += 1
        nddata.outnum = counter.counter
        if backtrackfun:
            backtrackfun(prevnode, node)

    # FIXME: we don't need to duplicate the code, just need to unify the API for CFG and CFA
    def _foreachedge_cfa(self, fun, backtrackfun, backtrackedge, loc, counter):
        getdata = self._getdata
        counter.counter += 1

        nddata = getdata(loc)
        nddata.visited = True
        nddata.innum = counter.counter

        only_vertices = self._vertices
        stop_verts = self._stop_vertices
        for succedge in loc.successors():
            succ = succedge.target()
            assert succedge.source() is loc

            if only_vertices and succ not in only_vertices:
                continue

            succdata = getdata(succ)
            if succdata.visited:
                sin = succdata.innum
                din = nddata.innum
                assert sin is not None

                if sin < din:
                    sout = succdata.outnum
                    if sout is None:
                        fun(succedge, DFSEdgeType.BACK)
                    elif sout < din:
                        fun(succedge, DFSEdgeType.CROSS)
                else:
                    fun(succedge, DFSEdgeType.FORWARD)
            else:
                fun(succedge, DFSEdgeType.TREE)
                if not (stop_verts and succ in stop_verts):
                    self._foreachedge_cfa(fun, backtrackfun, succedge, succ, counter)

        counter.counter += 1
        nddata.outnum = counter.counter
        if backtrackfun:
            backtrackfun(backtrackedge)

    def dump(self, graph, outfl=None):
        out = None
        if outfl is None:
            from sys import stdout

            out = stdout
        else:
            if isinstance(outfl, str):
                out = open(out, "w")
            else:
                assert not outfl.closed, "Invalid stream"
                out = outfl
        assert out, "Do not have the output stream"
        assert not out.closed, "Invalid stream"

        def edgecol(val):
            if val == DFSEdgeType.TREE:
                return "green"
            elif val == DFSEdgeType.BACK:
                return "red"
            elif val == DFSEdgeType.FORWARD:
                return "blue"
            elif val == DFSEdgeType.CROSS:
                return "orange"
            return "black"

        def dumpdot(start, end, edgetype):
            print(
                '  {0} -> {1} [label="{2}", color="{3}"]'.format(
                    _get_id(start),
                    _get_id(end),
                    DFSEdgeType.tostr(edgetype),
                    edgecol(edgetype),
                ),
                file=out,
            )

        print("digraph {", file=out)

        # dump nodes
        if isinstance(graph, CFA):
            nodes = graph.locations()
        else:
            nodes = graph.get_nodes()
        for n in nodes:
            print("  {0}".format(_get_id(n)), file=out)

        # dump edges
        print("", file=out)
        if isinstance(graph, CFA):
            self.foreachedge(
                graph.entry(), lambda e, t: dumpdot(e.source(), e.target(), t)
            )
        else:
            self.foreachedge(graph.entry(), dumpdot)

        # dump the in/out counters
        for n in nodes:
            print(
                '  {0} [label="{0}\\nin,out = {1}, {2}"]'.format(
                    _get_id(n),
                    self._getdata(n).innum,
                    self._getdata(n).outnum,
                ),
                file=out,
            )

        print("}", file=out)
        if isinstance(outfl, str):
            out.close()  # we opened it
