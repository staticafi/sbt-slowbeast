from slowbeast.analysis.callgraph import CallGraph
from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.dfs import DFSEdgeType, DFSVisitor
from slowbeast.analysis.loops import compute_loops


class ProgramStructure:
    """
    Class that contains information about control-flow and call structure
    of the program.
    """

    def __init__(self, prog, new_dbg_file=None):
        self.new_dbg_file = new_dbg_file
        callgraph = CallGraph(prog)
        if __debug__:
            with new_dbg_file("callgraph-full.txt") as f:
                callgraph.dump(f)

        callgraph.prune_unreachable(prog.entry())
        if __debug__:
            with new_dbg_file("callgraph.txt") as f:
                callgraph.dump(f)

        self.callgraph = callgraph
        cfas = CFA.from_program(prog, callgraph)
        if __debug__:
            for fun, cfa in cfas.items():
                with self.new_dbg_file(f"cfa.{fun.name()}.dot") as f:
                    cfa.dump(f)
        self.cfas = cfas
        # gather mapping from calls to call-edges
        self.calls = {
            e.elems()[0]: e for cfa in cfas.values() for e in cfa.edges() if e.is_call()
        }
        self.rets = {
            e.elems()[0]: e for cfa in cfas.values() for e in cfa.edges() if e.is_ret()
        }
        # entry location of the whole program
        self.entry_loc = cfas[prog.entry()].entry()

        self.loops = None

    def get_loop(self, loc):
        self._get_loops()
        return self.loops.get(loc)

    def get_loop_headers(self):
        # FIXME: do it separately for each CFA
        self._get_loops()
        return self.loops.keys()

    def _get_loops(self):
        loops = self.loops
        if loops is None:
            loops = {}
            for cfa in self.cfas.values():
                loops.update(compute_loops(cfa))
            self.loops = loops


def find_loop_headers(cfas, new_output_file=None):
    headers = set()

    def processedge(edge, dfstype):
        if dfstype == DFSEdgeType.BACK:
            headers.add(edge.target())

    for cfa in cfas.values():
        for loc, L in compute_loops(cfa).items():
            print(loc)
            print(L)

        if __debug__:
            if new_output_file:
                with new_output_file(f"{cfa.fun().name()}-dfs.dot") as f:
                    DFSVisitor().dump(cfa, f)

        DFSVisitor().foreachedge(cfa.entry(), processedge)

    return headers
