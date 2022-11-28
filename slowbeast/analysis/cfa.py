from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import Branch, Call, Assert, Return


class CFA:
    """Control flow automaton"""

    class Location:
        _counter = 0
        __slots__ = "_id", "_cfa", "_elem", "_successors", "_predecessors"

        def __init__(self, cfa, elem=None):
            CFA.Location._counter += 1
            self._id = CFA.Location._counter
            self._elem = elem
            self._cfa = cfa
            self._successors = []
            self._predecessors = []

        def successors(self):
            return self._successors

        def predecessors(self):
            return self._predecessors

        def has_predecessors(self):
            return len(self._predecessors) > 0

        def has_successors(self):
            return len(self._successors) > 0

        def is_branching(self):
            return len(self._successors) > 1

        def elem(self):
            return self._elem

        def cfa(self):
            return self._cfa

        def id(self):
            return self._id

        def __eq__(self, oth):
            return self._id == oth._id

        def __hash__(self):
            return self._id

        def __lt__(self, oth):
            return self._id < oth._id

        def __repr__(self):
            return f"L{self._id}"

    class Edge:
        __slots__ = "_source", "_target", "_type", "_elems", "_orig_elem"

        REGULAR = 1
        ASSUME = 2
        CALL = 4
        RET = 5
        SUMMARY = 6

        def __init__(self, ty, s, t, elem=None):
            self._type = ty
            self._source = s
            self._target = t
            # the original program element from which this edge was created
            self._orig_elem = elem
            self._elems = []

        def source(self):
            return self._source

        def target(self):
            return self._target

        def successors(self):
            return self._target.successors()

        def predecessors(self):
            return self._source.predecessors()

        def has_predecessors(self):
            return len(self._source._predecessors) > 0

        def has_successors(self):
            return len(self._target._successors) > 0

        def cfa(self):
            assert self._target._cfa is self._source._cfa
            return self._source._cfa

        def type(self):
            return self._type

        def is_assume(self):
            return self._type == CFA.Edge.ASSUME

        def is_call(self):
            return self._type == CFA.Edge.CALL

        def is_ret(self):
            return self._type == CFA.Edge.RET

        def is_summary(self):
            return self._type == CFA.Edge.SUMMARY

        def add_elem(self, e):
            self._elems.append(e)

        def elems(self):
            return self._elems

        def get_elem(self, idx):
            """Get element on index 'idx' or None if such elem does not exists"""
            if idx < len(self._elems):
                return self._elems[idx]
            return None

        def is_noop(self):
            return len(self._elems) == 0

        def __len__(self):
            return len(self._elems)

        def __repr__(self):
            return f"{self._source} -> {self._target}"

        def __iter__(self):
            return self._elems.__iter__()

        def __getitem__(self, item):
            return self._elems.__getitem__(item)

    class AssumeEdge(Edge):
        __slots__ = "_is_true"

        def __init__(self, s, t, elem, istrue):
            super().__init__(CFA.Edge.ASSUME, s, t, elem)
            self._is_true = istrue

        def assume_true(self):
            return self._is_true

        def assume_false(self):
            return not self._is_true

    class SummaryEdge(Edge):
        def __init__(self, s, t, elem):
            super().__init__(CFA.Edge.SUMMARY, s, t, elem)
            self._elems.append(elem)

        def summary_of(self):
            return self._orig_elem

    class CallEdge(Edge):
        def __init__(self, s, t, callinst):
            super().__init__(CFA.Edge.CALL, s, t, callinst)
            self._elems.append(callinst)

        def call(self):
            return self._elems[0]

        def called_function(self):
            return self._elems[0].called_function()

    class RetEdge(Edge):
        def __init__(self, s, t, retinst):
            super().__init__(CFA.Edge.RET, s, t, retinst)
            self._elems.append(retinst)

        def ret(self):
            return self._elems[0]

    def __init__(self, fun: Function):
        assert isinstance(fun, Function)
        self._fun = fun
        self._locs = []
        self._edges = []
        self._entry = None
        self._errors = set()

        self._build(fun)

    def fun(self):
        return self._fun

    def entry(self):
        return self._entry

    def edges(self):
        return self._edges

    def locations(self):
        return self._locs

    def errors(self):
        return self._errors

    def add_error_loc(self, l):
        self._errors.add(l)

    def is_init(self, l):
        if isinstance(l, CFA.Edge):
            return l.source() == self._entry
        assert isinstance(l, CFA.Location), l
        return l == self._entry

    def is_err(self, l):
        assert isinstance(l, CFA.Location), l
        return l in self._errors

    def from_program(prog: Program, callgraph=None):
        """
        Build CFAs from program and populate call edges
        """
        assert isinstance(prog, Program)
        # build a CFA for each function and then connect them with call edges
        cfas = {fun: CFA(fun) for fun in prog.funs() if not fun.is_undefined()}
        # FIXME: populate call edges
        return cfas

    def create_loc(self, elem=None):
        loc = CFA.Location(self, elem)
        self._locs.append(loc)
        return loc

    def _add_edge(self, e: Edge):
        e._target._predecessors.append(e)
        e._source._successors.append(e)
        # do we need this?
        self._edges.append(e)

    def _build(self, fun: Function):
        assert isinstance(fun, Function)
        locs = {}
        # create locations
        for B in fun.bblocks():
            loc1, loc2 = self.create_loc(B), self.create_loc(B)

            e = CFA.Edge(CFA.Edge.REGULAR, loc1, loc2, B)
            for i in B.instructions():
                # break on calls
                if isinstance(i, Branch):
                    break  # this is a last inst and we handle it later
                if isinstance(i, Call):
                    if e.is_noop():
                        e = CFA.CallEdge(e.source(), e.target(), i)  # replace the edge
                    else:
                        self._add_edge(e)
                        assert not e.is_noop()
                        # create the call edge
                        tmp = self.create_loc(B)
                        e = CFA.CallEdge(loc2, tmp, i)
                        loc2 = tmp
                    self._add_edge(e)
                    assert not e.is_noop()

                    # create a new edge
                    tmp = self.create_loc(B)
                    e = CFA.Edge(CFA.Edge.REGULAR, loc2, tmp, B)
                    loc2 = tmp
                elif isinstance(i, Return):
                    if e.is_noop():
                        e = CFA.RetEdge(e.source(), e.target(), i)  # replace the edge
                    else:
                        self._add_edge(e)
                        assert not e.is_noop()
                        # create the call edge
                        tmp = self.create_loc(B)
                        e = CFA.RetEdge(loc2, tmp, i)
                        loc2 = tmp
                    assert not e.is_noop()
                # break on assert
                elif isinstance(i, Assert):
                    err = self.create_loc(i)
                    self.add_error_loc(err)
                    if e.is_noop():
                        e = CFA.AssumeEdge(
                            e.source(), e.target(), i, True
                        )  # replace the edge
                        erre = CFA.AssumeEdge(e.source(), err, i, False)
                    else:
                        self._add_edge(e)
                        assert not e.is_noop()
                        # create the assert edges
                        tmp = self.create_loc(B)
                        e = CFA.AssumeEdge(loc2, tmp, i, True)
                        erre = CFA.AssumeEdge(loc2, err, i, False)
                        loc2 = tmp
                    self._add_edge(e)
                    self._add_edge(erre)
                    cond = i.condition()
                    e.add_elem(cond)
                    erre.add_elem(cond)

                    # create a new edge
                    tmp = self.create_loc(B)
                    e = CFA.Edge(CFA.Edge.REGULAR, loc2, tmp, B)
                    loc2 = tmp
                else:
                    e.add_elem(i)

            self._add_edge(e)
            locs[B] = (loc1, loc2)

        # create CFG edges
        for B in fun.bblocks():
            br = B.last()
            l = locs.get(B)
            if not isinstance(br, Branch):
                continue  # these were handled

            tsucc = locs[br.true_successor()][0]
            fsucc = locs[br.false_successor()][0]
            if tsucc is fsucc:
                self._add_edge(CFA.AssumeEdge(l[1], tsucc, br, True))
            else:
                # FIXME: assume True/False
                cond = br.condition()
                e = CFA.AssumeEdge(l[1], tsucc, br, True)
                e.add_elem(cond)
                self._add_edge(e)
                e = CFA.AssumeEdge(l[1], fsucc, br, False)
                e.add_elem(cond)
                self._add_edge(e)

        self._entry = locs.get(fun.bblock(0))[0]
        assert self._entry, "Do not have entry loc"

    def dump(self, stream):
        print(f"digraph CFA_{self._fun.name()} {{", file=stream)
        print(f'  label="{self._fun.name()}"', file=stream)
        entry = self._entry
        errs = self._errors
        for l in self._locs:
            if l is entry:
                print(f"{l} [color=blue]", file=stream)
            elif l in errs:
                print(f"{l} [color=red penwidth=2]", file=stream)
            else:
                print(l, file=stream)
        for e in self._edges:
            label = "\\l".join(map(lambda s: str(s).replace('"', '\\"'), e._elems))
            if e.is_assume() and label:
                label = f"{'!' if e.assume_false() else ''}[{label}]"
            if e.is_call():
                style = "color=blue"
            elif e.is_assume():
                style = "color=orange"
            else:
                style = ""
            print(e, f' [label="{label}", {style}]', file=stream)
        print("}", file=stream)
