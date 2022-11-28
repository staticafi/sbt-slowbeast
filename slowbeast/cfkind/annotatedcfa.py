from slowbeast.util.debugging import print_highlight
from slowbeast.analysis.cfa import CFA


def _loc_id(loc):
    if isinstance(loc, int):
        return loc
    return loc.id()


def _edge_str(edge, ab, aa):
    return "({0}{1}{2} -> {3}{4}{5})".format(
        "@ " if ab.get(_loc_id(edge.source())) else "",
        edge.source(),
        " @" if aa.get(_loc_id(edge.source())) else "",
        "@ " if ab.get(_loc_id(edge.target())) else "",
        edge.target(),
        " @" if aa.get(_loc_id(edge.source())) else "",
    )


def _str_loc(loc, ab, aa):
    return "{0}{1}{2}".format(
        "@ " if ab.get(_loc_id(loc)) else "",
        loc,
        " @" if aa.get(_loc_id(loc)) else "",
    )


def _copy_annots(dst, src):
    # FIXME: do cow?
    dst._annot_after_loc = src._annot_after_loc.copy()
    dst._annot_before_loc = src._annot_before_loc.copy()
    dst._annot_before = src._annot_before.copy()
    dst._annot_after = src._annot_after.copy()


class AnnotatedCFAPath:
    """
    A CFA path that contains annotations. These annotations can put assumptions
    on values or similar. The annotations are a special set of instructions that
    are executed on given places.
    """

    __slots__ = (
        "_edges",
        "_annot_after_loc",
        "_annot_before_loc",
        "_annot_before",
        "_annot_after",
    )

    def __init__(self, edges=None):
        self._edges = edges or []
        self._annot_after_loc = {}
        self._annot_before_loc = {}
        self._annot_before = []
        self._annot_after = []

    def get_first_inst(self):
        edges = self._edges
        if edges:
            for e in edges:
                elems = e.elems()
                if elems:  # edge may be empty
                    return elems[0]
        return None

    def first_assume_edge_idx(self):
        edges = self._edges
        if edges:
            for idx, e in enumerate(edges):
                if e.is_assume():
                    return idx
        return None

    def first_assume_edge(self):
        idx = self.first_assume_edge_idx()
        if idx is not None:
            return self._edges[idx]
        return None

    def last_assume_edge_idx(self):
        edges = self._edges
        if edges:
            for idx in range(-1, -(len(edges) + 1), -1):
                if edges[idx].is_assume():
                    return idx
        return None

    def last_edge_of_idx(self, elem):
        if not hasattr(elem, "__iter__"):
            elem = (elem,)
        edges = self._edges
        for idx in range(-1, -(len(edges) + 1), -1):
            if edges[idx] in elem:
                return idx
        return None

    def last_loc_of_idx(self, elem):
        if not hasattr(elem, "__iter__"):
            elem = (elem,)
        edges = self._edges
        for idx in range(-1, -(len(edges) + 1), -1):
            e = edges[idx]
            if e.target() in elem or e.source() in elem:
                return idx
        return None

    def edges(self):
        return self._edges

    def num_of_occurences(self, elem):
        n = 0
        if isinstance(elem, CFA.Edge):
            for e in self._edges:
                if e == elem:
                    n += 1
        else:
            assert isinstance(elem, CFA.Location), elem
            for e in self._edges:
                if e.source() == elem:
                    n += 1
                if e.target() == elem:
                    n += 1
        return n

    def last_idx_of(self, elem):
        edges = self._edges
        if isinstance(elem, CFA.Edge):
            for idx in range(-1, -(len(edges) + 1), -1):
                if edges[idx] == elem:
                    return idx
        else:
            for idx in range(-1, -(len(edges) + 1), -1):
                if edges[idx].target() == elem:
                    return idx
                if edges[idx].source() == elem:
                    return idx
        return None

    def __getitem__(self, item):
        return self._edges.__getitem__(item)

    def __iter__(self):
        return self._edges.__iter__()

    def __lt__(self, rhs):
        return len(self._edges) < len(rhs._edges)

    def first_loc(self):
        return self._edges[0].source()

    def last_loc(self):
        return self._edges[-1].target()

    def annot_after_loc(self, loc):
        return self._annot_after_loc.get(_loc_id(loc))

    def annot_before_loc(self, loc):
        return self._annot_before_loc.get(_loc_id(loc))

    def annot_before(self):
        return self._annot_before

    def annot_after(self):
        return self._annot_after

    def add_annot_after(self, annot):
        self._annot_after.append(annot)

    def add_annot_before(self, annot):
        self._annot_before.append(annot)

    def add_annot_after_loc(self, annot, loc):
        self._annot_after_loc.setdefault(_loc_id(loc), []).append(annot)

    def add_annot_before_loc(self, annot, loc):
        self._annot_before_loc.setdefault(_loc_id(loc), []).append(annot)

    def subpath(self, start, end=None):
        if end is None:
            n = AnnotatedCFAPath(self._edges[start:])
        else:
            n = AnnotatedCFAPath(self._edges[start : end + 1])
        _copy_annots(n, self)
        return n

    def copy(self):
        n = AnnotatedCFAPath(self._edges.copy())
        _copy_annots(n, self)
        return n

    def copyandprepend(self, edges):
        # FIXME: this is not efficient...
        if not isinstance(edges, list):
            edges = [edges]
        n = AnnotatedCFAPath(edges + self._edges)
        _copy_annots(n, self)
        return n

    def copyandappend(self, edges):
        # FIXME: this is not efficient...
        if not isinstance(edges, list):
            edges = [edges]
        n = AnnotatedCFAPath(self._edges + edges)
        _copy_annots(n, self)
        return n

    def copyandsetpath(self, locs):
        n = AnnotatedCFAPath(locs)
        _copy_annots(n, self)
        return n

    def __len__(self):
        return len(self._edges)

    def dump(self):
        ab, aa = self._annot_before_loc, self._annot_after_loc
        print_highlight(
            "{0}{1}{2}".format(
                "[A] " if self._annot_before else "",
                "".join(map(lambda e: _edge_str(e, ab, aa), self.edges())),
                " [A]" if self._annot_after else "",
            ),
            words={"[A]": "green"},
        )

    def __repr__(self):
        ab, aa = self._annot_before_loc, self._annot_after_loc
        if len(self) < 13:
            return "{0}{1} -> {2}{3}".format(
                "[A] " if self._annot_before else "",
                " -> ".join(map(lambda e: _str_loc(e.source(), ab, aa), self._edges)),
                _str_loc(self._edges[-1].target(), ab, aa),
                " [A]" if self._annot_after else "",
            )

        N = 5
        return "{0}{1} ... ({2} edges) ... {3} -> {4}{5}".format(
            "[A] " if self._annot_before else "",
            " -> ".join(
                map(
                    lambda e: _str_loc(e.source(), ab, aa),
                    (ed for n, ed in enumerate(self._edges) if n < N),
                )
            ),
            len(self) - N,
            _str_loc(self._edges[-1].source(), ab, aa),
            _str_loc(self._edges[-1].target(), ab, aa),
            " [A]" if self._annot_after else "",
        )
