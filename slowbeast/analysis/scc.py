# Taken from:
# https://raw.githubusercontent.com/alviano/python/master/rewrite_aggregates/scc.py
# Licensed under GPLv3: https://github.com/alviano/python/blob/master/LICENSE


def strongly_connected_components_path(vertices, edges):
    """
    Find the strongly connected components of a directed graph.

    Uses a recursive linear-time algorithm described by Gabow [1]_ to find all
    strongly connected components of a directed graph.

    Parameters
    ----------
    vertices : iterable
        A sequence or other iterable of vertices.  Each vertex should be
        hashable.

    edges : mapping
        Dictionary (or mapping) that maps each vertex v to an iterable of the
        vertices w that are linked to v by a directed edge (v, w).

    Returns
    -------
    components : iterator
        An iterator that yields sets of vertices.  Each set produced gives the
        vertices of one strongly connected component.

    Raises
    ------
    RuntimeError
        If the graph is deep enough that the algorithm exceeds Python's
        recursion limit.

    Notes
    -----
    The algorithm has running time proportional to the total number of vertices
    and edges.  It's practical to use this algorithm on graphs with hundreds of
    thousands of vertices and edges.

    The algorithm is recursive.  Deep graphs may cause Python to exceed its
    recursion limit.

    `vertices` will be iterated over exactly once, and `edges[v]` will be
    iterated over exactly once for each vertex `v`.  `edges[v]` is permitted to
    specify the same vertex multiple times, and it's permissible for `edges[v]`
    to include `v` itself.  (In graph-theoretic terms, loops and multiple edges
    are permitted.)

    References
    ----------
    .. [1] Harold N. Gabow, "Path-based depth-first search for strong and
       biconnected components," Inf. Process. Lett. 74 (2000) 107--114.

    .. [2] Robert E. Tarjan, "Depth-first search and linear graph algorithms,"
       SIAM J.Comput. 1 (2) (1972) 146--160.

    Examples
    --------
    Example from Gabow's paper [1]_.

    >>> vertices = [1, 2, 3, 4, 5, 6]
    >>> edges = {1: [2, 3], 2: [3, 4], 3: [], 4: [3, 5], 5: [2, 6], 6: [3, 4]}
    >>> for scc in strongly_connected_components_path(vertices, edges):
    ...     print(scc)
    ...
    set([3])
    set([2, 4, 5, 6])
    set([1])

    Example from Tarjan's paper [2]_.

    >>> vertices = [1, 2, 3, 4, 5, 6, 7, 8]
    >>> edges = {1: [2], 2: [3, 8], 3: [4, 7], 4: [5],
    ...          5: [3, 6], 6: [], 7: [4, 6], 8: [1, 7]}
    >>> for scc in  strongly_connected_components_path(vertices, edges):
    ...     print(scc)
    ...
    set([6])
    set([3, 4, 5, 7])
    set([8, 1, 2])

    """
    identified = set()
    stack = []
    index = {}
    boundaries = []

    def dfs(v):
        index[v] = len(stack)
        stack.append(v)
        boundaries.append(index[v])

        for w in edges[v]:
            if w not in index:
                # For Python >= 3.3, replace with "yield from dfs(w)"
                for scc in dfs(w):
                    yield scc
            elif w not in identified:
                while index[w] < boundaries[-1]:
                    boundaries.pop()

        if boundaries[-1] == index[v]:
            boundaries.pop()
            scc = set(stack[index[v] :])
            del stack[index[v] :]
            identified.update(scc)
            yield scc

    for v in vertices:
        if v not in index:
            # For Python >= 3.3, replace with "yield from dfs(v)"
            for scc in dfs(v):
                yield scc


def strongly_connected_components_tree(vertices, edges):
    """
    Find the strongly connected components of a directed graph.

    Uses a recursive linear-time algorithm described by Tarjan [2]_ to find all
    strongly connected components of a directed graph.

    Parameters
    ----------
    vertices : iterable
        A sequence or other iterable of vertices.  Each vertex should be
        hashable.

    edges : mapping
        Dictionary (or mapping) that maps each vertex v to an iterable of the
        vertices w that are linked to v by a directed edge (v, w).

    Returns
    -------
    components : iterator
        An iterator that yields sets of vertices.  Each set produced gives the
        vertices of one strongly connected component.

    Raises
    ------
    RuntimeError
        If the graph is deep enough that the algorithm exceeds Python's
        recursion limit.

    Notes
    -----
    The algorithm has running time proportional to the total number of vertices
    and edges.  It's practical to use this algorithm on graphs with hundreds of
    thousands of vertices and edges.

    The algorithm is recursive.  Deep graphs may cause Python to exceed its
    recursion limit.

    `vertices` will be iterated over exactly once, and `edges[v]` will be
    iterated over exactly once for each vertex `v`.  `edges[v]` is permitted to
    specify the same vertex multiple times, and it's permissible for `edges[v]`
    to include `v` itself.  (In graph-theoretic terms, loops and multiple edges
    are permitted.)

    References
    ----------
    .. [1] Harold N. Gabow, "Path-based depth-first search for strong and
       biconnected components," Inf. Process. Lett. 74 (2000) 107--114.

    .. [2] Robert E. Tarjan, "Depth-first search and linear graph algorithms,"
       SIAM J.Comput. 1 (2) (1972) 146--160.

    Examples
    --------
    Example from Gabow's paper [1]_.

    >>> vertices = [1, 2, 3, 4, 5, 6]
    >>> edges = {1: [2, 3], 2: [3, 4], 3: [], 4: [3, 5], 5: [2, 6], 6: [3, 4]}
    >>> for scc in strongly_connected_components_tree(vertices, edges):
    ...     print(scc)
    ...
    set([3])
    set([2, 4, 5, 6])
    set([1])

    Example from Tarjan's paper [2]_.

    >>> vertices = [1, 2, 3, 4, 5, 6, 7, 8]
    >>> edges = {1: [2], 2: [3, 8], 3: [4, 7], 4: [5],
    ...          5: [3, 6], 6: [], 7: [4, 6], 8: [1, 7]}
    >>> for scc in  strongly_connected_components_tree(vertices, edges):
    ...     print(scc)
    ...
    set([6])
    set([3, 4, 5, 7])
    set([8, 1, 2])

    """
    identified = set()
    stack = []
    index = {}
    lowlink = {}

    def dfs(v):
        index[v] = len(stack)
        stack.append(v)
        lowlink[v] = index[v]

        for w in edges[v]:
            if w not in index:
                # For Python >= 3.3, replace with "yield from dfs(w)"
                for scc in dfs(w):
                    yield scc
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w not in identified:
                lowlink[v] = min(lowlink[v], lowlink[w])

        if lowlink[v] == index[v]:
            scc = set(stack[index[v] :])
            del stack[index[v] :]
            identified.update(scc)
            yield scc

    for v in vertices:
        if v not in index:
            # For Python >= 3.3, replace with "yield from dfs(v)"
            for scc in dfs(v):
                yield scc


def strongly_connected_components_iterative(vertices, edges):
    """
    This is a non-recursive version of strongly_connected_components_path.
    See the docstring of that function for more details.

    Examples
    --------
    Example from Gabow's paper [1]_.

    >>> vertices = [1, 2, 3, 4, 5, 6]
    >>> edges = {1: [2, 3], 2: [3, 4], 3: [], 4: [3, 5], 5: [2, 6], 6: [3, 4]}
    >>> for scc in strongly_connected_components_iterative(vertices, edges):
    ...     print(scc)
    ...
    set([3])
    set([2, 4, 5, 6])
    set([1])

    Example from Tarjan's paper [2]_.

    >>> vertices = [1, 2, 3, 4, 5, 6, 7, 8]
    >>> edges = {1: [2], 2: [3, 8], 3: [4, 7], 4: [5],
    ...          5: [3, 6], 6: [], 7: [4, 6], 8: [1, 7]}
    >>> for scc in  strongly_connected_components_iterative(vertices, edges):
    ...     print(scc)
    ...
    set([6])
    set([3, 4, 5, 7])
    set([8, 1, 2])

    """
    identified = set()
    stack = []
    index = {}
    boundaries = []

    for v in vertices:
        if v not in index:
            to_do = [("VISIT", v)]
            while to_do:
                operation_type, v = to_do.pop()
                if operation_type == "VISIT":
                    index[v] = len(stack)
                    stack.append(v)
                    boundaries.append(index[v])
                    to_do.append(("POSTVISIT", v))
                    # We reverse to keep the search order identical to that of
                    # the recursive code;  the reversal is not necessary for
                    # correctness, and can be omitted.
                    to_do.extend(reversed([("VISITEDGE", w) for w in edges[v]]))
                elif operation_type == "VISITEDGE":
                    if v not in index:
                        to_do.append(("VISIT", v))
                    elif v not in identified:
                        while index[v] < boundaries[-1]:
                            boundaries.pop()
                else:
                    # operation_type == 'POSTVISIT'
                    if boundaries[-1] == index[v]:
                        boundaries.pop()
                        scc = set(stack[index[v] :])
                        del stack[index[v] :]
                        identified.update(scc)
                        yield scc


class StronglyConnectedComponents:
    def __init__(self, G):
        """
        G - Directed graph, either CFG or CFA
        """
        self._graph = G

    def __iter__(self):
        G = self._graph
        # TODO: make the functions use directly the methods
        edges = {l: [succ.target() for succ in l.successors()] for l in G.locations()}
        yield from strongly_connected_components_iterative(G.locations(), edges)


class SCCCondensation:
    class SCC:
        def __init__(self, nodes):
            assert len(nodes) >= 1
            self.nodes = nodes
            self._successors = set()
            self._predecessors = set()

        def successors(self):
            return self._successors

        def predecessors(self):
            return self._predecessors

        def has_successors(self):
            return len(self._successors) > 0

        def is_trivial(self):
            return len(self.nodes) <= 1

    def _add_edges(self):
        for scc in self.sccs:
            for n in scc.nodes:
                for s in n.successors():
                    t = self._node_to_scc[s.target()]
                    scc._successors.add(t)
                    t._predecessors.add(scc)

    def __init__(self, G):
        """G - Directed graph, either CFG or CFA"""

        self._graph = G
        self._node_to_scc = {}
        self.sccs = []
        for scc in StronglyConnectedComponents(G):
            S = SCCCondensation.SCC(scc)
            self.sccs.append(S)
            for n in scc:
                assert self._node_to_scc.get(n) is None
                self._node_to_scc[n] = S
        self._add_edges()

    def roots(self):
        return [s for s in self.sccs if not s.predecessors()]

    def get(self, n):
        return self._node_to_scc[n]
