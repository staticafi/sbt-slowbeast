from slowbeast.solvers.solver import IncrementalSolver
from slowbeast.symexe.statesset import StatesSet, complement, intersection


class InductiveSet:
    """
    Class representing an inductive set that we derive for a loop header.
    """

    def __init__(self, initial_set: StatesSet = None):
        assert initial_set is None or isinstance(initial_set, StatesSet)
        if initial_set:
            self.I = initial_set
            cI = IncrementalSolver()
            cI.add(complement(initial_set).as_expr())
            self.cI = cI
            # track all added sets
            self.sets = [initial_set]
        else:
            self.I = None
            self.cI = IncrementalSolver()
            self.sets = []

    def add(self, elem):
        self.sets.append(elem)
        I = self.I
        cI = self.cI
        expr = elem.as_expr()
        if cI.is_sat(expr):
            assert I is None or not intersection(complement(I), elem).is_empty()
            # the elem is not a subset of current set
            if I:
                I.add(elem)
            else:
                self.I = elem
            cI.add(complement(elem).as_expr())

    def includes(self, elem):
        if isinstance(elem, InductiveSet):
            elem = elem.I
        # intersection(complement(self.I), elem).is_empty()
        return self.cI.is_sat(elem.as_expr()) is False

    def includes_any(self, *elems):
        is_sat = self.cI.is_sat
        return any(
            map(
                lambda e: is_sat((e.I if isinstance(e, InductiveSet) else e).as_expr())
                is False,
                elems,
            )
        )

    def __repr__(self):
        return self.I.__repr__()
