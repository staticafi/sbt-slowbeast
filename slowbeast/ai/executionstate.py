from slowbeast.core.executionstate import ExecutionState

# from slowbeast.domains.sign import ZODomain
from slowbeast.domains.signul import SignULDomain as Domain
from slowbeast.domains.concrete import ConcreteVal


class AbstractState(ExecutionState):
    """State of abstract interpretation"""

    # XXX do not store warnings in the state but keep them in a map in the interpreter or so?
    # FIXME: move this to the super class?
    __slots__ = (
        "_executor",
        "_id",
    )
    _statesCounter = 0

    def __init__(self, executor, pc, m):
        super().__init__(pc, m)

        AbstractState._statesCounter += 1
        self._id = AbstractState._statesCounter

        self._executor = executor

    def get_id(self):
        return self._id

    def is_sat(self, *e):
        return Domain.may_be_true(Domain.conjunction(*e))

    def eval(self, v):
        if isinstance(v, ConcreteVal):
            return Domain.lift(v)
        value = self.get(v)
        if value is None:
            raise RuntimeError("Use of uninitialized/unknown variable {0}".format(v))
        return value

    def is_feasible(self):
        """
        Solve the PC and return True if it is sat. Handy in the cases
        when the state is constructed manually.
        """
        return True

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = AbstractState(self._executor, self.pc, self.memory)
        super()._copy_to(new)  # cow copy of super class

        return new

    def concretize(self, *e):
        return (Domain.concretize(x) for x in e)

    def nondets(self):
        return ()

    def __hash__(self):
        return self.memory.__hash__() ^ hash(self.pc) ^ hash(self.status)
