from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.executionstate import LazySEState
from slowbeast.util.debugging import ldbgv
from .bsestate import BSEState
from .memorymodel import BSEMemoryModel


class Executor(PathExecutor):
    """
    Symbolic Executor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(self, program, solver, opts, memorymodel=None):
        super().__init__(program, solver, opts, memorymodel or BSEMemoryModel(opts))

    def create_state(self, pc=None, m=None):
        """
        Overridden method for creating states.
        Since the path may not be initial, we must use states
        that are able to lazily create unknown values
        """
        if m is None:
            m = self.get_memory_model().create_memory()
        s = BSEState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s

    def execute_edge(self, states, edge, invariants=None):
        """
        states - pre-condition states (execute from these states)
        """
        assert all(map(lambda s: isinstance(s, LazySEState), states))

        ldbgv(" -- {0} --", (edge,))

        source, target = edge.source(), edge.target()
        ready, nonready = states, []
        # annotations before taking the edge (proably an invariant)
        execannot = self.execute_annotations
        # annotations before source
        locannot = invariants.get(source) if invariants else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_ret():
            # we handle passing return values manually in BSE, so just skip the return
            ldbgv("Skipping ret edge: {0}", (edge[0],))
        elif edge.is_call() and not edge.called_function().is_undefined():
            fn = edge.called_function().name()
            for s in ready:
                s.set_killed(f"Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        # annotations before target
        locannot = invariants.get(target) if invariants else None
        if locannot:
            assert all(
                map(lambda a: not a.is_assert(), locannot)
            ), f"An invariant is assertion: {locannot}"
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after target

        return ready, nonready

    def execute_bse_path(self, states, path, invariants=None):
        badstates = []
        execute_edge = self.execute_edge
        for edge in path:
            states, tmpbad = execute_edge(states, edge, invariants)
            badstates.extend(tmpbad)
        return states, badstates

    #
    # def execute_annotated_edge(
    #     self,
    #     states,
    #     edge,
    #     pre=None,
    #     post=None,
    #     annot_before_loc=None,
    #     annot_after_loc=None,
    # ):
    #     """
    #     states - pre-condition states (execute from these states)
    #     """
    #     assert all(map(lambda s: isinstance(s, LazySEState), states))
    #
    #     source, target = edge.source(), edge.target()
    #     ready, nonready = states, []
    #     # annotations before taking the edge (proably an invariant)
    #     execannot = self.execute_annotations
    #     if pre:
    #         ready, tu = execannot(ready, pre)
    #         nonready += tu
    #     # annotations before source
    #     locannot = annot_before_loc(source) if annot_before_loc else None
    #     if locannot:
    #         ready, tu = execannot(ready, locannot)
    #         nonready += tu
    #     # annotations after source
    #     locannot = annot_after_loc(source) if annot_after_loc else None
    #     if locannot:
    #         ready, tu = execannot(ready, locannot)
    #         nonready += tu
    #
    #     # execute the instructions from the edge
    #     if edge.is_assume():
    #         ready, tmpnonready = self._exec_assume_edge(ready, edge)
    #         nonready += tmpnonready
    #     elif edge.is_call() and not edge.called_function().is_undefined():
    #         fn = edge.called_function().name()
    #         for s in ready:
    #             s.set_terminated(f"Called function {fn} on intraprocedural path")
    #             return [], nonready + ready
    #         raise NotImplementedError("Call edges not implemented")
    #     else:
    #         ready, tmpnonready = self.execute_seq(ready, edge)
    #         nonready += tmpnonready
    #
    #     # annotations before target
    #     locannot = annot_before_loc(target) if annot_before_loc else None
    #     if locannot:
    #         ready, tu = execannot(ready, locannot)
    #         nonready += tu
    #     # annotations after target
    #     locannot = annot_after_loc(target) if annot_after_loc else None
    #     if locannot:
    #         ready, tu = execannot(ready, locannot)
    #         nonready += tu
    #     if post:
    #         ready, tu = execannot(ready, post)
    #         nonready += tu
    #
    #     return ready, nonready
