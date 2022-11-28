from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.util.debugging import print_stderr, print_stdout, dbg, ldbgv

from slowbeast.analysis.cfa import CFA
from slowbeast.symexe.symbolicexecution import (
    SymbolicExecutor as SymbolicInterpreter,
)
from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.cfkind import KindSEOptions


def report_state(stats, n, fn=print_stderr):
    if n.has_error():
        if fn:
            fn(
                "state {0}: {1}, {2}".format(n.get_id(), n.pc, n.get_error()),
                color="RED",
            )
        stats.errors += 1
    elif n.was_killed():
        if fn:
            fn(n.status_detail(), prefix="KILLED STATE: ", color="WINE")
        stats.killed_paths += 1


def check_paths(executor, paths, pre=None, post=None):
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.add_annot_after(post.as_assert_annotation())

        if pre:
            p.add_annot_before(pre.as_assume_annotation())

        r = executor.execute_path(p)
        result.merge(r)

    return result


class KindSymbolicExecutor(SymbolicInterpreter):
    def __init__(
        self, prog, ohandler=None, opts=KindSEOptions(), programstructure=None
    ):
        super().__init__(
            P=prog, ohandler=ohandler, opts=opts, ExecutorClass=PathExecutor
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = LazySymbolicMemoryModel(opts)
        indexecutor = PathExecutor(prog, self.solver(), opts, memorymodel)
        # add error funs and forbid defined calls...
        dbg("Forbidding calls in induction step for now with k-induction")
        indexecutor.forbid_calls()
        self._indexecutor = indexecutor

        if programstructure is None:
            programstructure = ProgramStructure(prog, self.new_output_file)
        self.programstructure = programstructure

        self._entry_loc = programstructure.entry_loc
        # paths to run
        self.paths = []
        # as we run the executor in nested manners,
        # we want to give different outputs
        self.reportfn = print_stdout

        self.problematic_paths = []
        # here we report error states
        self.return_states = None

    def ind_executor(self):
        return self._indexecutor

    def problematic_paths_as_result(self):
        r = PathExecutionResult()
        r.other = self.problematic_paths
        return r

    def get_cfa(self, F):
        assert self.programstructure.cfas.get(F), f"Have no CFA for function {F.name()}"
        return self.programstructure.cfas.get(F)

    def get_return_states(self):
        """
        The states that caused killing the execution,
        i.e., error states or killed states
        """
        return self.return_states

    def execute_path(self, path, fromInit=False, invariants=None):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        if fromInit:
            # we must execute without lazy memory
            executor = self.executor()

            if not self.states:
                self.prepare()
            states = [s.copy() for s in self.states]
            assert states

            ldbgv("Executing (init) path: {0}", (path,), fn=self.reportfn)
        else:
            executor = self.ind_executor()

            s = executor.create_clean_state()
            states = [s]

            ldbgv("Executing path: {0}", (path,), fn=self.reportfn, color="orange")

        assert all(map(lambda s: not s.constraints(), states)), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.execute_annotated_path(states, path, invariants)
        self.stats.paths += 1

        earl = r.early
        if fromInit and earl:
            # this is an initial path, so every error is taken as real
            errs = r.errors or []
            for e in (e for e in earl if e.has_error()):
                errs.append(e)
            r.errors = errs

        return r

    def _is_init(self, loc):
        assert isinstance(loc, CFA.Location), loc
        return loc is self._entry_loc

    def extend_to_caller(self, path, states):
        self.problematic_paths.append(path)
        print_stdout("Killing a path that goes to caller")
        return []

    # fun = path[0].source().cfa().fun()
    # PS = self.programstructure
    # cgnode = PS.callgraph.get_node(fun)
    # paths = []
    # assert states.errors
    # for s in states.errors:
    #    for callerfun, callsite in cgnode.callers():
    #        for pred in PS.calls[callsite].predecessors():
    #            p = AnnotatedCFAPath([pred])
    #            p.add_annot_after(state_to_annotation(s, toassert=True))
    #            print('tocaller', p)
    #            paths.append(p)
    # return paths

    def extend_path(self, path, states, steps=-1, atmost=False, stoppoints=[]):
        """
        Take a path and extend it by prepending one or more
        predecessors.

        \param steps     Number of predecessors to prepend.
                         Values less or equal to 0 have a special
                         meaning:
                           0  -> prepend until a join is find
                           -1 -> prepend until a branch is find
        \param atmost    if set to True, we allow to extend
                         less than the specified number of steps
                         if there are no predecessors.
                         If set to False, the path is dropped
                         if it cannot be extended (there are
                         not enough predecessors)
        """

        num = 0
        newpaths = []
        locs = path.edges()[:]
        locs.reverse()  # reverse the list so that we can do append
        worklist = [locs]
        while worklist:
            num += 1
            newworklist = []

            for p in worklist:
                front = p[-1]  # the list is reversed, so the front is at the end
                preds = front.source().predecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    if len(path) == len(p) and states:
                        # we did not extend the path at all, so this
                        # is a path that ends in the entry block and
                        # we already processed it...
                        dbg("Extending a path to the caller")
                        np = self.extend_to_caller(path, states)
                        newpaths += np
                    else:
                        # FIXME: do not do this reverse, rather execute in reverse
                        # order (do a reverse iterator?)
                        p.reverse()
                        n = path.copyandsetpath(p)
                        newpaths.append(path.copyandsetpath(p))
                    continue

                for pred in preds:
                    newpath = p[:]
                    newpath.append(pred)

                    # if this is the initial path and we are not stepping by 1,
                    # we must add it too, otherwise we could miss such paths
                    # (note that this is not covered by 'predsnum == 0',
                    # because init may have predecessors)
                    added = False
                    if atmost and steps != 1 and self._is_init(pred.source()):
                        added = True
                        tmp = newpath[:]
                        tmp.reverse()
                        newpaths.append(path.copyandsetpath(tmp))
                        # fall-through to further extending this path

                    assert all(map(lambda x: isinstance(x, CFA.Location), stoppoints))
                    if pred in stoppoints:
                        newpath.reverse()
                        newpaths.append(path.copyandsetpath(newpath))
                    elif steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    elif steps == -1 and len(pred.source().successors()) > 1:
                        newworklist.append(newpath)
                    else:  # we're done with this path
                        if not added:
                            newpath.reverse()
                            newpaths.append(path.copyandsetpath(newpath))

            worklist = newworklist

        return newpaths

    def check_initial_error_path(self, path):
        """
        Execute a path from initial states
        \requires an initial path
        """

        r = self.execute_path(path, fromInit=True)
        if not r.errors:
            killed = any(True for s in r.early if s.was_killed()) if r.early else None
            if killed:
                return Result.UNKNOWN, r
            killed = any(True for s in r.other if s.was_killed()) if r.other else None
            if killed:
                return Result.UNKNOWN, r
            if len(self._entry_loc.predecessors()) == 0:
                # this path is safe and we do not need to extend it
                return Result.SAFE, r
            # else just fall-through to execution from clear state
            # as we can still prolong this path
        else:
            return Result.UNSAFE, r

        return None, r

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            first_loc = path[0].source()
            if self._is_init(first_loc):
                r, states = self.checkInitialPath(path)
                if r is Result.UNSAFE:
                    return r, states.errors  # found a real error
                elif r is Result.SAFE:
                    continue  # this path is safe
                assert r is None

            r = self.execute_path(path)

            oth = r.other
            if oth and any(map(lambda s: s.was_killed(), oth)):
                return Result.UNKNOWN, oth

            step = -1  # self.get_options().step
            if r.errors:
                has_err = True
                newpaths += self.extend_path(path, r, steps=step, atmost=step != 1)

        self.paths = newpaths

        if not has_err:
            return Result.SAFE, None

        return None, None

    def unfinished_paths(self):
        return self.paths

    def run(self, paths, maxk=None):
        dbg(
            f"Performing the k-ind algorithm for specified paths with maxk={maxk}",
            color="ORANGE",
        )

        k = 1

        self.paths = paths

        if len(self.paths) == 0:
            dbg("Found no error state!", color="GREEN")
            return 0

        while True:
            dbg("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r, states = self.checkPaths()
            if r is Result.SAFE:
                dbg("All possible error paths ruled out!", color="GREEN")
                dbg("Induction step succeeded!", color="GREEN")
                return r
            elif r is Result.UNSAFE:
                self.return_states = states
                print_stdout("Error found.", color="RED")
                return r
            elif r is Result.UNKNOWN:
                self.return_states = states
                dbg("Hit a problem, giving up.", color="ORANGE")
                return r
            else:
                assert r is None

            k += 1
            if maxk and maxk <= k:
                dbg("Hit the maximal number of iterations, giving up.", color="ORANGE")
                return Result.UNKNOWN
