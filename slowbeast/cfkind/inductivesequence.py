from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.annotations import (
    AssumeAnnotation,
    AssertAnnotation,
    or_annotations,
)
from slowbeast.symexe.statesset import union
from slowbeast.solvers.solver import global_expr_mgr


class InductiveSequence:
    """
    A sequence of states that are inductive towards each other.
    """

    class Frame:
        """
        A frame is a pair 'states' and their
        inductive strengthening.
        """

        def __init__(self, states, strengthening):
            assert states, "BUG: empty states"
            self.states = states
            self.strengthening = strengthening

            if strengthening:
                e = strengthening.expr()
                if e.is_concrete() and e.value() is True:
                    self.strengthening = None

            assert strengthening is None or (
                states.substitutions() and strengthening.substitutions()
            )
            assert strengthening is None or (
                states.substitutions() == strengthening.substitutions()
            ), strengthening

        def toannot(self):
            EM = global_expr_mgr()
            states = self.states
            stren = self.strengthening

            assert states and states.substitutions() is not None
            assert (
                stren is None or (states.substitutions() == stren.substitutions()),
            ), stren
            expr = EM.And(states.expr(), stren.expr()) if stren else states.expr()
            return expr, states.substitutions()

        def toassert(self):
            EM = global_expr_mgr()
            return AssertAnnotation(*self.toannot(), EM)

        def toassume(self):
            EM = global_expr_mgr()
            return AssumeAnnotation(*self.toannot(), EM)

        def __eq__(self, rhs):
            st1 = self.strengthening
            st2 = rhs.strengthening
            if st1:
                return st2 and st1 == st2 and self.states == rhs.states
            return st2 is None and self.states == rhs.states

        def __repr__(self):
            return f"{self.states} with {self.strengthening}"

    def __init__(self, fst=None, fststr=None):
        self.frames = []
        if fst:
            # the first frame is supposed to be inductive
            self.frames.append(InductiveSequence.Frame(fst, fststr))

    def copy(self):
        n = InductiveSequence()
        n.frames = self.frames.copy()
        return n

    def __len__(self):
        return len(self.frames)

    def append(self, states, strength):
        assert states
        self.frames.append(InductiveSequence.Frame(states, strength))

    def pop(self):
        return self.frames.pop()

    def strengthen(self, annot, idx):
        assert idx < len(self.frames)
        self.frames[idx].strengthen(annot)

    def toannotation(self, toassert=True):
        EM = global_expr_mgr()
        A = or_annotations(EM, toassert, *map(lambda f: f.toassume(), self.frames))
        assert toassert or A.is_assume()
        assert not toassert or A.is_assert()
        return A

    def __getitem__(self, idx):
        return self.frames[idx]

    def __iter__(self):
        return self.frames.__iter__()

    def __repr__(self):
        return "\nvv seq vv\n{0}\n^^ seq ^^\n".format(
            "\n-----\n".join(map(str, self.frames))
        )

    def check_on_paths(
        self,
        executor,
        paths,
        target,
        tmpframes=None,
        pre=None,
        post=None,
        self_as_pre=False,
    ):
        """
        Check whether when we execute paths, we get to one of the frames
        tmpframes are frames that should be appended to the self.frames
        """

        result = PathExecutionResult()
        oldframes = self.frames
        self.frames = oldframes + (tmpframes or [])
        selfassert = self.toannotation(toassert=True)
        for path in paths:
            p = path.copy()
            # the post-condition is the whole frame
            if target:
                p.add_annot_after(union(target, selfassert).as_assert_annotation())
            else:
                p.add_annot_after(selfassert)
            if post:
                p.add_annot_after(post.as_assert_annotation())

            if self_as_pre:
                p.add_annot_before(selfassert)
            if pre:
                p.add_annot_before(pre.as_assume_annotation())

            r = executor.execute_edge(p)
            result.merge(r)

        self.frames = oldframes
        return result

    def check_last_frame(self, executor, paths, pre=None, post=None):
        """
        Check whether when we execute paths, we get to one of the frames
        """

        result = PathExecutionResult()
        frame = self.frames[-1]
        frameassert = frame.toassert()
        for path in paths:
            p = path.copy()
            # the post-condition is the whole frame
            p.add_postcondition(frameassert)
            for e in post or ():
                p.add_postcondition(e)

            for e in pre or ():
                p.add_precondition(e)

            r = executor.execute_edge(p)
            result.merge(r)

        # if r.ready:
        #    print_stdout(f"safe along {path}", color="GREEN")
        # if r.errors:
        #    print_stdout(f"unsafe along {path}", color="RED")
        # if not r.ready and not r.errors and not r.other:
        #    print_stdout(f"infeasible along {path}", color="DARK_GREEN")

        return result

    def check_ind_on_paths(self, executor, paths, target=None):
        return self.check_on_paths(executor, paths, target=target, self_as_pre=True)


# can be used to split formula to abstraction and the rest
# def _simplify_with_assumption(lhs, rhs):
#     """
#     Remove from 'rhs' (some) parts implied by the 'lhs'
#     'rhs' is a list of Or expressions
#     'lhs' is a list of Or expressions
#     """
#     # FIXME do this with an incremental solver
#     assumptions = lhs.copy()
#
#     # split clauses to singleton clauses and the others
#     singletons = []
#     rest = []
#     for c in rhs:
#         if c.isOr():
#             rest.append(c)
#         else:  # the formula is in CNF, so this must be a singleton
#             singletons.append(c)
#
#     assumptions += singletons
#
#     # remove the implied parts of the rest of clauses
#     changed = False
#     newrhs = []
#     newsingletons = []
#     solver = Solver()
#     EM = global_expr_mgr()
#     Not = EM.Not
#     for c in rest:
#         newliterals = []
#         for l in c.children():
#             assert l.is_bool()
#             q = solver.is_sat(*assumptions, l)
#             if q is not False:
#                 q = solver.is_sat(*assumptions, Not(l))
#                 if q is False:
#                     # this literal is implied and thus the whole clause is true
#                     changed = True
#                     break
#                 else:
#                     # we know that the literal can be true
#                     # or the solver failed, so keep the literal
#                     newliterals.append(l)
#             else:
#                 # we dropped the literal
#                 changed = True
#
#         assert len(newliterals) > 0, "Unsat clause..."
#         if len(newliterals) == 1:
#             # XXX: we could do this also for non-singletons,
#             # but do we want to?
#             assumptions.append(literals[0])
#             newsingletons.append(literals[0])
#         else:
#             newrhs.append(newliterals)
#
#     # get rid of redundant singletons
#     assumptions = lhs.copy()
#     tmp = []
#     for c in singletons:
#         assert c.is_bool()
#         q = solver.is_sat(*assumptions, Not(c))
#         if q is False:
#             # this literal is implied and we can drop it
#             changed = True
#             continue
#         else:
#             # we know that the literal can be true
#             # or the solver failed, so keep the literal
#             tmp.append(c)
#     singletons = tmp
#
#     return newsingletons, singletons + newrhs, changed
#
#
# def simplify_with_assumption(lhs, rhs):
#     lhs = list(lhs.to_cnf().children())
#     rhs = list(rhs.to_cnf().children())
#     changed = True
#
#     while changed:
#         singletons, rhs, changed = _simplify_with_assumption(lhs, rhs)
#         lhs += singletons
#
#     return global_expr_mgr().conjunction(*rhs)
