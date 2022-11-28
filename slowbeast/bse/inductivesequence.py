from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.statesset import union, StatesSet


class InductiveSequence:
    """
    A sequence of states that are inductive towards each other.
    """

    def __init__(self, fst=None):
        "NOTE: overtakes the ownership of the 'fst' set!"
        assert fst is None or isinstance(fst, StatesSet), fst
        self.frames = [fst] if fst else []
        self.seq_as_set = fst.copy() if fst else None

    def copy(self):
        n = InductiveSequence()
        if self.frames:
            assert self.seq_as_set
            n.frames = self.frames.copy()
            n.seq_as_set = self.seq_as_set.copy()
        return n

    def __len__(self):
        return len(self.frames)

    def as_set(self):
        return self.seq_as_set

    def append(self, S):
        assert isinstance(S, StatesSet)
        self.frames.append(S)
        self.seq_as_set.add(S)

    def as_assume_annotation(self):
        return self.seq_as_set.as_assume_annotation()

    def as_assert_annotation(self):
        return self.seq_as_set.as_assert_annotation()

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
        selfassert = self.to_assert_annotation()
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
