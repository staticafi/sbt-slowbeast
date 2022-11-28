from slowbeast.bse.bse import check_paths
from slowbeast.symexe.statesset import union


class LoopInfo:
    def __init__(self, executor, loop):
        self.loop = loop
        self.cfa = loop.cfa
        self.header = loop.header
        self.entries = loop.entries
        self.get_exit_paths = loop.get_exit_paths
        self.paths_to_header = loop.paths_to_header
        self.exits = loop.exits

        self.checker = executor
        self.indexecutor = executor.ind_executor()

    # self.prestate = executor.ind_executor().create_clean_state()
    # poststates = check_paths(executor, loop.paths()).ready
    # assert poststates, "Loop has no infeasible path"
    # self.poststates = poststates

    def paths(self):
        return self.loop.paths()

    def set_is_inductive(self, S):
        r = check_paths(self.checker, self.loop.paths(), pre=S, post=S)
        if r.errors:
            return False
        return True

    # em = global_expr_mgr()
    # solver = IncrementalSolver()

    # annot = S.as_assume_annotation()
    # prestates, _ = execute_annotation_substitutions(
    #    self.indexecutor, [self.prestate], annot
    # )
    # assert len(prestates) == 1, prestates
    # solver.add(annot.do_substitutions(prestates[0]))

    # poststates, _ = execute_annotation_substitutions(
    #    self.indexecutor, self.poststates, annot
    # )
    # Not = em.Not
    # for s in poststates:
    #    solver.push()
    #    solver.add(s.path_condition())
    #    expr = annot.do_substitutions(s)
    #    if solver.is_sat(Not(expr)) is True:
    #        solver.pop()
    #        return False
    #    solver.pop()

    # return True

    def set_is_inductive_towards(self, S, target, allow_infeasible_only=False):
        r = check_paths(self.checker, self.loop.paths(), pre=S, post=union(S, target))
        if r.errors:
            return False
        return bool(r.ready) or allow_infeasible_only

    # em = global_expr_mgr()
    # solver = IncrementalSolver()

    # preannot = S.as_assume_annotation()
    # postannot = union(S, target).as_assume_annotation()
    # prestates, _ = execute_annotation_substitutions(
    #    self.indexecutor, [self.prestate], preannot
    # )
    # poststates, _ = execute_annotation_substitutions(
    #    self.indexecutor, self.poststates, postannot
    # )

    # assert len(prestates) == 1, prestates
    # solver.add(preannot.do_substitutions(prestates[0]))

    # Not = em.Not
    # has_feasible = False
    # for s in poststates:
    #    solver.push()
    #    solver.add(s.path_condition())
    #    if solver.is_sat() is False:
    #        solver.pop()
    #        continue # infeasible path
    #    has_feasible = True
    #    expr = postannot.do_substitutions(s)
    #    if solver.is_sat(Not(expr)) is True:
    #        solver.pop()
    #        return False
    #    solver.pop()

    # return has_feasible or allow_infeasible_only

    def check_set_inductivity(self, S):
        r = check_paths(self.checker, self.loop.paths(), pre=S, post=S)
        ind_on_some_path = bool(r.ready)
        ind_on_all_paths = not bool(r.errors)
        return ind_on_some_path, ind_on_all_paths
