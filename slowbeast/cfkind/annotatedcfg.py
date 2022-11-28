from slowbeast.analysis.cfg import CFG as PureCFG
from slowbeast.analysis.cfg import CFGPath as PureCFGPath
from slowbeast.ir.instruction import Assert
from slowbeast.ir.bblock import BBlock


class CFG(PureCFG):
    """
    CFG with nodes annotated with information
    about possible error sites and other
    useful information.
    """

    class AnnotatedNode(PureCFG.Node):
        __slots__ = ["_has_assert", "_annotations_after", "_annotations_before"]

        def __init__(self, cfg, B):
            super(CFG.AnnotatedNode, self).__init__(cfg, B)
            # find out whether this node has an assert
            self._has_assert = False
            for i in B.instructions():
                if isinstance(i, Assert):
                    self._has_assert = True
                    break

            # after _header execution
            self._annotations_after = []
            # before _header execution
            self._annotations_before = []

        def __repr__(self):
            return "{0}{1}{2}{3}".format(
                "a" if self._annotations_before else "",
                self.bblock_id(),
                "a" if self._annotations_after else "",
                "!" if self._has_assert else "",
            )

        def has_assert(self):
            return self._has_assert

        def add_annotation_after(self, annot):
            """
            The annotation should be evaluated "after"
            executing the location.
            """
            self._annotations_after.append(annot)

        def add_annotation_before(self, annot):
            """
            The annotation should be evaluated "before"
            executing the location.
            """
            self._annotations_before.append(annot)

        def bblock_id(self):
            return self.bblock().get_id()

    def __init__(self, F):
        super().__init__(F)

    def create_node(self, *args):
        assert len(args) == 1
        return CFG.AnnotatedNode(self, *args)


class CFGPath(PureCFGPath):
    def __init__(self, locs=None):
        super().__init__(locs or [])

    def reaches_assert(self):
        if len(self.locations()) <= 0:
            return False

        return self.locations()[-1].has_assert()


def _get_loc_key(loc):
    if isinstance(loc, CFG.AnnotatedNode):
        return loc.bblock().get_id()
    if isinstance(loc, BBlock):
        return loc.get_id()
    raise NotImplementedError(f"Unhandled key value: {loc}")


class AnnotatedCFGPath(CFGPath):
    """
    A CFG path that contains annotations.
    These annotations can put assumptions
    on values or similar. The annotations
    are a special set of instructions that
    are executed on given places.
    """

    __slots__ = "locannotations", "locannotationsafter", "precondition", "postcondition"

    def __init__(self, locs=None):
        super().__init__(locs or [])
        self.locannotations = {}
        self.locannotationsafter = {}
        self._precondition = []
        self._postcondition = []

    def addLocAnnotationAfter(self, annot, loc):
        self.locannotationsafter.setdefault(_get_loc_key(loc), []).append(annot)

    def getLocAnnotationsAfter(self, loc):
        return self.locannotationsafter.get(_get_loc_key(loc))

    def addLocAnnotationBefore(self, annot, loc):
        self.locannotations.setdefault(_get_loc_key(loc), []).append(annot)

    def getLocAnnotationsBefore(self, loc):
        return self.locannotations.get(_get_loc_key(loc))

    # FIXME: this can be also assert, do we want to call it post-condition?
    def add_postcondition(self, p):
        self._postcondition.append(p)

    def add_precondition(self, p):
        self._precondition.append(p)

    def get_postcondition(self):
        return self._postcondition

    def get_precondition(self):
        return self._precondition

    # def add_annotation_after(self, annot, idx=0):
    #    """
    #    Add annotation to the given location on the path.
    #    The annotation should be evaluated "after"
    #    executing the location.
    #    """
    #    assert idx < self.length()
    #    self.locations()[idx]._annotations_after.append(annot)

    # def add_annotation_before(self, annot, idx=0):
    #    """
    #    Add annotation to the given location on the path.
    #    The annotation should be evaluated "before"
    #    executing the location.
    #    """
    #    assert idx < self.length()
    #    self.locations()[idx]._annotations_before.append(annot)

    def copy(self):
        n = AnnotatedCFGPath(self.locations())
        n.locannotations = self.locannotations.copy()
        n.locannotationsafter = self.locannotationsafter.copy()
        n._postcondition = self._postcondition.copy()
        n._precondition = self._precondition.copy()
        return n

    def copyandprepend(self, loc):
        # FIXME: this is not efficient...
        n = AnnotatedCFGPath([loc] + self.locations())
        # FIXME: do cow?
        n.locannotations = self.locannotations.copy()
        n.locannotationsafter = self.locannotationsafter.copy()
        n._postcondition = self._postcondition.copy()
        n._precondition = self._precondition.copy()

        return n

    def copyandsetpath(self, locs):
        n = AnnotatedCFGPath(locs)
        # FIXME: do cow?
        n.locannotations = self.locannotations.copy()
        n.locannotationsafter = self.locannotationsafter.copy()
        n._postcondition = self._postcondition.copy()
        n._precondition = self._precondition.copy()

        return n

    def __repr__(self):
        def loc_str(x):
            blk = x.bblock()
            return "{0}{1}{2}".format(
                "a" if self.getLocAnnotationsBefore(blk) else "",
                blk.get_id(),
                "a" if self.getLocAnnotationsAfter(blk) else "",
            )

        return "{0}{1}{2}".format(
            "pre " if self._precondition else "",
            " -> ".join(map(loc_str, self.locations())),
            " post" if self._postcondition else "",
        )
