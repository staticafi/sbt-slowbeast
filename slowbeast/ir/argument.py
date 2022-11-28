from .program import ProgramElement


class Argument(ProgramElement):
    def __init__(self, ty):
        super().__init__()
        self._type = ty

    def type(self):
        return self._type

    def __str__(self):
        return "a{0}:{1}".format(self.get_id(), self._type)

    def as_value(self):
        return "a{0}".format(self.get_id())
