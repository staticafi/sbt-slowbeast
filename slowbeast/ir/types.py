##
# We have five sorts of values:
# boolean
# value with a specified bitwidth
# floating-point value
# a sequence of bytes
# and a pointer to a value (not boolean)

POINTER_BIT_WIDTH = 64


def get_pointer_bitwidth():
    return POINTER_BIT_WIDTH


def get_size_type():
    return IntType(POINTER_BIT_WIDTH)


def get_offset_type():
    return IntType(POINTER_BIT_WIDTH)


def get_size_type_size():
    return POINTER_BIT_WIDTH


def get_offset_type_size():
    return POINTER_BIT_WIDTH


def sb_set_pointer_width(width):
    global POINTER_BIT_WIDTH
    assert width % 8 == 0
    POINTER_BIT_WIDTH = width
    # we must reset the types that use POINTER_BIT_WIDTH


class Type:
    __slots__ = "_bitwidth"

    def __init__(self, bw):
        assert isinstance(bw, int)
        self._bitwidth = bw

    def bytewidth(self):
        return max(int(self._bitwidth / 8), 1)

    def bitwidth(self):
        return self._bitwidth

    def is_pointer(self):
        return False

    def is_int(self):
        return False

    def is_float(self):
        return False

    def is_bytes(self):
        """Uninterpreted sequence of bytes"""
        return False

    def is_bool(self):
        return False

    def __eq__(self, x):

        return (
            self.is_bool() == x.is_bool()
            and self.is_pointer() == x.is_pointer()
            and self.is_float() == x.is_float()
            and self.bitwidth() == x.bitwidth()
        )

    def __str__(self):
        if self.is_bool():
            return "bool"
        if self.is_float():
            s = "f{0}b".format(self._bitwidth)
        elif self.is_bytes():
            s = "x{0}".format(self._bitwidth)
        else:
            s = "{0}b".format(self._bitwidth)
        if self.is_pointer():
            s += "*"
        return s


#  FIXME: add type manager that will manage the types,
#  mainly, we will not create a new object for every value,
#  but the types will be shared (and thus we can also modify them
#  easily)


class PointerType(Type):
    def __init__(self):
        Type.__init__(self, get_pointer_bitwidth())

    def is_pointer(self):
        return True


class IntType(Type):
    def __init__(self, bw):
        Type.__init__(self, bw)

    def is_int(self):
        return True


class FloatType(Type):
    def __init__(self, bw):
        Type.__init__(self, bw)

    def is_float(self):
        return True


class BoolType(Type):
    def __init__(self):
        Type.__init__(self, 1)

    def is_bool(self):
        return True


class Bytes(Type):
    def __init__(self, bytenum):
        Type.__init__(self, bytenum * 8)

    def is_bytes(self):
        return True
