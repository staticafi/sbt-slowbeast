import sys
from copy import copy

from slowbeast.core.callstack import CallStack
from slowbeast.core.errors import MemError
from slowbeast.domains.pointer import Pointer
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import get_size_type

from .memoryobject import MemoryObject


class Memory:
    """
    This is the object that keeps track of the state of memory
    in an execution state. It is created by MemoryModel object
    which also handles its updates and queries.
    """

    def __init__(self):
        self._objects = {}
        self._objects_ro = False
        self._glob_objects = {}
        self._glob_objects_ro = False
        self._glob_bindings = {}
        self._glob_bindings_ro = False
        # callstack containing top-level values for the current
        # function (values of computation of instructions).
        # In the future, move there also the objects bound
        # to particular frames
        self._cs = CallStack()

    def _copy_to(self, new):
        new._objects = self._objects
        new._objects_ro = True
        self._objects_ro = True
        new._glob_objects = self._glob_objects
        new._glob_objects_ro = True
        self._glob_objects_ro = True
        new._glob_bindings = self._glob_bindings
        new._glob_bindings_ro = True
        self._glob_bindings_ro = True
        for o in self._objects.values():
            o._set_ro()
        for o in self._glob_objects.values():
            o._set_ro()
        # do not take a reference, but do directly a copy,
        # we'll very probably modify it soon (it's cow internally)
        new._cs = self._cs.copy()
        return new

    def copy(self):
        new = type(self)()
        self._copy_to(new)
        return new

    def create_memory_object(self, size, nm=None, objid=None, is_glob=False):
        """
        Create a new memory object -- may be overriden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid, is_glob)

    def _objs_reown(self):
        if self._objects_ro:
            assert all([x._is_ro() for x in self._objects.values()])
            self._objects = copy(self._objects)
            self._objects_ro = False

    def _globs_reown(self):
        if self._glob_objects_ro:
            assert all([x._is_ro() for x in self._glob_objects.values()])
            self._glob_objects = copy(self._glob_objects)
            self._glob_objects_ro = False

    def _globs_bindings_reown(self):
        if self._glob_bindings_ro:
            self._glob_bindings = copy(self._glob_bindings)
            self._glob_bindings_ro = False

    def __eq__(self, rhs):
        return self._objects == rhs._objects and self._cs == self._cs

    def _allocate(self, size, instr=None, nm=None, objid=None, is_glob=False):
        """Allocate a new memory object and return it"""
        o = self.create_memory_object(size, nm, objid, is_glob)
        assert o._is_ro() is False, "Created object is read-only (COW bug)"

        if instr:
            o.set_allocation(instr)

        return o

    def allocate(self, size, instr=None, nm=None, objid=None):
        """Allocate a new memory object and return a pointer to it"""
        assert (
            objid is None or self._objects.get(objid) is None
        ), "Already has an object with id {0}".format(objid)

        o = self._allocate(size, instr, nm, objid)

        self._objs_reown()
        assert self._objects.get(o.get_id()) is None
        self._objects[o.get_id()] = o

        return Pointer(ConcreteVal(o.get_id(), get_size_type()))

    def allocate_global(self, G, objid=None, zeroed=False):
        """Allocate a new memory object and return a pointer to it"""
        assert (
            objid is None or self._glob_objects.get(objid) is None
        ), "Already has a global object with id {0}".format(objid)

        o = self._allocate(G.size(), G, G.name(), objid, is_glob=True)
        if zeroed:
            o.set_zeroed()

        self._globs_reown()
        assert self._glob_objects.get(o.get_id()) is None
        self._glob_objects[o.get_id()] = o

        self._globs_bindings_reown()
        assert self._glob_bindings_ro is False
        assert self._glob_bindings.get(G) is None
        ptr = Pointer(ConcreteVal(o.get_id(), get_size_type()))
        self._glob_bindings[G] = ptr

        return ptr

    def has_global_object(self, moid):
        return self._glob_objects.get(moid) is not None

    def has_object(self, moid):
        return self._objects.get(moid) is not None or self.has_global_object(moid)

    def get_obj(self, moid):
        if isinstance(moid, ConcreteVal):
            moid = moid.value()
        assert isinstance(moid, int), f"Invalid MO ID: {moid}"
        obj = self._objects.get(moid)
        if obj is None:
            return self._glob_objects.get(moid)
        return obj

    def write(self, ptr, x):
        isglob = False
        objid = ptr.object().value()
        obj = self._objects.get(objid)
        if obj is None:
            obj = self._glob_objects.get(objid)
            isglob = True

        if obj is None:
            return None, MemError(MemError.INVALID_OBJ, str(ptr.object()))

        if isglob:
            self._globs_reown()
        else:
            self._objs_reown()

        if obj._is_ro():  # copy on write
            obj = obj.writable_copy()
            assert not obj._is_ro()
            if isglob:
                self._glob_objects[obj.get_id()] = obj
            else:
                self._objects[obj.get_id()] = obj

        return obj.write(x, ptr.offset())

    def read(self, ptr, bytesNum):
        obj = self._objects.get(ptr.object().value())
        if obj is None:
            obj = self._glob_objects.get(ptr.object().value())

        if obj is None:
            return None, MemError(MemError.INVALID_OBJ, str(ptr.object()))

        return obj.read(bytesNum, ptr.offset())

    def get_cs(self):
        return self._cs

    def set_cs(self, cs):
        assert isinstance(cs, CallStack)
        self._cs = cs

    def frame(self, idx=-1):
        return self._cs.frame(idx)

    def set(self, what, v):
        self._cs.set(what, v)

    def get(self, v):
        ret = self._glob_bindings.get(v)
        if ret is None:
            ret = self._cs.get(v)
        return ret

    def bound_globals(self):
        """Return the bound globals in this state"""
        return self._glob_bindings.items()

    def globals_list(self):
        """Return the list of globals in this state"""
        # return only list, so that we must get them through "get"
        return self._glob_bindings.keys()

    def values_list(self):
        return self._cs.values_list()

    def push_call(self, callsite, fun, argsMapping={}):
        self._cs.push_call(callsite, fun, argsMapping)

    def pop_call(self):
        return self._cs.pop_call()

    def dump(self, stream=sys.stdout):
        stream.write("-- Global objects:\n")
        for o in self._glob_objects.values():
            o.dump(stream)
        stream.write("-- Global bindings:\n")
        for g, v in self._glob_bindings.items():
            stream.write("{0} -> {1}\n".format(g.as_value(), v.as_value()))
        stream.write("-- Objects:\n")
        for o in self._objects.values():
            o.dump(stream)
        stream.write("-- Call stack:\n")
        self._cs.dump(stream)

    def havoc_obj(self, objid):
        isglob = False
        obj = self._objects.get(objid)
        if obj is None:
            obj = self._glob_objects.get(objid)
            isglob = True

        if obj is None:
            return

        if isglob:
            self._globs_reown()
        else:
            self._objs_reown()

        if obj._is_ro():
            obj = obj.clean_copy()
            assert not obj._is_ro()
            if isglob:
                self._glob_objects[obj.get_id()] = obj
            else:
                self._objects[obj.get_id()] = obj
        else:
            obj.clear()

    def havoc(self, objs=None, without=None):
        """Havoc the contents of memory"""
        # FIXME: we do not have to havoc constants and some other values
        if objs:
            havoc_obj = self.havoc_obj
            for o in objs:
                if without and o in without:
                    continue
                havoc_obj(o.get_id())
            return

        # create clean objects
        newobjs = {}
        for p, o in self._objects.items():
            if without and o in without:
                newobjs[p] = o.copy()
            else:
                newobjs[p] = o.clean_copy()
        self._objects = newobjs
        self._objects_ro = False

        # create clean global objects
        newobjs = {}
        for p, o in self._glob_objects.items():
            if without and o in without:
                newobjs[p] = o.copy()
            else:
                newobjs[p] = o.clean_copy()
        self._glob_objects = newobjs
        self._glob_objects_ro = False

        # clear values in call stack
        # FIXME: do not havoc the 'without' objects
        for frame in self._cs:
            frame.clear()
