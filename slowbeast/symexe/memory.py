from slowbeast.symexe.memoryobject import MemoryObject
from slowbeast.core.memory import Memory as CoreMemory


class Memory(CoreMemory):
    def create_memory_object(self, size, nm=None, objid=None, is_global=False):
        """
        Create a new memory object -- may be overridden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid, is_global)
