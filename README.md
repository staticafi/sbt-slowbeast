# Slowbeast

Playground for symbolic execution.

## Requirements

Slowbeast needs python3 and Z3 accesible from python (z3-solver). Alternatively, slowbeast can use PySMT solver layer (experimental).

To use the LLVM front-end, you need llvmlite. For many LLVM programs, the official package is good to go. However, our LLVM parser relies on some modifications that we did to the package. Our version of llvmlite can be downloaded from https://github.com/mchalupa/llvmlite.

For running tests:
For running tests, you need LLVM lit and make. Further, LLVM lit requires python-setuptools.
