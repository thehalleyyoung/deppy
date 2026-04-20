"""
deppy.types — Public type-level constructs for Deppy.

Re-exports core types so that ``from deppy.types import PathType`` works
as shown in the Deppy tutorial book.
"""
from __future__ import annotations

# Core types
from deppy.core.types import (           # noqa: F401
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Var, Literal, PyObjType, PyIntType, PyFloatType, PyStrType,
    PyBoolType, PyNoneType, PyListType, PyDictType, PySetType,
    PyTupleType, PyCallableType, PyClassType,
    PiType, SigmaType, RefinementType, UnionType, OptionalType,
    ProtocolType, PathType,
)

# Proof terms (also available from deppy.core.kernel)
from deppy.core.kernel import (          # noqa: F401
    Refl, Sym, Trans, Cong, Ap, FunExt, Univalence,
    TransportProof, PathComp, CechGlue, Fiber, Patch,
    DuckPath, Cut, Assume, Z3Proof,
)

# Convenience aliases used in book
Transport = TransportProof
J = TransportProof  # J-elimination is transport in cubical setting

# Refined type aliases
from deppy.proofs.sugar import (         # noqa: F401
    Nat, Pos, NonEmpty, NonNull, Sorted, Bounded, SizedExact,
    Refine as refined,
)
Refined = refined  # alias used in book examples

# Additional type aliases for book examples
from dataclasses import dataclass          # noqa: F401

class Empty:
    """The empty type (no inhabitants)."""
    pass

class Unit:
    """The unit type (single inhabitant)."""
    _instance = None
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

class Sigma:
    """Dependent pair type Σ(x:A). B(x)."""
    def __init__(self, fst, snd):
        self.fst = fst
        self.snd = snd

# Symbolic types for SymPy sidecar proofs
class SymExpr:
    """A symbolic expression type (for sidecar proofs over SymPy)."""
    pass

class SymVar(SymExpr):
    """A symbolic variable."""
    def __init__(self, name: str):
        self.name = name

class SymMatrix:
    """A symbolic matrix type."""
    pass

class NatLiteral:
    """A natural number literal with compile-time value."""
    def __init__(self, value: int):
        assert value >= 0
        self.value = value

# NumPy/Torch-style type aliases
class NDArray:
    """N-dimensional array type (for NumPy sidecar proofs)."""
    pass

class PosDefMatrix:
    """Positive definite matrix type."""
    pass

class NonNegFloat:
    """Non-negative float type."""
    pass

PosInt = Pos
