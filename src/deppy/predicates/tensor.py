"""Tensor-specific predicates for array/tensor refinement types.

Provides predicates about tensor shape, rank, dtype, device, and
inter-tensor relationships used heavily in NumPy / PyTorch / JAX
library theories.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    ClassVar,
    Dict,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.predicates.base import (
    IntLit,
    Predicate,
    SourceLocation,
    StrLit,
    Term,
    TupleLit,
    Var,
)


# ===================================================================
#  ShapePred
# ===================================================================

@dataclass(frozen=True)
class ShapePred(Predicate):
    """Shape equality: ``tensor.shape == (d₁, d₂, …)``."""

    tensor: Term
    shape: Tuple[Term, ...] = field(default_factory=tuple)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        tensor: Term,
        shape: Sequence[Term] = (),
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        object.__setattr__(self, "tensor", tensor)
        object.__setattr__(self, "shape", tuple(shape))
        object.__setattr__(self, "source_location", source_location)

    def free_variables(self) -> Set[str]:
        result = self.tensor.free_variables()
        for s in self.shape:
            result |= s.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return ShapePred(
            tensor=self.tensor.substitute(mapping),
            shape=[s.substitute(mapping) for s in self.shape],
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        dims = ", ".join(s.pretty() for s in self.shape)
        return f"{self.tensor.pretty()}.shape == ({dims})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()
        for s in self.shape:
            yield from s.walk_terms()

    @property
    def rank(self) -> int:
        """Return the number of dimensions asserted by this shape predicate."""
        return len(self.shape)

    def __repr__(self) -> str:
        return f"ShapePred({self.tensor!r}, {list(self.shape)!r})"


# ===================================================================
#  RankPred
# ===================================================================

@dataclass(frozen=True)
class RankPred(Predicate):
    """Rank predicate: ``tensor.dim() op n``.

    *op* is one of ``==``, ``>=``, ``<=``, ``<``, ``>``, ``!=``.
    """

    tensor: Term
    op: str
    rank: int
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    _VALID_OPS: ClassVar[frozenset[str]] = frozenset({"<", "<=", ">", ">=", "==", "!="})
    _NEGATE: ClassVar[dict[str, str]] = {
        "<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "==",
    }

    def __post_init__(self) -> None:
        if self.op not in self._VALID_OPS:
            raise ValueError(f"Unknown operator: {self.op!r}")

    def free_variables(self) -> Set[str]:
        return self.tensor.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return RankPred(
            tensor=self.tensor.substitute(mapping),
            op=self.op,
            rank=self.rank,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return RankPred(
            tensor=self.tensor,
            op=self._NEGATE[self.op],
            rank=self.rank,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        # dim() is always non-negative
        if self.op == ">=" and self.rank <= 0:
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        if self.op == "<" and self.rank <= 0:
            from deppy.predicates.boolean import _FALSE
            return _FALSE
        return self

    def pretty(self) -> str:
        return f"{self.tensor.pretty()}.dim() {self.op} {self.rank}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()

    def __repr__(self) -> str:
        return f"RankPred({self.tensor!r}, {self.op!r}, {self.rank!r})"


# ===================================================================
#  DtypePred
# ===================================================================

@dataclass(frozen=True)
class DtypePred(Predicate):
    """Data-type predicate: ``tensor.dtype == dtype_name``."""

    tensor: Term
    dtype: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.tensor.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return DtypePred(
            tensor=self.tensor.substitute(mapping),
            dtype=self.dtype,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"{self.tensor.pretty()}.dtype == {self.dtype}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()

    def __repr__(self) -> str:
        return f"DtypePred({self.tensor!r}, {self.dtype!r})"


# ===================================================================
#  DevicePred
# ===================================================================

@dataclass(frozen=True)
class DevicePred(Predicate):
    """Device predicate: ``tensor.device == device_name``."""

    tensor: Term
    device: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.tensor.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return DevicePred(
            tensor=self.tensor.substitute(mapping),
            device=self.device,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"{self.tensor.pretty()}.device == {self.device!r}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()

    def __repr__(self) -> str:
        return f"DevicePred({self.tensor!r}, {self.device!r})"


# ===================================================================
#  BroadcastCompatible
# ===================================================================

@dataclass(frozen=True)
class BroadcastCompatible(Predicate):
    """Two tensors' shapes are broadcast-compatible.

    Broadcasting follows NumPy semantics: dimensions are compared from
    the trailing end, and two dimensions are compatible when they are
    equal or one of them is 1.
    """

    left: Term
    right: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return BroadcastCompatible(
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        if self.left == self.right:
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        return self

    def pretty(self) -> str:
        return (
            f"broadcast_compatible({self.left.pretty()}, "
            f"{self.right.pretty()})"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"BroadcastCompatible({self.left!r}, {self.right!r})"


# ===================================================================
#  ShapeRelation
# ===================================================================

@dataclass(frozen=True)
class ShapeRelation(Predicate):
    """Arbitrary relationship between two tensor shapes.

    *relation* is a human-readable label like ``"matmul_compatible"``,
    ``"concat_along_0"``, etc.  Additional *constraints* capture the
    per-dimension equalities/inequalities.
    """

    left: Term
    right: Term
    relation: str
    constraints: Tuple[Predicate, ...] = field(default_factory=tuple)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        left: Term,
        right: Term,
        relation: str,
        constraints: Sequence[Predicate] = (),
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        object.__setattr__(self, "left", left)
        object.__setattr__(self, "right", right)
        object.__setattr__(self, "relation", relation)
        object.__setattr__(self, "constraints", tuple(constraints))
        object.__setattr__(self, "source_location", source_location)

    def free_variables(self) -> Set[str]:
        result = self.left.free_variables() | self.right.free_variables()
        for c in self.constraints:
            result |= c.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return ShapeRelation(
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
            relation=self.relation,
            constraints=[c.substitute(mapping) for c in self.constraints],
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        simplified = [c.simplify() for c in self.constraints]
        from deppy.predicates.boolean import is_false
        for s in simplified:
            if is_false(s):
                from deppy.predicates.boolean import _FALSE
                return _FALSE
        return ShapeRelation(
            left=self.left, right=self.right,
            relation=self.relation, constraints=simplified,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        base = (
            f"shape_rel({self.left.pretty()}, {self.right.pretty()}, "
            f"{self.relation!r})"
        )
        if self.constraints:
            cs = ", ".join(c.pretty() for c in self.constraints)
            base += f" where [{cs}]"
        return base

    def walk(self) -> Iterator[Predicate]:
        yield self
        for c in self.constraints:
            yield from c.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()
        for c in self.constraints:
            yield from c.walk_terms()

    def __repr__(self) -> str:
        return (
            f"ShapeRelation({self.left!r}, {self.right!r}, "
            f"{self.relation!r})"
        )


# ===================================================================
#  SortedTensor
# ===================================================================

@dataclass(frozen=True)
class SortedTensor(Predicate):
    """Tensor values are sorted along an axis.

    *axis* defaults to the last axis when ``None``.
    """

    tensor: Term
    axis: Optional[int] = None
    descending: bool = False
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.tensor.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return SortedTensor(
            tensor=self.tensor.substitute(mapping),
            axis=self.axis,
            descending=self.descending,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        parts = [self.tensor.pretty()]
        if self.axis is not None:
            parts.append(f"axis={self.axis}")
        if self.descending:
            parts.append("descending=True")
        return f"sorted_tensor({', '.join(parts)})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()

    def __repr__(self) -> str:
        return (
            f"SortedTensor({self.tensor!r}, axis={self.axis!r}, "
            f"descending={self.descending!r})"
        )


# ===================================================================
#  ValidIndex
# ===================================================================

@dataclass(frozen=True)
class ValidIndex(Predicate):
    """Index tensor has valid indices for *source*.

    *axis* specifies which axis of the source tensor the indices address.
    """

    index_tensor: Term
    source: Term
    axis: int = 0
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.index_tensor.free_variables() | self.source.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return ValidIndex(
            index_tensor=self.index_tensor.substitute(mapping),
            source=self.source.substitute(mapping),
            axis=self.axis,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return (
            f"valid_index({self.index_tensor.pretty()}, "
            f"{self.source.pretty()}, axis={self.axis})"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.index_tensor.walk_terms()
        yield from self.source.walk_terms()

    def __repr__(self) -> str:
        return (
            f"ValidIndex({self.index_tensor!r}, {self.source!r}, "
            f"axis={self.axis!r})"
        )


# ===================================================================
#  ContiguousPred
# ===================================================================

@dataclass(frozen=True)
class ContiguousPred(Predicate):
    """Tensor memory layout is contiguous (C or Fortran order)."""

    tensor: Term
    order: str = "C"
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.tensor.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return ContiguousPred(
            tensor=self.tensor.substitute(mapping),
            order=self.order,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"{self.tensor.pretty()}.is_contiguous(order={self.order!r})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.tensor.walk_terms()

    def __repr__(self) -> str:
        return f"ContiguousPred({self.tensor!r}, order={self.order!r})"
