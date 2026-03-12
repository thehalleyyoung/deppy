"""Collection predicates.

Provides predicates about collections (lists, sets, tuples, dicts):

- **LengthPred**: ``len(x) op n``
- **NonEmpty**: ``len(x) > 0``
- **Contains**: ``elem in collection``
- **Sorted**: collection is sorted
- **Unique**: all elements are distinct
- **Subset**: ``A ⊆ B``
- **Disjoint**: ``A ∩ B = ∅``
- **Permutation**: ``A`` is a permutation of ``B``
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Dict,
    Iterator,
    List,
    Optional,
    Set,
)

from deppy.predicates.base import (
    Call,
    IntLit,
    Predicate,
    SourceLocation,
    Term,
    Var,
)


# ===================================================================
#  LengthPred
# ===================================================================

_LENGTH_CMP_OPS: frozenset[str] = frozenset({"<", "<=", ">", ">=", "==", "!="})
_LENGTH_CMP_NEGATE: dict[str, str] = {
    "<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "==",
}


@dataclass(frozen=True)
class LengthPred(Predicate):
    """Length predicate: ``len(collection) op bound``.

    *op* is one of ``<``, ``<=``, ``>``, ``>=``, ``==``, ``!=``.
    *collection* is the term whose length is constrained, and *bound*
    is a term representing the threshold value.
    """

    collection: Term
    op: str
    bound: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __post_init__(self) -> None:
        if self.op not in _LENGTH_CMP_OPS:
            raise ValueError(f"Unknown comparison operator: {self.op!r}")

    def free_variables(self) -> Set[str]:
        return self.collection.free_variables() | self.bound.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return LengthPred(
            collection=self.collection.substitute(mapping),
            op=self.op,
            bound=self.bound.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return LengthPred(
            collection=self.collection,
            op=_LENGTH_CMP_NEGATE[self.op],
            bound=self.bound,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        if isinstance(self.bound, IntLit):
            n = self.bound.value
            # len(x) >= 0 is always true
            if self.op == ">=" and n <= 0:
                from deppy.predicates.boolean import _TRUE
                return _TRUE
            # len(x) < 0 is always false
            if self.op == "<" and n <= 0:
                from deppy.predicates.boolean import _FALSE
                return _FALSE
        return self

    def pretty(self) -> str:
        return f"len({self.collection.pretty()}) {self.op} {self.bound.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield Call("len", [self.collection])
        yield from self.collection.walk_terms()
        yield from self.bound.walk_terms()

    def to_comparison(self) -> Predicate:
        """Convert to a ``Comparison`` over ``len(collection)``."""
        from deppy.predicates.arithmetic import Comparison
        return Comparison(
            op=self.op,
            left=Call("len", [self.collection]),
            right=self.bound,
            source_location=self.source_location,
        )

    def __repr__(self) -> str:
        return (
            f"LengthPred({self.collection!r}, {self.op!r}, {self.bound!r})"
        )


# ===================================================================
#  NonEmpty
# ===================================================================

@dataclass(frozen=True)
class NonEmpty(Predicate):
    """Non-emptiness predicate: ``len(collection) > 0``."""

    collection: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.collection.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return NonEmpty(
            collection=self.collection.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return LengthPred(
            collection=self.collection,
            op="==",
            bound=IntLit(0),
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"len({self.collection.pretty()}) > 0"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.collection.walk_terms()

    def to_length_pred(self) -> LengthPred:
        """Expand into an explicit ``LengthPred``."""
        return LengthPred(
            collection=self.collection,
            op=">",
            bound=IntLit(0),
            source_location=self.source_location,
        )

    def __repr__(self) -> str:
        return f"NonEmpty({self.collection!r})"


# ===================================================================
#  Contains
# ===================================================================

@dataclass(frozen=True)
class Contains(Predicate):
    """Membership predicate: ``element in collection``."""

    element: Term
    collection: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.element.free_variables() | self.collection.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Contains(
            element=self.element.substitute(mapping),
            collection=self.collection.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"{self.element.pretty()} in {self.collection.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.element.walk_terms()
        yield from self.collection.walk_terms()

    def __repr__(self) -> str:
        return f"Contains({self.element!r}, {self.collection!r})"


# ===================================================================
#  Sorted
# ===================================================================

@dataclass(frozen=True)
class Sorted(Predicate):
    """The collection is sorted.

    Optionally parameterised by a *key* function name and *reverse* flag.
    """

    collection: Term
    key: Optional[str] = None
    reverse: bool = False
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.collection.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Sorted(
            collection=self.collection.substitute(mapping),
            key=self.key,
            reverse=self.reverse,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        base = f"sorted({self.collection.pretty()}"
        if self.key:
            base += f", key={self.key}"
        if self.reverse:
            base += ", reverse=True"
        return base + ")"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.collection.walk_terms()

    def __repr__(self) -> str:
        return (
            f"Sorted({self.collection!r}, key={self.key!r}, "
            f"reverse={self.reverse!r})"
        )


# ===================================================================
#  Unique
# ===================================================================

@dataclass(frozen=True)
class Unique(Predicate):
    """All elements of the collection are distinct."""

    collection: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.collection.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Unique(
            collection=self.collection.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"unique({self.collection.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.collection.walk_terms()

    def __repr__(self) -> str:
        return f"Unique({self.collection!r})"


# ===================================================================
#  Subset
# ===================================================================

@dataclass(frozen=True)
class Subset(Predicate):
    """Subset relation: ``left ⊆ right``."""

    left: Term
    right: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Subset(
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
        return f"{self.left.pretty()} ⊆ {self.right.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"Subset({self.left!r}, {self.right!r})"


# ===================================================================
#  Disjoint
# ===================================================================

@dataclass(frozen=True)
class Disjoint(Predicate):
    """Disjointness: ``left ∩ right = ∅``."""

    left: Term
    right: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Disjoint(
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"{self.left.pretty()} ∩ {self.right.pretty()} = ∅"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"Disjoint({self.left!r}, {self.right!r})"


# ===================================================================
#  Permutation
# ===================================================================

@dataclass(frozen=True)
class Permutation(Predicate):
    """``left`` is a permutation of ``right``."""

    left: Term
    right: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Permutation(
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
        return f"perm({self.left.pretty()}, {self.right.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"Permutation({self.left!r}, {self.right!r})"
