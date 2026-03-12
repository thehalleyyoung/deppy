"""Nullability and type-narrowing predicates.

Provides:

- **IsNone / IsNotNone**: ``x is None`` / ``x is not None``
- **IsInstance / IsNotInstance**: ``isinstance(x, T)``
- **Truthy / Falsy**: ``bool(x)``
- **TypeNarrowing**: applies guard predicates to narrow types.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.predicates.base import (
    Predicate,
    SourceLocation,
    Term,
    Var,
)


# ===================================================================
#  IsNone / IsNotNone
# ===================================================================

@dataclass(frozen=True)
class IsNone(Predicate):
    """``term is None``."""

    term: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return IsNone(
            term=self.term.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return IsNotNone(
            term=self.term,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        from deppy.predicates.base import NoneLit
        if isinstance(self.term, NoneLit):
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        return self

    def pretty(self) -> str:
        return f"{self.term.pretty()} is None"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"IsNone({self.term!r})"


@dataclass(frozen=True)
class IsNotNone(Predicate):
    """``term is not None``."""

    term: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return IsNotNone(
            term=self.term.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return IsNone(
            term=self.term,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        from deppy.predicates.base import NoneLit
        if isinstance(self.term, NoneLit):
            from deppy.predicates.boolean import _FALSE
            return _FALSE
        return self

    def pretty(self) -> str:
        return f"{self.term.pretty()} is not None"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"IsNotNone({self.term!r})"


# ===================================================================
#  IsInstance / IsNotInstance
# ===================================================================

@dataclass(frozen=True)
class IsInstance(Predicate):
    """``isinstance(term, type_name)``."""

    term: Term
    type_name: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return IsInstance(
            term=self.term.substitute(mapping),
            type_name=self.type_name,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return IsNotInstance(
            term=self.term,
            type_name=self.type_name,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"isinstance({self.term.pretty()}, {self.type_name})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"IsInstance({self.term!r}, {self.type_name!r})"


@dataclass(frozen=True)
class IsNotInstance(Predicate):
    """``not isinstance(term, type_name)``."""

    term: Term
    type_name: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return IsNotInstance(
            term=self.term.substitute(mapping),
            type_name=self.type_name,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return IsInstance(
            term=self.term,
            type_name=self.type_name,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"not isinstance({self.term.pretty()}, {self.type_name})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"IsNotInstance({self.term!r}, {self.type_name!r})"


# ===================================================================
#  Truthy / Falsy
# ===================================================================

@dataclass(frozen=True)
class Truthy(Predicate):
    """``bool(term) is True``."""

    term: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Truthy(
            term=self.term.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return Falsy(
            term=self.term,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        from deppy.predicates.base import BoolLit, IntLit, NoneLit
        if isinstance(self.term, BoolLit):
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if self.term.value else _FALSE
        if isinstance(self.term, IntLit):
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if self.term.value != 0 else _FALSE
        if isinstance(self.term, NoneLit):
            from deppy.predicates.boolean import _FALSE
            return _FALSE
        return self

    def pretty(self) -> str:
        return f"bool({self.term.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"Truthy({self.term!r})"


@dataclass(frozen=True)
class Falsy(Predicate):
    """``bool(term) is False``."""

    term: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.term.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Falsy(
            term=self.term.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return Truthy(
            term=self.term,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        from deppy.predicates.base import BoolLit, IntLit, NoneLit
        if isinstance(self.term, BoolLit):
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if not self.term.value else _FALSE
        if isinstance(self.term, IntLit):
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if self.term.value == 0 else _FALSE
        if isinstance(self.term, NoneLit):
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        return self

    def pretty(self) -> str:
        return f"not bool({self.term.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.term.walk_terms()

    def __repr__(self) -> str:
        return f"Falsy({self.term!r})"


# ===================================================================
#  TypeNarrowing
# ===================================================================

class TypeNarrowing:
    """Applies type narrowing based on guard predicates.

    Type narrowing is the process of deducing a more specific type for
    a variable after a conditional test.  For example:

    - ``x is not None`` narrows ``Optional[T]`` to ``T``.
    - ``isinstance(x, int)`` narrows ``Union[int, str]`` to ``int``.
    - ``bool(x)`` narrows ``Optional[T]`` by removing ``None``.

    The *narrow* method receives a type descriptor (as ``Any`` to avoid
    hard-coupling to the types package) and a predicate, and returns
    the narrowed type.  If no narrowing applies, the original type is
    returned unchanged.
    """

    def narrow(self, typ: Any, pred: Predicate) -> Any:
        """Narrow *typ* under the assumption that *pred* holds.

        Args:
            typ: A type descriptor (e.g. from ``deppy.types``).
            pred: The guard predicate that is known to be true.

        Returns:
            A (possibly) more specific type, or *typ* unchanged.
        """
        if isinstance(pred, IsNotNone):
            return self._narrow_not_none(typ)
        if isinstance(pred, IsNone):
            return self._narrow_none(typ)
        if isinstance(pred, IsInstance):
            return self._narrow_isinstance(typ, pred.type_name)
        if isinstance(pred, IsNotInstance):
            return self._narrow_not_isinstance(typ, pred.type_name)
        if isinstance(pred, Truthy):
            return self._narrow_truthy(typ)
        if isinstance(pred, Falsy):
            return self._narrow_falsy(typ)
        return typ

    def _narrow_not_none(self, typ: Any) -> Any:
        """Remove ``None`` from an ``Optional[T]`` / ``Union[..., None]``."""
        if isinstance(typ, str):
            # Simple string-based Optional removal
            if typ.startswith("Optional[") and typ.endswith("]"):
                return typ[len("Optional["):-1]
        return typ

    def _narrow_none(self, typ: Any) -> Any:
        """Narrow to ``None`` type."""
        return "None"

    def _narrow_isinstance(self, typ: Any, type_name: str) -> Any:
        """Narrow to the intersection with *type_name*."""
        return type_name

    def _narrow_not_isinstance(self, typ: Any, type_name: str) -> Any:
        """Remove *type_name* from a union type."""
        if isinstance(typ, str) and typ.startswith("Union[") and typ.endswith("]"):
            inner = typ[len("Union["):-1]
            parts = [p.strip() for p in inner.split(",")]
            remaining = [p for p in parts if p != type_name]
            if len(remaining) == 1:
                return remaining[0]
            if remaining:
                return f"Union[{', '.join(remaining)}]"
        return typ

    def _narrow_truthy(self, typ: Any) -> Any:
        """Remove ``None`` and falsy singletons from the type."""
        return self._narrow_not_none(typ)

    def _narrow_falsy(self, typ: Any) -> Any:
        """Narrow to falsy values (None, 0, False, '', [])."""
        return typ
