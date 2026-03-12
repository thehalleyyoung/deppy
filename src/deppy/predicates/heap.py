"""Heap and protocol predicates.

Provides predicates about object fields, protocol conformance,
initialization state, mutation tracking, ownership, and aliasing.
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
    Predicate,
    SourceLocation,
    StrLit,
    Term,
    Var,
)


# ===================================================================
#  HasField
# ===================================================================

@dataclass(frozen=True)
class HasField(Predicate):
    """Object has a field of a given name (and optionally type).

    ``type_name`` is a string annotation to avoid importing type objects.
    """

    obj: Term
    field_name: str
    type_name: Optional[str] = None
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return HasField(
            obj=self.obj.substitute(mapping),
            field_name=self.field_name,
            type_name=self.type_name,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        base = f"hasattr({self.obj.pretty()}, {self.field_name!r})"
        if self.type_name is not None:
            base += f" : {self.type_name}"
        return base

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return (
            f"HasField({self.obj!r}, {self.field_name!r}, "
            f"type_name={self.type_name!r})"
        )


# ===================================================================
#  FieldValue
# ===================================================================

@dataclass(frozen=True)
class FieldValue(Predicate):
    """A field of an object satisfies a nested predicate.

    Semantics: ``predicate[v / obj.field_name]`` holds.
    """

    obj: Term
    field_name: str
    predicate: Predicate
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables() | self.predicate.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return FieldValue(
            obj=self.obj.substitute(mapping),
            field_name=self.field_name,
            predicate=self.predicate.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return FieldValue(
            obj=self.obj,
            field_name=self.field_name,
            predicate=self.predicate.negate(),
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        inner = self.predicate.simplify()
        from deppy.predicates.boolean import is_true
        if is_true(inner):
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        return FieldValue(
            obj=self.obj,
            field_name=self.field_name,
            predicate=inner,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        return (
            f"{self.obj.pretty()}.{self.field_name} satisfies "
            f"({self.predicate.pretty()})"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.predicate.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()
        yield from self.predicate.walk_terms()

    def __repr__(self) -> str:
        return (
            f"FieldValue({self.obj!r}, {self.field_name!r}, "
            f"{self.predicate!r})"
        )


# ===================================================================
#  ProtocolConformance
# ===================================================================

@dataclass(frozen=True)
class ProtocolConformance(Predicate):
    """Object conforms to a named structural protocol.

    ``protocol_name`` is the fully-qualified name of the protocol class.
    ``required_methods`` lists method signatures the protocol demands.
    """

    obj: Term
    protocol_name: str
    required_methods: Tuple[str, ...] = field(default_factory=tuple)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        obj: Term,
        protocol_name: str,
        required_methods: Sequence[str] = (),
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        object.__setattr__(self, "obj", obj)
        object.__setattr__(self, "protocol_name", protocol_name)
        object.__setattr__(self, "required_methods", tuple(required_methods))
        object.__setattr__(self, "source_location", source_location)

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return ProtocolConformance(
            obj=self.obj.substitute(mapping),
            protocol_name=self.protocol_name,
            required_methods=list(self.required_methods),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return (
            f"{self.obj.pretty()} conforms to {self.protocol_name}"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return (
            f"ProtocolConformance({self.obj!r}, {self.protocol_name!r})"
        )


# ===================================================================
#  Initialized
# ===================================================================

@dataclass(frozen=True)
class Initialized(Predicate):
    """A field has been initialised (definite assignment)."""

    obj: Term
    field_name: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Initialized(
            obj=self.obj.substitute(mapping),
            field_name=self.field_name,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"initialized({self.obj.pretty()}.{self.field_name})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return (
            f"Initialized({self.obj!r}, {self.field_name!r})"
        )


# ===================================================================
#  NotMutated
# ===================================================================

@dataclass(frozen=True)
class NotMutated(Predicate):
    """A field has not been mutated since a given program point.

    ``since_label`` is a symbolic label identifying the program point
    (e.g. a function-entry label).
    """

    obj: Term
    field_name: str
    since_label: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return NotMutated(
            obj=self.obj.substitute(mapping),
            field_name=self.field_name,
            since_label=self.since_label,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return (
            f"not_mutated({self.obj.pretty()}.{self.field_name}, "
            f"since={self.since_label!r})"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return (
            f"NotMutated({self.obj!r}, {self.field_name!r}, "
            f"{self.since_label!r})"
        )


# ===================================================================
#  OwnershipPred
# ===================================================================

@dataclass(frozen=True)
class OwnershipPred(Predicate):
    """Ownership / borrowing predicate.

    *kind* is one of ``"owned"``, ``"borrowed"``, ``"shared"``,
    ``"moved"``.
    """

    obj: Term
    kind: str
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    _VALID_KINDS: ClassVar[frozenset[str]] = frozenset({
        "owned", "borrowed", "shared", "moved",
    })

    def __post_init__(self) -> None:
        if self.kind not in self._VALID_KINDS:
            raise ValueError(f"Unknown ownership kind: {self.kind!r}")

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return OwnershipPred(
            obj=self.obj.substitute(mapping),
            kind=self.kind,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        from deppy.predicates.boolean import Not
        return Not(self, source_location=self.source_location)

    def simplify(self) -> Predicate:
        return self

    def pretty(self) -> str:
        return f"ownership({self.obj.pretty()}, {self.kind!r})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return f"OwnershipPred({self.obj!r}, {self.kind!r})"


# ===================================================================
#  AliasRelation
# ===================================================================

@dataclass(frozen=True)
class AliasRelation(Predicate):
    """Two references may or must alias.

    *kind* is ``"may"`` (may-alias) or ``"must"`` (must-alias).
    """

    left: Term
    right: Term
    kind: str = "may"
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    _VALID_KINDS: ClassVar[frozenset[str]] = frozenset({"may", "must"})

    def __post_init__(self) -> None:
        if self.kind not in self._VALID_KINDS:
            raise ValueError(f"Unknown alias kind: {self.kind!r}")

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return AliasRelation(
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
            kind=self.kind,
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
            f"{self.kind}_alias({self.left.pretty()}, {self.right.pretty()})"
        )

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return (
            f"AliasRelation({self.left!r}, {self.right!r}, "
            f"kind={self.kind!r})"
        )
