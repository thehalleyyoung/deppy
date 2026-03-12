"""Refinement types and qualifiers for DepPy.

A refinement type ``{v: τ | φ}`` pairs a base type *τ* with a predicate *φ*
over a binder variable *v*.  This module provides:

- :class:`Predicate` — abstract predicate base and concrete combinators
  (comparison, logical connectives, membership, …).
- :class:`RefinementType` — the core ``{v: τ | φ}`` type.
- :class:`Qualifier` — lightweight named qualifiers (NonNull, Positive, …).
- :class:`QualifiedType` — a base type annotated with a list of qualifiers.
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from .base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE


# ═══════════════════════════════════════════════════════════════════════════════
# Predicates
# ═══════════════════════════════════════════════════════════════════════════════


class Predicate(ABC):
    """Abstract base for refinement predicates.

    A predicate *φ* may reference a distinguished *binder* variable that
    represents the value being refined.
    """

    @abstractmethod
    def free_vars(self) -> FrozenSet[str]:
        """Return the set of free variable names in this predicate."""
        ...

    @abstractmethod
    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        """Rename variables according to *mapping* (var name → var name)."""
        ...

    @abstractmethod
    def negate(self) -> Predicate:
        """Return the logical negation of this predicate."""
        ...

    @abstractmethod
    def __eq__(self, other: object) -> bool: ...

    @abstractmethod
    def __hash__(self) -> int: ...

    @abstractmethod
    def __repr__(self) -> str: ...

    def and_(self, other: Predicate) -> Predicate:
        """Conjunction: ``self ∧ other``."""
        return ConjunctionPred((self, other))

    def or_(self, other: Predicate) -> Predicate:
        """Disjunction: ``self ∨ other``."""
        return DisjunctionPred((self, other))

    def implies(self, other: Predicate) -> Predicate:
        """Implication: ``self ⇒ other``."""
        return ImplicationPred(self, other)


# ── Trivial predicates ─────────────────────────────────────────────────────


@dataclass(frozen=True)
class TruePred(Predicate):
    """The always-true predicate ``⊤``."""

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        return self

    def negate(self) -> Predicate:
        return FalsePred()

    def __repr__(self) -> str:
        return "True"


@dataclass(frozen=True)
class FalsePred(Predicate):
    """The always-false predicate ``⊥``."""

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        return self

    def negate(self) -> Predicate:
        return TruePred()

    def __repr__(self) -> str:
        return "False"


# ── Comparison predicates ──────────────────────────────────────────────────


class ComparisonOp(Enum):
    """Comparison operators used in refinement predicates."""

    EQ = "=="
    NE = "!="
    LT = "<"
    LE = "<="
    GT = ">"
    GE = ">="


@dataclass(frozen=True)
class ComparisonPred(Predicate):
    """Binary comparison: ``lhs op rhs``.

    Operands are variable names (``str``) or literal values (``int | float | str | bool``).
    """

    lhs: Union[str, int, float, str, bool]
    op: ComparisonOp
    rhs: Union[str, int, float, str, bool]

    def free_vars(self) -> FrozenSet[str]:
        result: set[str] = set()
        if isinstance(self.lhs, str) and self.lhs.isidentifier():
            result.add(self.lhs)
        if isinstance(self.rhs, str) and self.rhs.isidentifier():
            result.add(self.rhs)
        return frozenset(result)

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_lhs = mapping.get(self.lhs, self.lhs) if isinstance(self.lhs, str) else self.lhs
        new_rhs = mapping.get(self.rhs, self.rhs) if isinstance(self.rhs, str) else self.rhs
        if new_lhs is self.lhs and new_rhs is self.rhs:
            return self
        return ComparisonPred(new_lhs, self.op, new_rhs)

    def negate(self) -> Predicate:
        negated_op = {
            ComparisonOp.EQ: ComparisonOp.NE,
            ComparisonOp.NE: ComparisonOp.EQ,
            ComparisonOp.LT: ComparisonOp.GE,
            ComparisonOp.LE: ComparisonOp.GT,
            ComparisonOp.GT: ComparisonOp.LE,
            ComparisonOp.GE: ComparisonOp.LT,
        }
        return ComparisonPred(self.lhs, negated_op[self.op], self.rhs)

    def __repr__(self) -> str:
        return f"{self.lhs} {self.op.value} {self.rhs}"


# ── Logical connectives ───────────────────────────────────────────────────


@dataclass(frozen=True)
class NotPred(Predicate):
    """Logical negation ``¬inner``."""

    inner: Predicate

    def free_vars(self) -> FrozenSet[str]:
        return self.inner.free_vars()

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_inner = self.inner.substitute_pred(mapping)
        if new_inner is self.inner:
            return self
        return NotPred(new_inner)

    def negate(self) -> Predicate:
        return self.inner

    def __repr__(self) -> str:
        return f"¬({self.inner!r})"


@dataclass(frozen=True, eq=False)
class ConjunctionPred(Predicate):
    """Conjunction ``φ₁ ∧ φ₂ ∧ ...``."""

    conjuncts: Tuple[Predicate, ...]

    def __post_init__(self) -> None:
        # Flatten nested conjunctions
        flat: list[Predicate] = []
        for c in self.conjuncts:
            if isinstance(c, ConjunctionPred):
                flat.extend(c.conjuncts)
            elif not isinstance(c, TruePred):
                flat.append(c)
        if any(isinstance(c, FalsePred) for c in flat):
            object.__setattr__(self, "conjuncts", (FalsePred(),))
        else:
            object.__setattr__(self, "conjuncts", tuple(flat) if flat else (TruePred(),))

    def free_vars(self) -> FrozenSet[str]:
        result: set[str] = set()
        for c in self.conjuncts:
            result |= c.free_vars()
        return frozenset(result)

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_conjuncts = tuple(c.substitute_pred(mapping) for c in self.conjuncts)
        if all(n is o for n, o in zip(new_conjuncts, self.conjuncts)):
            return self
        return ConjunctionPred(new_conjuncts)

    def negate(self) -> Predicate:
        # De Morgan: ¬(A ∧ B) = ¬A ∨ ¬B
        return DisjunctionPred(tuple(c.negate() for c in self.conjuncts))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ConjunctionPred):
            return NotImplemented
        return frozenset(self.conjuncts) == frozenset(other.conjuncts)

    def __hash__(self) -> int:
        return hash(("Conj", frozenset(self.conjuncts)))

    def __repr__(self) -> str:
        return " ∧ ".join(repr(c) for c in self.conjuncts)


@dataclass(frozen=True, eq=False)
class DisjunctionPred(Predicate):
    """Disjunction ``φ₁ ∨ φ₂ ∨ ...``."""

    disjuncts: Tuple[Predicate, ...]

    def __post_init__(self) -> None:
        flat: list[Predicate] = []
        for d in self.disjuncts:
            if isinstance(d, DisjunctionPred):
                flat.extend(d.disjuncts)
            elif not isinstance(d, FalsePred):
                flat.append(d)
        if any(isinstance(d, TruePred) for d in flat):
            object.__setattr__(self, "disjuncts", (TruePred(),))
        else:
            object.__setattr__(self, "disjuncts", tuple(flat) if flat else (FalsePred(),))

    def free_vars(self) -> FrozenSet[str]:
        result: set[str] = set()
        for d in self.disjuncts:
            result |= d.free_vars()
        return frozenset(result)

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_disjuncts = tuple(d.substitute_pred(mapping) for d in self.disjuncts)
        if all(n is o for n, o in zip(new_disjuncts, self.disjuncts)):
            return self
        return DisjunctionPred(new_disjuncts)

    def negate(self) -> Predicate:
        return ConjunctionPred(tuple(d.negate() for d in self.disjuncts))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DisjunctionPred):
            return NotImplemented
        return frozenset(self.disjuncts) == frozenset(other.disjuncts)

    def __hash__(self) -> int:
        return hash(("Disj", frozenset(self.disjuncts)))

    def __repr__(self) -> str:
        return " ∨ ".join(repr(d) for d in self.disjuncts)


@dataclass(frozen=True)
class ImplicationPred(Predicate):
    """Implication ``antecedent ⇒ consequent``."""

    antecedent: Predicate
    consequent: Predicate

    def free_vars(self) -> FrozenSet[str]:
        return self.antecedent.free_vars() | self.consequent.free_vars()

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_ant = self.antecedent.substitute_pred(mapping)
        new_con = self.consequent.substitute_pred(mapping)
        if new_ant is self.antecedent and new_con is self.consequent:
            return self
        return ImplicationPred(new_ant, new_con)

    def negate(self) -> Predicate:
        # ¬(A ⇒ B) = A ∧ ¬B
        return ConjunctionPred((self.antecedent, self.consequent.negate()))

    def __repr__(self) -> str:
        return f"({self.antecedent!r}) ⇒ ({self.consequent!r})"


# ── Value predicates ───────────────────────────────────────────────────────


@dataclass(frozen=True)
class VarPred(Predicate):
    """A predicate that is just a named boolean variable."""

    var_name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return VarPred(new_name)

    def negate(self) -> Predicate:
        return NotPred(self)

    def __repr__(self) -> str:
        return self.var_name


@dataclass(frozen=True)
class IsInstancePred(Predicate):
    """Type-test predicate ``isinstance(var, type_name)``."""

    var_name: str
    type_name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return IsInstancePred(new_name, self.type_name)

    def negate(self) -> Predicate:
        return NotPred(self)

    def __repr__(self) -> str:
        return f"isinstance({self.var_name}, {self.type_name})"


@dataclass(frozen=True)
class IsNonePred(Predicate):
    """Predicate ``var is None``."""

    var_name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return IsNonePred(new_name)

    def negate(self) -> Predicate:
        return IsNotNonePred(self.var_name)

    def __repr__(self) -> str:
        return f"{self.var_name} is None"


@dataclass(frozen=True)
class IsNotNonePred(Predicate):
    """Predicate ``var is not None``."""

    var_name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return IsNotNonePred(new_name)

    def negate(self) -> Predicate:
        return IsNonePred(self.var_name)

    def __repr__(self) -> str:
        return f"{self.var_name} is not None"


@dataclass(frozen=True)
class MembershipPred(Predicate):
    """Predicate ``var in collection``."""

    var_name: str
    collection: Tuple[Any, ...]

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return MembershipPred(new_name, self.collection)

    def negate(self) -> Predicate:
        return NotPred(self)

    def __repr__(self) -> str:
        return f"{self.var_name} in {self.collection!r}"


@dataclass(frozen=True)
class LengthPred(Predicate):
    """Predicate on the length of a collection: ``len(var) op value``."""

    var_name: str
    op: ComparisonOp
    value: int

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var_name})

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_name = mapping.get(self.var_name, self.var_name)
        if new_name == self.var_name:
            return self
        return LengthPred(new_name, self.op, self.value)

    def negate(self) -> Predicate:
        negated = {
            ComparisonOp.EQ: ComparisonOp.NE,
            ComparisonOp.NE: ComparisonOp.EQ,
            ComparisonOp.LT: ComparisonOp.GE,
            ComparisonOp.LE: ComparisonOp.GT,
            ComparisonOp.GT: ComparisonOp.LE,
            ComparisonOp.GE: ComparisonOp.LT,
        }
        return LengthPred(self.var_name, negated[self.op], self.value)

    def __repr__(self) -> str:
        return f"len({self.var_name}) {self.op.value} {self.value}"


@dataclass(frozen=True)
class CallPred(Predicate):
    """Predicate referencing a named callable: ``func(var)``."""

    func_name: str
    args: Tuple[str, ...]

    def free_vars(self) -> FrozenSet[str]:
        return frozenset(self.args)

    def substitute_pred(self, mapping: Mapping[str, str]) -> Predicate:
        new_args = tuple(mapping.get(a, a) for a in self.args)
        if all(n == o for n, o in zip(new_args, self.args)):
            return self
        return CallPred(self.func_name, new_args)

    def negate(self) -> Predicate:
        return NotPred(self)

    def __repr__(self) -> str:
        args_str = ", ".join(self.args)
        return f"{self.func_name}({args_str})"


# ═══════════════════════════════════════════════════════════════════════════════
# Refinement type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class RefinementType(TypeBase):
    """Refinement type ``{v: τ | φ}``.

    Attributes:
        base: The base type *τ*.
        binder: The variable name *v* used in *predicate*.
        predicate: The refinement predicate *φ* over *v*.
    """

    base: TypeBase
    binder: str
    predicate: Predicate

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        # Do not substitute into the binder itself — it's bound
        filtered = {k: v for k, v in mapping.items() if k != self.binder}
        new_base = self.base.substitute(filtered)
        if new_base is self.base:
            return self
        return RefinementType(new_base, self.binder, self.predicate)

    def free_variables(self) -> FrozenSet[str]:
        base_fv = self.base.free_variables()
        pred_fv = self.predicate.free_vars() - {self.binder}
        return base_fv | pred_fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.base.walk()

    def strengthen(self, additional: Predicate) -> RefinementType:
        """Return a new refinement with *additional* conjoined to the predicate."""
        combined = ConjunctionPred((self.predicate, additional))
        return RefinementType(self.base, self.binder, combined)

    def weaken(self) -> TypeBase:
        """Forget the refinement, returning just the base type."""
        return self.base

    def is_trivial(self) -> bool:
        """``True`` when the predicate is trivially true."""
        return isinstance(self.predicate, TruePred)

    def to_base(self) -> TypeBase:
        """Alias for :meth:`weaken`."""
        return self.base

    def rename_binder(self, new_name: str) -> RefinementType:
        """Alpha-rename the binder variable."""
        if new_name == self.binder:
            return self
        new_pred = self.predicate.substitute_pred({self.binder: new_name})
        return RefinementType(self.base, new_name, new_pred)

    def __repr__(self) -> str:
        return f"{{{self.binder}: {self.base!r} | {self.predicate!r}}}"


# ═══════════════════════════════════════════════════════════════════════════════
# Qualifiers and qualified types
# ═══════════════════════════════════════════════════════════════════════════════


class Qualifier(ABC):
    """A lightweight named qualifier attached to a type."""

    @abstractmethod
    def name(self) -> str:
        """Short human-readable name of the qualifier."""
        ...

    def to_predicate(self, binder: str) -> Predicate:
        """Convert to an equivalent refinement predicate over *binder*.

        Subclasses should override this to provide a precise translation.
        The default returns ``True``, meaning "no additional constraint".
        """
        return TruePred()

    @abstractmethod
    def __eq__(self, other: object) -> bool: ...

    @abstractmethod
    def __hash__(self) -> int: ...

    def __repr__(self) -> str:
        return self.name()


# ── Built-in qualifiers ───────────────────────────────────────────────────


@dataclass(frozen=True)
class NonNull(Qualifier):
    """Value is guaranteed not to be ``None``."""

    def name(self) -> str:
        return "NonNull"

    def to_predicate(self, binder: str) -> Predicate:
        return IsNotNonePred(binder)


@dataclass(frozen=True)
class Positive(Qualifier):
    """Numeric value is strictly positive (``> 0``)."""

    def name(self) -> str:
        return "Positive"

    def to_predicate(self, binder: str) -> Predicate:
        return ComparisonPred(binder, ComparisonOp.GT, 0)


@dataclass(frozen=True)
class NonNegative(Qualifier):
    """Numeric value is non-negative (``>= 0``)."""

    def name(self) -> str:
        return "NonNegative"

    def to_predicate(self, binder: str) -> Predicate:
        return ComparisonPred(binder, ComparisonOp.GE, 0)


@dataclass(frozen=True)
class Negative(Qualifier):
    """Numeric value is strictly negative (``< 0``)."""

    def name(self) -> str:
        return "Negative"

    def to_predicate(self, binder: str) -> Predicate:
        return ComparisonPred(binder, ComparisonOp.LT, 0)


@dataclass(frozen=True)
class NonEmpty(Qualifier):
    """Collection is non-empty (``len > 0``)."""

    def name(self) -> str:
        return "NonEmpty"

    def to_predicate(self, binder: str) -> Predicate:
        return LengthPred(binder, ComparisonOp.GT, 0)


@dataclass(frozen=True)
class Sorted(Qualifier):
    """Collection is sorted in non-decreasing order."""

    def name(self) -> str:
        return "Sorted"

    def to_predicate(self, binder: str) -> Predicate:
        return CallPred("is_sorted", (binder,))


@dataclass(frozen=True)
class Unique(Qualifier):
    """Collection contains no duplicate elements."""

    def name(self) -> str:
        return "Unique"

    def to_predicate(self, binder: str) -> Predicate:
        return CallPred("all_unique", (binder,))


@dataclass(frozen=True)
class Bounded(Qualifier):
    """Numeric value is within an inclusive range ``[lo, hi]``."""

    lo: Union[int, float]
    hi: Union[int, float]

    def name(self) -> str:
        return f"Bounded[{self.lo}, {self.hi}]"

    def to_predicate(self, binder: str) -> Predicate:
        return ConjunctionPred((
            ComparisonPred(binder, ComparisonOp.GE, self.lo),
            ComparisonPred(binder, ComparisonOp.LE, self.hi),
        ))


@dataclass(frozen=True)
class MaxLength(Qualifier):
    """Collection has length at most *max_len*."""

    max_len: int

    def name(self) -> str:
        return f"MaxLength[{self.max_len}]"

    def to_predicate(self, binder: str) -> Predicate:
        return LengthPred(binder, ComparisonOp.LE, self.max_len)


@dataclass(frozen=True)
class MinLength(Qualifier):
    """Collection has length at least *min_len*."""

    min_len: int

    def name(self) -> str:
        return f"MinLength[{self.min_len}]"

    def to_predicate(self, binder: str) -> Predicate:
        return LengthPred(binder, ComparisonOp.GE, self.min_len)


@dataclass(frozen=True)
class Immutable(Qualifier):
    """Value is conceptually immutable (frozen)."""

    def name(self) -> str:
        return "Immutable"


@dataclass(frozen=True)
class Trusted(Qualifier):
    """Value comes from a trusted source (e.g. validated user input)."""

    def name(self) -> str:
        return "Trusted"


# ═══════════════════════════════════════════════════════════════════════════════
# Qualified type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True, eq=False)
class QualifiedType(TypeBase):
    """A base type annotated with one or more :class:`Qualifier` instances.

    ``QualifiedType(int, [Positive(), Bounded(0, 100)])`` means an ``int``
    that is both positive and bounded.
    """

    base: TypeBase
    qualifiers: Tuple[Qualifier, ...]

    def __post_init__(self) -> None:
        # Deduplicate qualifiers while preserving order
        seen: set[Qualifier] = set()
        deduped: list[Qualifier] = []
        for q in self.qualifiers:
            if q not in seen:
                seen.add(q)
                deduped.append(q)
        object.__setattr__(self, "qualifiers", tuple(deduped))

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_base = self.base.substitute(mapping)
        if new_base is self.base:
            return self
        return QualifiedType(new_base, self.qualifiers)

    def free_variables(self) -> FrozenSet[str]:
        return self.base.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.base.walk()

    def add_qualifier(self, q: Qualifier) -> QualifiedType:
        """Return a new qualified type with *q* added."""
        if q in self.qualifiers:
            return self
        return QualifiedType(self.base, self.qualifiers + (q,))

    def remove_qualifier(self, q: Qualifier) -> QualifiedType:
        """Return a new qualified type with *q* removed."""
        new_quals = tuple(x for x in self.qualifiers if x != q)
        if len(new_quals) == len(self.qualifiers):
            return self
        return QualifiedType(self.base, new_quals)

    def has_qualifier(self, qualifier_type: type) -> bool:
        """Check whether any qualifier is an instance of *qualifier_type*."""
        return any(isinstance(q, qualifier_type) for q in self.qualifiers)

    def to_refinement(self, binder: str = "v") -> RefinementType:
        """Convert to an equivalent :class:`RefinementType`."""
        predicates = [q.to_predicate(binder) for q in self.qualifiers]
        if not predicates:
            combined: Predicate = TruePred()
        elif len(predicates) == 1:
            combined = predicates[0]
        else:
            combined = ConjunctionPred(tuple(predicates))
        return RefinementType(self.base, binder, combined)

    def strip(self) -> TypeBase:
        """Return the base type without qualifiers."""
        return self.base

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, QualifiedType):
            return NotImplemented
        return self.base == other.base and frozenset(self.qualifiers) == frozenset(other.qualifiers)

    def __hash__(self) -> int:
        return hash(("Qualified", self.base, frozenset(self.qualifiers)))

    def __repr__(self) -> str:
        quals = ", ".join(q.name() for q in self.qualifiers)
        return f"{self.base!r} @[{quals}]"


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience constructors
# ═══════════════════════════════════════════════════════════════════════════════


def refine(base: TypeBase, binder: str, predicate: Predicate) -> RefinementType:
    """Shorthand constructor for :class:`RefinementType`."""
    return RefinementType(base, binder, predicate)


def positive_int() -> RefinementType:
    """``{v: int | v > 0}``."""
    from .base import INT_TYPE
    return RefinementType(INT_TYPE, "v", ComparisonPred("v", ComparisonOp.GT, 0))


def non_negative_int() -> RefinementType:
    """``{v: int | v >= 0}``."""
    from .base import INT_TYPE
    return RefinementType(INT_TYPE, "v", ComparisonPred("v", ComparisonOp.GE, 0))


def bounded_int(lo: int, hi: int) -> RefinementType:
    """``{v: int | lo <= v <= hi}``."""
    from .base import INT_TYPE
    pred = ConjunctionPred((
        ComparisonPred("v", ComparisonOp.GE, lo),
        ComparisonPred("v", ComparisonOp.LE, hi),
    ))
    return RefinementType(INT_TYPE, "v", pred)


def non_empty_list(element: TypeBase) -> RefinementType:
    """``{v: List[T] | len(v) > 0}``."""
    from .base import ListType
    return RefinementType(
        ListType(element), "v",
        LengthPred("v", ComparisonOp.GT, 0),
    )


def non_null(base: TypeBase) -> QualifiedType:
    """Wrap *base* with a ``NonNull`` qualifier."""
    return QualifiedType(base, (NonNull(),))
