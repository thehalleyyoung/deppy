"""Witness-bearing types for DepPy.

This module provides types that pair values with proof witnesses, supporting
the sheaf-descent framework's need to carry evidence alongside computed
results.  Key constructs:

- :class:`WitnessCarrier` — a value paired with a proof term and proposition.
- :class:`ExistentialWitness` — a witness for an existential statement.
- :class:`TransportWitness` — a witness for type transport along an equality path.
- :class:`RefinementWitness` — a witness that a value satisfies a refinement predicate.
- :class:`CompositeWitness` — a witness assembled from multiple sub-witnesses.
- :class:`WitnessRegistry` — a registry for storing and querying witnesses.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from .base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE


# ═══════════════════════════════════════════════════════════════════════════════
# Proof term hierarchy
# ═══════════════════════════════════════════════════════════════════════════════


class ProofTerm:
    """Abstract base for proof terms.

    A proof term is a piece of evidence that a proposition holds.
    """

    def description(self) -> str:
        """Human-readable description of what this proof term witnesses."""
        return "unknown proof term"

    def __repr__(self) -> str:
        return f"ProofTerm({self.description()})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ProofTerm):
            return NotImplemented
        return self.description() == other.description()

    def __hash__(self) -> int:
        return hash(self.description())


@dataclass(frozen=True)
class ReflProof(ProofTerm):
    """Reflexivity proof: ``refl : a = a``."""

    term: Any = None

    def description(self) -> str:
        if self.term is not None:
            return f"refl({self.term!r})"
        return "refl"


@dataclass(frozen=True)
class AssumptionProof(ProofTerm):
    """A proof that is assumed (axiom / hypothesis).

    Attributes:
        name: Name of the assumption.
        trust_level: A string indicating how trusted this assumption is.
    """

    name: str = "assumption"
    trust_level: str = "assumed"

    def description(self) -> str:
        return f"assume({self.name}, {self.trust_level})"


@dataclass(frozen=True)
class RuntimeCheckProof(ProofTerm):
    """A proof obtained by a runtime check (e.g. ``assert x > 0``).

    Attributes:
        check_description: What was checked.
        location: Optional source location (file:line).
    """

    check_description: str = ""
    location: str = ""

    def description(self) -> str:
        loc = f" at {self.location}" if self.location else ""
        return f"runtime_check({self.check_description}){loc}"


@dataclass(frozen=True)
class StaticProof(ProofTerm):
    """A proof obtained through static analysis or type checking.

    Attributes:
        method: The static analysis method used (e.g. "type_narrowing", "flow_analysis").
        detail: Additional detail.
    """

    method: str = ""
    detail: str = ""

    def description(self) -> str:
        return f"static({self.method}: {self.detail})"


@dataclass(frozen=True)
class CompositeProof(ProofTerm):
    """A proof assembled from multiple sub-proofs.

    Attributes:
        sub_proofs: The constituent proof terms.
        combiner: How they were combined (e.g. "conjunction", "transitivity").
    """

    sub_proofs: Tuple[ProofTerm, ...]
    combiner: str = "conjunction"

    def description(self) -> str:
        parts = ", ".join(p.description() for p in self.sub_proofs)
        return f"{self.combiner}({parts})"


@dataclass(frozen=True)
class TransitivityProof(ProofTerm):
    """Proof by transitivity: from ``a = b`` and ``b = c``, derive ``a = c``.

    Attributes:
        left: Proof of ``a = b``.
        right: Proof of ``b = c``.
    """

    left: ProofTerm = field(default_factory=ProofTerm)
    right: ProofTerm = field(default_factory=ProofTerm)

    def description(self) -> str:
        return f"trans({self.left.description()}, {self.right.description()})"


@dataclass(frozen=True)
class SymmetryProof(ProofTerm):
    """Proof by symmetry: from ``a = b`` derive ``b = a``.

    Attributes:
        inner: Proof of ``a = b``.
    """

    inner: ProofTerm = field(default_factory=ProofTerm)

    def description(self) -> str:
        return f"sym({self.inner.description()})"


@dataclass(frozen=True)
class CongruenceProof(ProofTerm):
    """Proof by congruence: from ``a = b`` derive ``f(a) = f(b)``.

    Attributes:
        inner: Proof of ``a = b``.
        function_name: The function being applied.
    """

    inner: ProofTerm = field(default_factory=ProofTerm)
    function_name: str = ""

    def description(self) -> str:
        return f"cong({self.function_name}, {self.inner.description()})"


# ═══════════════════════════════════════════════════════════════════════════════
# Witness carrier
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class WitnessCarrier:
    """A value paired with a proof witness and the proposition it witnesses.

    This is the primary structure used in DepPy's section framework to carry
    evidence alongside typed values.

    Attributes:
        value_type: The type of the witnessed value.
        witness: The proof term providing evidence.
        proposition: A description of what is being witnessed.
    """

    value_type: TypeBase
    witness: ProofTerm
    proposition: Any

    def with_strengthened_witness(self, new_witness: ProofTerm) -> WitnessCarrier:
        """Return a copy with a stronger (more specific) witness."""
        return WitnessCarrier(self.value_type, new_witness, self.proposition)

    def forget_witness(self) -> TypeBase:
        """Erase the witness, returning just the value type."""
        return self.value_type

    def is_assumed(self) -> bool:
        """``True`` if the witness is merely assumed (not proven)."""
        return isinstance(self.witness, AssumptionProof)

    def is_runtime_checked(self) -> bool:
        """``True`` if the witness comes from a runtime check."""
        return isinstance(self.witness, RuntimeCheckProof)

    def is_statically_proven(self) -> bool:
        """``True`` if the witness comes from static analysis."""
        return isinstance(self.witness, StaticProof)

    def combine(self, other: WitnessCarrier) -> WitnessCarrier:
        """Combine two witnesses via conjunction."""
        from .base import TupleType
        combined_type = TupleType((self.value_type, other.value_type))
        combined_witness = CompositeProof(
            (self.witness, other.witness), "conjunction"
        )
        combined_prop = (self.proposition, other.proposition)
        return WitnessCarrier(combined_type, combined_witness, combined_prop)

    def __repr__(self) -> str:
        return (
            f"WitnessCarrier({self.value_type!r}, "
            f"witness={self.witness.description()}, "
            f"prop={self.proposition!r})"
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, WitnessCarrier):
            return NotImplemented
        return (
            self.value_type == other.value_type
            and self.witness == other.witness
            and self.proposition == other.proposition
        )

    def __hash__(self) -> int:
        try:
            return hash((self.value_type, self.witness, self.proposition))
        except TypeError:
            return hash((self.value_type, self.witness))


# ═══════════════════════════════════════════════════════════════════════════════
# Existential witness
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ExistentialWitness:
    """Witness for an existential statement: ``∃x:A. P(x)``.

    Provides a concrete *witness_term* of type *witness_type* and evidence
    that the property is satisfied.

    Attributes:
        witness_term: The concrete value witnessing the existential.
        witness_type: The type of the witness term.
        property_satisfied: A description of the property ``P`` that holds.
    """

    witness_term: Any
    witness_type: TypeBase
    property_satisfied: Any

    def to_carrier(self) -> WitnessCarrier:
        """Convert to a :class:`WitnessCarrier`."""
        proof = RuntimeCheckProof(
            f"existential witness: {self.property_satisfied!r}"
        )
        return WitnessCarrier(self.witness_type, proof, self.property_satisfied)

    def map_witness(self, f: Callable[[Any], Any]) -> ExistentialWitness:
        """Apply *f* to the witness term."""
        return ExistentialWitness(
            f(self.witness_term),
            self.witness_type,
            self.property_satisfied,
        )

    def __repr__(self) -> str:
        return (
            f"ExistentialWitness(term={self.witness_term!r}, "
            f"type={self.witness_type!r}, "
            f"prop={self.property_satisfied!r})"
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ExistentialWitness):
            return NotImplemented
        return (
            self.witness_term == other.witness_term
            and self.witness_type == other.witness_type
            and self.property_satisfied == other.property_satisfied
        )

    def __hash__(self) -> int:
        try:
            return hash((self.witness_term, self.witness_type, self.property_satisfied))
        except TypeError:
            return hash((id(self.witness_term), self.witness_type))


# ═══════════════════════════════════════════════════════════════════════════════
# Transport witness
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class TransportWitness:
    """Witness for type transport along an equality path.

    Given a proof that ``source_type = target_type``, a value of
    *source_type* can be transported to *target_type*.

    Attributes:
        source_type: The original type.
        target_type: The transported-to type.
        path: The equality proof (a :class:`ProofTerm` or any evidence).
    """

    source_type: TypeBase
    target_type: TypeBase
    path: Any

    def transport(self, value_type: TypeBase) -> TypeBase:
        """Transport *value_type* from source to target.

        If *value_type* matches :attr:`source_type`, returns :attr:`target_type`.
        Otherwise returns *value_type* unchanged.
        """
        if value_type == self.source_type:
            return self.target_type
        return value_type

    def reverse(self) -> TransportWitness:
        """Reverse the transport direction."""
        reversed_path = self.path
        if isinstance(self.path, ProofTerm):
            reversed_path = SymmetryProof(self.path)
        return TransportWitness(self.target_type, self.source_type, reversed_path)

    def compose(self, other: TransportWitness) -> TransportWitness:
        """Compose transports: ``self`` followed by *other*.

        Requires ``self.target_type == other.source_type``.
        """
        if self.target_type != other.source_type:
            raise ValueError(
                f"cannot compose: {self.target_type!r} != {other.source_type!r}"
            )
        if isinstance(self.path, ProofTerm) and isinstance(other.path, ProofTerm):
            composed_path = TransitivityProof(self.path, other.path)
        else:
            composed_path = ("compose", self.path, other.path)
        return TransportWitness(self.source_type, other.target_type, composed_path)

    def is_identity(self) -> bool:
        """``True`` when source and target types are the same."""
        return self.source_type == self.target_type

    def __repr__(self) -> str:
        return (
            f"TransportWitness({self.source_type!r} → "
            f"{self.target_type!r}, path={self.path!r})"
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TransportWitness):
            return NotImplemented
        return (
            self.source_type == other.source_type
            and self.target_type == other.target_type
            and self.path == other.path
        )

    def __hash__(self) -> int:
        try:
            return hash((self.source_type, self.target_type, self.path))
        except TypeError:
            return hash((self.source_type, self.target_type))


# ═══════════════════════════════════════════════════════════════════════════════
# Refinement witness
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class RefinementWitness:
    """Witness that a value satisfies a refinement predicate.

    Attributes:
        base_type: The unrefined base type.
        predicate_description: A textual description of the refinement predicate.
        proof: The proof term evidencing satisfaction.
        binder: The binder variable used in the predicate.
    """

    base_type: TypeBase
    predicate_description: str
    proof: ProofTerm
    binder: str = "v"

    def to_carrier(self) -> WitnessCarrier:
        """Convert to a :class:`WitnessCarrier`."""
        return WitnessCarrier(
            self.base_type,
            self.proof,
            f"{self.binder} satisfies {self.predicate_description}",
        )

    def strengthen(self, additional_proof: ProofTerm, additional_desc: str) -> RefinementWitness:
        """Return a strengthened witness with an additional predicate."""
        combined = CompositeProof((self.proof, additional_proof), "conjunction")
        return RefinementWitness(
            self.base_type,
            f"({self.predicate_description}) ∧ ({additional_desc})",
            combined,
            self.binder,
        )

    def __repr__(self) -> str:
        return (
            f"RefinementWitness({self.base_type!r}, "
            f"{self.predicate_description!r}, "
            f"proof={self.proof.description()})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Composite witness
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CompositeWitness:
    """A witness assembled from multiple sub-witnesses.

    Used when a proposition is a conjunction and each conjunct has its own
    witness.

    Attributes:
        components: The individual sub-witnesses.
        combiner: How the components are combined (e.g. "conjunction", "pair").
    """

    components: Tuple[WitnessCarrier, ...]
    combiner: str = "conjunction"

    def to_carrier(self) -> WitnessCarrier:
        """Collapse into a single :class:`WitnessCarrier`."""
        if len(self.components) == 0:
            return WitnessCarrier(ANY_TYPE, ReflProof(), "trivial")
        if len(self.components) == 1:
            return self.components[0]
        result = self.components[0]
        for c in self.components[1:]:
            result = result.combine(c)
        return result

    @property
    def value_types(self) -> Tuple[TypeBase, ...]:
        """The value types of all components."""
        return tuple(c.value_type for c in self.components)

    @property
    def all_proofs(self) -> Tuple[ProofTerm, ...]:
        """All proof terms from the components."""
        return tuple(c.witness for c in self.components)

    def add(self, carrier: WitnessCarrier) -> CompositeWitness:
        """Return a new composite with an additional component."""
        return CompositeWitness(
            self.components + (carrier,),
            self.combiner,
        )

    def __repr__(self) -> str:
        parts = ", ".join(repr(c) for c in self.components)
        return f"CompositeWitness({self.combiner}: [{parts}])"


# ═══════════════════════════════════════════════════════════════════════════════
# Witness registry
# ═══════════════════════════════════════════════════════════════════════════════


class WitnessRegistry:
    """A mutable registry for storing and querying witnesses.

    Maintains a mapping from (value_type, proposition) pairs to their
    witnesses, enabling reuse of previously established evidence.
    """

    def __init__(self) -> None:
        self._entries: Dict[Tuple[TypeBase, Any], WitnessCarrier] = {}
        self._by_type: Dict[TypeBase, List[WitnessCarrier]] = {}

    def register(self, carrier: WitnessCarrier) -> None:
        """Register a witness carrier."""
        key = (carrier.value_type, _make_hashable(carrier.proposition))
        self._entries[key] = carrier
        self._by_type.setdefault(carrier.value_type, []).append(carrier)

    def lookup(
        self,
        value_type: TypeBase,
        proposition: Any = None,
    ) -> Optional[WitnessCarrier]:
        """Look up a registered witness.

        If *proposition* is ``None``, returns any witness for *value_type*.
        """
        if proposition is not None:
            key = (value_type, _make_hashable(proposition))
            return self._entries.get(key)
        witnesses = self._by_type.get(value_type)
        if witnesses:
            return witnesses[0]
        return None

    def lookup_all(self, value_type: TypeBase) -> List[WitnessCarrier]:
        """Return all registered witnesses for *value_type*."""
        return list(self._by_type.get(value_type, []))

    def has_witness(self, value_type: TypeBase, proposition: Any = None) -> bool:
        """Check whether a witness exists."""
        return self.lookup(value_type, proposition) is not None

    def remove(self, value_type: TypeBase, proposition: Any) -> bool:
        """Remove a specific witness.  Returns ``True`` if found."""
        key = (value_type, _make_hashable(proposition))
        removed = self._entries.pop(key, None)
        if removed is not None:
            by_type_list = self._by_type.get(value_type, [])
            self._by_type[value_type] = [
                w for w in by_type_list if w is not removed
            ]
            return True
        return False

    def clear(self) -> None:
        """Remove all registered witnesses."""
        self._entries.clear()
        self._by_type.clear()

    @property
    def size(self) -> int:
        """Number of registered witnesses."""
        return len(self._entries)

    def all_witnesses(self) -> List[WitnessCarrier]:
        """Return all registered witnesses."""
        return list(self._entries.values())

    def merge(self, other: WitnessRegistry) -> None:
        """Merge all witnesses from *other* into this registry."""
        for carrier in other.all_witnesses():
            self.register(carrier)

    def __repr__(self) -> str:
        return f"WitnessRegistry({self.size} entries)"


def _make_hashable(value: Any) -> Any:
    """Make a value hashable for use as a dict key."""
    try:
        hash(value)
        return value
    except TypeError:
        if isinstance(value, list):
            return tuple(_make_hashable(v) for v in value)
        if isinstance(value, dict):
            return tuple(sorted(
                (_make_hashable(k), _make_hashable(v))
                for k, v in value.items()
            ))
        if isinstance(value, set):
            return frozenset(_make_hashable(v) for v in value)
        return id(value)
