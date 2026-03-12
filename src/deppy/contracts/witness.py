"""Witness-carrying contracts.

A *witness* is a piece of evidence that a proposition holds.  In the
sheaf framework, witnesses travel as extra data on :class:`LocalSection`
objects.  A ``WitnessContract`` declares that a function produces a
witness; ``WitnessExport`` / ``WitnessImport`` model how witnesses flow
between call sites.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.contracts.base import (
    Contract,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
    TypeBase,
)
from deppy.core._protocols import TrustLevel

if TYPE_CHECKING:
    from deppy.contracts.seed import BoundarySeed


# ---------------------------------------------------------------------------
# WitnessContract
# ---------------------------------------------------------------------------


class WitnessContract(Contract):
    """Witness-carrying contract: the result carries proof evidence.

    A witness contract declares that a function not only computes a
    result but also produces evidence (a *witness*) that a certain
    proposition holds.  The witness is attached to the
    :class:`~deppy.core._protocols.LocalSection` at the call-result site
    and can be consumed downstream.

    Usage::

        @deppy.witness("sorted_proof", proposition=lambda xs: is_sorted(xs))
        def sort(xs: List[int]) -> List[int]: ...

    Attributes:
        proposition: The proposition that the witness evidences.
        witness_name: A name for the witness (for import/export tracking).
        witness_type: Optional type of the witness value itself.
        description: Optional human-readable gloss.
    """

    def __init__(
        self,
        *,
        witness_name: str,
        proposition: Optional[Predicate] = None,
        proposition_fn: Optional[Callable[..., bool]] = None,
        witness_type: Optional[TypeBase] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.PROOF_BACKED,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.witness_name: str = witness_name
        self.witness_type: Optional[TypeBase] = witness_type
        self.description: Optional[str] = description

        if proposition is not None:
            self.proposition: Predicate = proposition
        elif proposition_fn is not None:
            self.proposition = Predicate.from_callable(proposition_fn, description=description)
        else:
            self.proposition = Predicate.true_()

    # -- Contract interface --------------------------------------------------

    def to_predicate(self) -> Predicate:
        return self.proposition

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "proof_backed": SeedProvenance.PROOF_BACKED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.PROOF_BACKED)

        return OutputBoundarySeed(
            predicate=self.proposition,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
            result_component=f"witness:{self.witness_name}",
            guarantee=self.proposition,
        )

    def pretty(self) -> str:
        type_str = f": {self.witness_type.pretty()}" if self.witness_type else ""
        desc = f"  # {self.description}" if self.description else ""
        return f"witness({self.witness_name}{type_str}) ⊢ {self.proposition.pretty()}{desc}"

    # -- operations ----------------------------------------------------------

    def to_export(self) -> WitnessExport:
        """Convert this contract into a WitnessExport for inter-procedural flow."""
        return WitnessExport(
            name=self.witness_name,
            proposition=self.proposition,
            carrier=self.witness_type,
        )

    def bind_proposition(self, bindings: Dict[str, Term]) -> WitnessContract:
        """Substitute variables in the witness proposition."""
        result = copy.copy(self)
        result.proposition = self.proposition.substitute(bindings)
        return result

    def evaluate(self, env: Mapping[str, Any]) -> bool:
        """Evaluate whether the witness proposition holds."""
        return self.proposition.evaluate(env)

    def __repr__(self) -> str:
        return f"<WitnessContract name={self.witness_name!r} prop={self.proposition.pretty()!r}>"


# ---------------------------------------------------------------------------
# WitnessExport
# ---------------------------------------------------------------------------


@dataclass
class WitnessExport:
    """Exported witness from a function.

    When a function decorated with ``@witness`` is called, it produces a
    ``WitnessExport`` that is stored on the call-result
    :class:`~deppy.core._protocols.LocalSection` and can be imported by
    downstream callers.

    Attributes:
        name: Witness identifier.
        proposition: What the witness proves.
        carrier: Optional type of the witness value.
    """

    name: str
    proposition: Predicate
    carrier: Optional[TypeBase] = None

    def to_section_data(self) -> Dict[str, Any]:
        """Serialise into the ``witnesses`` dict of a LocalSection."""
        return {
            self.name: {
                "proposition": self.proposition.pretty(),
                "carrier": self.carrier.pretty() if self.carrier else None,
            }
        }

    def reindex(self, mapping: Dict[str, str]) -> WitnessExport:
        """Rename variables in the proposition (for parameter reindexing).

        *mapping* is ``{formal_param: actual_arg}`` at a call site.
        """
        bindings = {k: Term.var(v) for k, v in mapping.items()}
        new_prop = self.proposition.substitute(bindings)
        return WitnessExport(name=self.name, proposition=new_prop, carrier=self.carrier)

    def matches_import(self, imp: WitnessImport) -> bool:
        """Check whether this export satisfies *imp*."""
        if self.name != imp.witness_name:
            return False
        # After reindexing, the propositions should match structurally.
        # As a conservative check, compare pretty-printed forms.
        reindexed = self.reindex(imp.reindexing)
        return reindexed.proposition.pretty() == imp.proposition.pretty()

    def pretty(self) -> str:
        carrier = f": {self.carrier.pretty()}" if self.carrier else ""
        return f"export witness {self.name}{carrier} ⊢ {self.proposition.pretty()}"

    def __repr__(self) -> str:
        return f"<WitnessExport {self.name!r}>"


# ---------------------------------------------------------------------------
# WitnessImport
# ---------------------------------------------------------------------------


@dataclass
class WitnessImport:
    """Imported witness at a call site.

    When code relies on a witness produced by another function, it
    declares a ``WitnessImport``.  The reindexing maps formal parameter
    names of the producing function to the actual arguments at the
    consuming call site.

    Attributes:
        source_function: Qualified name of the function that exports the witness.
        witness_name: Which witness to import.
        proposition: The proposition as understood at the import site.
        reindexing: ``{formal_param: actual_arg}`` mapping.
    """

    source_function: str
    witness_name: str
    proposition: Predicate
    reindexing: Dict[str, str] = field(default_factory=dict)

    def apply_reindexing(self) -> Predicate:
        """Return the proposition with reindexing applied."""
        if not self.reindexing:
            return self.proposition
        bindings = {k: Term.var(v) for k, v in self.reindexing.items()}
        return self.proposition.substitute(bindings)

    def is_compatible_with(self, export: WitnessExport) -> bool:
        """Check whether *export* can satisfy this import."""
        return export.matches_import(self)

    def with_reindexing(self, mapping: Dict[str, str]) -> WitnessImport:
        """Return a copy with updated reindexing."""
        merged = dict(self.reindexing)
        merged.update(mapping)
        return WitnessImport(
            source_function=self.source_function,
            witness_name=self.witness_name,
            proposition=self.proposition,
            reindexing=merged,
        )

    def pretty(self) -> str:
        reindex_str = ""
        if self.reindexing:
            pairs = ", ".join(f"{k}↦{v}" for k, v in self.reindexing.items())
            reindex_str = f" [{pairs}]"
        return (
            f"import witness {self.witness_name} from {self.source_function}"
            f"{reindex_str} ⊢ {self.proposition.pretty()}"
        )

    def __repr__(self) -> str:
        return f"<WitnessImport {self.witness_name!r} from {self.source_function!r}>"


# ---------------------------------------------------------------------------
# WitnessRegistry (collection of exports for matching)
# ---------------------------------------------------------------------------


class WitnessRegistry:
    """Registry of available witness exports, for resolving imports.

    The registry collects all ``WitnessExport`` objects from analysed
    functions and provides lookup by name and proposition matching.
    """

    def __init__(self) -> None:
        self._by_name: Dict[str, List[WitnessExport]] = {}
        self._by_function: Dict[str, List[WitnessExport]] = {}

    def register(self, function_name: str, export: WitnessExport) -> None:
        """Register a witness export from a function."""
        self._by_name.setdefault(export.name, []).append(export)
        self._by_function.setdefault(function_name, []).append(export)

    def register_contract(self, function_name: str, contract: WitnessContract) -> None:
        """Register all exports from a WitnessContract."""
        self.register(function_name, contract.to_export())

    def lookup_by_name(self, name: str) -> List[WitnessExport]:
        """Find all exports with the given witness name."""
        return list(self._by_name.get(name, []))

    def lookup_by_function(self, function_name: str) -> List[WitnessExport]:
        """Find all exports from a given function."""
        return list(self._by_function.get(function_name, []))

    def resolve_import(self, imp: WitnessImport) -> Optional[WitnessExport]:
        """Find an export that satisfies the given import.

        Returns the first matching export, or None if no match.
        """
        candidates = self._by_name.get(imp.witness_name, [])
        for export in candidates:
            if export.matches_import(imp):
                return export
        return None

    def all_exports(self) -> List[WitnessExport]:
        """All registered exports."""
        result: List[WitnessExport] = []
        for exports in self._by_name.values():
            result.extend(exports)
        return result

    def __len__(self) -> int:
        return sum(len(v) for v in self._by_name.values())

    def __repr__(self) -> str:
        return f"<WitnessRegistry exports={len(self)} functions={len(self._by_function)}>"


# ---------------------------------------------------------------------------
# Decorator factory
# ---------------------------------------------------------------------------


def witness(
    name: str,
    *,
    proposition: Optional[Callable[..., bool]] = None,
    witness_type: Optional[Any] = None,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.PROOF_BACKED,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.witness``.

    Usage::

        @witness("sorted_proof", proposition=lambda xs: all(xs[i] <= xs[i+1] for i in range(len(xs)-1)))
        def sort(xs: List[int]) -> List[int]: ...
    """

    wt: Optional[TypeBase] = None
    if witness_type is not None:
        wt = TypeBase.from_annotation(witness_type)

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        contract = WitnessContract(
            witness_name=name,
            proposition_fn=proposition,
            witness_type=wt,
            description=description,
            trust=trust,
        )
        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator
