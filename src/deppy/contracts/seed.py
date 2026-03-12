"""Boundary seeds for sheaf-cover synthesis.

A *boundary seed* is the atomic unit of contract information fed into
cover synthesis.  Input seeds constrain function parameters; output seeds
constrain results.  Seeds carry provenance and trust, allowing the
synthesiser to weight them when combining contracts from different
sources (user annotations, inference, traces, library packs).
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
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
    Union,
)

from deppy.contracts.base import (
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TypeBase,
)
from deppy.core._protocols import TrustLevel

if TYPE_CHECKING:
    from deppy.core._protocols import SiteId


# ---------------------------------------------------------------------------
# SeedProvenance
# ---------------------------------------------------------------------------


class SeedProvenance(enum.Enum):
    """How the seed was obtained."""

    SOURCE_ANNOTATION = "source_annotation"
    SYNTHESIZED = "synthesized"
    PROOF_BACKED = "proof_backed"
    TRACE_BACKED = "trace_backed"
    LIBRARY_PACK = "library_pack"
    INFERRED = "inferred"


# ---------------------------------------------------------------------------
# BoundarySeed (base)
# ---------------------------------------------------------------------------


@dataclass
class BoundarySeed:
    """A seed for the input or output boundary of a cover.

    Seeds are the raw material consumed by cover synthesis (Stage 1 of
    the DepPy pipeline).  Each seed represents one atomic assertion about
    a boundary site, together with metadata about where it came from and
    how much to trust it.

    Attributes:
        site_id: Optional explicit site identifier (may be assigned later).
        predicate: The logical assertion.
        trust: How much to trust this seed.
        provenance: How the seed was produced.
        source_location: Where in source code the seed originates.
    """

    predicate: Predicate
    trust: TrustLevel = TrustLevel.RESIDUAL
    provenance: SeedProvenance = SeedProvenance.SOURCE_ANNOTATION
    source_location: Optional[SourceLocation] = None
    site_id: Optional[Any] = None  # Optional[SiteId], Any to avoid import issues

    def with_site(self, site_id: Any) -> BoundarySeed:
        """Return a copy assigned to a specific site."""
        return BoundarySeed(
            site_id=site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=self.provenance,
            source_location=self.source_location,
        )

    def with_trust(self, trust: TrustLevel) -> BoundarySeed:
        return BoundarySeed(
            site_id=self.site_id,
            predicate=self.predicate,
            trust=trust,
            provenance=self.provenance,
            source_location=self.source_location,
        )

    def with_provenance(self, prov: SeedProvenance) -> BoundarySeed:
        return BoundarySeed(
            site_id=self.site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
        )

    @property
    def is_trivial(self) -> bool:
        return self.predicate.is_trivially_true

    def pretty(self) -> str:
        site = f"@{self.site_id}" if self.site_id else "@?"
        return f"seed{site}[{self.trust.value}/{self.provenance.value}]: {self.predicate.pretty()}"

    def __repr__(self) -> str:
        return f"<BoundarySeed trust={self.trust.value} prov={self.provenance.value}>"


# ---------------------------------------------------------------------------
# InputBoundarySeed
# ---------------------------------------------------------------------------


@dataclass
class InputBoundarySeed(BoundarySeed):
    """Seed for the input boundary: becomes part of a synthesised ``requires``.

    An input seed constrains a specific parameter of a function.

    Attributes:
        parameter: Parameter name this seed constrains.
        requirement: The requirement predicate (may equal *predicate*).
    """

    parameter: str = ""
    requirement: Predicate = field(default_factory=Predicate.true_)

    def with_site(self, site_id: Any) -> InputBoundarySeed:
        return InputBoundarySeed(
            site_id=site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=self.provenance,
            source_location=self.source_location,
            parameter=self.parameter,
            requirement=self.requirement,
        )

    def bind_to_parameter(self, param: str) -> InputBoundarySeed:
        """Return a copy bound to a different parameter name."""
        bindings = {self.parameter: Term.var(param)} if self.parameter else {}
        new_pred = self.predicate.substitute(bindings) if bindings else self.predicate
        new_req = self.requirement.substitute(bindings) if bindings else self.requirement
        return InputBoundarySeed(
            site_id=self.site_id,
            predicate=new_pred,
            trust=self.trust,
            provenance=self.provenance,
            source_location=self.source_location,
            parameter=param,
            requirement=new_req,
        )

    def to_site_id(self) -> Any:
        """Generate a SiteId for this input seed."""
        from deppy.core._protocols import SiteId, SiteKind

        loc = None
        if self.source_location:
            loc = (self.source_location.file, self.source_location.line, self.source_location.col)
        return SiteId(
            kind=SiteKind.ARGUMENT_BOUNDARY,
            name=self.parameter,
            source_location=loc,
        )

    def pretty(self) -> str:
        return (
            f"input_seed({self.parameter})"
            f"[{self.trust.value}/{self.provenance.value}]: "
            f"{self.requirement.pretty()}"
        )

    def __repr__(self) -> str:
        return f"<InputBoundarySeed param={self.parameter!r}>"


# ---------------------------------------------------------------------------
# OutputBoundarySeed
# ---------------------------------------------------------------------------


@dataclass
class OutputBoundarySeed(BoundarySeed):
    """Seed for the output boundary: becomes part of a synthesised ``ensures``.

    An output seed constrains a specific component of the function result
    (usually just ``"result"``, but may be ``"raises:ValueError"`` for
    exceptional paths or ``"witness:name"`` for witness-carrying results).

    Attributes:
        result_component: Which result component (``"result"``, ``"raises:X"``, etc.).
        guarantee: The guarantee predicate.
    """

    result_component: str = "result"
    guarantee: Predicate = field(default_factory=Predicate.true_)

    def with_site(self, site_id: Any) -> OutputBoundarySeed:
        return OutputBoundarySeed(
            site_id=site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=self.provenance,
            source_location=self.source_location,
            result_component=self.result_component,
            guarantee=self.guarantee,
        )

    def bind_to_component(self, component: str) -> OutputBoundarySeed:
        """Return a copy bound to a different result component."""
        return OutputBoundarySeed(
            site_id=self.site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=self.provenance,
            source_location=self.source_location,
            result_component=component,
            guarantee=self.guarantee,
        )

    @property
    def is_exceptional(self) -> bool:
        return self.result_component.startswith("raises:")

    @property
    def is_witness(self) -> bool:
        return self.result_component.startswith("witness:")

    def to_site_id(self) -> Any:
        """Generate a SiteId for this output seed."""
        from deppy.core._protocols import SiteId, SiteKind

        loc = None
        if self.source_location:
            loc = (self.source_location.file, self.source_location.line, self.source_location.col)
        return SiteId(
            kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
            name=self.result_component,
            source_location=loc,
        )

    def pretty(self) -> str:
        return (
            f"output_seed({self.result_component})"
            f"[{self.trust.value}/{self.provenance.value}]: "
            f"{self.guarantee.pretty()}"
        )

    def __repr__(self) -> str:
        return f"<OutputBoundarySeed component={self.result_component!r}>"


# ---------------------------------------------------------------------------
# SeedCollection
# ---------------------------------------------------------------------------


class SeedCollection:
    """Collection of boundary seeds, with deduplication and merging.

    A ``SeedCollection`` accumulates seeds from multiple sources
    (annotations, inference, library packs) and provides methods to
    filter, deduplicate, and merge them before feeding into cover
    synthesis.
    """

    def __init__(
        self,
        *,
        input_seeds: Optional[List[InputBoundarySeed]] = None,
        output_seeds: Optional[List[OutputBoundarySeed]] = None,
    ) -> None:
        self.input_seeds: List[InputBoundarySeed] = input_seeds if input_seeds is not None else []
        self.output_seeds: List[OutputBoundarySeed] = output_seeds if output_seeds is not None else []

    # -- mutation -----------------------------------------------------------

    def add_input(self, seed: InputBoundarySeed) -> None:
        self.input_seeds.append(seed)

    def add_output(self, seed: OutputBoundarySeed) -> None:
        self.output_seeds.append(seed)

    def add(self, seed: BoundarySeed) -> None:
        """Add any boundary seed, dispatching by type."""
        if isinstance(seed, InputBoundarySeed):
            self.add_input(seed)
        elif isinstance(seed, OutputBoundarySeed):
            self.add_output(seed)
        else:
            # Generic seed — cannot classify; skip
            pass

    def add_all(self, seeds: Sequence[BoundarySeed]) -> None:
        """Add multiple seeds."""
        for s in seeds:
            self.add(s)

    # -- combination --------------------------------------------------------

    def merge(self, other: SeedCollection) -> SeedCollection:
        """Return a new collection containing seeds from both."""
        return SeedCollection(
            input_seeds=self.input_seeds + other.input_seeds,
            output_seeds=self.output_seeds + other.output_seeds,
        )

    # -- deduplication ------------------------------------------------------

    def deduplicate(self) -> SeedCollection:
        """Remove duplicate seeds (same predicate text and parameter/component).

        When duplicates exist, the one with higher trust wins.
        """
        deduped_inputs = _dedup_input_seeds(self.input_seeds)
        deduped_outputs = _dedup_output_seeds(self.output_seeds)
        return SeedCollection(input_seeds=deduped_inputs, output_seeds=deduped_outputs)

    # -- filtering ----------------------------------------------------------

    def filter_by_trust(self, min_trust: TrustLevel) -> SeedCollection:
        """Return only seeds at or above *min_trust*."""
        threshold = _TRUST_ORD.get(min_trust, 0)

        def _keep(seed: BoundarySeed) -> bool:
            return _TRUST_ORD.get(seed.trust, 0) >= threshold

        return SeedCollection(
            input_seeds=[s for s in self.input_seeds if _keep(s)],
            output_seeds=[s for s in self.output_seeds if _keep(s)],
        )

    def filter_by_provenance(self, *provenances: SeedProvenance) -> SeedCollection:
        """Return only seeds with one of the given provenances."""
        prov_set = set(provenances)
        return SeedCollection(
            input_seeds=[s for s in self.input_seeds if s.provenance in prov_set],
            output_seeds=[s for s in self.output_seeds if s.provenance in prov_set],
        )

    def filter_nontrivial(self) -> SeedCollection:
        """Drop seeds whose predicate is trivially true."""
        return SeedCollection(
            input_seeds=[s for s in self.input_seeds if not s.is_trivial],
            output_seeds=[s for s in self.output_seeds if not s.is_trivial],
        )

    def inputs_for_param(self, param: str) -> List[InputBoundarySeed]:
        """Get all input seeds for a specific parameter."""
        return [s for s in self.input_seeds if s.parameter == param]

    def outputs_for_component(self, component: str) -> List[OutputBoundarySeed]:
        """Get all output seeds for a specific result component."""
        return [s for s in self.output_seeds if s.result_component == component]

    # -- queries ------------------------------------------------------------

    @property
    def all_input_params(self) -> FrozenSet[str]:
        return frozenset(s.parameter for s in self.input_seeds)

    @property
    def all_output_components(self) -> FrozenSet[str]:
        return frozenset(s.result_component for s in self.output_seeds)

    def is_empty(self) -> bool:
        return not self.input_seeds and not self.output_seeds

    def __len__(self) -> int:
        return len(self.input_seeds) + len(self.output_seeds)

    def __iter__(self) -> Iterator[BoundarySeed]:
        yield from self.input_seeds
        yield from self.output_seeds

    # -- site assignment ----------------------------------------------------

    def assign_sites(self) -> SeedCollection:
        """Auto-assign SiteIds to seeds that don't have one."""
        new_inputs = []
        for s in self.input_seeds:
            if s.site_id is None:
                new_inputs.append(s.with_site(s.to_site_id()))
            else:
                new_inputs.append(s)

        new_outputs = []
        for s in self.output_seeds:
            if s.site_id is None:
                new_outputs.append(s.with_site(s.to_site_id()))
            else:
                new_outputs.append(s)

        return SeedCollection(input_seeds=new_inputs, output_seeds=new_outputs)

    # -- conversion to boundary sections ------------------------------------

    def to_input_boundary(self) -> Any:
        """Convert input seeds to a BoundarySection."""
        from deppy.core._protocols import BoundarySection, LocalSection, SiteId, SiteKind

        sites: Dict[Any, Any] = {}
        for seed in self.input_seeds:
            sid = seed.site_id or seed.to_site_id()
            section = LocalSection(
                site_id=sid,
                refinements={"predicate": seed.predicate.pretty()},
                trust=seed.trust,
                provenance=seed.provenance.value,
            )
            sites[sid] = section

        return BoundarySection(boundary_sites=sites, is_input=True)

    def to_output_boundary(self) -> Any:
        """Convert output seeds to a BoundarySection."""
        from deppy.core._protocols import BoundarySection, LocalSection, SiteId, SiteKind

        sites: Dict[Any, Any] = {}
        for seed in self.output_seeds:
            sid = seed.site_id or seed.to_site_id()
            section = LocalSection(
                site_id=sid,
                refinements={"predicate": seed.predicate.pretty()},
                trust=seed.trust,
                provenance=seed.provenance.value,
            )
            sites[sid] = section

        return BoundarySection(boundary_sites=sites, is_input=False)

    # -- display ------------------------------------------------------------

    def pretty(self) -> str:
        lines: List[str] = []
        if self.input_seeds:
            lines.append("Input seeds:")
            for s in self.input_seeds:
                lines.append(f"  {s.pretty()}")
        if self.output_seeds:
            lines.append("Output seeds:")
            for s in self.output_seeds:
                lines.append(f"  {s.pretty()}")
        return "\n".join(lines) if lines else "<empty SeedCollection>"

    def __repr__(self) -> str:
        return f"<SeedCollection inputs={len(self.input_seeds)} outputs={len(self.output_seeds)}>"


# ---------------------------------------------------------------------------
# Deduplication helpers
# ---------------------------------------------------------------------------


def _dedup_input_seeds(seeds: List[InputBoundarySeed]) -> List[InputBoundarySeed]:
    """Deduplicate input seeds by (parameter, predicate text), keeping highest trust."""
    best: Dict[Tuple[str, str], InputBoundarySeed] = {}
    for s in seeds:
        key = (s.parameter, s.requirement.pretty())
        existing = best.get(key)
        if existing is None or _TRUST_ORD.get(s.trust, 0) > _TRUST_ORD.get(existing.trust, 0):
            best[key] = s
    return list(best.values())


def _dedup_output_seeds(seeds: List[OutputBoundarySeed]) -> List[OutputBoundarySeed]:
    """Deduplicate output seeds by (component, predicate text), keeping highest trust."""
    best: Dict[Tuple[str, str], OutputBoundarySeed] = {}
    for s in seeds:
        key = (s.result_component, s.guarantee.pretty())
        existing = best.get(key)
        if existing is None or _TRUST_ORD.get(s.trust, 0) > _TRUST_ORD.get(existing.trust, 0):
            best[key] = s
    return list(best.values())


# Trust ordering
_TRUST_ORD: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}
