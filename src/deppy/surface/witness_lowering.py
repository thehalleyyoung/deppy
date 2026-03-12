"""Witness lowering: witness declarations to witness carriers and cover sites.

This module converts user-facing witness declarations (``@deppy.witness``)
into *witness carriers* and injects them into the sheaf cover.  Witnesses
are typed evidence that a proposition holds; they travel on
``LocalSection`` objects and are consumed downstream via witness-flow
restriction maps.

The lowering pipeline is:

1. Parse decorator data into ``WitnessSeed`` frozen intermediates.
2. ``lower_witness_declaration`` converts a ``WitnessContract`` into a
   ``WitnessSeed``.
3. ``inject_witness_into_cover`` enriches a ``Cover`` with a witness-
   exporting proof site and witness-flow morphisms.
4. Variant seeds: ``ExistentialWitnessSeed``, ``TransportWitnessSeed``,
   ``DecreasesWitnessSeed``.
"""

from __future__ import annotations

import enum
import uuid
from dataclasses import dataclass, field
from typing import (
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
    ContractSet,
    Predicate as ContractPredicate,
    SourceLocation,
    Term,
)
from deppy.contracts.base import TypeBase as ContractTypeBase
from deppy.contracts.witness import (
    WitnessContract,
    WitnessExport,
    WitnessImport,
)
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.static_analysis.observation_sites import (
    SourceSpan,
    make_proof_site,
    make_return_boundary_site,
)
from deppy.static_analysis.restriction_maps import (
    make_witness_flow_restriction,
    make_proof_transport,
)
from deppy.types.carriers import CarrierSchema, SchemaConstraint
from deppy.types.witnesses import (
    ExistentialWitness,
    ProofTerm,
    AssumptionProof,
    RuntimeCheckProof,
    StaticProof,
    TransportWitness,
    WitnessCarrier,
)


# ---------------------------------------------------------------------------
# WitnessKind: variant classification
# ---------------------------------------------------------------------------

class WitnessKind(enum.Enum):
    """Classification of witness seed variants."""
    GENERIC = "generic"
    EXISTENTIAL = "existential"
    TRANSPORT = "transport"
    DECREASES = "decreases"
    REFINEMENT = "refinement"


# ---------------------------------------------------------------------------
# WitnessSeed: generic frozen intermediate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class WitnessSeed:
    """Frozen intermediate for a lowered witness declaration.

    A witness seed pairs a witness name with the proposition it
    evidences, a witness type (if known), and a target site for
    injection into the cover.

    Attributes:
        witness_name: Identifier for the witness.
        proposition: The proposition the witness evidences.
        witness_kind: Which variant of witness this is.
        witness_type: Optional type of the witness value.
        construction: How the witness is constructed (AST, callable, etc.).
        target: Target site name or site id for injection.
        trust: Trust level.
        source_location: Source code location.
        description: Optional human-readable gloss.
        uid: Unique identifier.
    """
    witness_name: str
    proposition: ContractPredicate
    witness_kind: WitnessKind = WitnessKind.GENERIC
    witness_type: Optional[ContractTypeBase] = None
    construction: Optional[Any] = None
    target: Optional[str] = None
    trust: TrustLevel = TrustLevel.PROOF_BACKED
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def is_trivial(self) -> bool:
        return self.proposition.is_trivially_true

    @property
    def free_variables(self) -> FrozenSet[str]:
        return self.proposition.free_variables()

    def to_site_id(self, func_name: str) -> SiteId:
        """Generate a SiteId for this witness's proof site."""
        loc: Optional[Tuple[str, int, int]] = None
        if self.source_location:
            loc = (
                self.source_location.file,
                self.source_location.line,
                self.source_location.col,
            )
        return SiteId(
            kind=SiteKind.PROOF,
            name=f"{func_name}.witness_{self.witness_name}",
            source_location=loc,
        )

    def to_local_section(self, func_name: str) -> LocalSection:
        """Create a LocalSection carrying the witness proposition."""
        sid = self.to_site_id(func_name)
        refinements: Dict[str, Any] = {
            "witness_name": self.witness_name,
            "proposition": self.proposition.pretty(),
            "witness_kind": self.witness_kind.value,
        }
        if self.witness_type is not None:
            refinements["witness_type"] = self.witness_type.pretty()
        if self.description:
            refinements["description"] = self.description

        witnesses: Dict[str, Any] = {
            self.witness_name: {
                "proposition": self.proposition.pretty(),
                "kind": self.witness_kind.value,
                "carrier": (
                    self.witness_type.pretty()
                    if self.witness_type
                    else None
                ),
            }
        }

        return LocalSection(
            site_id=sid,
            refinements=refinements,
            trust=self.trust,
            provenance=f"witness:{self.witness_name}",
            witnesses=witnesses,
        )

    def to_witness_export(self) -> WitnessExport:
        """Convert to a ``WitnessExport`` for inter-procedural flow."""
        return WitnessExport(
            name=self.witness_name,
            proposition=self.proposition,
            carrier=self.witness_type,
        )

    def pretty(self) -> str:
        ty = f": {self.witness_type.pretty()}" if self.witness_type else ""
        desc = f" # {self.description}" if self.description else ""
        return (
            f"WitnessSeed({self.witness_name}{ty})"
            f"[{self.witness_kind.value}] |-> "
            f"{self.proposition.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return (
            f"<WitnessSeed {self.witness_name!r} "
            f"kind={self.witness_kind.value}>"
        )


# ---------------------------------------------------------------------------
# Variant seeds
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExistentialWitnessSeed(WitnessSeed):
    """Witness seed for an existential statement: there exists x such that P(x).

    The construction should be a term or callable that provides the
    concrete witness value.

    Attributes:
        existential_var: The bound variable of the existential.
        body_proposition: The body proposition P(x).
    """
    existential_var: str = "x"
    body_proposition: Optional[ContractPredicate] = None

    def __post_init__(self) -> None:
        # Frozen dataclass: cannot assign directly, use object.__setattr__
        if self.witness_kind != WitnessKind.EXISTENTIAL:
            object.__setattr__(self, "witness_kind", WitnessKind.EXISTENTIAL)

    def to_local_section(self, func_name: str) -> LocalSection:
        """Override to add existential-specific data."""
        section = super().to_local_section(func_name)
        extra_refinements = dict(section.refinements)
        extra_refinements["existential_var"] = self.existential_var
        if self.body_proposition is not None:
            extra_refinements["body_proposition"] = self.body_proposition.pretty()
        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=extra_refinements,
            trust=section.trust,
            provenance=section.provenance,
            witnesses=dict(section.witnesses),
        )

    def pretty(self) -> str:
        body = (
            self.body_proposition.pretty()
            if self.body_proposition
            else self.proposition.pretty()
        )
        desc = f" # {self.description}" if self.description else ""
        return (
            f"ExistentialWitness({self.witness_name}): "
            f"exists {self.existential_var}. {body}{desc}"
        )


@dataclass(frozen=True)
class TransportWitnessSeed(WitnessSeed):
    """Witness seed for type transport along an equality path.

    Carries evidence that a value can be transported from one type
    context to another.

    Attributes:
        source_type_name: Name/description of the source type.
        target_type_name: Name/description of the target type.
        path_description: Description of the equality path.
    """
    source_type_name: str = ""
    target_type_name: str = ""
    path_description: str = ""

    def __post_init__(self) -> None:
        if self.witness_kind != WitnessKind.TRANSPORT:
            object.__setattr__(self, "witness_kind", WitnessKind.TRANSPORT)

    def to_local_section(self, func_name: str) -> LocalSection:
        """Override to add transport-specific data."""
        section = super().to_local_section(func_name)
        extra_refinements = dict(section.refinements)
        extra_refinements["source_type"] = self.source_type_name
        extra_refinements["target_type"] = self.target_type_name
        extra_refinements["path"] = self.path_description
        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=extra_refinements,
            trust=section.trust,
            provenance=section.provenance,
            witnesses=dict(section.witnesses),
        )

    def pretty(self) -> str:
        desc = f" # {self.description}" if self.description else ""
        return (
            f"TransportWitness({self.witness_name}): "
            f"{self.source_type_name} -> {self.target_type_name} "
            f"via {self.path_description}{desc}"
        )


@dataclass(frozen=True)
class DecreasesWitnessSeed(WitnessSeed):
    """Witness seed for a well-founded decreasing measure.

    Used with ``@decreases`` to provide evidence that a ranking
    function decreases on each loop iteration or recursive call.

    Attributes:
        ranking_expression: The expression that decreases.
        bound_type: Type of the well-founded order (e.g. ``"nat"``).
        variables: Variables involved in the ranking expression.
    """
    ranking_expression: str = ""
    bound_type: str = "nat"
    variables: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.witness_kind != WitnessKind.DECREASES:
            object.__setattr__(self, "witness_kind", WitnessKind.DECREASES)

    def to_local_section(self, func_name: str) -> LocalSection:
        """Override to add decreases-specific data."""
        section = super().to_local_section(func_name)
        extra_refinements = dict(section.refinements)
        extra_refinements["ranking_expression"] = self.ranking_expression
        extra_refinements["bound_type"] = self.bound_type
        if self.variables:
            extra_refinements["ranking_variables"] = list(self.variables)
        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=extra_refinements,
            trust=section.trust,
            provenance=section.provenance,
            witnesses=dict(section.witnesses),
        )

    def pretty(self) -> str:
        desc = f" # {self.description}" if self.description else ""
        return (
            f"DecreasesWitness({self.witness_name}): "
            f"decreases {self.ranking_expression} : {self.bound_type}{desc}"
        )


# ---------------------------------------------------------------------------
# Lowering functions
# ---------------------------------------------------------------------------

def lower_witness_declaration(
    contract: WitnessContract,
    *,
    func_name: str = "",
) -> WitnessSeed:
    """Lower a ``WitnessContract`` into a ``WitnessSeed``.

    Parameters:
        contract: The witness contract to lower.
        func_name: Name of the function producing the witness.

    Returns:
        A ``WitnessSeed`` intermediate.
    """
    return WitnessSeed(
        witness_name=contract.witness_name,
        proposition=contract.proposition,
        witness_kind=WitnessKind.GENERIC,
        witness_type=contract.witness_type,
        target=func_name if func_name else None,
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
    )


def lower_existential_witness(
    witness_name: str,
    proposition: ContractPredicate,
    existential_var: str,
    *,
    body_proposition: Optional[ContractPredicate] = None,
    witness_type: Optional[ContractTypeBase] = None,
    construction: Optional[Any] = None,
    source_location: Optional[SourceLocation] = None,
    description: Optional[str] = None,
) -> ExistentialWitnessSeed:
    """Create an existential witness seed.

    Parameters:
        witness_name: Name for the witness.
        proposition: The full existential proposition.
        existential_var: The bound variable.
        body_proposition: The body of the existential (P(x)).
        witness_type: Type of the witness value.
        construction: How to compute the witness.
        source_location: Source code location.
        description: Optional gloss.

    Returns:
        An ``ExistentialWitnessSeed``.
    """
    return ExistentialWitnessSeed(
        witness_name=witness_name,
        proposition=proposition,
        witness_kind=WitnessKind.EXISTENTIAL,
        witness_type=witness_type,
        construction=construction,
        trust=TrustLevel.PROOF_BACKED,
        source_location=source_location,
        description=description,
        existential_var=existential_var,
        body_proposition=body_proposition,
    )


def lower_transport_witness(
    witness_name: str,
    proposition: ContractPredicate,
    source_type_name: str,
    target_type_name: str,
    *,
    path_description: str = "",
    source_location: Optional[SourceLocation] = None,
    description: Optional[str] = None,
) -> TransportWitnessSeed:
    """Create a transport witness seed.

    Parameters:
        witness_name: Name for the witness.
        proposition: The transport proposition.
        source_type_name: Source type description.
        target_type_name: Target type description.
        path_description: Equality path description.
        source_location: Source code location.
        description: Optional gloss.

    Returns:
        A ``TransportWitnessSeed``.
    """
    return TransportWitnessSeed(
        witness_name=witness_name,
        proposition=proposition,
        witness_kind=WitnessKind.TRANSPORT,
        trust=TrustLevel.PROOF_BACKED,
        source_location=source_location,
        description=description,
        source_type_name=source_type_name,
        target_type_name=target_type_name,
        path_description=path_description,
    )


def lower_decreases_witness(
    witness_name: str,
    proposition: ContractPredicate,
    ranking_expression: str,
    *,
    bound_type: str = "nat",
    variables: Sequence[str] = (),
    source_location: Optional[SourceLocation] = None,
    description: Optional[str] = None,
) -> DecreasesWitnessSeed:
    """Create a decreases witness seed.

    Parameters:
        witness_name: Name for the witness.
        proposition: The termination proposition.
        ranking_expression: The decreasing expression.
        bound_type: Type of the well-founded order.
        variables: Variables in the ranking expression.
        source_location: Source code location.
        description: Optional gloss.

    Returns:
        A ``DecreasesWitnessSeed``.
    """
    return DecreasesWitnessSeed(
        witness_name=witness_name,
        proposition=proposition,
        witness_kind=WitnessKind.DECREASES,
        trust=TrustLevel.PROOF_BACKED,
        source_location=source_location,
        description=description,
        ranking_expression=ranking_expression,
        bound_type=bound_type,
        variables=tuple(variables),
    )


# ---------------------------------------------------------------------------
# Lower all witnesses from a ContractSet
# ---------------------------------------------------------------------------

def lower_witness_contracts(
    contract_set: ContractSet,
    func_name: str,
) -> List[WitnessSeed]:
    """Lower all witness contracts in a ``ContractSet``.

    Parameters:
        contract_set: The contract set to lower.
        func_name: The function name.

    Returns:
        A list of ``WitnessSeed`` instances.
    """
    seeds: List[WitnessSeed] = []
    for wit in contract_set.witnesses:
        if isinstance(wit, WitnessContract):
            seed = lower_witness_declaration(wit, func_name=func_name)
            seeds.append(seed)
    return seeds


# ---------------------------------------------------------------------------
# inject_witness_into_cover
# ---------------------------------------------------------------------------

def inject_witness_into_cover(
    seed: WitnessSeed,
    cover: Cover,
    func_name: str,
    *,
    consumer_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Cover:
    """Inject a witness seed into the cover as a proof site with witness flow.

    Creates a proof site for the witness and optionally adds
    witness-flow restriction maps to consumer sites.

    Parameters:
        seed: The witness seed to inject.
        cover: The existing cover.
        func_name: Function name.
        consumer_site_ids: Sites that consume this witness.
        source_file: Source file path.

    Returns:
        A new ``Cover`` with the witness site and flow morphisms added.
    """
    if seed.is_trivial:
        return cover

    new_sites: Dict[SiteId, Any] = dict(cover.sites)
    new_morphisms: List[Any] = list(cover.morphisms)
    new_overlaps: List[Tuple[SiteId, SiteId]] = list(cover.overlaps)
    new_error_sites: Set[SiteId] = set(cover.error_sites)
    new_input_boundary: Set[SiteId] = set(cover.input_boundary)
    new_output_boundary: Set[SiteId] = set(cover.output_boundary)

    # -- create the witness proof site --------------------------------------

    sid = seed.to_site_id(func_name)

    if sid not in new_sites:
        loc = seed.source_location
        span = SourceSpan(
            file=loc.file if loc else source_file,
            start_line=loc.line if loc else 0,
            start_col=loc.col if loc else 0,
        )
        site = make_proof_site(
            func_name=func_name,
            proof_label=f"witness_{seed.witness_name}",
            span=span,
            is_witness_export=True,
            obligation_text=seed.proposition.pretty(),
        )
        new_sites[sid] = site

    # -- add witness-flow morphisms to consumer sites -----------------------

    if consumer_site_ids:
        for consumer_id in consumer_site_ids:
            morph = make_witness_flow_restriction(
                witness_site=sid,
                consumer_site=consumer_id,
            )
            new_morphisms.append(morph)

            pair = (sid, consumer_id)
            rpair = (consumer_id, sid)
            if pair not in new_overlaps and rpair not in new_overlaps:
                new_overlaps.append(pair)

    # -- also add witness-flow to existing return boundary sites ------------

    for output_id in cover.output_boundary:
        morph = make_witness_flow_restriction(
            witness_site=sid,
            consumer_site=output_id,
        )
        new_morphisms.append(morph)

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=new_overlaps,
        error_sites=new_error_sites,
        input_boundary=new_input_boundary,
        output_boundary=new_output_boundary,
    )


def inject_all_witnesses(
    seeds: Sequence[WitnessSeed],
    cover: Cover,
    func_name: str,
    *,
    consumer_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Cover:
    """Inject all witness seeds into the cover.

    Parameters:
        seeds: Witness seeds to inject.
        cover: The existing cover.
        func_name: Function name.
        consumer_site_ids: Sites that consume witnesses.
        source_file: Source file path.

    Returns:
        A new ``Cover`` with all witness sites and flow morphisms added.
    """
    result = cover
    for seed in seeds:
        result = inject_witness_into_cover(
            seed, result, func_name,
            consumer_site_ids=consumer_site_ids,
            source_file=source_file,
        )
    return result
