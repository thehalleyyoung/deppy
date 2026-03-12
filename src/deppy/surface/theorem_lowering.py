"""Theorem lowering: @theorem/@lemma to proof sites and transport maps.

This module converts user-facing ``@deppy.theorem`` and ``@deppy.lemma``
decorators into *proof sites* and *transport morphisms* within the sheaf
cover.  Proved facts become PROOF_BACKED local sections that can be
transported to program sites via restriction maps.

The lowering pipeline is:

1. Parse decorator data into ``TheoremSeed`` / ``LemmaSeed`` intermediates.
2. ``lower_theorem`` and ``lower_lemma`` create proof-site objects and
   compute the transport morphisms that carry proved facts into the
   program-level cover.
3. ``create_proof_sites`` enriches a ``Cover`` with all proof-site and
   transport data from a collection of theorem/lemma seeds.
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
    Contract,
    ContractSet,
    Predicate as ContractPredicate,
    SourceLocation,
    Term,
)
from deppy.contracts.theorem import (
    AssumptionContract,
    LemmaContract,
    TheoremContract,
    TransportContract,
)
from deppy.contracts.transport_seed import (
    TransportJustification,
    TransportSeed,
    TransportSeedCollection,
)
from deppy.core._protocols import (
    BoundarySection,
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
)
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    make_proof_transport,
    make_witness_flow_restriction,
)
from deppy.types.carriers import CarrierSchema, SchemaConstraint


# ---------------------------------------------------------------------------
# Trust ordering
# ---------------------------------------------------------------------------

_TRUST_ORD: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}


# ---------------------------------------------------------------------------
# TheoremSeed
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TheoremSeed:
    """Frozen intermediate for a lowered ``@theorem`` decorator.

    A theorem seed pairs a named statement with its proof body and
    dependency list.  During lowering it produces a proof site and
    transport morphisms that carry the proved fact to program sites.

    Attributes:
        name: Theorem identifier.
        statement: The proposition being proved.
        variables: Free variables in the statement.
        proof_body: The proof code (AST or callable, retained for
            potential future verification).
        dependencies: Names of theorems/lemmas this theorem depends on.
        trust: Trust level (defaults to PROOF_BACKED).
        source_location: Source code location.
        description: Optional human-readable gloss.
        target_sites: Program sites to which this theorem transports facts.
        uid: Unique identifier.
    """
    name: str
    statement: ContractPredicate
    variables: Tuple[str, ...] = ()
    proof_body: Optional[Any] = None
    dependencies: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.PROOF_BACKED
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    target_sites: Tuple[str, ...] = ()
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def is_trivial(self) -> bool:
        return self.statement.is_trivially_true

    @property
    def has_proof(self) -> bool:
        return self.proof_body is not None

    @property
    def free_variables(self) -> FrozenSet[str]:
        return self.statement.free_variables()

    def to_site_id(self) -> SiteId:
        """Generate a SiteId for this theorem's proof site."""
        loc: Optional[Tuple[str, int, int]] = None
        if self.source_location:
            loc = (
                self.source_location.file,
                self.source_location.line,
                self.source_location.col,
            )
        return SiteId(
            kind=SiteKind.PROOF,
            name=self.name,
            source_location=loc,
        )

    def to_local_section(self) -> LocalSection:
        """Create a LocalSection carrying the theorem's proposition."""
        sid = self.to_site_id()
        refinements: Dict[str, Any] = {
            "statement": self.statement.pretty(),
            "theorem_name": self.name,
            "has_proof": self.has_proof,
        }
        if self.dependencies:
            refinements["dependencies"] = list(self.dependencies)
        if self.description:
            refinements["description"] = self.description

        witnesses: Dict[str, Any] = {}
        if self.has_proof:
            witnesses["proof_body"] = {
                "kind": "theorem_proof",
                "name": self.name,
            }

        return LocalSection(
            site_id=sid,
            refinements=refinements,
            trust=self.trust,
            provenance=f"theorem:{self.name}",
            witnesses=witnesses,
        )

    def dependency_graph_entry(self) -> Tuple[str, List[str]]:
        """Return ``(name, dependencies)`` for dependency graph construction."""
        return self.name, list(self.dependencies)

    def pretty(self) -> str:
        deps = ""
        if self.dependencies:
            deps = f" using [{', '.join(self.dependencies)}]"
        desc = f" # {self.description}" if self.description else ""
        return f"TheoremSeed({self.name}): {self.statement.pretty()}{deps}{desc}"

    def __repr__(self) -> str:
        has = "proved" if self.has_proof else "unproved"
        return f"<TheoremSeed {self.name!r} [{has}]>"


# ---------------------------------------------------------------------------
# LemmaSeed
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LemmaSeed:
    """Frozen intermediate for a lowered ``@lemma`` decorator.

    Structurally similar to ``TheoremSeed`` but scoped as a helper fact
    used by other proofs rather than part of the public API.

    Attributes:
        name: Lemma identifier.
        statement: The proposition.
        variables: Free variables.
        proof_body: Proof code.
        used_by: Theorems/lemmas that reference this lemma.
        trust: Trust level.
        source_location: Source code location.
        description: Optional gloss.
        uid: Unique identifier.
    """
    name: str
    statement: ContractPredicate
    variables: Tuple[str, ...] = ()
    proof_body: Optional[Any] = None
    used_by: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.PROOF_BACKED
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def is_trivial(self) -> bool:
        return self.statement.is_trivially_true

    @property
    def has_proof(self) -> bool:
        return self.proof_body is not None

    @property
    def free_variables(self) -> FrozenSet[str]:
        return self.statement.free_variables()

    def to_site_id(self) -> SiteId:
        """Generate a SiteId for this lemma's proof site."""
        loc: Optional[Tuple[str, int, int]] = None
        if self.source_location:
            loc = (
                self.source_location.file,
                self.source_location.line,
                self.source_location.col,
            )
        return SiteId(
            kind=SiteKind.PROOF,
            name=f"lemma:{self.name}",
            source_location=loc,
        )

    def to_local_section(self) -> LocalSection:
        """Create a LocalSection carrying the lemma's proposition."""
        sid = self.to_site_id()
        refinements: Dict[str, Any] = {
            "statement": self.statement.pretty(),
            "lemma_name": self.name,
            "is_lemma": True,
            "has_proof": self.has_proof,
        }
        if self.used_by:
            refinements["used_by"] = list(self.used_by)
        if self.description:
            refinements["description"] = self.description

        witnesses: Dict[str, Any] = {}
        if self.has_proof:
            witnesses["proof_body"] = {
                "kind": "lemma_proof",
                "name": self.name,
            }

        return LocalSection(
            site_id=sid,
            refinements=refinements,
            trust=self.trust,
            provenance=f"lemma:{self.name}",
            witnesses=witnesses,
        )

    def as_theorem_seed(self) -> TheoremSeed:
        """Promote this lemma to a full theorem seed."""
        return TheoremSeed(
            name=self.name,
            statement=self.statement,
            variables=self.variables,
            proof_body=self.proof_body,
            dependencies=(),
            trust=self.trust,
            source_location=self.source_location,
            description=self.description,
        )

    def pretty(self) -> str:
        used = ""
        if self.used_by:
            used = f" (used by {', '.join(self.used_by)})"
        desc = f" # {self.description}" if self.description else ""
        return f"LemmaSeed({self.name}): {self.statement.pretty()}{used}{desc}"

    def __repr__(self) -> str:
        has = "proved" if self.has_proof else "unproved"
        return f"<LemmaSeed {self.name!r} [{has}]>"


# ---------------------------------------------------------------------------
# TransportSeed for proof-to-program transport
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProofTransportSeed:
    """Specifies which proof facts transport to which program sites.

    A transport seed creates a morphism from a proof site to a program
    site that carries the proved proposition as a PROOF_BACKED section
    refinement.

    Attributes:
        proof_site_name: Name of the source proof site.
        program_site_name: Name of the target program site.
        transported_proposition: The fact being transported.
        justification: How the transport is justified.
        preserved_keys: Refinement keys preserved by the transport.
        description: Optional gloss.
        uid: Unique identifier.
    """
    proof_site_name: str
    program_site_name: str
    transported_proposition: ContractPredicate
    justification: TransportJustification = TransportJustification.THEOREM
    preserved_keys: FrozenSet[str] = frozenset()
    description: Optional[str] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    def to_transport_seed(self) -> TransportSeed:
        """Convert to the core TransportSeed type."""
        return TransportSeed(
            source_prop=self.transported_proposition,
            target_prop=self.transported_proposition,
            justification=self.justification,
            description=self.description or (
                f"proof transport: {self.proof_site_name} -> {self.program_site_name}"
            ),
        )

    def pretty(self) -> str:
        desc = f" # {self.description}" if self.description else ""
        return (
            f"ProofTransport({self.proof_site_name} -> "
            f"{self.program_site_name}): "
            f"{self.transported_proposition.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return (
            f"<ProofTransportSeed {self.proof_site_name!r} -> "
            f"{self.program_site_name!r}>"
        )


# ---------------------------------------------------------------------------
# Lowering functions
# ---------------------------------------------------------------------------

def lower_theorem(
    contract: TheoremContract,
    *,
    target_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Tuple[TheoremSeed, List[ConcreteMorphism]]:
    """Lower a ``TheoremContract`` into a theorem seed and transport morphisms.

    Parameters:
        contract: The theorem contract to lower.
        target_site_ids: Optional explicit target sites for transport.
        source_file: Source file path for span construction.

    Returns:
        A tuple of ``(theorem_seed, transport_morphisms)``.
    """
    fv = contract.statement.free_variables()

    seed = TheoremSeed(
        name=contract.name,
        statement=contract.statement,
        variables=tuple(sorted(fv)),
        proof_body=contract.proof_body,
        dependencies=tuple(contract.dependencies),
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
    )

    # Build transport morphisms to target sites
    morphisms: List[ConcreteMorphism] = []
    proof_site_id = seed.to_site_id()

    if target_site_ids:
        for target_id in target_site_ids:
            morph = make_proof_transport(
                proof_site=proof_site_id,
                program_site=target_id,
                theorem_name=contract.name,
            )
            morphisms.append(morph)

    return seed, morphisms


def lower_lemma(
    contract: LemmaContract,
    *,
    target_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Tuple[LemmaSeed, List[ConcreteMorphism]]:
    """Lower a ``LemmaContract`` into a lemma seed and transport morphisms.

    Parameters:
        contract: The lemma contract to lower.
        target_site_ids: Optional target sites for transport.
        source_file: Source file path.

    Returns:
        A tuple of ``(lemma_seed, transport_morphisms)``.
    """
    fv = contract.statement.free_variables()

    seed = LemmaSeed(
        name=contract.name,
        statement=contract.statement,
        variables=tuple(sorted(fv)),
        used_by=tuple(contract.used_by),
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
    )

    morphisms: List[ConcreteMorphism] = []
    proof_site_id = seed.to_site_id()

    if target_site_ids:
        for target_id in target_site_ids:
            morph = make_proof_transport(
                proof_site=proof_site_id,
                program_site=target_id,
                theorem_name=contract.name,
            )
            morphisms.append(morph)

    return seed, morphisms


def lower_transport_contract(
    contract: TransportContract,
) -> TransportSeed:
    """Lower a ``TransportContract`` into a transport seed."""
    return contract.to_transport_seed()


def lower_assumption(
    contract: AssumptionContract,
) -> TheoremSeed:
    """Lower an ``AssumptionContract`` into a theorem seed with ASSUMED trust.

    Assumptions become theorem seeds with weakened trust, creating proof
    debt that should eventually be discharged.
    """
    fv = contract.proposition.free_variables()

    return TheoremSeed(
        name=f"assumption:{contract.uid}",
        statement=contract.proposition,
        variables=tuple(sorted(fv)),
        proof_body=None,
        trust=TrustLevel.ASSUMED,
        source_location=contract.source_location,
        description=(
            contract.justification
            if contract.justification
            else "unproven assumption"
        ),
    )


# ---------------------------------------------------------------------------
# Lower from a ContractSet
# ---------------------------------------------------------------------------

def lower_theorem_contracts(
    contract_set: ContractSet,
    *,
    target_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Tuple[List[TheoremSeed], List[LemmaSeed], List[ConcreteMorphism], List[TransportSeed]]:
    """Lower all theorem-related contracts in a ``ContractSet``.

    Parameters:
        contract_set: The contract set to lower.
        target_site_ids: Optional target sites for transport morphisms.
        source_file: Source file path.

    Returns:
        A tuple of ``(theorem_seeds, lemma_seeds, morphisms, transport_seeds)``.
    """
    theorem_seeds: List[TheoremSeed] = []
    lemma_seeds: List[LemmaSeed] = []
    morphisms: List[ConcreteMorphism] = []
    transport_seeds: List[TransportSeed] = []

    for thm in contract_set.theorems:
        if isinstance(thm, TheoremContract):
            seed, morph_list = lower_theorem(
                thm,
                target_site_ids=target_site_ids,
                source_file=source_file,
            )
            theorem_seeds.append(seed)
            morphisms.extend(morph_list)

        elif isinstance(thm, LemmaContract):
            seed_l, morph_list_l = lower_lemma(
                thm,
                target_site_ids=target_site_ids,
                source_file=source_file,
            )
            lemma_seeds.append(seed_l)
            morphisms.extend(morph_list_l)

        elif isinstance(thm, TransportContract):
            ts = lower_transport_contract(thm)
            transport_seeds.append(ts)

        elif isinstance(thm, AssumptionContract):
            aseed = lower_assumption(thm)
            theorem_seeds.append(aseed)

    return theorem_seeds, lemma_seeds, morphisms, transport_seeds


# ---------------------------------------------------------------------------
# Dependency resolution
# ---------------------------------------------------------------------------

def build_dependency_graph(
    theorem_seeds: Sequence[TheoremSeed],
    lemma_seeds: Sequence[LemmaSeed],
) -> Dict[str, List[str]]:
    """Build a dependency graph from theorem and lemma seeds.

    Returns a dict mapping each theorem/lemma name to the list of names
    it depends on.
    """
    graph: Dict[str, List[str]] = {}

    for ts in theorem_seeds:
        name, deps = ts.dependency_graph_entry()
        graph[name] = deps

    for ls in lemma_seeds:
        graph[ls.name] = list(ls.used_by)

    return graph


def topological_order(graph: Dict[str, List[str]]) -> List[str]:
    """Return a topological ordering of the dependency graph.

    If a cycle is detected, raises ``ValueError``.
    """
    visited: Set[str] = set()
    in_stack: Set[str] = set()
    order: List[str] = []

    def _visit(node: str) -> None:
        if node in in_stack:
            raise ValueError(f"Cycle detected involving theorem/lemma {node!r}")
        if node in visited:
            return
        in_stack.add(node)
        for dep in graph.get(node, []):
            if dep in graph:
                _visit(dep)
        in_stack.discard(node)
        visited.add(node)
        order.append(node)

    for name in graph:
        _visit(name)

    return order


def resolve_dependencies(
    theorem_seeds: Sequence[TheoremSeed],
    lemma_seeds: Sequence[LemmaSeed],
) -> List[str]:
    """Return a topological ordering of theorem/lemma dependencies.

    Lemmas that are used by theorems come first.
    """
    graph = build_dependency_graph(theorem_seeds, lemma_seeds)
    return topological_order(graph)


# ---------------------------------------------------------------------------
# create_proof_sites: enrich Cover with proof sites
# ---------------------------------------------------------------------------

def create_proof_sites(
    theorem_seeds: Sequence[TheoremSeed],
    lemma_seeds: Sequence[LemmaSeed],
    transport_morphisms: Sequence[ConcreteMorphism],
    transport_seeds: Sequence[TransportSeed],
    cover: Cover,
    *,
    source_file: str = "<unknown>",
) -> Cover:
    """Enrich *cover* with proof sites and transport morphisms.

    For each theorem/lemma seed, a proof site is created with a
    PROOF_BACKED local section.  Transport morphisms connect proof
    sites to program sites, allowing proved facts to flow into the
    cover.

    Parameters:
        theorem_seeds: Theorem seeds to install.
        lemma_seeds: Lemma seeds to install.
        transport_morphisms: Pre-built morphisms from lowering.
        transport_seeds: Transport seeds for inter-site fact flow.
        cover: The existing cover to enrich.
        source_file: Source file path for span construction.

    Returns:
        A new ``Cover`` with proof sites and transport morphisms added.
    """
    new_sites: Dict[SiteId, Any] = dict(cover.sites)
    new_morphisms: List[Any] = list(cover.morphisms)
    new_overlaps: List[Tuple[SiteId, SiteId]] = list(cover.overlaps)
    new_error_sites: Set[SiteId] = set(cover.error_sites)
    new_input_boundary: Set[SiteId] = set(cover.input_boundary)
    new_output_boundary: Set[SiteId] = set(cover.output_boundary)

    proof_site_ids: List[SiteId] = []

    # -- install theorem proof sites ----------------------------------------

    for seed in theorem_seeds:
        if seed.is_trivial:
            continue

        sid = seed.to_site_id()
        proof_site_ids.append(sid)

        if sid not in new_sites:
            loc = seed.source_location
            span = SourceSpan(
                file=loc.file if loc else source_file,
                start_line=loc.line if loc else 0,
                start_col=loc.col if loc else 0,
            )
            site = make_proof_site(
                func_name=seed.name,
                proof_label=seed.name,
                span=span,
                theorem_name=seed.name,
                obligation_text=seed.statement.pretty(),
            )
            new_sites[sid] = site

    # -- install lemma proof sites ------------------------------------------

    for seed in lemma_seeds:
        if seed.is_trivial:
            continue

        sid = seed.to_site_id()
        proof_site_ids.append(sid)

        if sid not in new_sites:
            loc = seed.source_location
            span = SourceSpan(
                file=loc.file if loc else source_file,
                start_line=loc.line if loc else 0,
                start_col=loc.col if loc else 0,
            )
            site = make_proof_site(
                func_name=seed.name,
                proof_label=f"lemma_{seed.name}",
                span=span,
                theorem_name=seed.name,
                is_lemma=True,
                obligation_text=seed.statement.pretty(),
            )
            new_sites[sid] = site

    # -- add transport morphisms from lowering ------------------------------

    new_morphisms.extend(transport_morphisms)

    # -- build transport morphisms from transport seeds ---------------------

    for ts in transport_seeds:
        if ts.source_site is not None and ts.target_site is not None:
            src_id = ts.source_site
            tgt_id = ts.target_site
            if isinstance(src_id, SiteId) and isinstance(tgt_id, SiteId):
                morph = make_proof_transport(
                    proof_site=src_id,
                    program_site=tgt_id,
                )
                new_morphisms.append(morph)

    # -- add overlaps between proof sites -----------------------------------

    for i, pid_a in enumerate(proof_site_ids):
        for pid_b in proof_site_ids[i + 1:]:
            pair = (pid_a, pid_b)
            rpair = (pid_b, pid_a)
            if pair not in new_overlaps and rpair not in new_overlaps:
                new_overlaps.append(pair)

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=new_overlaps,
        error_sites=new_error_sites,
        input_boundary=new_input_boundary,
        output_boundary=new_output_boundary,
    )


# ---------------------------------------------------------------------------
# Convenience: full theorem-lowering pipeline
# ---------------------------------------------------------------------------

def lower_and_install_theorems(
    contract_set: ContractSet,
    cover: Cover,
    *,
    target_site_ids: Optional[Sequence[SiteId]] = None,
    source_file: str = "<unknown>",
) -> Tuple[Cover, List[TheoremSeed], List[LemmaSeed]]:
    """Full pipeline: lower theorems/lemmas and install proof sites.

    Parameters:
        contract_set: Contracts attached to a scope.
        cover: The existing cover to enrich.
        target_site_ids: Program sites to transport proved facts to.
        source_file: Source file path.

    Returns:
        A tuple of ``(enriched_cover, theorem_seeds, lemma_seeds)``.
    """
    theorem_seeds, lemma_seeds, morphisms, transport_seeds = (
        lower_theorem_contracts(
            contract_set,
            target_site_ids=target_site_ids,
            source_file=source_file,
        )
    )

    enriched = create_proof_sites(
        theorem_seeds, lemma_seeds, morphisms, transport_seeds,
        cover, source_file=source_file,
    )

    return enriched, theorem_seeds, lemma_seeds
