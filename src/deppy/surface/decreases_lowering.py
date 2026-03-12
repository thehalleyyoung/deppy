"""Decreases lowering: @decreases to ranking function sites.

This module converts user-facing ``@deppy.decreases`` annotations into
*ranking-function sites* in the sheaf cover.  A ranking function is a
map from program state to a well-ordered set (typically natural numbers)
that strictly decreases on each iteration or recursive call, proving
termination.

The lowering pipeline is:

1. Parse decorator data into ``DecreasesSeed`` frozen intermediates.
2. ``lower_decreases`` converts a loop-invariant's termination measure
   or standalone decreases annotation into a ``DecreasesSeed``.
3. ``create_ranking_sites`` emits observation sites and morphisms that
   enforce the well-foundedness condition in the cover.

In the sheaf framework, a ranking function becomes a *proof site* whose
local section carries the current measure value and a witness that it
is bounded below and strictly decreasing.
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
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
)
from deppy.contracts.invariant import LoopInvariant
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder
from deppy.static_analysis.restriction_maps import RestrictionKind
from deppy.types.carriers import CarrierSchema, CarrierType, SchemaConstraint
from deppy.types.witnesses import (
    ProofTerm,
    RuntimeCheckProof,
    StaticProof,
    WitnessCarrier,
)


# ---------------------------------------------------------------------------
# BoundType -- what well-ordered domain the measure maps into
# ---------------------------------------------------------------------------


class BoundType(enum.Enum):
    """Well-ordered domain for the ranking function."""

    NATURAL = "natural"
    ORDINAL = "ordinal"
    LEXICOGRAPHIC = "lexicographic"
    CUSTOM = "custom"


# ---------------------------------------------------------------------------
# DecreasesSeed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DecreasesSeed:
    """Frozen intermediate for a single termination-measure annotation.

    A decreases seed captures one ranking function expression, the
    variables it depends on, and the well-ordered domain it maps into.

    Attributes:
        uid: Unique seed identifier.
        ranking_expression: The termination measure as a contracts-layer Term.
        ranking_expression_str: Human-readable string form of the measure.
        variables: Free variables referenced by the ranking expression.
        bound_type: The well-ordered domain (NATURAL, ORDINAL, etc.).
        scope_name: Enclosing scope (function, loop label).
        trust: How the termination claim was established.
        source_location: Where the annotation appears in source.
        description: Optional human-readable gloss.
        is_lexicographic: Whether this is one component of a lexicographic tuple.
        lex_index: Position in lexicographic tuple (0-based), or -1 if not lex.
    """

    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    ranking_expression: Optional[Term] = None
    ranking_expression_str: str = ""
    variables: Tuple[str, ...] = ()
    bound_type: BoundType = BoundType.NATURAL
    scope_name: str = ""
    trust: TrustLevel = TrustLevel.RESIDUAL
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    is_lexicographic: bool = False
    lex_index: int = -1

    def pretty(self) -> str:
        expr = self.ranking_expression_str or (
            self.ranking_expression.pretty() if self.ranking_expression else "?"
        )
        lex = f" [lex {self.lex_index}]" if self.is_lexicographic else ""
        return (
            f"DecreasesSeed(expr={expr}, bound={self.bound_type.value}, "
            f"scope={self.scope_name!r}{lex})"
        )


# ---------------------------------------------------------------------------
# Lowering: Term -> DecreasesSeed
# ---------------------------------------------------------------------------


def lower_decreases(
    decreases_term: Term,
    scope_name: str = "",
    source_location: Optional[SourceLocation] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> DecreasesSeed:
    """Lower a single termination-measure ``Term`` into a ``DecreasesSeed``.

    Parameters
    ----------
    decreases_term:
        The ranking expression from the contract layer.
    scope_name:
        Enclosing scope name (function or loop label).
    source_location:
        Source location of the annotation.
    trust:
        Trust level for the termination claim.

    Returns
    -------
    DecreasesSeed:
        A frozen seed ready for site creation.
    """
    variables = tuple(sorted(decreases_term.free_variables()))
    expr_str = decreases_term.pretty()

    return DecreasesSeed(
        ranking_expression=decreases_term,
        ranking_expression_str=expr_str,
        variables=variables,
        bound_type=BoundType.NATURAL,
        scope_name=scope_name,
        trust=trust,
        source_location=source_location,
        description=f"decreases {expr_str}",
    )


# ---------------------------------------------------------------------------
# Lowering: LoopInvariant -> DecreasesSeed (extract termination measure)
# ---------------------------------------------------------------------------


def lower_decreases_from_loop(
    contract: LoopInvariant,
    scope_name: str = "",
) -> Optional[DecreasesSeed]:
    """Extract a ``DecreasesSeed`` from a ``LoopInvariant`` if it has a
    termination measure.

    Parameters
    ----------
    contract:
        The loop invariant contract.
    scope_name:
        Enclosing scope name.

    Returns
    -------
    Optional[DecreasesSeed]:
        A seed if the contract has a ``decreases`` term, else None.
    """
    if contract.decreases is None:
        return None

    return lower_decreases(
        decreases_term=contract.decreases,
        scope_name=scope_name or contract.scope or "loop",
        source_location=contract.source_location,
        trust=contract.trust,
    )


# ---------------------------------------------------------------------------
# Lowering: string expression -> DecreasesSeed
# ---------------------------------------------------------------------------


def lower_decreases_from_string(
    expression: str,
    scope_name: str = "",
    source_location: Optional[SourceLocation] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> DecreasesSeed:
    """Lower a string-form termination measure into a ``DecreasesSeed``.

    The string is wrapped in a ``Term.var`` (symbolic variable reference).
    This is the entry point for ``@deppy.decreases("n - i")``.

    Parameters
    ----------
    expression:
        The ranking expression as a string.
    scope_name:
        Enclosing scope name.
    source_location:
        Source location of the annotation.
    trust:
        Trust level for the termination claim.

    Returns
    -------
    DecreasesSeed:
        A frozen seed ready for site creation.
    """
    term = Term.var(expression)
    return DecreasesSeed(
        ranking_expression=term,
        ranking_expression_str=expression,
        variables=(expression,),  # conservative: treat whole expr as one var
        bound_type=BoundType.NATURAL,
        scope_name=scope_name,
        trust=trust,
        source_location=source_location,
        description=f"decreases {expression}",
    )


# ---------------------------------------------------------------------------
# Lexicographic tuple lowering
# ---------------------------------------------------------------------------


def lower_lexicographic_decreases(
    expressions: Sequence[Union[Term, str]],
    scope_name: str = "",
    source_location: Optional[SourceLocation] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> List[DecreasesSeed]:
    """Lower a lexicographic termination measure (tuple of expressions).

    A lexicographic measure ``(e1, e2, ..., en)`` is modelled as *n*
    linked ``DecreasesSeed`` objects, each carrying its position in the
    tuple.  The well-founded ordering is: the first component that changes
    must decrease, and earlier components must not increase.

    Parameters
    ----------
    expressions:
        Ordered components of the lexicographic tuple.
    scope_name:
        Enclosing scope name.
    source_location:
        Source location of the annotation.
    trust:
        Trust level.

    Returns
    -------
    List[DecreasesSeed]:
        One seed per component, ordered by lex_index.
    """
    seeds: List[DecreasesSeed] = []
    shared_uid = uuid.uuid4().hex[:12]

    for idx, expr in enumerate(expressions):
        if isinstance(expr, str):
            term = Term.var(expr)
            expr_str = expr
        else:
            term = expr
            expr_str = expr.pretty()

        variables = tuple(sorted(term.free_variables()))

        seeds.append(
            DecreasesSeed(
                uid=f"{shared_uid}_lex{idx}",
                ranking_expression=term,
                ranking_expression_str=expr_str,
                variables=variables,
                bound_type=BoundType.LEXICOGRAPHIC,
                scope_name=scope_name,
                trust=trust,
                source_location=source_location,
                description=f"decreases lex[{idx}] = {expr_str}",
                is_lexicographic=True,
                lex_index=idx,
            )
        )

    return seeds


# ---------------------------------------------------------------------------
# Site construction
# ---------------------------------------------------------------------------


def _make_ranking_site(
    seed: DecreasesSeed,
    func_name: str,
) -> ConcreteSite:
    """Create a proof-kind observation site for a ranking function."""
    lex_suffix = f"$lex{seed.lex_index}" if seed.is_lexicographic else ""
    site_id = SiteId(
        kind=SiteKind.PROOF,
        name=f"{func_name}${seed.scope_name}$rank{lex_suffix}",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )

    constraint_desc = f"Ranking function: {seed.ranking_expression_str}"
    if seed.is_lexicographic:
        constraint_desc += f" (lex component {seed.lex_index})"

    schema = CarrierSchema(
        name=f"rank_{seed.scope_name}{lex_suffix}",
        constraints=(
            SchemaConstraint(
                description=constraint_desc,
                field_names=seed.variables + ("__rank_current", "__rank_next"),
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "decreases_lowering",
            "seed_uid": seed.uid,
            "bound_type": seed.bound_type.value,
            "ranking_expression": seed.ranking_expression_str,
            "is_lexicographic": seed.is_lexicographic,
            "lex_index": seed.lex_index,
        },
    )


def _make_well_foundedness_site(
    seed: DecreasesSeed,
    func_name: str,
) -> ConcreteSite:
    """Create a proof site asserting the measure is bounded below.

    This site witnesses that the ranking function maps into a
    well-ordered set (e.g., naturals >= 0).
    """
    lex_suffix = f"$lex{seed.lex_index}" if seed.is_lexicographic else ""
    site_id = SiteId(
        kind=SiteKind.PROOF,
        name=f"{func_name}${seed.scope_name}$wf{lex_suffix}",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )
    schema = CarrierSchema(
        name=f"wf_{seed.scope_name}{lex_suffix}",
        constraints=(
            SchemaConstraint(
                description=f"Well-foundedness: {seed.ranking_expression_str} >= 0",
                field_names=seed.variables + ("__rank_lower_bound",),
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "decreases_lowering",
            "seed_uid": seed.uid,
            "purpose": "well_foundedness",
            "bound_type": seed.bound_type.value,
        },
    )


# ---------------------------------------------------------------------------
# Morphism construction
# ---------------------------------------------------------------------------


def _make_decrease_morphism(
    ranking_site: ConcreteSite,
    loop_header_site_id: Optional[SiteId],
    seed: DecreasesSeed,
) -> Optional[ConcreteMorphism]:
    """Create a morphism linking the ranking site to a loop-header site.

    This restriction map transports the "current measure" from the loop
    header to the ranking proof site, enabling the checker to verify
    strict decrease.
    """
    if loop_header_site_id is None:
        return None

    return ConcreteMorphism(
        _source=loop_header_site_id,
        _target=ranking_site.site_id,
        _metadata={
            "kind": "ranking_transport",
            "restriction_kind": RestrictionKind.PROOF_TRANSPORT.value,
            "seed_uid": seed.uid,
            "description": f"Transport measure {seed.ranking_expression_str} to ranking proof",
        },
    )


def _make_wf_morphism(
    ranking_site: ConcreteSite,
    wf_site: ConcreteSite,
    seed: DecreasesSeed,
) -> ConcreteMorphism:
    """Link the ranking site to the well-foundedness site.

    The restriction projects the current measure value to the WF check.
    """
    return ConcreteMorphism(
        _source=ranking_site.site_id,
        _target=wf_site.site_id,
        _metadata={
            "kind": "well_foundedness_check",
            "restriction_kind": RestrictionKind.WITNESS_FLOW.value,
            "seed_uid": seed.uid,
            "description": f"WF check for {seed.ranking_expression_str}",
        },
    )


# ---------------------------------------------------------------------------
# create_ranking_sites: single seed
# ---------------------------------------------------------------------------


def create_ranking_sites(
    seed: DecreasesSeed,
    cover: Cover,
    func_name: str = "",
    loop_header_site_id: Optional[SiteId] = None,
) -> Cover:
    """Create ranking-function sites and morphisms for a single seed.

    Parameters
    ----------
    seed:
        The decreases seed to install.
    cover:
        The current cover to enrich.
    func_name:
        Enclosing function name.
    loop_header_site_id:
        Optional site ID of the loop header site, so we can link
        the ranking proof to the induction variable.

    Returns
    -------
    Cover:
        A new Cover with ranking sites and morphisms added.
    """
    ranking_site = _make_ranking_site(seed, func_name)
    wf_site = _make_well_foundedness_site(seed, func_name)
    wf_morph = _make_wf_morphism(ranking_site, wf_site, seed)

    new_sites = dict(cover.sites)
    new_sites[ranking_site.site_id] = ranking_site
    new_sites[wf_site.site_id] = wf_site

    new_morphisms = list(cover.morphisms) + [wf_morph]

    # Link to loop header if available
    dec_morph = _make_decrease_morphism(ranking_site, loop_header_site_id, seed)
    if dec_morph is not None:
        new_morphisms.append(dec_morph)

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=cover.overlaps,
        error_sites=cover.error_sites,
        input_boundary=cover.input_boundary,
        output_boundary=cover.output_boundary,
    )


# ---------------------------------------------------------------------------
# Batch: create ranking sites for multiple seeds
# ---------------------------------------------------------------------------


def create_all_ranking_sites(
    seeds: Sequence[DecreasesSeed],
    cover: Cover,
    func_name: str = "",
    loop_header_site_ids: Optional[Mapping[str, SiteId]] = None,
) -> Cover:
    """Create ranking sites for all decreases seeds.

    Parameters
    ----------
    seeds:
        All decreases seeds to install.
    cover:
        The initial cover.
    func_name:
        Enclosing function name.
    loop_header_site_ids:
        Optional mapping from scope name to loop-header SiteId.

    Returns
    -------
    Cover:
        The cover enriched with all ranking sites and morphisms.
    """
    result = cover
    header_map = loop_header_site_ids or {}

    for seed in seeds:
        header_id = header_map.get(seed.scope_name)
        result = create_ranking_sites(
            seed, result, func_name=func_name, loop_header_site_id=header_id,
        )

    return result


# ---------------------------------------------------------------------------
# Extract decreases from contract set
# ---------------------------------------------------------------------------


def extract_decreases_seeds(
    contract_set: Any,
    scope_name: str = "",
) -> List[DecreasesSeed]:
    """Extract all ``DecreasesSeed`` objects from a ``ContractSet``.

    Scans the ``invariants`` list for ``LoopInvariant`` contracts with
    termination measures.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    scope_name:
        Enclosing scope name.

    Returns
    -------
    List[DecreasesSeed]:
        Extracted decreases seeds, one per loop invariant with a
        termination measure.
    """
    invariants = getattr(contract_set, "invariants", [])
    seeds: List[DecreasesSeed] = []

    for inv in invariants:
        if isinstance(inv, LoopInvariant):
            seed = lower_decreases_from_loop(inv, scope_name=scope_name)
            if seed is not None:
                seeds.append(seed)

    return seeds


# ---------------------------------------------------------------------------
# Convenience pipeline
# ---------------------------------------------------------------------------


def lower_and_install_decreases(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    loop_header_site_ids: Optional[Mapping[str, SiteId]] = None,
) -> Cover:
    """End-to-end pipeline: extract decreases from a ContractSet and
    install ranking sites into a Cover.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The cover to enrich.
    func_name:
        Enclosing function name.
    loop_header_site_ids:
        Optional mapping from scope name to loop-header SiteId.

    Returns
    -------
    Cover:
        The enriched cover.
    """
    seeds = extract_decreases_seeds(contract_set, scope_name=func_name)
    return create_all_ranking_sites(
        seeds, cover, func_name=func_name, loop_header_site_ids=loop_header_site_ids,
    )
