"""Restriction and reindexing maps for the observation site category.

In sheaf-descent semantics, morphisms between sites are restriction maps
that project local sections from a larger neighbourhood to a smaller one.
This module provides constructors for all standard restriction map patterns
that arise from Python program structure.

A restriction map is *not* a dataflow edge.  It is a declaration that the
semantic content at one site can be projected, restricted, or reindexed to
produce semantic content at another site.  The key patterns are:

- **Lineage restriction**: An SSA value derived from another value inherits
  a restricted view of its parent's section.
- **Control restriction**: A branch guard restricts sections into the
  true/false arms by adding predicate refinements.
- **Call reindexing**: Actual arguments at a call site are reindexed to
  formal parameters of the callee.
- **Pack transport**: A theory pack declares that facts at one site
  restrict to facts at a related site (e.g., sort → order + permutation).
- **Overlap restriction**: Two sites that share lineage or control provenance
  define overlap edges where sections must agree (sheaf gluing condition).
- **Boundary projection**: Interior sites project to input/output boundary.
- **Error pullback**: Error-site viability restricts backward to upstream
  sites as a safety constraint.
"""

from __future__ import annotations

import enum
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
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism


# ---------------------------------------------------------------------------
# Restriction map kinds
# ---------------------------------------------------------------------------

class RestrictionKind(enum.Enum):
    """Classification of restriction/reindexing maps."""
    # Structural
    LINEAGE = "lineage"              # Value derived from value
    CONTROL_TRUE = "control_true"    # Guard → true-arm
    CONTROL_FALSE = "control_false"  # Guard → false-arm
    PHI_MERGE = "phi_merge"          # Predecessors → phi-node overlap
    SCOPE_ENTRY = "scope_entry"      # Outer scope → inner scope

    # Interprocedural
    ACTUAL_TO_FORMAL = "actual_to_formal"  # Caller arg → callee param
    FORMAL_TO_RETURN = "formal_to_return"  # Callee return → caller result
    CALLEE_ERROR_PULLBACK = "callee_error_pullback"  # Callee error → caller input

    # Theory-pack transport
    PACK_TRANSPORT = "pack_transport"      # Theory-declared transport
    SHAPE_PROPAGATION = "shape_propagation"  # Shape flows through operations
    ORDER_PROJECTION = "order_projection"    # Sort → values/indices decomposition
    INDEX_DOMAIN = "index_domain"            # Index operation domain constraint

    # Boundary
    INPUT_PROJECTION = "input_projection"    # Interior → input boundary
    OUTPUT_PROJECTION = "output_projection"  # Interior → output boundary

    # Error
    ERROR_VIABILITY = "error_viability"      # Error site ← upstream viability
    ERROR_PULLBACK = "error_pullback"        # Error site → input requirement

    # Proof
    PROOF_TRANSPORT = "proof_transport"      # Proof site → program site
    WITNESS_FLOW = "witness_flow"            # Witness export → consumer

    # Heap
    FIELD_INIT = "field_init"               # Constructor → field state
    ALIAS_CHAIN = "alias_chain"             # Alias source → alias target
    FRAME_RESTRICTION = "frame_restriction" # Outer frame → inner frame


# ---------------------------------------------------------------------------
# Restriction map data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RestrictionData:
    """Metadata attached to a restriction map.

    The ``restrict`` method on ``ConcreteMorphism`` uses this data to
    determine how to project a ``LocalSection`` from source to target.
    """
    kind: RestrictionKind
    description: str = ""

    # Which refinement keys survive the restriction
    preserved_keys: FrozenSet[str] = frozenset()
    dropped_keys: FrozenSet[str] = frozenset()

    # For control restrictions: the predicate to add/remove
    guard_predicate: Optional[Any] = None
    guard_polarity: bool = True

    # For call reindexing: the mapping from actual to formal names
    actual_to_formal: Optional[Mapping[str, str]] = None

    # For pack transport: the theory pack that declared this transport
    pack_name: Optional[str] = None
    transport_rule: Optional[str] = None

    # For error pullback: the viability predicate to impose
    viability_predicate: Optional[Any] = None

    # Trust level: does this restriction preserve trust or downgrade it?
    trust_preservation: bool = True
    forced_trust: Optional[TrustLevel] = None


# ---------------------------------------------------------------------------
# Restriction map constructors
# ---------------------------------------------------------------------------

def _make_morphism(
    source: SiteId,
    target: SiteId,
    data: RestrictionData,
) -> ConcreteMorphism:
    """Create a concrete morphism with restriction data in metadata."""
    return ConcreteMorphism(
        _source=source,
        _target=target,
        _metadata={"restriction": data},
    )


def make_lineage_restriction(
    parent_site: SiteId,
    child_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
    description: str = "",
) -> ConcreteMorphism:
    """Restriction from a parent SSA value to a derived value.

    The child inherits a restricted view of the parent's local section.
    Lineage chains are the primary mechanism by which wrapper transparency
    is expressed: if the restriction preserves all refinement keys, the
    wrapper is semantically transparent.
    """
    data = RestrictionData(
        kind=RestrictionKind.LINEAGE,
        description=description or f"lineage: {parent_site.name} → {child_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(parent_site, child_site, data)


def make_control_restriction(
    guard_site: SiteId,
    arm_site: SiteId,
    *,
    polarity: bool = True,
    guard_predicate: Optional[Any] = None,
    narrowed_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Restriction from a branch guard to a controlled arm.

    The guard predicate narrows the section: in the true arm, the guard
    holds; in the false arm, its negation holds.  This is how if-statements,
    assertions, and match structures introduce local refinements.
    """
    kind = RestrictionKind.CONTROL_TRUE if polarity else RestrictionKind.CONTROL_FALSE
    pol_str = "true" if polarity else "false"
    data = RestrictionData(
        kind=kind,
        description=f"control({pol_str}): {guard_site.name} → {arm_site.name}",
        guard_predicate=guard_predicate,
        guard_polarity=polarity,
        preserved_keys=narrowed_keys,
    )
    return _make_morphism(guard_site, arm_site, data)


def make_phi_merge_restriction(
    predecessor_site: SiteId,
    phi_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Restriction from a predecessor to a phi-merge overlap site.

    In sheaf-descent semantics, a phi-node is not a bookkeeping device but
    an overlap site where sections from predecessor blocks must agree or
    expose an obstruction.  This morphism declares one side of that overlap.
    """
    data = RestrictionData(
        kind=RestrictionKind.PHI_MERGE,
        description=f"phi_merge: {predecessor_site.name} → {phi_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(predecessor_site, phi_site, data)


def make_actual_to_formal_restriction(
    caller_arg_site: SiteId,
    callee_param_site: SiteId,
    *,
    actual_name: str,
    formal_name: str,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Reindexing from a caller argument to a callee formal parameter.

    This is how interprocedural section transport begins: the caller's
    actual argument section is reindexed to the callee's parameter site.
    """
    data = RestrictionData(
        kind=RestrictionKind.ACTUAL_TO_FORMAL,
        description=f"call_reindex: {actual_name} → {formal_name}",
        actual_to_formal={actual_name: formal_name},
        preserved_keys=preserved_keys,
    )
    return _make_morphism(caller_arg_site, callee_param_site, data)


def make_return_to_caller_restriction(
    callee_return_site: SiteId,
    caller_result_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Restriction from callee return to caller call-result site.

    This completes the interprocedural round-trip: the callee's output
    boundary section flows back into the caller's cover at the call-result
    site.
    """
    data = RestrictionData(
        kind=RestrictionKind.FORMAL_TO_RETURN,
        description=f"return_import: {callee_return_site.name} → {caller_result_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(callee_return_site, caller_result_site, data)


def make_pack_transport(
    source_site: SiteId,
    target_site: SiteId,
    *,
    pack_name: str,
    transport_rule: str,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Transport declared by a theory pack.

    Theory packs create sites and declare how facts restrict across them.
    For example, a sort pack declares that order-site facts transport to
    downstream indexing sites via permutation witnesses.
    """
    data = RestrictionData(
        kind=RestrictionKind.PACK_TRANSPORT,
        description=f"pack({pack_name}): {source_site.name} → {target_site.name}",
        pack_name=pack_name,
        transport_rule=transport_rule,
        preserved_keys=preserved_keys,
    )
    return _make_morphism(source_site, target_site, data)


def make_error_viability_restriction(
    upstream_site: SiteId,
    error_site: SiteId,
    *,
    viability_predicate: Optional[Any] = None,
    description: str = "",
) -> ConcreteMorphism:
    """Viability restriction from an upstream site to an error site.

    This declares that the error site's safety depends on facts at the
    upstream site.  During backward synthesis, the viability predicate
    is pulled back through this morphism to generate safe input requirements.
    """
    data = RestrictionData(
        kind=RestrictionKind.ERROR_VIABILITY,
        description=description or f"viability: {upstream_site.name} → {error_site.name}",
        viability_predicate=viability_predicate,
    )
    return _make_morphism(upstream_site, error_site, data)


def make_error_pullback_restriction(
    error_site: SiteId,
    input_site: SiteId,
    *,
    viability_predicate: Optional[Any] = None,
    description: str = "",
) -> ConcreteMorphism:
    """Pullback from an error site to the input boundary.

    This is the backward direction: an error site's viability requirement
    becomes a constraint on the input boundary.  This is how runtime-error
    anticipation becomes precondition synthesis.
    """
    data = RestrictionData(
        kind=RestrictionKind.ERROR_PULLBACK,
        description=description or f"pullback: {error_site.name} → {input_site.name}",
        viability_predicate=viability_predicate,
    )
    return _make_morphism(error_site, input_site, data)


def make_input_projection(
    interior_site: SiteId,
    boundary_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Projection from an interior site to the input boundary."""
    data = RestrictionData(
        kind=RestrictionKind.INPUT_PROJECTION,
        description=f"input_proj: {interior_site.name} → {boundary_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(interior_site, boundary_site, data)


def make_output_projection(
    interior_site: SiteId,
    boundary_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Projection from an interior site to the output boundary."""
    data = RestrictionData(
        kind=RestrictionKind.OUTPUT_PROJECTION,
        description=f"output_proj: {interior_site.name} → {boundary_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(interior_site, boundary_site, data)


def make_proof_transport(
    proof_site: SiteId,
    program_site: SiteId,
    *,
    theorem_name: Optional[str] = None,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Transport from a proof site to a program site.

    This is how theorem modules inject checked facts into the cover.
    The transported section gets PROOF_BACKED trust level.
    """
    data = RestrictionData(
        kind=RestrictionKind.PROOF_TRANSPORT,
        description=f"proof_transport: {proof_site.name} → {program_site.name}",
        forced_trust=TrustLevel.PROOF_BACKED,
        preserved_keys=preserved_keys,
    )
    return _make_morphism(proof_site, program_site, data)


def make_field_init_restriction(
    constructor_site: SiteId,
    field_site: SiteId,
    *,
    field_name: str,
) -> ConcreteMorphism:
    """Restriction from a constructor site to a field-state site."""
    data = RestrictionData(
        kind=RestrictionKind.FIELD_INIT,
        description=f"field_init: {constructor_site.name}.{field_name}",
    )
    return _make_morphism(constructor_site, field_site, data)


def make_alias_chain_restriction(
    source_site: SiteId,
    alias_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Restriction along an alias chain.

    Alias chains are lineage-like but for heap objects: two textual variables
    refer to the same underlying object, so their sections must agree.
    """
    data = RestrictionData(
        kind=RestrictionKind.ALIAS_CHAIN,
        description=f"alias: {source_site.name} → {alias_site.name}",
        preserved_keys=preserved_keys,
    )
    return _make_morphism(source_site, alias_site, data)


def make_witness_flow_restriction(
    witness_site: SiteId,
    consumer_site: SiteId,
    *,
    preserved_keys: FrozenSet[str] = frozenset(),
) -> ConcreteMorphism:
    """Flow from a witness-exporting site to a consumer site."""
    data = RestrictionData(
        kind=RestrictionKind.WITNESS_FLOW,
        description=f"witness_flow: {witness_site.name} → {consumer_site.name}",
        preserved_keys=preserved_keys,
        forced_trust=TrustLevel.PROOF_BACKED,
    )
    return _make_morphism(witness_site, consumer_site, data)


# ---------------------------------------------------------------------------
# Restriction application
# ---------------------------------------------------------------------------

def apply_restriction(
    morphism: ConcreteMorphism,
    section: LocalSection,
) -> LocalSection:
    """Apply a restriction map to project a local section.

    This is the core sheaf operation: given a section at the source site
    and a morphism, produce the restricted section at the target site.
    """
    restriction: Optional[RestrictionData] = None
    if hasattr(morphism, "metadata") and isinstance(morphism.metadata, dict):
        restriction = morphism.metadata.get("restriction")

    if restriction is None:
        # Default: copy section with new site_id
        return LocalSection(
            site_id=morphism.target,
            carrier_type=section.carrier_type,
            refinements=dict(section.refinements),
            trust=section.trust,
            provenance=section.provenance,
            witnesses=dict(section.witnesses),
        )

    # Filter refinements by preserved/dropped keys
    new_refinements = dict(section.refinements)
    if restriction.preserved_keys:
        new_refinements = {
            k: v for k, v in new_refinements.items()
            if k in restriction.preserved_keys
        }
    if restriction.dropped_keys:
        new_refinements = {
            k: v for k, v in new_refinements.items()
            if k not in restriction.dropped_keys
        }

    # Add guard predicate for control restrictions
    if restriction.guard_predicate is not None:
        pred_key = f"guard_{restriction.kind.value}"
        if restriction.guard_polarity:
            new_refinements[pred_key] = restriction.guard_predicate
        else:
            new_refinements[pred_key] = ("not", restriction.guard_predicate)

    # Handle trust modification
    new_trust = section.trust
    if restriction.forced_trust is not None:
        new_trust = restriction.forced_trust
    elif not restriction.trust_preservation:
        # Downgrade to BOUNDED_AUTO if trust is not preserved
        if new_trust == TrustLevel.TRUSTED_AUTO:
            new_trust = TrustLevel.BOUNDED_AUTO

    # Handle actual-to-formal reindexing
    if restriction.actual_to_formal is not None:
        reindexed = {}
        for k, v in new_refinements.items():
            new_key = k
            for actual, formal in restriction.actual_to_formal.items():
                new_key = new_key.replace(actual, formal)
            reindexed[new_key] = v
        new_refinements = reindexed

    return LocalSection(
        site_id=morphism.target,
        carrier_type=section.carrier_type,
        refinements=new_refinements,
        trust=new_trust,
        provenance=f"restricted from {section.site_id} via {restriction.kind.value}",
        witnesses=dict(section.witnesses),
    )


# ---------------------------------------------------------------------------
# Overlap detection
# ---------------------------------------------------------------------------

def sites_overlap(
    site_a: SiteId,
    site_b: SiteId,
    morphisms: Sequence[ConcreteMorphism],
) -> bool:
    """Check whether two sites share an overlap through the given morphisms.

    Two sites overlap if there exists a morphism path connecting them,
    meaning their local sections must agree on the overlap (sheaf gluing
    condition).
    """
    # Direct morphism
    for m in morphisms:
        if (m.source == site_a and m.target == site_b) or \
           (m.source == site_b and m.target == site_a):
            return True

    # Shared target (both restrict to same site)
    targets_a = {m.target for m in morphisms if m.source == site_a}
    targets_b = {m.target for m in morphisms if m.source == site_b}
    if targets_a & targets_b:
        return True

    # Shared source (both are restricted from same site)
    sources_a = {m.source for m in morphisms if m.target == site_a}
    sources_b = {m.source for m in morphisms if m.target == site_b}
    if sources_a & sources_b:
        return True

    return False


def find_overlaps(
    sites: Sequence[SiteId],
    morphisms: Sequence[ConcreteMorphism],
) -> List[Tuple[SiteId, SiteId]]:
    """Find all overlapping site pairs.

    Returns pairs of sites whose local sections must agree for the
    sheaf gluing condition to hold.
    """
    overlaps: List[Tuple[SiteId, SiteId]] = []
    for i, a in enumerate(sites):
        for b in sites[i + 1:]:
            if sites_overlap(a, b, morphisms):
                overlaps.append((a, b))
    return overlaps
