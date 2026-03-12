"""Aggregator -- merge all harvested predicates per site.

Combines the outputs of all individual harvesters (guards, type guards,
None guards, arithmetic bounds, collection facts, tensor facts, exception
regions, and protocol hints) into a unified ``HarvestResult``.  Provides
``apply_harvest_to_cover`` to enrich a ``Cover`` with harvested sections.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.predicates.base import Predicate

from deppy.harvest.guard_harvester import HarvestedGuard
from deppy.harvest.type_guard_harvester import TypeNarrowingFact
from deppy.harvest.none_guard_harvester import NoneGuard
from deppy.harvest.arithmetic_harvester import ArithmeticBound
from deppy.harvest.collection_harvester import CollectionFact
from deppy.harvest.tensor_harvester import TensorFact
from deppy.harvest.exception_harvester import ExceptionRegion
from deppy.harvest.protocol_harvester import ProtocolHint


# ===================================================================
#  Per-variable harvest bundle
# ===================================================================

@dataclass(frozen=True)
class VariableHarvest:
    """All harvested facts for a single variable.

    Bundles guard predicates, type narrowings, None checks, arithmetic
    bounds, collection facts, tensor facts, and protocol hints.
    """
    variable: str
    guards: Tuple[HarvestedGuard, ...] = ()
    type_narrowings: Tuple[TypeNarrowingFact, ...] = ()
    none_guards: Tuple[NoneGuard, ...] = ()
    arithmetic_bounds: Tuple[ArithmeticBound, ...] = ()
    collection_facts: Tuple[CollectionFact, ...] = ()
    tensor_facts: Tuple[TensorFact, ...] = ()
    protocol_hints: Tuple[ProtocolHint, ...] = ()

    @property
    def has_facts(self) -> bool:
        """Return True if any facts are present."""
        return bool(
            self.guards or self.type_narrowings or self.none_guards
            or self.arithmetic_bounds or self.collection_facts
            or self.tensor_facts or self.protocol_hints
        )

    @property
    def all_predicates(self) -> List[Predicate]:
        """Collect all predicates from all fact types."""
        preds: List[Predicate] = []
        for g in self.guards:
            preds.append(g.predicate)
        for t in self.type_narrowings:
            if t.predicate is not None:
                preds.append(t.predicate)
        for n in self.none_guards:
            if n.predicate is not None:
                preds.append(n.predicate)
        for a in self.arithmetic_bounds:
            if a.predicate is not None:
                preds.append(a.predicate)
        for c in self.collection_facts:
            if c.predicate is not None:
                preds.append(c.predicate)
        for tf in self.tensor_facts:
            if tf.predicate is not None:
                preds.append(tf.predicate)
        for p in self.protocol_hints:
            preds.append(p.to_predicate())
        return preds

    @property
    def best_trust(self) -> TrustLevel:
        """Return the best (most trusted) trust level across all facts."""
        trust_order = [
            TrustLevel.PROOF_BACKED,
            TrustLevel.TRUSTED_AUTO,
            TrustLevel.BOUNDED_AUTO,
            TrustLevel.TRACE_BACKED,
            TrustLevel.RESIDUAL,
            TrustLevel.ASSUMED,
        ]
        best = TrustLevel.RESIDUAL
        all_trusts: List[TrustLevel] = []
        for g in self.guards:
            all_trusts.append(g.trust_level)
        for t in self.type_narrowings:
            all_trusts.append(t.trust_level)
        for n in self.none_guards:
            all_trusts.append(n.trust_level)
        for a in self.arithmetic_bounds:
            all_trusts.append(a.trust_level)
        for c in self.collection_facts:
            all_trusts.append(c.trust_level)
        for tf in self.tensor_facts:
            all_trusts.append(tf.trust_level)
        for p in self.protocol_hints:
            all_trusts.append(p.trust_level)

        for trust in trust_order:
            if trust in all_trusts:
                return trust
        return best


# ===================================================================
#  HarvestResult
# ===================================================================

@dataclass(frozen=True)
class HarvestResult:
    """Aggregated harvest result containing all facts organized by variable/site.

    Attributes:
        guards: All harvested guards.
        type_narrowings: All type guard narrowings.
        none_guards: All None-check guards.
        arithmetic_bounds: All arithmetic bounds.
        collection_facts: All collection facts.
        tensor_facts: All tensor facts.
        exception_regions: All exception-guarded regions.
        protocol_hints: All protocol conformance hints.
        by_variable: Facts organized by variable name.
        file: Source file name.
    """
    guards: Tuple[HarvestedGuard, ...] = ()
    type_narrowings: Tuple[TypeNarrowingFact, ...] = ()
    none_guards: Tuple[NoneGuard, ...] = ()
    arithmetic_bounds: Tuple[ArithmeticBound, ...] = ()
    collection_facts: Tuple[CollectionFact, ...] = ()
    tensor_facts: Tuple[TensorFact, ...] = ()
    exception_regions: Tuple[ExceptionRegion, ...] = ()
    protocol_hints: Tuple[ProtocolHint, ...] = ()
    by_variable: Tuple[Tuple[str, VariableHarvest], ...] = ()
    file: str = "<unknown>"

    @property
    def total_facts(self) -> int:
        """Total number of individual facts across all categories."""
        return (
            len(self.guards)
            + len(self.type_narrowings)
            + len(self.none_guards)
            + len(self.arithmetic_bounds)
            + len(self.collection_facts)
            + len(self.tensor_facts)
            + len(self.exception_regions)
            + len(self.protocol_hints)
        )

    @property
    def variables(self) -> FrozenSet[str]:
        """Return all variable names that have harvested facts."""
        return frozenset(v for v, _ in self.by_variable)

    def for_variable(self, variable: str) -> Optional[VariableHarvest]:
        """Retrieve the harvest bundle for a specific variable."""
        for v, harvest in self.by_variable:
            if v == variable:
                return harvest
        return None

    @property
    def all_predicates(self) -> List[Predicate]:
        """Collect all predicates from all fact categories."""
        preds: List[Predicate] = []
        for g in self.guards:
            preds.append(g.predicate)
        for t in self.type_narrowings:
            if t.predicate is not None:
                preds.append(t.predicate)
        for n in self.none_guards:
            if n.predicate is not None:
                preds.append(n.predicate)
        for a in self.arithmetic_bounds:
            if a.predicate is not None:
                preds.append(a.predicate)
        for c in self.collection_facts:
            if c.predicate is not None:
                preds.append(c.predicate)
        for tf in self.tensor_facts:
            if tf.predicate is not None:
                preds.append(tf.predicate)
        for p in self.protocol_hints:
            preds.append(p.to_predicate())
        return preds


# ===================================================================
#  Aggregation logic
# ===================================================================

def _collect_variables(
    guards: Sequence[HarvestedGuard],
    type_narrowings: Sequence[TypeNarrowingFact],
    none_guards: Sequence[NoneGuard],
    arithmetic_bounds: Sequence[ArithmeticBound],
    collection_facts: Sequence[CollectionFact],
    tensor_facts: Sequence[TensorFact],
    protocol_hints: Sequence[ProtocolHint],
) -> Set[str]:
    """Collect all variable names mentioned across all fact types."""
    variables: Set[str] = set()
    for g in guards:
        variables |= g.narrowed_variables
    for t in type_narrowings:
        variables.add(t.variable)
    for n in none_guards:
        variables.add(n.variable)
    for a in arithmetic_bounds:
        variables.add(a.variable)
    for c in collection_facts:
        variables.add(c.variable)
    for tf in tensor_facts:
        variables.add(tf.variable)
    for p in protocol_hints:
        variables.add(p.variable_name)
    return variables


def _build_variable_harvest(
    variable: str,
    guards: Sequence[HarvestedGuard],
    type_narrowings: Sequence[TypeNarrowingFact],
    none_guards: Sequence[NoneGuard],
    arithmetic_bounds: Sequence[ArithmeticBound],
    collection_facts: Sequence[CollectionFact],
    tensor_facts: Sequence[TensorFact],
    protocol_hints: Sequence[ProtocolHint],
) -> VariableHarvest:
    """Build a VariableHarvest for a specific variable."""
    return VariableHarvest(
        variable=variable,
        guards=tuple(g for g in guards if variable in g.narrowed_variables),
        type_narrowings=tuple(t for t in type_narrowings if t.variable == variable),
        none_guards=tuple(n for n in none_guards if n.variable == variable),
        arithmetic_bounds=tuple(a for a in arithmetic_bounds if a.variable == variable),
        collection_facts=tuple(c for c in collection_facts if c.variable == variable),
        tensor_facts=tuple(tf for tf in tensor_facts if tf.variable == variable),
        protocol_hints=tuple(p for p in protocol_hints if p.variable_name == variable),
    )


def aggregate_harvests(
    guards: Sequence[HarvestedGuard],
    type_narrowings: Sequence[TypeNarrowingFact],
    none_guards: Sequence[NoneGuard],
    arithmetic_bounds: Sequence[ArithmeticBound],
    collection_facts: Sequence[CollectionFact],
    tensor_facts: Sequence[TensorFact],
    exception_regions: Sequence[ExceptionRegion],
    protocol_hints: Sequence[ProtocolHint],
    *,
    file: str = "<unknown>",
) -> HarvestResult:
    """Merge all harvested facts into a single ``HarvestResult``.

    Organizes facts both globally (by category) and per-variable.

    Args:
        guards: Guard predicates from ``harvest_guards``.
        type_narrowings: Type narrowings from ``harvest_type_guards``.
        none_guards: None guards from ``harvest_none_guards``.
        arithmetic_bounds: Arithmetic bounds from ``harvest_arithmetic_bounds``.
        collection_facts: Collection facts from ``harvest_collection_facts``.
        tensor_facts: Tensor facts from ``harvest_tensor_facts``.
        exception_regions: Exception regions from ``harvest_exception_regions``.
        protocol_hints: Protocol hints from ``harvest_protocol_hints``.
        file: Source file name for provenance.

    Returns:
        A ``HarvestResult`` containing all facts.
    """
    # Collect all mentioned variables
    all_vars = _collect_variables(
        guards, type_narrowings, none_guards,
        arithmetic_bounds, collection_facts, tensor_facts,
        protocol_hints,
    )

    # Build per-variable bundles
    by_variable: List[Tuple[str, VariableHarvest]] = []
    for var in sorted(all_vars):
        harvest = _build_variable_harvest(
            var, guards, type_narrowings, none_guards,
            arithmetic_bounds, collection_facts, tensor_facts,
            protocol_hints,
        )
        if harvest.has_facts:
            by_variable.append((var, harvest))

    return HarvestResult(
        guards=tuple(guards),
        type_narrowings=tuple(type_narrowings),
        none_guards=tuple(none_guards),
        arithmetic_bounds=tuple(arithmetic_bounds),
        collection_facts=tuple(collection_facts),
        tensor_facts=tuple(tensor_facts),
        exception_regions=tuple(exception_regions),
        protocol_hints=tuple(protocol_hints),
        by_variable=tuple(by_variable),
        file=file,
    )


# ===================================================================
#  Apply harvest to cover
# ===================================================================

def _harvest_to_refinements(
    var_harvest: VariableHarvest,
) -> Dict[str, Any]:
    """Convert a variable's harvest into refinement dict entries."""
    refinements: Dict[str, Any] = {}

    # Guard predicates
    if var_harvest.guards:
        refinements["guards"] = [g.predicate for g in var_harvest.guards]

    # Type narrowings
    if var_harvest.type_narrowings:
        refinements["type_narrowings"] = [
            {"type": t.narrowed_type, "kind": t.narrowing_kind.value}
            for t in var_harvest.type_narrowings
        ]

    # None guards
    if var_harvest.none_guards:
        refinements["none_guards"] = [
            {"is_none": n.is_none_check, "kind": n.none_check_kind.value}
            for n in var_harvest.none_guards
        ]

    # Arithmetic bounds
    if var_harvest.arithmetic_bounds:
        refinements["arithmetic_bounds"] = [
            {"op": a.operator, "bound_type": a.bound_type.value}
            for a in var_harvest.arithmetic_bounds
        ]

    # Collection facts
    if var_harvest.collection_facts:
        refinements["collection_facts"] = [
            {"kind": c.fact_kind.value}
            for c in var_harvest.collection_facts
        ]

    # Tensor facts
    if var_harvest.tensor_facts:
        refinements["tensor_facts"] = [
            {
                "kind": tf.fact_kind.value,
                "dtype": tf.dtype_value,
                "device": tf.device_value,
                "rank": tf.rank_value,
            }
            for tf in var_harvest.tensor_facts
        ]

    # Protocol hints
    if var_harvest.protocol_hints:
        refinements["protocol_hints"] = [
            {
                "protocol": p.protocol_name,
                "required_methods": list(p.required_methods),
                "required_attributes": list(p.required_attributes),
            }
            for p in var_harvest.protocol_hints
        ]

    return refinements


def _select_trust_for_site(
    var_harvest: VariableHarvest,
    site_kind: SiteKind,
) -> TrustLevel:
    """Select the appropriate trust level for a site based on harvest data."""
    # Use the best trust from the harvest
    return var_harvest.best_trust


def apply_harvest_to_cover(
    harvest_result: HarvestResult,
    cover: Cover,
) -> Cover:
    """Enrich a cover's sites with harvested section data.

    For each site in the cover, looks up the corresponding variable's
    harvested facts and populates a ``LocalSection`` with refinements,
    trust levels, and witnesses derived from the harvest.

    Args:
        harvest_result: The aggregated harvest result.
        cover: The cover to enrich.

    Returns:
        The same cover, modified in-place with enriched local sections.
    """
    # Build a mapping from site_id to local sections
    for site_id, site in cover.sites.items():
        # Extract the variable name from the site name
        var_name = _site_id_to_variable(site_id)
        if var_name is None:
            continue

        var_harvest = harvest_result.for_variable(var_name)
        if var_harvest is None or not var_harvest.has_facts:
            continue

        # Build refinements from harvest
        refinements = _harvest_to_refinements(var_harvest)
        trust = _select_trust_for_site(var_harvest, site_id.kind)

        # Build witnesses (predicates that serve as evidence)
        witnesses: Dict[str, Any] = {}
        all_preds = var_harvest.all_predicates
        if all_preds:
            witnesses["harvested_predicates"] = all_preds

        # Create or update the local section
        section = LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements=refinements,
            trust=trust,
            provenance=f"harvest:{harvest_result.file}",
            witnesses=witnesses,
        )

        # Store the section in the site metadata
        metadata = getattr(site, "_metadata", None)
        if isinstance(metadata, dict):
            metadata["harvest_section"] = section

    # Enrich guard sites specifically
    for guard in harvest_result.guards:
        # Find matching branch guard sites
        for site_id in cover.sites:
            if site_id.kind == SiteKind.BRANCH_GUARD:
                if guard.source_span is not None:
                    loc = site_id.source_location
                    if loc is not None:
                        span_loc = guard.source_span.as_tuple()
                        if loc == span_loc:
                            _enrich_guard_site(cover, site_id, guard)

    # Enrich exception-related error sites
    for region in harvest_result.exception_regions:
        for site_id in cover.error_sites:
            if site_id.kind == SiteKind.ERROR:
                _enrich_error_site(cover, site_id, region)

    return cover


def _site_id_to_variable(site_id: SiteId) -> Optional[str]:
    """Extract a variable name from a SiteId's name.

    Convention: site names are like ``func.var_0`` for SSA sites,
    ``func.param`` for argument sites, etc.
    """
    name = site_id.name
    parts = name.rsplit(".", 1)
    if len(parts) == 2:
        var_part = parts[1]
        # Strip SSA version suffix
        if "_" in var_part:
            base = var_part.rsplit("_", 1)[0]
            return base
        return var_part
    return name


def _enrich_guard_site(
    cover: Cover,
    site_id: SiteId,
    guard: HarvestedGuard,
) -> None:
    """Enrich a branch guard site with harvested guard data."""
    site = cover.sites.get(site_id)
    if site is None:
        return
    metadata = getattr(site, "_metadata", None)
    if isinstance(metadata, dict):
        existing = metadata.get("harvested_guards", [])
        existing.append(guard)
        metadata["harvested_guards"] = existing


def _enrich_error_site(
    cover: Cover,
    site_id: SiteId,
    region: ExceptionRegion,
) -> None:
    """Enrich an error site with exception region data."""
    site = cover.sites.get(site_id)
    if site is None:
        return
    metadata = getattr(site, "_metadata", None)
    if isinstance(metadata, dict):
        existing = metadata.get("exception_regions", [])
        existing.append(region)
        metadata["exception_regions"] = existing


# ===================================================================
#  Full pipeline: harvest_all
# ===================================================================

def harvest_all(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> HarvestResult:
    """Run all harvesters on an AST and aggregate the results.

    This is the main entry point for the harvest stage.  It runs:
    1. Guard harvester
    2. Type guard harvester
    3. None guard harvester
    4. Arithmetic bound harvester
    5. Collection fact harvester
    6. Tensor fact harvester
    7. Exception region harvester
    8. Protocol hint harvester

    And then aggregates all results into a single ``HarvestResult``.

    Args:
        ast_tree: The parsed Python AST.
        file: Source file name for provenance.

    Returns:
        A ``HarvestResult`` containing all discovered facts.
    """
    from deppy.harvest.guard_harvester import harvest_guards
    from deppy.harvest.type_guard_harvester import harvest_type_guards
    from deppy.harvest.none_guard_harvester import harvest_none_guards
    from deppy.harvest.arithmetic_harvester import harvest_arithmetic_bounds
    from deppy.harvest.collection_harvester import harvest_collection_facts
    from deppy.harvest.tensor_harvester import harvest_tensor_facts
    from deppy.harvest.exception_harvester import harvest_exception_regions
    from deppy.harvest.protocol_harvester import harvest_protocols

    guards = harvest_guards(ast_tree, file=file)
    type_narr = harvest_type_guards(ast_tree, file=file)
    none_g = harvest_none_guards(ast_tree, file=file)
    arith = harvest_arithmetic_bounds(ast_tree, file=file)
    coll = harvest_collection_facts(ast_tree, file=file)
    tensor = harvest_tensor_facts(ast_tree, file=file)
    exc = harvest_exception_regions(ast_tree, file=file)
    proto = harvest_protocols(ast_tree, file=file)

    return aggregate_harvests(
        guards, type_narr, none_g, arith,
        coll, tensor, exc, proto,
        file=file,
    )
