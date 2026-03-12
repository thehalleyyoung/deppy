"""Pack composition engine for combining multiple theory packs.

Provides sophisticated composition strategies beyond simple delegation:
  - Priority-based conflict resolution
  - Sequential refinement pipelines
  - Parallel analysis with result merging
  - Cross-theory constraint propagation
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
    narrow_section,
    upgrade_trust,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Composition strategy
# ═══════════════════════════════════════════════════════════════════════════════


class CompositionStrategy(Enum):
    """How to compose results from multiple packs."""
    PRIORITY = auto()       # Use highest-priority pack only
    SEQUENTIAL = auto()     # Apply packs in sequence, each refining previous
    PARALLEL_MEET = auto()  # Run all packs, take meet of results
    PARALLEL_JOIN = auto()  # Run all packs, take join of results
    FIRST_SUCCESS = auto()  # Use first pack that succeeds


@dataclass
class CompositionConflict:
    """Records a conflict between two packs' results."""
    site_id: SiteId
    pack_a: str
    pack_b: str
    key: str
    value_a: Any
    value_b: Any
    resolution: str = ""

    def __repr__(self) -> str:
        return (
            f"Conflict({self.site_id}: {self.pack_a}.{self.key}={self.value_a!r} "
            f"vs {self.pack_b}.{self.key}={self.value_b!r}, "
            f"resolved={self.resolution})"
        )


@dataclass
class CompositionReport:
    """Report from a pack composition operation."""
    strategy: CompositionStrategy
    packs_consulted: List[str] = field(default_factory=list)
    conflicts: List[CompositionConflict] = field(default_factory=list)
    final_status: SolverStatus = SolverStatus.UNKNOWN
    explanation: str = ""

    @property
    def has_conflicts(self) -> bool:
        return len(self.conflicts) > 0


# ═══════════════════════════════════════════════════════════════════════════════
# Pack Composer
# ═══════════════════════════════════════════════════════════════════════════════


class PackComposer:
    """Composes multiple theory packs into a unified solver.

    The composer takes a set of packs and a strategy, then delegates
    operations to the appropriate pack(s) based on the strategy and
    the site kind being processed.

    Priority-based routing ensures each site kind goes to at most one
    pack in PRIORITY mode, while SEQUENTIAL mode chains them.
    """

    def __init__(
        self,
        packs: Sequence[TheoryPackBase],
        strategy: CompositionStrategy = CompositionStrategy.PRIORITY,
    ) -> None:
        self._packs = sorted(packs, key=lambda p: p.pack_priority)
        self._strategy = strategy
        self._kind_to_packs: Dict[SiteKind, List[TheoryPackBase]] = {}
        for pack in self._packs:
            for kind in pack.applicable_site_kinds():
                if kind not in self._kind_to_packs:
                    self._kind_to_packs[kind] = []
                self._kind_to_packs[kind].append(pack)
        self._conflict_log: List[CompositionConflict] = []
        self._reports: List[CompositionReport] = []

    @property
    def strategy(self) -> CompositionStrategy:
        return self._strategy

    @strategy.setter
    def strategy(self, value: CompositionStrategy) -> None:
        self._strategy = value

    @property
    def packs(self) -> List[TheoryPackBase]:
        return list(self._packs)

    @property
    def conflicts(self) -> List[CompositionConflict]:
        return list(self._conflict_log)

    def clear_conflicts(self) -> None:
        self._conflict_log.clear()

    # ── Primary dispatch ──────────────────────────────────────────────────

    def _get_packs_for_site(self, site_id: SiteId) -> List[TheoryPackBase]:
        """Get applicable packs for a site, in priority order."""
        return self._kind_to_packs.get(site_id.kind, [])

    def _get_packs_for_kind(self, kind: SiteKind) -> List[TheoryPackBase]:
        """Get applicable packs for a site kind, in priority order."""
        return self._kind_to_packs.get(kind, [])

    # ── Solve local ───────────────────────────────────────────────────────

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Solve locally using the configured composition strategy."""
        packs = self._get_packs_for_site(site)
        if not packs:
            return SolverResult(
                status=SolverStatus.UNKNOWN,
                section=section,
                explanation="no pack for site kind",
            )

        if self._strategy == CompositionStrategy.PRIORITY:
            return self._solve_priority(site, section, packs)
        elif self._strategy == CompositionStrategy.SEQUENTIAL:
            return self._solve_sequential(site, section, packs)
        elif self._strategy == CompositionStrategy.PARALLEL_MEET:
            return self._solve_parallel_meet(site, section, packs)
        elif self._strategy == CompositionStrategy.PARALLEL_JOIN:
            return self._solve_parallel_join(site, section, packs)
        elif self._strategy == CompositionStrategy.FIRST_SUCCESS:
            return self._solve_first_success(site, section, packs)
        else:
            return self._solve_priority(site, section, packs)

    def _solve_priority(
        self, site: SiteId, section: LocalSection, packs: List[TheoryPackBase]
    ) -> SolverResult:
        """Use the highest-priority pack only."""
        return packs[0].solve_local(site, section)

    def _solve_sequential(
        self, site: SiteId, section: LocalSection, packs: List[TheoryPackBase]
    ) -> SolverResult:
        """Apply packs sequentially, each refining the previous result."""
        current = section
        combined_constraints: List[str] = []
        combined_obligations: List[str] = []
        final_status = SolverStatus.UNCHANGED
        explanations: List[str] = []

        for pack in packs:
            result = pack.solve_local(site, current)
            if result.is_failure:
                return result
            if result.is_success:
                current = result.section
                final_status = result.status
            combined_constraints.extend(result.constraints_remaining)
            combined_obligations.extend(result.proof_obligations)
            if result.explanation:
                explanations.append(f"[{pack.pack_name}] {result.explanation}")

        return SolverResult(
            status=final_status,
            section=current,
            constraints_remaining=combined_constraints,
            explanation=" -> ".join(explanations),
            proof_obligations=combined_obligations,
        )

    def _solve_parallel_meet(
        self, site: SiteId, section: LocalSection, packs: List[TheoryPackBase]
    ) -> SolverResult:
        """Run all packs, take the meet (intersection) of refinements."""
        results = [pack.solve_local(site, section) for pack in packs]

        for r in results:
            if r.is_failure:
                return r

        successful = [r for r in results if r.is_success]
        if not successful:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no pack made progress",
            )

        merged_refs = dict(section.refinements)
        for r in successful:
            merged_refs = merge_refinements(merged_refs, r.section.refinements, "meet")

        conflicts = self._detect_conflicts(site, results, packs)
        self._conflict_log.extend(conflicts)

        best_trust = section.trust
        _trust_order = {
            TrustLevel.ASSUMED: 0, TrustLevel.RESIDUAL: 1,
            TrustLevel.TRACE_BACKED: 2, TrustLevel.BOUNDED_AUTO: 3,
            TrustLevel.TRUSTED_AUTO: 4, TrustLevel.PROOF_BACKED: 5,
        }
        for r in successful:
            if _trust_order.get(r.section.trust, 0) > _trust_order.get(best_trust, 0):
                best_trust = r.section.trust

        merged_section = LocalSection(
            site_id=section.site_id,
            carrier_type=successful[0].section.carrier_type,
            refinements=merged_refs,
            trust=best_trust,
            provenance="parallel_meet composition",
        )

        return SolverResult(
            status=SolverStatus.REFINED,
            section=merged_section,
            explanation=f"meet of {len(successful)} pack results",
        )

    def _solve_parallel_join(
        self, site: SiteId, section: LocalSection, packs: List[TheoryPackBase]
    ) -> SolverResult:
        """Run all packs, take the join (union) of refinements."""
        results = [pack.solve_local(site, section) for pack in packs]

        successful = [r for r in results if r.is_success]
        if not successful:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no pack made progress",
            )

        merged_refs = dict(section.refinements)
        for r in successful:
            merged_refs = merge_refinements(merged_refs, r.section.refinements, "join")

        merged_section = LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=merged_refs,
            trust=section.trust,
            provenance="parallel_join composition",
        )

        return SolverResult(
            status=SolverStatus.REFINED,
            section=merged_section,
            explanation=f"join of {len(successful)} pack results",
        )

    def _solve_first_success(
        self, site: SiteId, section: LocalSection, packs: List[TheoryPackBase]
    ) -> SolverResult:
        """Use the first pack that returns a successful result."""
        for pack in packs:
            result = pack.solve_local(site, section)
            if result.is_success:
                return result
        return SolverResult(
            status=SolverStatus.UNKNOWN,
            section=section,
            explanation="no pack succeeded",
        )

    # ── Forward / backward ────────────────────────────────────────────────

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Forward refinement using the configured strategy."""
        packs = self._get_packs_for_kind(morphism.source.kind)
        if not packs:
            packs = self._get_packs_for_kind(morphism.target.kind)
        if not packs:
            return morphism.restrict(section)

        if self._strategy == CompositionStrategy.SEQUENTIAL:
            current = section
            for pack in packs:
                current = pack.forward_refine(current, morphism)
            return current
        else:
            return packs[0].forward_refine(section, morphism)

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Backward pullback using the configured strategy."""
        packs = self._get_packs_for_kind(morphism.target.kind)
        if not packs:
            packs = self._get_packs_for_kind(morphism.source.kind)
        if not packs:
            return LocalSection(
                site_id=morphism.source,
                carrier_type=section.carrier_type,
                refinements=dict(section.refinements),
                trust=section.trust,
                provenance=f"default pullback from {section.site_id}",
            )

        if self._strategy == CompositionStrategy.SEQUENTIAL:
            current = section
            for pack in reversed(packs):
                current = pack.backward_pullback(current, morphism)
            return current
        else:
            return packs[0].backward_pullback(section, morphism)

    # ── Viability & classification ────────────────────────────────────────

    def viability_predicate(self, error_site: SiteId) -> str:
        """Get viability predicate from the appropriate pack."""
        packs = self._get_packs_for_site(error_site)
        if not packs:
            return f"unknown viability for {error_site}"
        predicates = []
        for pack in packs:
            pred = pack.viability_predicate(error_site)
            if pred and pred != f"unknown viability for {error_site}":
                predicates.append(pred)
        if not predicates:
            return f"no viability predicate for {error_site}"
        return " AND ".join(predicates)

    def classify_proof_boundary(
        self, section: LocalSection
    ) -> BoundaryClassification:
        """Classify a section's proof boundary status."""
        packs = self._get_packs_for_site(section.site_id)
        if not packs:
            return BoundaryClassification.ASSUMED
        return packs[0].classify_proof_boundary(section)

    # ── Conflict detection ────────────────────────────────────────────────

    def _detect_conflicts(
        self,
        site: SiteId,
        results: List[SolverResult],
        packs: List[TheoryPackBase],
    ) -> List[CompositionConflict]:
        """Detect conflicting refinements across pack results."""
        conflicts: List[CompositionConflict] = []
        successful = [
            (pack, result)
            for pack, result in zip(packs, results)
            if result.is_success
        ]
        for i, (pack_a, res_a) in enumerate(successful):
            for pack_b, res_b in successful[i + 1:]:
                shared_keys = (
                    set(res_a.section.refinements.keys())
                    & set(res_b.section.refinements.keys())
                )
                for key in shared_keys:
                    val_a = res_a.section.refinements[key]
                    val_b = res_b.section.refinements[key]
                    if val_a != val_b:
                        conflict = CompositionConflict(
                            site_id=site,
                            pack_a=pack_a.pack_name,
                            pack_b=pack_b.pack_name,
                            key=key,
                            value_a=val_a,
                            value_b=val_b,
                            resolution="meet",
                        )
                        conflicts.append(conflict)
        return conflicts

    # ── Batch operations ──────────────────────────────────────────────────

    def solve_cover(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, SolverResult]:
        """Solve all sites in a cover."""
        results: Dict[SiteId, SolverResult] = {}
        for site_id in cover.sites:
            if site_id in sections:
                results[site_id] = self.solve_local(site_id, sections[site_id])
        return results

    def propagate_forward(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Forward-propagate refinements along all morphisms in a cover."""
        updated = dict(sections)
        for morphism in cover.morphisms:
            if morphism.source in updated:
                source_section = updated[morphism.source]
                refined = self.forward_refine(source_section, morphism)
                if morphism.target in updated:
                    existing = updated[morphism.target]
                    merged = merge_refinements(
                        existing.refinements, refined.refinements, "meet"
                    )
                    updated[morphism.target] = LocalSection(
                        site_id=morphism.target,
                        carrier_type=refined.carrier_type,
                        refinements=merged,
                        trust=existing.trust,
                        provenance="forward propagation",
                    )
                else:
                    updated[morphism.target] = refined
        return updated

    def propagate_backward(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Backward-propagate requirements along all morphisms in a cover."""
        updated = dict(sections)
        for morphism in reversed(cover.morphisms):
            if morphism.target in updated:
                target_section = updated[morphism.target]
                pulled = self.backward_pullback(target_section, morphism)
                if morphism.source in updated:
                    existing = updated[morphism.source]
                    merged = merge_refinements(
                        existing.refinements, pulled.refinements, "meet"
                    )
                    updated[morphism.source] = LocalSection(
                        site_id=morphism.source,
                        carrier_type=existing.carrier_type,
                        refinements=merged,
                        trust=existing.trust,
                        provenance="backward propagation",
                    )
                else:
                    updated[morphism.source] = pulled
        return updated

    def bidirectional_pass(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        max_iterations: int = 10,
    ) -> Tuple[Dict[SiteId, LocalSection], bool]:
        """Run forward and backward passes until convergence.

        Returns:
            Tuple of (refined sections, converged flag).
        """
        current = dict(sections)
        for _iteration in range(max_iterations):
            forward_result = self.propagate_forward(cover, current)
            backward_result = self.propagate_backward(cover, forward_result)
            if self._sections_equal(current, backward_result):
                return backward_result, True
            current = backward_result
        return current, False

    def _sections_equal(
        self,
        a: Dict[SiteId, LocalSection],
        b: Dict[SiteId, LocalSection],
    ) -> bool:
        """Check if two section dictionaries have equal refinements."""
        if set(a.keys()) != set(b.keys()):
            return False
        for site_id in a:
            if a[site_id].refinements != b[site_id].refinements:
                return False
            if a[site_id].carrier_type != b[site_id].carrier_type:
                return False
        return True

    def __repr__(self) -> str:
        names = ", ".join(p.pack_name for p in self._packs)
        return (
            f"PackComposer(strategy={self._strategy.name}, "
            f"packs=[{names}])"
        )
