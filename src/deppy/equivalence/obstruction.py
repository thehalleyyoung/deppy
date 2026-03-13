"""Equivalence-specific obstruction analysis.

When two programs are *not* equivalent, the obstruction analysis explains
*why* by classifying the failures into actionable categories and suggesting
potential repairs.

The obstructions live in H^1(U, Iso(Sem_f, Sem_g)):

    Non-trivial H^1 ⟹ local equivalences cannot be glued globally

The ObstructionClassifier categorises each obstruction by kind:
- **CARRIER_TYPE_MISMATCH**: τ_f and τ_g are structurally different types
- **PREDICATE_GAP**: φ_f ⟹ φ_g holds but φ_g ⟹ φ_f does not (or vice versa)
- **BOUNDARY_DISAGREEMENT**: input/output boundaries carry different constraints
- **GLUING_FAILURE**: local equivalences are inconsistent on overlaps
- **COCYCLE_FAILURE**: triple-overlap cocycle condition violated
- **STRUCTURAL_MISMATCH**: programs have different control-flow structure

The RepairSuggester then proposes concrete changes:
- Strengthen a predicate to close a gap
- Add a type coercion to resolve a carrier mismatch
- Restrict to a subdomain where equivalence holds
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    ObstructionData,
    RepairSuggestion,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonPred,
    DisjunctionPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
)
from deppy.types.witnesses import ProofTerm

from deppy.equivalence._protocols import (
    EquivalenceJudgment,
    EquivalenceObligation,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    RefinementEquivalencePred,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Obstruction classification
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ClassifiedObstruction:
    """An obstruction with classification, severity, and repair suggestions."""
    obstruction: EquivalenceObstruction
    category: str  # "type", "predicate", "boundary", "structural", "gluing"
    severity_score: float  # 0.0 (info) to 1.0 (fatal)
    repairs: List[EquivalenceRepairSuggestion] = field(default_factory=list)
    explanation: str = ""


@dataclass
class EquivalenceRepairSuggestion:
    """A concrete repair suggestion for an equivalence obstruction.

    Repairs are expressed in terms of the sheaf-theoretic machinery:
    - **strengthen_predicate**: add conjuncts to a refinement predicate
    - **weaken_predicate**: remove conjuncts
    - **add_coercion**: insert a type coercion at a site
    - **restrict_domain**: limit equivalence to a subdomain
    - **split_site**: decompose a site into finer sites
    """
    kind: str  # "strengthen", "weaken", "coerce", "restrict", "split"
    target_site: SiteId
    target_program: str  # "f" or "g"
    description: str
    predicate_delta: Optional[Predicate] = None  # what to add/remove
    confidence: float = 0.5  # 0.0 = wild guess, 1.0 = certain
    locality_score: float = 1.0  # how local is this fix


class ObstructionClassifier:
    """Classify equivalence obstructions into categories."""

    def classify(
        self,
        obstruction: EquivalenceObstruction,
        judgment: Optional[LocalEquivalenceJudgment] = None,
    ) -> ClassifiedObstruction:
        """Classify a single obstruction."""
        kind = obstruction.kind
        category = self._kind_to_category(kind)
        severity = self._compute_severity(kind, judgment)
        explanation = self._explain(obstruction, judgment)

        return ClassifiedObstruction(
            obstruction=obstruction,
            category=category,
            severity_score=severity,
            explanation=explanation,
        )

    def classify_all(
        self,
        obstructions: List[EquivalenceObstruction],
        judgments: Optional[List[LocalEquivalenceJudgment]] = None,
    ) -> List[ClassifiedObstruction]:
        """Classify all obstructions."""
        judgment_map: Dict[SiteId, LocalEquivalenceJudgment] = {}
        if judgments is not None:
            for j in judgments:
                judgment_map[j.site_id] = j

        classified: List[ClassifiedObstruction] = []
        for obs in obstructions:
            # Find the most relevant judgment
            relevant_j = None
            for site_id in obs.sites:
                if site_id in judgment_map:
                    relevant_j = judgment_map[site_id]
                    break

            classified.append(self.classify(obs, relevant_j))

        return classified

    def _kind_to_category(self, kind: EquivalenceObstructionKind) -> str:
        """Map obstruction kind to category."""
        mapping = {
            EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH: "type",
            EquivalenceObstructionKind.PREDICATE_GAP: "predicate",
            EquivalenceObstructionKind.BOUNDARY_DISAGREEMENT: "boundary",
            EquivalenceObstructionKind.GLUING_FAILURE: "gluing",
            EquivalenceObstructionKind.COCYCLE_FAILURE: "gluing",
            EquivalenceObstructionKind.STRUCTURAL_MISMATCH: "structural",
        }
        return mapping.get(kind, "unknown")

    def _compute_severity(
        self,
        kind: EquivalenceObstructionKind,
        judgment: Optional[LocalEquivalenceJudgment],
    ) -> float:
        """Compute severity score.

        Higher = more fundamental / harder to repair.
        """
        base_severity = {
            EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH: 0.9,
            EquivalenceObstructionKind.STRUCTURAL_MISMATCH: 0.85,
            EquivalenceObstructionKind.BOUNDARY_DISAGREEMENT: 0.7,
            EquivalenceObstructionKind.PREDICATE_GAP: 0.5,
            EquivalenceObstructionKind.GLUING_FAILURE: 0.6,
            EquivalenceObstructionKind.COCYCLE_FAILURE: 0.4,
        }.get(kind, 0.5)

        # Adjust based on judgment
        if judgment is not None:
            if judgment.forward_holds and not judgment.backward_holds:
                base_severity *= 0.7  # one direction holds — closer to repair
            elif not judgment.forward_holds and judgment.backward_holds:
                base_severity *= 0.7

        return min(base_severity, 1.0)

    def _explain(
        self,
        obstruction: EquivalenceObstruction,
        judgment: Optional[LocalEquivalenceJudgment],
    ) -> str:
        """Generate a human-readable explanation."""
        parts = [obstruction.explanation]

        if judgment is not None:
            if judgment.counterexample:
                parts.append(
                    f"Counterexample: {judgment.counterexample}"
                )
            if judgment.forward_holds is not None:
                parts.append(
                    f"Forward (φ_f ⟹ φ_g): {'holds' if judgment.forward_holds else 'fails'}"
                )
            if judgment.backward_holds is not None:
                parts.append(
                    f"Backward (φ_g ⟹ φ_f): {'holds' if judgment.backward_holds else 'fails'}"
                )

        return "; ".join(parts)


# ═══════════════════════════════════════════════════════════════════════════════
# Repair suggestion engine
# ═══════════════════════════════════════════════════════════════════════════════


class RepairSuggester:
    """Suggest repairs for equivalence obstructions.

    Given a classified obstruction, propose concrete changes to one or
    both programs that would make them equivalent.

    The suggestion strategy depends on the obstruction category:

    - **type**: Suggest type coercions or wrappers
    - **predicate**: Suggest predicate strengthening/weakening
    - **boundary**: Suggest boundary constraint alignment
    - **structural**: Suggest refactoring or domain restriction
    - **gluing**: Suggest site refinement or constraint weakening
    """

    def suggest(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation] = None,
    ) -> List[EquivalenceRepairSuggestion]:
        """Generate repair suggestions for a classified obstruction."""
        kind = classified.obstruction.kind
        sites = classified.obstruction.sites

        if kind == EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH:
            return self._suggest_type_repair(classified, obligation)
        elif kind == EquivalenceObstructionKind.PREDICATE_GAP:
            return self._suggest_predicate_repair(classified, obligation)
        elif kind == EquivalenceObstructionKind.BOUNDARY_DISAGREEMENT:
            return self._suggest_boundary_repair(classified, obligation)
        elif kind == EquivalenceObstructionKind.GLUING_FAILURE:
            return self._suggest_gluing_repair(classified, obligation)
        elif kind == EquivalenceObstructionKind.COCYCLE_FAILURE:
            return self._suggest_cocycle_repair(classified, obligation)
        elif kind == EquivalenceObstructionKind.STRUCTURAL_MISMATCH:
            return self._suggest_structural_repair(classified, obligation)
        else:
            return []

    def suggest_all(
        self,
        classified_list: List[ClassifiedObstruction],
        obligations: Optional[Dict[SiteId, EquivalenceObligation]] = None,
    ) -> List[EquivalenceRepairSuggestion]:
        """Generate all repair suggestions, deduplicated and ranked."""
        all_suggestions: List[EquivalenceRepairSuggestion] = []

        for classified in classified_list:
            obligation = None
            if obligations is not None:
                for site_id in classified.obstruction.sites:
                    if site_id in obligations:
                        obligation = obligations[site_id]
                        break

            suggestions = self.suggest(classified, obligation)
            all_suggestions.extend(suggestions)

        # Deduplicate by description
        seen: set = set()
        unique: List[EquivalenceRepairSuggestion] = []
        for s in all_suggestions:
            key = (s.kind, s.target_site.name, s.description)
            if key not in seen:
                seen.add(key)
                unique.append(s)

        # Sort by confidence (descending), then locality (descending)
        unique.sort(key=lambda s: (-s.confidence, -s.locality_score))

        return unique

    # ── Per-category repair strategies ────────────────────────────────────

    def _suggest_type_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for carrier type mismatches."""
        suggestions: List[EquivalenceRepairSuggestion] = []
        sites = classified.obstruction.sites

        if not sites:
            return suggestions

        site = sites[0]

        if obligation is not None:
            type_f = obligation.carrier_type_f
            type_g = obligation.carrier_type_g

            suggestions.append(EquivalenceRepairSuggestion(
                kind="coerce",
                target_site=site,
                target_program="g",
                description=(
                    f"Add type coercion from {type_g} to {type_f} "
                    f"at site {site.name}"
                ),
                confidence=0.6,
                locality_score=0.9,
            ))

            suggestions.append(EquivalenceRepairSuggestion(
                kind="restrict",
                target_site=site,
                target_program="both",
                description=(
                    f"Restrict domain to intersection of {type_f} and {type_g}"
                ),
                confidence=0.4,
                locality_score=0.7,
            ))

        return suggestions

    def _suggest_predicate_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for predicate gaps."""
        suggestions: List[EquivalenceRepairSuggestion] = []
        sites = classified.obstruction.sites

        if not sites:
            return suggestions

        site = sites[0]

        if obligation is not None:
            fwd = obligation.forward_predicate
            bwd = obligation.backward_predicate

            # If forward holds but not backward, strengthen g
            if fwd is not None and isinstance(fwd, ImplicationPred):
                suggestions.append(EquivalenceRepairSuggestion(
                    kind="strengthen",
                    target_site=site,
                    target_program="g",
                    description=(
                        f"Strengthen predicate in program g at {site.name} "
                        f"to imply the predicate of program f"
                    ),
                    predicate_delta=fwd.consequent,
                    confidence=0.5,
                    locality_score=0.95,
                ))

            if bwd is not None and isinstance(bwd, ImplicationPred):
                suggestions.append(EquivalenceRepairSuggestion(
                    kind="strengthen",
                    target_site=site,
                    target_program="f",
                    description=(
                        f"Strengthen predicate in program f at {site.name} "
                        f"to imply the predicate of program g"
                    ),
                    predicate_delta=bwd.consequent,
                    confidence=0.5,
                    locality_score=0.95,
                ))

        # Domain restriction
        suggestions.append(EquivalenceRepairSuggestion(
            kind="restrict",
            target_site=site,
            target_program="both",
            description=(
                f"Restrict equivalence to the subdomain where "
                f"both predicates agree at {site.name}"
            ),
            confidence=0.7,
            locality_score=0.8,
        ))

        return suggestions

    def _suggest_boundary_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for boundary disagreements."""
        sites = classified.obstruction.sites
        if not sites:
            return []

        site = sites[0]
        return [
            EquivalenceRepairSuggestion(
                kind="strengthen",
                target_site=site,
                target_program="both",
                description=(
                    f"Align boundary constraints at {site.name}: "
                    f"ensure input/output boundaries carry the same refinements"
                ),
                confidence=0.5,
                locality_score=0.85,
            ),
        ]

    def _suggest_gluing_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for gluing failures."""
        sites = classified.obstruction.sites
        suggestions: List[EquivalenceRepairSuggestion] = []

        if len(sites) >= 2:
            suggestions.append(EquivalenceRepairSuggestion(
                kind="split",
                target_site=sites[0],
                target_program="both",
                description=(
                    f"Refine cover to resolve overlap conflict between "
                    f"{sites[0].name} and {sites[1].name}"
                ),
                confidence=0.4,
                locality_score=0.6,
            ))

            suggestions.append(EquivalenceRepairSuggestion(
                kind="weaken",
                target_site=sites[0],
                target_program="both",
                description=(
                    f"Weaken local equivalence at {sites[0].name} or "
                    f"{sites[1].name} to ensure overlap consistency"
                ),
                confidence=0.3,
                locality_score=0.7,
            ))

        return suggestions

    def _suggest_cocycle_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for cocycle failures."""
        sites = classified.obstruction.sites
        if not sites:
            return []

        return [
            EquivalenceRepairSuggestion(
                kind="split",
                target_site=sites[0],
                target_program="both",
                description=(
                    f"Add missing overlap sites to satisfy the cocycle condition "
                    f"on {', '.join(s.name for s in sites)}"
                ),
                confidence=0.3,
                locality_score=0.5,
            ),
        ]

    def _suggest_structural_repair(
        self,
        classified: ClassifiedObstruction,
        obligation: Optional[EquivalenceObligation],
    ) -> List[EquivalenceRepairSuggestion]:
        """Suggest repairs for structural mismatches."""
        sites = classified.obstruction.sites
        if not sites:
            return []

        site = sites[0]
        return [
            EquivalenceRepairSuggestion(
                kind="restrict",
                target_site=site,
                target_program="both",
                description=(
                    f"Programs have different control-flow structure at {site.name}; "
                    f"consider restricting to a common subdomain or refactoring"
                ),
                confidence=0.2,
                locality_score=0.3,
            ),
        ]


# ═══════════════════════════════════════════════════════════════════════════════
# Obstruction summary builder
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ObstructionSummary:
    """Summary of all obstructions in an equivalence judgment."""
    total_obstructions: int
    by_category: Dict[str, int]
    by_severity: Dict[str, int]  # "error", "warning", "info"
    top_repairs: List[EquivalenceRepairSuggestion]
    cohomology_trivial: bool
    explanation: str


def summarise_obstructions(
    judgment: EquivalenceJudgment,
) -> ObstructionSummary:
    """Build a summary of all obstructions in a judgment."""
    classifier = ObstructionClassifier()
    suggester = RepairSuggester()

    classified = classifier.classify_all(
        judgment.obstructions,
        judgment.local_judgments,
    )

    # Gather repair suggestions
    obligation_map: Dict[SiteId, EquivalenceObligation] = {}
    for j in judgment.local_judgments:
        if j.obligation is not None:
            obligation_map[j.site_id] = j.obligation

    for c in classified:
        c.repairs = suggester.suggest(c, obligation_map.get(
            c.obstruction.sites[0] if c.obstruction.sites else None
        ))

    # Aggregate
    by_category: Dict[str, int] = {}
    by_severity: Dict[str, int] = {"error": 0, "warning": 0, "info": 0}

    for c in classified:
        by_category[c.category] = by_category.get(c.category, 0) + 1
        sev = c.obstruction.severity
        if sev in by_severity:
            by_severity[sev] += 1
        else:
            by_severity[sev] = 1

    all_repairs = suggester.suggest_all(classified, obligation_map)
    top_repairs = all_repairs[:5]

    h1_trivial = (
        judgment.cohomology_class.is_trivial
        if judgment.cohomology_class is not None
        else True
    )

    # Build explanation
    total = len(judgment.obstructions)
    if total == 0:
        explanation = "No obstructions found — programs are equivalent."
    else:
        parts = [f"{total} obstruction(s) found:"]
        for cat, count in sorted(by_category.items()):
            parts.append(f"  {cat}: {count}")
        if not h1_trivial:
            parts.append("H¹ is non-trivial: local equivalences cannot glue globally.")
        explanation = "\n".join(parts)

    return ObstructionSummary(
        total_obstructions=total,
        by_category=by_category,
        by_severity=by_severity,
        top_repairs=top_repairs,
        cohomology_trivial=h1_trivial,
        explanation=explanation,
    )
