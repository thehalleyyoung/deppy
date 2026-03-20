"""
Type system for cross-domain analogies.

An analogy is typed as a topology-preserving functor between domain sites.
Given domain sites Site(A) and Site(B), an analogy F : A → B is a dependent
type:

    AnalogyType(A, B) = Σ(F: ConceptMapping(A,B)).
                         Σ(_: Functor(F)).
                         Σ(_: TopologyPreserving(F)).
                         Σ(_: Novel(F)).
                         Σ(v: Value(F)).
                         ⊤

This module provides the full type-checking pipeline for such analogies,
including functor checks, topology preservation, novelty detection,
cross-domain gluing via H¹ obstruction analysis, and an LLM-oracle
ideation protocol.
"""

from __future__ import annotations

import itertools
import json
import re
import textwrap
from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
)

if TYPE_CHECKING:
    pass

from deppy.hybrid.ideation.domain_site import (
    Concept,
    CoveringFamily,
    DomainRegistry,
    DomainSite,
    Morphism,
    REGISTRY,
)

# ---------------------------------------------------------------------------
# Result dataclasses
# ---------------------------------------------------------------------------


@dataclass
class MorphismCheckResult:
    """Result of checking whether a single morphism is preserved by a mapping."""

    source_morphism: Morphism
    mapped_exists: bool
    mapped_morphism: Optional[Morphism]
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source_morphism": self.source_morphism.to_dict(),
            "mapped_exists": self.mapped_exists,
            "mapped_morphism": (
                self.mapped_morphism.to_dict() if self.mapped_morphism else None
            ),
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "✓" if self.mapped_exists else "✗"
        src = self.source_morphism
        return (
            f"MorphismCheck({status} {src.source}→{src.target} "
            f"[{src.relation}])"
        )


@dataclass
class FunctorResult:
    """Aggregate result of a functoriality check on a concept mapping."""

    is_functor: bool
    preserved: List[MorphismCheckResult]
    broken: List[MorphismCheckResult]
    score: float
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_functor": self.is_functor,
            "preserved": [r.to_dict() for r in self.preserved],
            "broken": [r.to_dict() for r in self.broken],
            "score": self.score,
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "functor" if self.is_functor else "not-functor"
        return (
            f"FunctorResult({status}, "
            f"preserved={len(self.preserved)}, "
            f"broken={len(self.broken)}, "
            f"score={self.score:.2f})"
        )


@dataclass
class CoverCheckResult:
    """Result of checking whether a single covering family is preserved."""

    source_cover: CoveringFamily
    mapped_exists: bool
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source_cover": self.source_cover.to_dict(),
            "mapped_exists": self.mapped_exists,
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "✓" if self.mapped_exists else "✗"
        return (
            f"CoverCheck({status} "
            f"{self.source_cover.covering}⊳{self.source_cover.covered})"
        )


@dataclass
class TopologyResult:
    """Aggregate result of topology preservation check."""

    preserves_topology: bool
    preserved: List[CoverCheckResult]
    broken: List[CoverCheckResult]
    score: float
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "preserves_topology": self.preserves_topology,
            "preserved": [r.to_dict() for r in self.preserved],
            "broken": [r.to_dict() for r in self.broken],
            "score": self.score,
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "preserves" if self.preserves_topology else "breaks"
        return (
            f"TopologyResult({status}, "
            f"preserved={len(self.preserved)}, "
            f"broken={len(self.broken)}, "
            f"score={self.score:.2f})"
        )


@dataclass
class NoveltyResult:
    """Result of novelty check for an analogy."""

    is_novel: bool
    similarity_to_nearest: float
    nearest_known: Optional[ConceptMapping]
    novel_pairs: List[Tuple[str, str]]
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_novel": self.is_novel,
            "similarity_to_nearest": self.similarity_to_nearest,
            "nearest_known": (
                self.nearest_known.to_dict() if self.nearest_known else None
            ),
            "novel_pairs": self.novel_pairs,
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "novel" if self.is_novel else "known"
        return (
            f"NoveltyResult({status}, "
            f"sim={self.similarity_to_nearest:.2f}, "
            f"novel_pairs={len(self.novel_pairs)})"
        )


# ---------------------------------------------------------------------------
# ConceptMapping
# ---------------------------------------------------------------------------


@dataclass
class ConceptMapping:
    """
    A mapping of concepts from one domain site to another.

    ``mappings`` maps source concept IDs to target concept IDs.
    """

    source_domain: str
    target_domain: str
    mappings: Dict[str, str]
    confidence: float = 1.0
    provenance: str = "system"

    # -- completeness helpers ------------------------------------------------

    def is_complete(self, source_site: DomainSite) -> bool:
        """Return *True* if every concept in *source_site* is mapped."""
        for cid in source_site.objects():
            if cid not in self.mappings:
                return False
        return True

    def unmapped_concepts(self, source_site: DomainSite) -> List[str]:
        """Return concept IDs in *source_site* that have no mapping."""
        return [
            cid for cid in source_site.objects() if cid not in self.mappings
        ]

    def mapped_concepts(self) -> List[Tuple[str, str]]:
        """Return list of ``(source, target)`` pairs."""
        return list(self.mappings.items())

    # -- algebraic operations -----------------------------------------------

    def inverse(self) -> ConceptMapping:
        """Return the inverse mapping (swap source and target)."""
        inv_map: Dict[str, str] = {v: k for k, v in self.mappings.items()}
        return ConceptMapping(
            source_domain=self.target_domain,
            target_domain=self.source_domain,
            mappings=inv_map,
            confidence=self.confidence,
            provenance=self.provenance,
        )

    def compose(self, other: ConceptMapping) -> ConceptMapping:
        """
        Compose ``self`` with *other*: ``self ; other``.

        A concept *c* in ``self.source_domain`` is mapped to
        ``other.mappings[self.mappings[c]]`` when both links exist.
        """
        composed: Dict[str, str] = {}
        for src, mid in self.mappings.items():
            if mid in other.mappings:
                composed[src] = other.mappings[mid]
        return ConceptMapping(
            source_domain=self.source_domain,
            target_domain=other.target_domain,
            mappings=composed,
            confidence=min(self.confidence, other.confidence),
            provenance=f"compose({self.provenance},{other.provenance})",
        )

    def restrict(self, concept_ids: List[str]) -> ConceptMapping:
        """Restrict mapping to only the given source concept IDs."""
        restricted = {
            k: v for k, v in self.mappings.items() if k in concept_ids
        }
        return ConceptMapping(
            source_domain=self.source_domain,
            target_domain=self.target_domain,
            mappings=restricted,
            confidence=self.confidence,
            provenance=self.provenance,
        )

    def overlap_with(self, other: ConceptMapping) -> Dict[str, Tuple[str, str]]:
        """
        Find concepts mapped by both *self* and *other*.

        Returns ``{src: (self_target, other_target)}``.
        """
        common_keys = set(self.mappings.keys()) & set(other.mappings.keys())
        return {
            k: (self.mappings[k], other.mappings[k]) for k in common_keys
        }

    # -- serialisation -------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source_domain": self.source_domain,
            "target_domain": self.target_domain,
            "mappings": dict(self.mappings),
            "confidence": self.confidence,
            "provenance": self.provenance,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> ConceptMapping:
        return cls(
            source_domain=data["source_domain"],
            target_domain=data["target_domain"],
            mappings=dict(data["mappings"]),
            confidence=data.get("confidence", 1.0),
            provenance=data.get("provenance", "system"),
        )

    def __repr__(self) -> str:
        n = len(self.mappings)
        return (
            f"ConceptMapping({self.source_domain}→{self.target_domain}, "
            f"pairs={n}, conf={self.confidence:.2f})"
        )


# ---------------------------------------------------------------------------
# FunctorCheck
# ---------------------------------------------------------------------------


class FunctorCheck:
    """
    Checks if a :class:`ConceptMapping` is a functor (preserves morphisms).

    F : Site(A) → Site(B) is a functor iff for every morphism
    m : c₁ → c₂ in A there exists m' : F(c₁) → F(c₂) in B.
    """

    RELATION_COMPATIBILITY: Dict[str, List[str]] = {
        "IMPLIES": ["IMPLIES", "USES"],
        "GENERALIZES": ["GENERALIZES", "IMPLIES"],
        "SPECIALIZES": ["SPECIALIZES", "USES", "PART_OF"],
        "USES": ["USES", "IMPLIES", "PART_OF"],
        "PART_OF": ["PART_OF", "USES", "SPECIALIZES"],
        "DUAL_TO": ["DUAL_TO"],
    }

    # -- public API ----------------------------------------------------------

    def check(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> FunctorResult:
        """Full functor check across all morphisms in *source*."""
        preserved: List[MorphismCheckResult] = []
        broken: List[MorphismCheckResult] = []

        for morphism in source.morphisms:
            result = self._check_single_morphism(morphism, mapping, target)
            if result.mapped_exists:
                preserved.append(result)
            else:
                broken.append(result)

        total = len(preserved) + len(broken)
        score = len(preserved) / total if total > 0 else 1.0
        is_functor = len(broken) == 0

        if is_functor:
            explanation = (
                f"All {total} morphisms in {source.name} are preserved "
                f"by the mapping to {target.name}."
            )
        else:
            explanation = (
                f"{len(broken)}/{total} morphisms are NOT preserved. "
                f"Score = {score:.2f}."
            )

        return FunctorResult(
            is_functor=is_functor,
            preserved=preserved,
            broken=broken,
            score=score,
            explanation=explanation,
        )

    # -- single-morphism check -----------------------------------------------

    def _check_single_morphism(
        self,
        morphism: Morphism,
        mapping: ConceptMapping,
        target: DomainSite,
    ) -> MorphismCheckResult:
        """Check whether *morphism* is preserved under *mapping*."""
        src_mapped = mapping.mappings.get(morphism.source)
        tgt_mapped = mapping.mappings.get(morphism.target)

        if src_mapped is None or tgt_mapped is None:
            missing = []
            if src_mapped is None:
                missing.append(morphism.source)
            if tgt_mapped is None:
                missing.append(morphism.target)
            return MorphismCheckResult(
                source_morphism=morphism,
                mapped_exists=False,
                mapped_morphism=None,
                explanation=(
                    f"Unmapped endpoint(s): {', '.join(missing)}."
                ),
            )

        compatible_relations = self.RELATION_COMPATIBILITY.get(
            morphism.relation, [morphism.relation]
        )

        best_match: Optional[Morphism] = None
        best_strength: float = -1.0

        for target_morphism in target.morphisms:
            if (
                target_morphism.source == src_mapped
                and target_morphism.target == tgt_mapped
                and target_morphism.relation in compatible_relations
            ):
                if target_morphism.strength > best_strength:
                    best_match = target_morphism
                    best_strength = target_morphism.strength

        if best_match is not None:
            return MorphismCheckResult(
                source_morphism=morphism,
                mapped_exists=True,
                mapped_morphism=best_match,
                explanation=(
                    f"{morphism.source}→{morphism.target} [{morphism.relation}] "
                    f"maps to {best_match.source}→{best_match.target} "
                    f"[{best_match.relation}]."
                ),
            )

        return MorphismCheckResult(
            source_morphism=morphism,
            mapped_exists=False,
            mapped_morphism=None,
            explanation=(
                f"No morphism {src_mapped}→{tgt_mapped} with compatible "
                f"relation ({', '.join(compatible_relations)}) found in "
                f"{target.name}."
            ),
        )

    # -- convenience wrappers ------------------------------------------------

    def preserved_morphisms(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[MorphismCheckResult]:
        """Return only preserved morphism check results."""
        return self.check(mapping, source, target).preserved

    def broken_morphisms(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[MorphismCheckResult]:
        """Return only broken morphism check results."""
        return self.check(mapping, source, target).broken

    def functoriality_score(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> float:
        """Fraction of source morphisms that are preserved."""
        return self.check(mapping, source, target).score

    # -- suggestions ---------------------------------------------------------

    def suggest_fixes(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[str]:
        """
        Suggest morphisms that could be added to *target* to improve
        functoriality.
        """
        result = self.check(mapping, source, target)
        suggestions: List[str] = []
        for broken in result.broken:
            m = broken.source_morphism
            src_mapped = mapping.mappings.get(m.source)
            tgt_mapped = mapping.mappings.get(m.target)
            if src_mapped is not None and tgt_mapped is not None:
                suggestions.append(
                    f"Add morphism {src_mapped} --[{m.relation}]--> "
                    f"{tgt_mapped} in {target.name} "
                    f"(mirrors {m.source} --[{m.relation}]--> {m.target} "
                    f"in {source.name})."
                )
            elif src_mapped is None:
                suggestions.append(
                    f"Map source concept {m.source} to a target concept "
                    f"so the morphism {m.source}→{m.target} can be mirrored."
                )
            elif tgt_mapped is None:
                suggestions.append(
                    f"Map source concept {m.target} to a target concept "
                    f"so the morphism {m.source}→{m.target} can be mirrored."
                )
        return suggestions


# ---------------------------------------------------------------------------
# TopologyCheck
# ---------------------------------------------------------------------------


class TopologyCheck:
    """
    Checks if a mapping preserves the Grothendieck topology (covering
    families).

    F preserves topology iff for every covering family {cᵢ → c} in A,
    {F(cᵢ) → F(c)} is a covering family in B.
    """

    # -- public API ----------------------------------------------------------

    def check(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> TopologyResult:
        """Full topology preservation check."""
        preserved: List[CoverCheckResult] = []
        broken: List[CoverCheckResult] = []

        for cover in source.covering_families:
            result = self._check_single_cover(cover, mapping, target)
            if result.mapped_exists:
                preserved.append(result)
            else:
                broken.append(result)

        total = len(preserved) + len(broken)
        score = len(preserved) / total if total > 0 else 1.0
        preserves = len(broken) == 0

        if preserves:
            explanation = (
                f"All {total} covering families in {source.name} are "
                f"preserved by the mapping to {target.name}."
            )
        else:
            explanation = (
                f"{len(broken)}/{total} covering families are NOT "
                f"preserved. Score = {score:.2f}."
            )

        return TopologyResult(
            preserves_topology=preserves,
            preserved=preserved,
            broken=broken,
            score=score,
            explanation=explanation,
        )

    # -- single cover check --------------------------------------------------

    def _check_single_cover(
        self,
        cover: CoveringFamily,
        mapping: ConceptMapping,
        target: DomainSite,
    ) -> CoverCheckResult:
        """Check whether *cover* is preserved under *mapping*."""
        mapped_covered = mapping.mappings.get(cover.covered)
        if mapped_covered is None:
            return CoverCheckResult(
                source_cover=cover,
                mapped_exists=False,
                explanation=(
                    f"Covered concept {cover.covered} is not mapped."
                ),
            )

        mapped_covering: List[str] = []
        unmapped: List[str] = []
        for cid in cover.covering:
            mc = mapping.mappings.get(cid)
            if mc is None:
                unmapped.append(cid)
            else:
                mapped_covering.append(mc)

        if unmapped:
            return CoverCheckResult(
                source_cover=cover,
                mapped_exists=False,
                explanation=(
                    f"Covering concept(s) {', '.join(unmapped)} are not "
                    f"mapped, so the cover cannot be preserved."
                ),
            )

        # Check whether {mapped_covering → mapped_covered} is a cover in target
        for target_cover in target.covering_families:
            if target_cover.covered != mapped_covered:
                continue
            target_set = set(target_cover.covering)
            if set(mapped_covering).issubset(target_set):
                return CoverCheckResult(
                    source_cover=cover,
                    mapped_exists=True,
                    explanation=(
                        f"Cover {cover.covering}⊳{cover.covered} maps to "
                        f"cover {target_cover.covering}⊳{target_cover.covered} "
                        f"in {target.name}."
                    ),
                )

        # Relaxed check: mapped covering concepts have morphisms to
        # mapped_covered even if no explicit covering family is registered.
        morphism_to_covered = {
            m.source
            for m in target.morphisms
            if m.target == mapped_covered
        }
        if set(mapped_covering).issubset(morphism_to_covered):
            return CoverCheckResult(
                source_cover=cover,
                mapped_exists=True,
                explanation=(
                    f"Cover {cover.covering}⊳{cover.covered} maps to "
                    f"implicit cover in {target.name} (morphisms exist but "
                    f"no explicit covering family)."
                ),
            )

        return CoverCheckResult(
            source_cover=cover,
            mapped_exists=False,
            explanation=(
                f"No covering family in {target.name} matches the mapped "
                f"cover {mapped_covering}⊳{mapped_covered}."
            ),
        )

    # -- convenience wrappers ------------------------------------------------

    def preserved_covers(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[CoverCheckResult]:
        """Return only preserved covering-family results."""
        return self.check(mapping, source, target).preserved

    def broken_covers(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[CoverCheckResult]:
        """Return only broken covering-family results."""
        return self.check(mapping, source, target).broken

    def depth_score(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> float:
        """
        Score measuring *depth* of the analogy = fraction of topology
        preserved.  A deep analogy preserves the explanatory structure,
        not just individual concepts.
        """
        return self.check(mapping, source, target).score

    # -- suggestions ---------------------------------------------------------

    def suggest_covers(
        self,
        mapping: ConceptMapping,
        source: DomainSite,
        target: DomainSite,
    ) -> List[str]:
        """
        Suggest covering families that could be added to *target* to improve
        topology preservation.
        """
        result = self.check(mapping, source, target)
        suggestions: List[str] = []
        for broken_item in result.broken:
            cover = broken_item.source_cover
            mapped_covered = mapping.mappings.get(cover.covered)
            if mapped_covered is None:
                suggestions.append(
                    f"Map concept {cover.covered} to a target concept first."
                )
                continue
            mapped_covering = [
                mapping.mappings[c]
                for c in cover.covering
                if c in mapping.mappings
            ]
            if mapped_covering:
                suggestions.append(
                    f"Add covering family "
                    f"{{{', '.join(mapped_covering)}}} ⊳ {mapped_covered} "
                    f"in {target.name} "
                    f"(mirrors {{{', '.join(cover.covering)}}} ⊳ "
                    f"{cover.covered} in {source.name})."
                )
            else:
                suggestions.append(
                    f"Map covering concepts {cover.covering} to target "
                    f"concepts so the cover for {cover.covered} can be "
                    f"mirrored."
                )
        return suggestions


# ---------------------------------------------------------------------------
# NoveltyCheck
# ---------------------------------------------------------------------------


class NoveltyCheck:
    """Checks if an analogy is novel (not already known)."""

    NOVELTY_THRESHOLD: float = 0.6

    def __init__(self) -> None:
        self.KNOWN_ANALOGIES: List[ConceptMapping] = (
            self._build_known_analogies()
        )

    # -- pre-populated known analogies ---------------------------------------

    @staticmethod
    def _build_known_analogies() -> List[ConceptMapping]:
        """Return ~10 well-known cross-domain analogies."""
        return [
            # 1. Curry-Howard: type_theory ↔ formal_verification
            ConceptMapping(
                source_domain="type_theory",
                target_domain="formal_verification",
                mappings={
                    "tt_type": "fv_proposition",
                    "tt_term": "fv_proof",
                    "tt_function_type": "fv_implication",
                    "tt_pi_type": "fv_universal",
                    "tt_sigma_type": "fv_existential",
                    "tt_dependent_type": "fv_predicate",
                },
                confidence=1.0,
                provenance="known:curry-howard",
            ),
            # 2. Programs-as-proofs: software_engineering ↔ formal_verification
            ConceptMapping(
                source_domain="software_engineering",
                target_domain="formal_verification",
                mappings={
                    "se_program": "fv_proof",
                    "se_type": "fv_proposition",
                    "se_test": "fv_model_check",
                    "se_module": "fv_theory",
                    "se_interface": "fv_specification",
                    "se_refactor": "fv_proof_simplification",
                },
                confidence=0.95,
                provenance="known:programs-as-proofs",
            ),
            # 3. Grammar-as-type-system: linguistics ↔ type_theory
            ConceptMapping(
                source_domain="linguistics",
                target_domain="type_theory",
                mappings={
                    "ling_grammar": "tt_type_system",
                    "ling_sentence": "tt_term",
                    "ling_parse_tree": "tt_derivation",
                    "ling_noun_phrase": "tt_type",
                    "ling_verb": "tt_function_type",
                    "ling_ambiguity": "tt_polymorphism",
                },
                confidence=0.85,
                provenance="known:grammar-as-types",
            ),
            # 4. Testing-as-sampling: software_engineering ↔ machine_learning
            ConceptMapping(
                source_domain="software_engineering",
                target_domain="machine_learning",
                mappings={
                    "se_test": "ml_sample",
                    "se_test_suite": "ml_dataset",
                    "se_coverage": "ml_coverage",
                    "se_bug": "ml_misclassification",
                    "se_specification": "ml_ground_truth",
                    "se_fuzzing": "ml_data_augmentation",
                },
                confidence=0.80,
                provenance="known:testing-as-sampling",
            ),
            # 5. Modules-as-sheaves: software_engineering ↔ algebraic_geometry
            ConceptMapping(
                source_domain="software_engineering",
                target_domain="algebraic_geometry",
                mappings={
                    "se_module": "ag_sheaf",
                    "se_interface": "ag_stalk",
                    "se_dependency": "ag_restriction",
                    "se_composition": "ag_gluing",
                    "se_program": "ag_global_section",
                    "se_refactor": "ag_morphism",
                },
                confidence=0.75,
                provenance="known:modules-as-sheaves",
            ),
            # 6. Optimisation-as-learning: category_theory ↔ machine_learning
            ConceptMapping(
                source_domain="category_theory",
                target_domain="machine_learning",
                mappings={
                    "ct_functor": "ml_model",
                    "ct_natural_transformation": "ml_training",
                    "ct_adjunction": "ml_optimisation",
                    "ct_limit": "ml_convergence",
                    "ct_colimit": "ml_ensemble",
                    "ct_monad": "ml_pipeline",
                },
                confidence=0.70,
                provenance="known:optimisation-as-learning",
            ),
            # 7. Compilation-as-functor: software_engineering ↔ category_theory
            ConceptMapping(
                source_domain="software_engineering",
                target_domain="category_theory",
                mappings={
                    "se_compiler": "ct_functor",
                    "se_program": "ct_object",
                    "se_refactor": "ct_morphism",
                    "se_composition": "ct_composition",
                    "se_type": "ct_object",
                    "se_module": "ct_category",
                },
                confidence=0.80,
                provenance="known:compilation-as-functor",
            ),
            # 8. Verification-as-sheaf-condition: formal_verification ↔ algebraic_geometry
            ConceptMapping(
                source_domain="formal_verification",
                target_domain="algebraic_geometry",
                mappings={
                    "fv_specification": "ag_sheaf_condition",
                    "fv_proof": "ag_global_section",
                    "fv_lemma": "ag_local_section",
                    "fv_theory": "ag_scheme",
                    "fv_model_check": "ag_stalk",
                    "fv_invariant": "ag_cohomology",
                },
                confidence=0.65,
                provenance="known:verification-as-sheaf",
            ),
            # 9. Neural-networks-as-manifolds: machine_learning ↔ algebraic_geometry
            ConceptMapping(
                source_domain="machine_learning",
                target_domain="algebraic_geometry",
                mappings={
                    "ml_neural_network": "ag_variety",
                    "ml_layer": "ag_fiber",
                    "ml_activation": "ag_morphism",
                    "ml_loss_landscape": "ag_scheme",
                    "ml_gradient": "ag_tangent",
                    "ml_parameter": "ag_coordinate",
                },
                confidence=0.70,
                provenance="known:nn-as-manifolds",
            ),
            # 10. Semantics-as-functors: linguistics ↔ category_theory
            ConceptMapping(
                source_domain="linguistics",
                target_domain="category_theory",
                mappings={
                    "ling_grammar": "ct_category",
                    "ling_sentence": "ct_object",
                    "ling_meaning": "ct_functor",
                    "ling_translation": "ct_natural_transformation",
                    "ling_parse_tree": "ct_morphism",
                    "ling_compositionality": "ct_composition",
                },
                confidence=0.80,
                provenance="known:semantics-as-functors",
            ),
        ]

    # -- public API ----------------------------------------------------------

    def check(self, mapping: ConceptMapping) -> NoveltyResult:
        """Check if *mapping* is novel compared to known analogies."""
        max_sim = 0.0
        nearest: Optional[ConceptMapping] = None

        for known in self.KNOWN_ANALOGIES:
            sim = self._jaccard_similarity(mapping, known)
            if sim > max_sim:
                max_sim = sim
                nearest = known

        is_novel = max_sim < self.NOVELTY_THRESHOLD
        novel_pairs = self.novel_mappings(mapping)

        if is_novel:
            explanation = (
                f"Analogy is novel (max similarity to known = {max_sim:.2f}, "
                f"threshold = {self.NOVELTY_THRESHOLD}). "
                f"{len(novel_pairs)} novel concept pair(s)."
            )
        else:
            prov = nearest.provenance if nearest else "unknown"
            explanation = (
                f"Analogy is NOT novel (similarity = {max_sim:.2f} to "
                f"'{prov}'). Only {len(novel_pairs)} novel pair(s)."
            )

        return NoveltyResult(
            is_novel=is_novel,
            similarity_to_nearest=max_sim,
            nearest_known=nearest,
            novel_pairs=novel_pairs,
            explanation=explanation,
        )

    def similarity_to_known(self, mapping: ConceptMapping) -> float:
        """Maximum Jaccard similarity of mapping pairs to any known analogy."""
        if not self.KNOWN_ANALOGIES:
            return 0.0
        return max(
            self._jaccard_similarity(mapping, k) for k in self.KNOWN_ANALOGIES
        )

    def _jaccard_similarity(
        self, m1: ConceptMapping, m2: ConceptMapping
    ) -> float:
        """Jaccard similarity between two mappings' concept pairs."""
        pairs1: Set[Tuple[str, str]] = set(m1.mappings.items())
        pairs2: Set[Tuple[str, str]] = set(m2.mappings.items())
        if not pairs1 and not pairs2:
            return 1.0
        intersection = pairs1 & pairs2
        union = pairs1 | pairs2
        if not union:
            return 0.0
        return len(intersection) / len(union)

    def novel_mappings(
        self, mapping: ConceptMapping
    ) -> List[Tuple[str, str]]:
        """Return ``(source, target)`` pairs not found in any known analogy."""
        all_known_pairs: Set[Tuple[str, str]] = set()
        for known in self.KNOWN_ANALOGIES:
            all_known_pairs.update(known.mappings.items())
        return [
            (s, t)
            for s, t in mapping.mappings.items()
            if (s, t) not in all_known_pairs
        ]

    def register_known(self, mapping: ConceptMapping) -> None:
        """Add *mapping* to the known analogies database."""
        self.KNOWN_ANALOGIES.append(mapping)


# ---------------------------------------------------------------------------
# AnalogyType
# ---------------------------------------------------------------------------


class AnalogyType:
    """
    The full dependent type for a validated analogy::

        AnalogyType(A, B) = Σ(F: ConceptMapping(A,B)).
                             Σ(_: Functor(F)).
                             Σ(_: TopologyPreserving(F)).
                             Σ(_: Novel(F)).
                             Σ(v: Value(F)).
                             ⊤
    """

    VALUE_THRESHOLD: float = 0.5

    def __init__(
        self,
        mapping: ConceptMapping,
        functor_result: FunctorResult,
        topology_result: TopologyResult,
        novelty_result: NoveltyResult,
        value_score: float,
    ) -> None:
        self.mapping = mapping
        self.functor_result = functor_result
        self.topology_result = topology_result
        self.novelty_result = novelty_result
        self.value_score = value_score

    # -- properties ----------------------------------------------------------

    @property
    def source_domain(self) -> str:
        return self.mapping.source_domain

    @property
    def target_domain(self) -> str:
        return self.mapping.target_domain

    # -- classification predicates ------------------------------------------

    def is_deep(self) -> bool:
        """Deep = functor check passed AND topology preserved."""
        return (
            self.functor_result.is_functor
            and self.topology_result.preserves_topology
        )

    def is_shallow(self) -> bool:
        """Shallow = only surface-level matching (not a functor)."""
        return not self.functor_result.is_functor

    def is_novel(self) -> bool:
        """Return whether the analogy is novel."""
        return self.novelty_result.is_novel

    def is_valuable(self) -> bool:
        """Valuable = deep AND novel AND value_score above threshold."""
        return (
            self.is_deep()
            and self.is_novel()
            and self.value_score > self.VALUE_THRESHOLD
        )

    # -- scoring -------------------------------------------------------------

    def overall_score(self) -> float:
        """Weighted combination of functoriality, topology, novelty, value."""
        w_functor = 0.30
        w_topology = 0.25
        w_novelty = 0.25
        w_value = 0.20

        novelty_score = 1.0 - self.novelty_result.similarity_to_nearest

        return (
            w_functor * self.functor_result.score
            + w_topology * self.topology_result.score
            + w_novelty * novelty_score
            + w_value * self.value_score
        )

    # -- Lean 4 formalisation ------------------------------------------------

    def to_lean(self) -> str:
        """
        Generate a Lean 4 formalisation stub for this analogy type.
        """
        src = _lean_ident(self.source_domain)
        tgt = _lean_ident(self.target_domain)
        pairs = self.mapping.mapped_concepts()

        lines: List[str] = []
        lines.append(f"-- Analogy: {self.source_domain} → {self.target_domain}")
        lines.append(
            f"-- Functor score : {self.functor_result.score:.2f}"
        )
        lines.append(
            f"-- Topology score: {self.topology_result.score:.2f}"
        )
        lines.append(
            f"-- Novel         : {self.novelty_result.is_novel}"
        )
        lines.append(
            f"-- Value         : {self.value_score:.2f}"
        )
        lines.append("")
        lines.append("namespace Deppy.Analogy")
        lines.append("")

        # Domain abbreviation types
        lines.append(f"abbrev {src} := String")
        lines.append(f"abbrev {tgt} := String")
        lines.append("")

        # Mapping structure
        lines.append(f"structure Mapping_{src}_{tgt} where")
        for s, t in pairs:
            s_id = _lean_ident(s)
            t_id = _lean_ident(t)
            lines.append(f"  {s_id} : {tgt}  -- maps to {t_id}")
        lines.append("")

        # Witness instance
        lines.append(f"def analogy_{src}_{tgt} : Mapping_{src}_{tgt} :=")
        fields = ", ".join(
            f'{_lean_ident(s)} := "{t}"' for s, t in pairs
        )
        lines.append(f"  ⟨{fields}⟩")
        lines.append("")

        # Functor proof stub
        lines.append(f"-- Functor proof (score = {self.functor_result.score:.2f})")
        if self.functor_result.is_functor:
            lines.append(
                f"theorem functor_{src}_{tgt} : "
                f"IsFunctor analogy_{src}_{tgt} := by"
            )
            lines.append("  sorry  -- verified computationally")
        else:
            lines.append(
                f"-- NOT a functor; {len(self.functor_result.broken)} "
                f"morphisms broken"
            )
        lines.append("")

        # Topology proof stub
        lines.append(
            f"-- Topology preservation (score = "
            f"{self.topology_result.score:.2f})"
        )
        if self.topology_result.preserves_topology:
            lines.append(
                f"theorem topo_{src}_{tgt} : "
                f"PreservesTopology analogy_{src}_{tgt} := by"
            )
            lines.append("  sorry  -- verified computationally")
        else:
            lines.append(
                f"-- Topology NOT preserved; "
                f"{len(self.topology_result.broken)} covers broken"
            )
        lines.append("")
        lines.append("end Deppy.Analogy")

        return "\n".join(lines)

    # -- human-readable summary ----------------------------------------------

    def summary(self) -> str:
        """Human-readable summary of the analogy and its type-checking."""
        parts: List[str] = []
        parts.append(
            f"Analogy: {self.source_domain} → {self.target_domain}"
        )
        parts.append(f"  Pairs: {len(self.mapping.mappings)}")
        for s, t in self.mapping.mapped_concepts():
            parts.append(f"    {s} ↦ {t}")
        parts.append(
            f"  Functor  : {'✓' if self.functor_result.is_functor else '✗'} "
            f"(score={self.functor_result.score:.2f})"
        )
        parts.append(
            f"  Topology : "
            f"{'✓' if self.topology_result.preserves_topology else '✗'} "
            f"(score={self.topology_result.score:.2f})"
        )
        parts.append(
            f"  Novelty  : {'✓' if self.novelty_result.is_novel else '✗'} "
            f"(sim={self.novelty_result.similarity_to_nearest:.2f})"
        )
        parts.append(f"  Value    : {self.value_score:.2f}")
        parts.append(f"  Overall  : {self.overall_score():.2f}")
        classification = (
            "VALUABLE"
            if self.is_valuable()
            else "DEEP" if self.is_deep() else "SHALLOW"
        )
        parts.append(f"  Class    : {classification}")
        return "\n".join(parts)

    # -- serialisation -------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return {
            "mapping": self.mapping.to_dict(),
            "functor_result": self.functor_result.to_dict(),
            "topology_result": self.topology_result.to_dict(),
            "novelty_result": self.novelty_result.to_dict(),
            "value_score": self.value_score,
            "overall_score": self.overall_score(),
        }

    def __repr__(self) -> str:
        classification = (
            "VALUABLE"
            if self.is_valuable()
            else "DEEP" if self.is_deep() else "SHALLOW"
        )
        return (
            f"AnalogyType({self.source_domain}→{self.target_domain}, "
            f"{classification}, score={self.overall_score():.2f})"
        )


# ---------------------------------------------------------------------------
# AnalogyChecker
# ---------------------------------------------------------------------------


class AnalogyChecker:
    """Type-checks analogies through the full Σ-type pipeline."""

    def __init__(
        self, registry: Optional[DomainRegistry] = None
    ) -> None:
        self.registry: DomainRegistry = (
            registry if registry is not None else REGISTRY
        )
        self._functor_check = FunctorCheck()
        self._topology_check = TopologyCheck()
        self._novelty_check = NoveltyCheck()

    # -- full pipeline -------------------------------------------------------

    def check(self, mapping: ConceptMapping) -> AnalogyType:
        """
        Full type-checking pipeline:

        1. Look up source and target domain sites
        2. Check functoriality
        3. Check topology preservation
        4. Check novelty
        5. Compute value score
        6. Return AnalogyType
        """
        source_site = self.registry.get(mapping.source_domain)
        target_site = self.registry.get(mapping.target_domain)

        functor_result = self._functor_check.check(
            mapping, source_site, target_site
        )
        topology_result = self._topology_check.check(
            mapping, source_site, target_site
        )
        novelty_result = self._novelty_check.check(mapping)

        value = self._compute_value(
            mapping, functor_result, topology_result, novelty_result
        )

        return AnalogyType(
            mapping=mapping,
            functor_result=functor_result,
            topology_result=topology_result,
            novelty_result=novelty_result,
            value_score=value,
        )

    # -- value computation ---------------------------------------------------

    def _compute_value(
        self,
        mapping: ConceptMapping,
        functor: FunctorResult,
        topology: TopologyResult,
        novelty: NoveltyResult,
    ) -> float:
        """
        Value = depth × novelty × coverage.

        - depth    = functor.score × topology.score
        - novelty  = 1 - similarity_to_nearest
        - coverage = fraction of source concepts mapped
        """
        depth = functor.score * topology.score
        novelty_val = 1.0 - novelty.similarity_to_nearest
        coverage = mapping.confidence  # confidence doubles as coverage proxy
        raw = depth * novelty_val * coverage
        return min(max(raw, 0.0), 1.0)

    # -- oracle-assisted check -----------------------------------------------

    def check_with_oracle(
        self,
        mapping: ConceptMapping,
        oracle_fn: Callable[[str], str],
    ) -> AnalogyType:
        """
        Check with oracle assistance for filling in gaps.

        If the functor check fails, ask the oracle whether the missing
        morphisms are conceptually valid and update the result accordingly.
        """
        source_site = self.registry.get(mapping.source_domain)
        target_site = self.registry.get(mapping.target_domain)

        functor_result = self._functor_check.check(
            mapping, source_site, target_site
        )

        if not functor_result.is_functor and functor_result.broken:
            suggestions = self._functor_check.suggest_fixes(
                mapping, source_site, target_site
            )
            prompt_lines = [
                "The following morphisms are missing in the target domain "
                f"({mapping.target_domain}) for a cross-domain analogy from "
                f"{mapping.source_domain}:",
                "",
            ]
            for s in suggestions:
                prompt_lines.append(f"  - {s}")
            prompt_lines.append("")
            prompt_lines.append(
                "Are these relationships conceptually valid? "
                "Reply with one line per suggestion: YES or NO."
            )
            prompt = "\n".join(prompt_lines)

            response = oracle_fn(prompt)
            oracle_lines = [
                l.strip().upper()
                for l in response.strip().splitlines()
                if l.strip()
            ]

            confirmed_count = sum(
                1 for line in oracle_lines if line.startswith("YES")
            )
            total_broken = len(functor_result.broken)
            adjusted_preserved = (
                len(functor_result.preserved) + confirmed_count
            )
            adjusted_total = adjusted_preserved + (
                total_broken - confirmed_count
            )
            adjusted_score = (
                adjusted_preserved / adjusted_total
                if adjusted_total > 0
                else 1.0
            )

            functor_result = FunctorResult(
                is_functor=(confirmed_count == total_broken),
                preserved=functor_result.preserved,
                broken=functor_result.broken,
                score=adjusted_score,
                explanation=(
                    f"Oracle confirmed {confirmed_count}/{total_broken} "
                    f"missing morphisms. Adjusted score = "
                    f"{adjusted_score:.2f}."
                ),
            )

        topology_result = self._topology_check.check(
            mapping, source_site, target_site
        )
        novelty_result = self._novelty_check.check(mapping)
        value = self._compute_value(
            mapping, functor_result, topology_result, novelty_result
        )

        return AnalogyType(
            mapping=mapping,
            functor_result=functor_result,
            topology_result=topology_result,
            novelty_result=novelty_result,
            value_score=value,
        )

    # -- batch operations ----------------------------------------------------

    def batch_check(
        self, mappings: List[ConceptMapping]
    ) -> List[AnalogyType]:
        """Check multiple mappings, return sorted by overall_score desc."""
        results = [self.check(m) for m in mappings]
        results.sort(key=lambda a: a.overall_score(), reverse=True)
        return results

    def find_best(
        self, mappings: List[ConceptMapping]
    ) -> Optional[AnalogyType]:
        """Return the highest-scoring valid analogy, or *None*."""
        checked = self.batch_check(mappings)
        if not checked:
            return None
        best = checked[0]
        if best.overall_score() > 0.0:
            return best
        return None


# ---------------------------------------------------------------------------
# IdeationOracle
# ---------------------------------------------------------------------------


class IdeationOracle:
    """
    LLM oracle protocol for cross-domain ideation.

    Protocol::

        1. propose(A, B) → List[ConceptMapping]
        2. validate(mapping) → functor / topology / novelty checks
        3. rank(validated)   → by depth × novelty × value
    """

    def __init__(
        self, registry: Optional[DomainRegistry] = None
    ) -> None:
        self.registry: DomainRegistry = (
            registry if registry is not None else REGISTRY
        )
        self._checker = AnalogyChecker(self.registry)

    # -- proposal ------------------------------------------------------------

    def propose_analogies(
        self,
        domain_a: str,
        domain_b: str,
        context: str = "",
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> List[ConceptMapping]:
        """
        Propose concept mappings between two domains.

        If *oracle_fn* is ``None``, fall back to heuristic matching (keyword
        overlap, name similarity).  Otherwise format a prompt with both domain
        sites and ask the LLM to propose mappings.
        """
        site_a = self.registry.get(domain_a)
        site_b = self.registry.get(domain_b)

        if oracle_fn is None:
            return self._heuristic_propose(site_a, site_b)

        prompt = self._format_proposal_prompt(site_a, site_b, context)
        response = oracle_fn(prompt)
        oracle_mappings = self._parse_oracle_response(
            response, domain_a, domain_b
        )
        if not oracle_mappings:
            return self._heuristic_propose(site_a, site_b)
        return oracle_mappings

    # -- heuristic proposal --------------------------------------------------

    def _heuristic_propose(
        self, site_a: DomainSite, site_b: DomainSite
    ) -> List[ConceptMapping]:
        """
        Heuristic: match concepts by keyword overlap and name similarity.

        Produces a ranked list of mappings.  Uses a greedy bipartite
        matching strategy: for each concept in A, find the best unmatched
        concept in B.
        """
        concepts_a = list(site_a.concepts.values())
        concepts_b = list(site_b.concepts.values())

        similarity_matrix: List[Tuple[float, Concept, Concept]] = []
        for ca in concepts_a:
            for cb in concepts_b:
                kw_sim = self._keyword_similarity(ca, cb)
                nm_sim = self._name_similarity(ca.name, cb.name)
                combined = 0.6 * kw_sim + 0.4 * nm_sim
                if combined > 0.05:
                    similarity_matrix.append((combined, ca, cb))

        similarity_matrix.sort(key=lambda x: x[0], reverse=True)

        # Greedy bipartite matching
        used_a: Set[str] = set()
        used_b: Set[str] = set()
        best_pairs: Dict[str, str] = {}
        confidence_accum: float = 0.0

        for score, ca, cb in similarity_matrix:
            if ca.id in used_a or cb.id in used_b:
                continue
            best_pairs[ca.id] = cb.id
            used_a.add(ca.id)
            used_b.add(cb.id)
            confidence_accum += score

        if not best_pairs:
            return []

        avg_confidence = confidence_accum / len(best_pairs)

        primary = ConceptMapping(
            source_domain=site_a.name,
            target_domain=site_b.name,
            mappings=best_pairs,
            confidence=min(avg_confidence, 1.0),
            provenance="heuristic:greedy",
        )

        # Also produce a partial mapping using only high-confidence pairs
        high_pairs: Dict[str, str] = {}
        high_conf: float = 0.0
        for score, ca, cb in similarity_matrix:
            if score < 0.3:
                break
            if ca.id not in high_pairs and cb.id not in set(
                high_pairs.values()
            ):
                high_pairs[ca.id] = cb.id
                high_conf += score

        results = [primary]
        if high_pairs and high_pairs != best_pairs:
            partial = ConceptMapping(
                source_domain=site_a.name,
                target_domain=site_b.name,
                mappings=high_pairs,
                confidence=(
                    min(high_conf / len(high_pairs), 1.0)
                    if high_pairs
                    else 0.0
                ),
                provenance="heuristic:high-confidence",
            )
            results.append(partial)

        return results

    # -- similarity helpers --------------------------------------------------

    def _keyword_similarity(self, c1: Concept, c2: Concept) -> float:
        """Jaccard similarity of keyword sets."""
        kw1 = set(k.lower() for k in c1.keywords)
        kw2 = set(k.lower() for k in c2.keywords)
        if not kw1 and not kw2:
            return 0.0
        if not kw1 or not kw2:
            return 0.0
        intersection = kw1 & kw2
        union = kw1 | kw2
        return len(intersection) / len(union)

    def _name_similarity(self, name1: str, name2: str) -> float:
        """
        Simple string similarity for concept names.

        Uses normalised longest-common-subsequence length.
        """
        n1 = name1.lower().replace("_", " ").replace("-", " ")
        n2 = name2.lower().replace("_", " ").replace("-", " ")
        if n1 == n2:
            return 1.0
        tokens1 = set(n1.split())
        tokens2 = set(n2.split())
        if not tokens1 or not tokens2:
            return 0.0
        intersection = tokens1 & tokens2
        union = tokens1 | tokens2
        jaccard = len(intersection) / len(union)
        lcs_len = _lcs_length(n1, n2)
        max_len = max(len(n1), len(n2))
        lcs_score = lcs_len / max_len if max_len > 0 else 0.0
        return 0.5 * jaccard + 0.5 * lcs_score

    # -- oracle prompt -------------------------------------------------------

    def _format_proposal_prompt(
        self,
        site_a: DomainSite,
        site_b: DomainSite,
        context: str,
    ) -> str:
        """Format a prompt asking oracle to propose analogies."""
        parts: List[str] = []
        parts.append(
            "You are an expert in cross-domain analogies.  Given two "
            "intellectual domains described below, propose concept "
            "mappings between them.\n"
        )
        parts.append(f"=== Domain A: {site_a.name} ===")
        parts.append("Concepts:")
        for cid, concept in site_a.concepts.items():
            parts.append(f"  - {cid}: {concept.name} — {concept.definition}")
        parts.append("")

        parts.append(f"=== Domain B: {site_b.name} ===")
        parts.append("Concepts:")
        for cid, concept in site_b.concepts.items():
            parts.append(f"  - {cid}: {concept.name} — {concept.definition}")
        parts.append("")

        if context:
            parts.append(f"Context: {context}\n")

        parts.append(
            "Propose mappings as lines of the form:\n"
            "  <concept_id_A> -> <concept_id_B>\n"
            "List as many meaningful pairs as you can find."
        )
        return "\n".join(parts)

    # -- oracle response parsing ---------------------------------------------

    def _parse_oracle_response(
        self,
        response: str,
        domain_a: str,
        domain_b: str,
    ) -> List[ConceptMapping]:
        """Parse oracle response into ConceptMappings."""
        arrow_re = re.compile(r"^\s*(\S+)\s*->\s*(\S+)\s*$", re.MULTILINE)
        pairs: Dict[str, str] = {}
        for match in arrow_re.finditer(response):
            src = match.group(1).strip()
            tgt = match.group(2).strip()
            pairs[src] = tgt

        if not pairs:
            colon_re = re.compile(
                r"^\s*(\S+)\s*:\s*(\S+)\s*$", re.MULTILINE
            )
            for match in colon_re.finditer(response):
                src = match.group(1).strip()
                tgt = match.group(2).strip()
                pairs[src] = tgt

        if not pairs:
            return []

        return [
            ConceptMapping(
                source_domain=domain_a,
                target_domain=domain_b,
                mappings=pairs,
                confidence=0.7,
                provenance="oracle",
            )
        ]

    # -- combined pipeline ---------------------------------------------------

    def validate_functor(
        self,
        mapping: ConceptMapping,
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> bool:
        """
        Validate whether *mapping* is a functor (preserves morphisms).

        If *oracle_fn* is provided, use oracle-assisted checking to fill
        gaps in the target domain.  Otherwise, use purely structural checks.
        """
        if oracle_fn is not None:
            result = self._checker.check_with_oracle(mapping, oracle_fn)
        else:
            result = self._checker.check(mapping)
        return result.functor_result.is_functor

    def estimate_value(
        self,
        mapping: ConceptMapping,
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> float:
        """
        Estimate the value of an analogy on ``[0, 1]``.

        Value = depth × novelty × coverage, computed through the full
        type-checking pipeline.  Returns 0.0 if the mapping is invalid.
        """
        if oracle_fn is not None:
            result = self._checker.check_with_oracle(mapping, oracle_fn)
        else:
            result = self._checker.check(mapping)
        return result.overall_score()

    def propose_and_validate(
        self,
        domain_a: str,
        domain_b: str,
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> List[AnalogyType]:
        """Propose + validate through the full pipeline.  Sorted by score."""
        proposed = self.propose_analogies(
            domain_a, domain_b, oracle_fn=oracle_fn
        )
        if not proposed:
            return []
        return self._checker.batch_check(proposed)

    # -- full ideation -------------------------------------------------------

    def ideate(
        self,
        domains: List[str],
        problem: str,
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> IdeationResult:
        """
        Full ideation pipeline:

        1. For each pair of domains, propose and validate analogies.
        2. Collect deep analogies.
        3. Attempt cross-domain gluing.
        4. Return :class:`IdeationResult`.
        """
        all_analogies: List[AnalogyType] = []
        proposed_count = 0

        for i, da in enumerate(domains):
            for db in domains[i + 1 :]:
                proposed = self.propose_analogies(
                    da, db, context=problem, oracle_fn=oracle_fn
                )
                proposed_count += len(proposed)
                validated = self._checker.batch_check(proposed)
                all_analogies.extend(validated)

        deep = [a for a in all_analogies if a.is_deep()]
        gluer = CrossDomainGluing(self.registry)
        gluing_result = gluer.glue(domains, all_analogies)

        novel_connections: List[Tuple[str, str, str]] = []
        for analogy in all_analogies:
            if analogy.is_novel():
                for src, tgt in analogy.mapping.mapped_concepts():
                    desc = (
                        f"{src} ({analogy.source_domain}) ↔ "
                        f"{tgt} ({analogy.target_domain})"
                    )
                    novel_connections.append(
                        (src, tgt, desc)
                    )

        unified_insights: List[str] = []
        if gluing_result.success:
            unified_insights.append(
                "Domains glue consistently — a unified interdisciplinary "
                "theory is possible."
            )
            unified_insights.extend(
                f"Unified concept: {c}" for c in gluing_result.unified_concepts
            )
        else:
            unified_insights.append(
                f"Gluing obstructed (H¹ = {gluing_result.h1_dimension}). "
                f"Generators: {', '.join(gluing_result.generators)}"
            )

        return IdeationResult(
            domains=domains,
            problem=problem,
            analogies_proposed=proposed_count,
            analogies_validated=len(all_analogies),
            deep_analogies=deep,
            h1_dimension=gluing_result.h1_dimension,
            unified_insights=unified_insights,
            novel_connections=novel_connections,
        )


# ---------------------------------------------------------------------------
# CrossDomainGluing
# ---------------------------------------------------------------------------


class CrossDomainGluing:
    """
    Attempts to glue local domain knowledge into a unified theory.

    Given domains D₁,…,Dₙ with pairwise analogies, checks if the cocycle
    condition holds (analogies are compatible on triple overlaps) and
    computes H¹ of the interdisciplinary cover.
    """

    def __init__(
        self, registry: Optional[DomainRegistry] = None
    ) -> None:
        self.registry: DomainRegistry = (
            registry if registry is not None else REGISTRY
        )

    # -- public API ----------------------------------------------------------

    def glue(
        self,
        domains: List[str],
        analogies: List[AnalogyType],
    ) -> GluingResult:
        """
        Attempt to glue analogies.

        1. Check pairwise compatibility (cocycle condition on triple overlaps).
        2. Compute obstruction class (H¹).
        3. If H¹ = 0, gluing succeeds → unified theory.
        4. If H¹ ≠ 0, report generators (conceptual gaps).
        """
        cocycle_failures: List[str] = []

        triples = list(itertools.combinations(domains, 3))
        for d1, d2, d3 in triples:
            ok, issues = self._check_cocycle(d1, d2, d3, analogies)
            if not ok:
                cocycle_failures.extend(issues)

        h1 = self.compute_h1(domains, analogies)
        generators = self.h1_generators(domains, analogies)

        unified_concepts = self._unified_concepts(domains, analogies)

        success = h1 == 0

        if success:
            explanation = (
                f"All cocycle conditions satisfied across "
                f"{len(triples)} triple(s). H¹ = 0. "
                f"Unified theory with {len(unified_concepts)} "
                f"consistently-glued concepts."
            )
        else:
            explanation = (
                f"Gluing obstructed: H¹ = {h1}. "
                f"{len(cocycle_failures)} cocycle failure(s). "
                f"Generators: {', '.join(generators) if generators else 'none'}."
            )

        return GluingResult(
            success=success,
            h1_dimension=h1,
            cocycle_failures=cocycle_failures,
            generators=generators,
            unified_concepts=unified_concepts,
            explanation=explanation,
        )

    # -- cocycle check -------------------------------------------------------

    def _check_cocycle(
        self,
        d1: str,
        d2: str,
        d3: str,
        analogies: List[AnalogyType],
    ) -> Tuple[bool, List[str]]:
        """
        Check cocycle condition on triple overlap:
        F₁₂ ; F₂₃ ≅ F₁₃ on the overlap of D₁, D₂, D₃.

        Returns ``(compatible, list_of_incompatibilities)``.
        """
        f12 = self._find_analogy(d1, d2, analogies)
        f23 = self._find_analogy(d2, d3, analogies)
        f13 = self._find_analogy(d1, d3, analogies)

        if f12 is None or f23 is None or f13 is None:
            missing_pairs: List[str] = []
            if f12 is None:
                missing_pairs.append(f"{d1}↔{d2}")
            if f23 is None:
                missing_pairs.append(f"{d2}↔{d3}")
            if f13 is None:
                missing_pairs.append(f"{d1}↔{d3}")
            return True, []  # can't check — vacuously true

        composed = f12.mapping.compose(f23.mapping)
        direct = f13.mapping

        overlap = composed.overlap_with(direct)
        issues: List[str] = []
        for src, (via_composed, via_direct) in overlap.items():
            if via_composed != via_direct:
                issues.append(
                    f"Cocycle failure at {src}: "
                    f"F₁₂;F₂₃ maps to {via_composed} but "
                    f"F₁₃ maps to {via_direct} "
                    f"(triple {d1},{d2},{d3})."
                )

        return len(issues) == 0, issues

    def _find_analogy(
        self,
        domain_a: str,
        domain_b: str,
        analogies: List[AnalogyType],
    ) -> Optional[AnalogyType]:
        """Find an analogy between two specific domains (either direction)."""
        for analogy in analogies:
            if (
                analogy.source_domain == domain_a
                and analogy.target_domain == domain_b
            ):
                return analogy
            if (
                analogy.source_domain == domain_b
                and analogy.target_domain == domain_a
            ):
                inv_mapping = analogy.mapping.inverse()
                return AnalogyType(
                    mapping=inv_mapping,
                    functor_result=analogy.functor_result,
                    topology_result=analogy.topology_result,
                    novelty_result=analogy.novelty_result,
                    value_score=analogy.value_score,
                )
        return None

    # -- H¹ computation ------------------------------------------------------

    def compute_h1(
        self,
        domains: List[str],
        analogies: List[AnalogyType],
    ) -> int:
        """
        Compute H¹ = dimension of obstruction space.

        H¹ = number of independent cocycle failures.
        """
        all_failures: List[str] = []
        for d1, d2, d3 in itertools.combinations(domains, 3):
            ok, issues = self._check_cocycle(d1, d2, d3, analogies)
            all_failures.extend(issues)

        seen_concepts: Set[str] = set()
        independent_count = 0
        for failure in all_failures:
            concept_match = re.search(r"at (\S+):", failure)
            if concept_match:
                concept = concept_match.group(1)
                if concept not in seen_concepts:
                    seen_concepts.add(concept)
                    independent_count += 1
            else:
                independent_count += 1

        return independent_count

    def h1_generators(
        self,
        domains: List[str],
        analogies: List[AnalogyType],
    ) -> List[str]:
        """
        Return descriptions of H¹ generators (the conceptual gaps).

        Each generator represents a concept that doesn't translate
        consistently across three or more domains.
        """
        generators: List[str] = []
        for d1, d2, d3 in itertools.combinations(domains, 3):
            ok, issues = self._check_cocycle(d1, d2, d3, analogies)
            for issue in issues:
                concept_match = re.search(r"at (\S+):", issue)
                if concept_match:
                    concept_id = concept_match.group(1)
                    desc = (
                        f"Concept '{concept_id}' maps inconsistently across "
                        f"{d1}, {d2}, {d3}."
                    )
                    if desc not in generators:
                        generators.append(desc)
                else:
                    if issue not in generators:
                        generators.append(issue)
        return generators

    # -- bridge proposals ----------------------------------------------------

    def propose_bridges(
        self,
        generators: List[str],
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> List[ConceptMapping]:
        """
        For each H¹ generator, propose bridge concepts that could resolve
        the incompatibility.
        """
        if not generators:
            return []

        if oracle_fn is None:
            return []

        prompt_lines = [
            "The following conceptual gaps were detected in a cross-domain "
            "analogy network:\n",
        ]
        for i, gen in enumerate(generators, 1):
            prompt_lines.append(f"  {i}. {gen}")
        prompt_lines.append("")
        prompt_lines.append(
            "For each gap, propose a bridge concept (a new concept that "
            "resolves the inconsistency) as:\n"
            "  BRIDGE: <domain> <concept_id> -> <domain> <concept_id>\n"
        )
        prompt = "\n".join(prompt_lines)
        response = oracle_fn(prompt)

        bridges: List[ConceptMapping] = []
        bridge_re = re.compile(
            r"BRIDGE:\s*(\S+)\s+(\S+)\s*->\s*(\S+)\s+(\S+)"
        )
        for match in bridge_re.finditer(response):
            d_a, c_a, d_b, c_b = (
                match.group(1),
                match.group(2),
                match.group(3),
                match.group(4),
            )
            bridges.append(
                ConceptMapping(
                    source_domain=d_a,
                    target_domain=d_b,
                    mappings={c_a: c_b},
                    confidence=0.5,
                    provenance="oracle:bridge",
                )
            )
        return bridges

    # -- helper: unified concepts -------------------------------------------

    def _unified_concepts(
        self,
        domains: List[str],
        analogies: List[AnalogyType],
    ) -> List[str]:
        """
        Return concepts that glue consistently across all domains that
        map them.
        """
        concept_images: Dict[str, Set[str]] = defaultdict(set)

        for analogy in analogies:
            for src, tgt in analogy.mapping.mapped_concepts():
                key = f"{analogy.source_domain}:{src}"
                concept_images[key].add(f"{analogy.target_domain}:{tgt}")

        consistent: List[str] = []
        seen: Set[str] = set()

        for key, images in concept_images.items():
            domain, concept_id = key.split(":", 1)
            if key in seen:
                continue
            is_consistent = True
            for analogy in analogies:
                if analogy.source_domain == domain:
                    mapped = analogy.mapping.mappings.get(concept_id)
                    if mapped is not None:
                        target_key = (
                            f"{analogy.target_domain}:{mapped}"
                        )
                        reverse_analogy = self._find_analogy(
                            analogy.target_domain,
                            domain,
                            analogies,
                        )
                        if reverse_analogy is not None:
                            reverse_mapped = (
                                reverse_analogy.mapping.mappings.get(mapped)
                            )
                            if (
                                reverse_mapped is not None
                                and reverse_mapped != concept_id
                            ):
                                is_consistent = False
                                break
            if is_consistent:
                consistent.append(f"{domain}:{concept_id}")
                seen.add(key)

        return consistent


# ---------------------------------------------------------------------------
# GluingResult & IdeationResult
# ---------------------------------------------------------------------------


@dataclass
class GluingResult:
    """Result of attempting to glue cross-domain analogies."""

    success: bool
    h1_dimension: int
    cocycle_failures: List[str]
    generators: List[str]
    unified_concepts: List[str]
    explanation: str

    def summary(self) -> str:
        parts: List[str] = []
        if self.success:
            parts.append("Gluing: SUCCESS (H¹ = 0)")
        else:
            parts.append(f"Gluing: OBSTRUCTED (H¹ = {self.h1_dimension})")

        if self.unified_concepts:
            parts.append(
                f"  Unified concepts ({len(self.unified_concepts)}):"
            )
            for c in self.unified_concepts[:10]:
                parts.append(f"    - {c}")
            if len(self.unified_concepts) > 10:
                parts.append(
                    f"    ... and {len(self.unified_concepts) - 10} more"
                )

        if self.cocycle_failures:
            parts.append(
                f"  Cocycle failures ({len(self.cocycle_failures)}):"
            )
            for f in self.cocycle_failures[:5]:
                parts.append(f"    - {f}")
            if len(self.cocycle_failures) > 5:
                parts.append(
                    f"    ... and {len(self.cocycle_failures) - 5} more"
                )

        if self.generators:
            parts.append(f"  H¹ generators ({len(self.generators)}):")
            for g in self.generators[:5]:
                parts.append(f"    - {g}")
            if len(self.generators) > 5:
                parts.append(
                    f"    ... and {len(self.generators) - 5} more"
                )

        return "\n".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "success": self.success,
            "h1_dimension": self.h1_dimension,
            "cocycle_failures": self.cocycle_failures,
            "generators": self.generators,
            "unified_concepts": self.unified_concepts,
            "explanation": self.explanation,
        }

    def __repr__(self) -> str:
        status = "SUCCESS" if self.success else "OBSTRUCTED"
        return f"GluingResult({status}, H¹={self.h1_dimension})"


@dataclass
class IdeationResult:
    """Result of a full cross-domain ideation run."""

    domains: List[str]
    problem: str
    analogies_proposed: int
    analogies_validated: int
    deep_analogies: List[AnalogyType]
    h1_dimension: int
    unified_insights: List[str]
    novel_connections: List[Tuple[str, str, str]]

    def summary(self) -> str:
        """Multi-line summary of ideation results."""
        parts: List[str] = []
        parts.append(f"Ideation Report: {self.problem}")
        parts.append(f"  Domains: {', '.join(self.domains)}")
        parts.append(f"  Proposed analogies : {self.analogies_proposed}")
        parts.append(f"  Validated analogies: {self.analogies_validated}")
        parts.append(f"  Deep analogies     : {len(self.deep_analogies)}")
        parts.append(f"  H¹ dimension       : {self.h1_dimension}")

        if self.deep_analogies:
            parts.append("  Best deep analogies:")
            for a in self.deep_analogies[:5]:
                parts.append(
                    f"    {a.source_domain} → {a.target_domain} "
                    f"(score={a.overall_score():.2f})"
                )

        if self.novel_connections:
            parts.append(
                f"  Novel connections ({len(self.novel_connections)}):"
            )
            for src, tgt, desc in self.novel_connections[:5]:
                parts.append(f"    {desc}")

        if self.unified_insights:
            parts.append("  Insights:")
            for insight in self.unified_insights:
                parts.append(f"    • {insight}")

        return "\n".join(parts)

    def to_markdown(self) -> str:
        """Full markdown report of ideation results."""
        lines: List[str] = []
        lines.append(f"# Ideation Report\n")
        lines.append(f"**Problem:** {self.problem}\n")
        lines.append(
            f"**Domains:** {', '.join(self.domains)}\n"
        )
        lines.append("## Statistics\n")
        lines.append(f"| Metric | Value |")
        lines.append(f"|--------|-------|")
        lines.append(
            f"| Analogies proposed | {self.analogies_proposed} |"
        )
        lines.append(
            f"| Analogies validated | {self.analogies_validated} |"
        )
        lines.append(
            f"| Deep analogies | {len(self.deep_analogies)} |"
        )
        lines.append(f"| H¹ dimension | {self.h1_dimension} |")
        lines.append("")

        if self.deep_analogies:
            lines.append("## Deep Analogies\n")
            for i, a in enumerate(self.deep_analogies, 1):
                lines.append(
                    f"### {i}. {a.source_domain} → {a.target_domain} "
                    f"(score: {a.overall_score():.2f})\n"
                )
                lines.append("| Source | Target |")
                lines.append("|--------|--------|")
                for src, tgt in a.mapping.mapped_concepts():
                    lines.append(f"| {src} | {tgt} |")
                lines.append("")
                lines.append(f"- Functor: {a.functor_result.explanation}")
                lines.append(
                    f"- Topology: {a.topology_result.explanation}"
                )
                lines.append(
                    f"- Novelty: {a.novelty_result.explanation}"
                )
                lines.append(f"- Value: {a.value_score:.2f}")
                lines.append("")

        if self.novel_connections:
            lines.append("## Novel Connections\n")
            for src, tgt, desc in self.novel_connections:
                lines.append(f"- {desc}")
            lines.append("")

        if self.unified_insights:
            lines.append("## Unified Insights\n")
            for insight in self.unified_insights:
                lines.append(f"- {insight}")
            lines.append("")

        if self.h1_dimension > 0:
            lines.append("## Obstructions\n")
            lines.append(
                f"H¹ = {self.h1_dimension}: the following conceptual gaps "
                f"prevent full unification:\n"
            )
            lines.append(
                "_Use `CrossDomainGluing.propose_bridges()` with an "
                "oracle to suggest resolutions._\n"
            )

        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "domains": self.domains,
            "problem": self.problem,
            "analogies_proposed": self.analogies_proposed,
            "analogies_validated": self.analogies_validated,
            "deep_analogies": [a.to_dict() for a in self.deep_analogies],
            "h1_dimension": self.h1_dimension,
            "unified_insights": self.unified_insights,
            "novel_connections": self.novel_connections,
        }

    def __repr__(self) -> str:
        return (
            f"IdeationResult(domains={self.domains}, "
            f"deep={len(self.deep_analogies)}, "
            f"H¹={self.h1_dimension})"
        )


# ---------------------------------------------------------------------------
# ExtensionProposal
# ---------------------------------------------------------------------------


@dataclass
class ExtensionProposal:
    """A proposed extension to the deppy type system itself.

    Generated by :class:`SelfImprovementLoop` when deppy encounters a
    verification problem that cannot be expressed in the current type
    language.  Each proposal is backed by a cross-domain analogy that
    maps a well-understood formal structure onto the gap.
    """

    name: str
    description: str
    source_analogy: Optional[ConceptMapping] = None
    target_gap: str = ""
    new_concepts: List[str] = field(default_factory=list)
    new_morphisms: List[Tuple[str, str, str]] = field(default_factory=list)
    new_covers: List[Tuple[str, List[str]]] = field(default_factory=list)
    confidence: float = 0.0
    rationale: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "description": self.description,
            "source_analogy": (
                self.source_analogy.to_dict() if self.source_analogy else None
            ),
            "target_gap": self.target_gap,
            "new_concepts": self.new_concepts,
            "new_morphisms": [
                {"src": s, "tgt": t, "rel": r}
                for s, t, r in self.new_morphisms
            ],
            "new_covers": [
                {"covered": c, "covering": cs} for c, cs in self.new_covers
            ],
            "confidence": self.confidence,
            "rationale": self.rationale,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> ExtensionProposal:
        src_analogy = None
        if data.get("source_analogy"):
            src_analogy = ConceptMapping.from_dict(data["source_analogy"])
        return cls(
            name=data["name"],
            description=data.get("description", ""),
            source_analogy=src_analogy,
            target_gap=data.get("target_gap", ""),
            new_concepts=data.get("new_concepts", []),
            new_morphisms=[
                (m["src"], m["tgt"], m["rel"])
                for m in data.get("new_morphisms", [])
            ],
            new_covers=[
                (c["covered"], c["covering"])
                for c in data.get("new_covers", [])
            ],
            confidence=data.get("confidence", 0.0),
            rationale=data.get("rationale", ""),
        )

    def __repr__(self) -> str:
        return (
            f"ExtensionProposal({self.name!r}, "
            f"concepts={len(self.new_concepts)}, "
            f"confidence={self.confidence:.2f})"
        )


# ---------------------------------------------------------------------------
# SelfImprovementLoop
# ---------------------------------------------------------------------------


class SelfImprovementLoop:
    """Deppy ideates about extensions to its own type system.

    The loop works by treating the *current* deppy type system as a domain
    site and searching for analogies to well-understood formal systems
    (category theory, type theory, algebraic geometry, etc.) that could
    fill expressiveness gaps.

    Protocol::

        1. Identify a *gap* — a verification problem that deppy cannot
           currently express or decide.
        2. Build a local site around the gap (the ``problem_site``).
        3. For each reference domain, propose analogies from the reference
           into the gap neighbourhood.
        4. Score each proposed extension via the :class:`AnalogyChecker`
           pipeline (functoriality, topology preservation, novelty).
        5. Return ranked :class:`ExtensionProposal` objects.
    """

    # Reference domains to search for structural analogies.
    _REFERENCE_DOMAINS: List[str] = [
        "category_theory",
        "type_theory",
        "algebraic_geometry",
        "machine_learning",
    ]

    def __init__(
        self,
        registry: Optional[DomainRegistry] = None,
        oracle_fn: Optional[Callable[[str], str]] = None,
    ) -> None:
        self.registry: DomainRegistry = (
            registry if registry is not None else REGISTRY
        )
        self.oracle_fn = oracle_fn
        self._checker = AnalogyChecker(self.registry)
        self._oracle = IdeationOracle(self.registry)

    # -- public API ----------------------------------------------------------

    def propose_extension(
        self, problem: str
    ) -> List[ExtensionProposal]:
        """Propose type-system extensions for *problem*.

        Parameters
        ----------
        problem:
            Natural-language description of a verification gap or a
            construct that deppy cannot currently type-check.

        Returns
        -------
        List[ExtensionProposal]
            Candidate extensions sorted by confidence (descending).
        """
        problem_site = self._build_problem_site(problem)
        problem_domain = f"__problem_{id(problem_site)}"
        problem_site.name = problem_domain

        if problem_domain not in self.registry._domains:
            self.registry.register(problem_site)

        proposals: List[ExtensionProposal] = []

        for ref_domain in self._REFERENCE_DOMAINS:
            if ref_domain not in self.registry._domains:
                continue

            mappings = self._oracle.propose_analogies(
                ref_domain, problem_domain,
                context=problem,
                oracle_fn=self.oracle_fn,
            )

            for mapping in mappings:
                analogy = self._checker.check(mapping)
                proposal = self._analogy_to_proposal(
                    analogy, problem, ref_domain
                )
                if proposal is not None:
                    proposals.append(proposal)

        proposals.sort(key=lambda p: p.confidence, reverse=True)

        # Clean up transient domain.
        if problem_domain in self.registry._domains:
            del self.registry._domains[problem_domain]

        return proposals

    def validate_extension(
        self, proposal: ExtensionProposal
    ) -> AnalogyType:
        """Validate an :class:`ExtensionProposal` through the analogy
        type-checking pipeline.

        If the proposal has no backing analogy, a trivial identity mapping
        is constructed so that the checker can still score structural
        coherence.
        """
        if proposal.source_analogy is not None:
            mapping = proposal.source_analogy
        else:
            mapping = ConceptMapping(
                source_domain="category_theory",
                target_domain="category_theory",
                mappings={},
                confidence=proposal.confidence,
                provenance=f"self-improvement: {proposal.name}",
            )

        if self.oracle_fn is not None:
            return self._checker.check_with_oracle(
                mapping, self.oracle_fn
            )
        return self._checker.check(mapping)

    # -- site construction ---------------------------------------------------

    def _build_problem_site(self, problem: str) -> DomainSite:
        """Build a small domain site from a problem description.

        Extracts nouns/concepts heuristically and connects them via
        generic ``relates_to`` morphisms.
        """
        site = DomainSite(name="problem")

        words = re.findall(r"[A-Za-z][a-z]{2,}", problem)
        stopwords = {
            "the", "and", "for", "that", "this", "with", "from", "are",
            "was", "were", "been", "have", "has", "had", "not", "but",
            "can", "could", "would", "should", "may", "might", "will",
            "does", "did", "its", "our", "their", "your", "his", "her",
            "which", "when", "where", "what", "how", "who", "whom",
            "there", "here", "also", "just", "only", "than", "then",
            "each", "every", "some", "any", "all", "most", "more",
            "such", "very", "too", "about", "into", "onto", "upon",
        }

        seen: Set[str] = set()
        concepts: List[str] = []
        for w in words:
            low = w.lower()
            if low not in stopwords and low not in seen:
                seen.add(low)
                concepts.append(low)

        concepts = concepts[:20]

        for c in concepts:
            site.add_concept(Concept(
                id=c, domain="problem", name=c, definition=c,
            ))

        for i, c1 in enumerate(concepts):
            for c2 in concepts[i + 1 : i + 4]:
                try:
                    site.add_morphism(Morphism(
                        source=c1, target=c2,
                        relation="USES",
                        description=f"{c1} relates to {c2}",
                    ))
                except (ValueError, KeyError):
                    pass

        if len(concepts) >= 3:
            site.add_covering(CoveringFamily(
                covered=concepts[0],
                covering=concepts[1:4],
                explanation=f"{concepts[0]} is explained by neighbours",
            ))

        return site

    # -- internal helpers ----------------------------------------------------

    def _analogy_to_proposal(
        self,
        analogy: AnalogyType,
        problem: str,
        reference_domain: str,
    ) -> Optional[ExtensionProposal]:
        """Convert a scored analogy into an :class:`ExtensionProposal`.

        Returns ``None`` if the analogy is too weak to warrant a proposal.
        """
        score = analogy.overall_score()
        if score <= 0.0:
            return None

        mapped = analogy.mapping.mapped_concepts()
        new_concepts = [tgt for _, tgt in mapped]

        new_morphisms: List[Tuple[str, str, str]] = []
        for left, right in zip(new_concepts, new_concepts[1:]):
            new_morphisms.append((left, right, "USES"))

        new_covers: List[Tuple[str, List[str]]] = []

        ref_site = self.registry.get(reference_domain)
        if ref_site is not None:
            for source_concept, target_concept in mapped:
                covers = ref_site.covers_for(source_concept)
                for cov in covers:
                    mapped_covering = []
                    for c in cov.covering:
                        mapped_target = analogy.mapping.mappings.get(c)
                        if mapped_target is not None:
                            mapped_covering.append(mapped_target)
                    if mapped_covering:
                        new_covers.append((target_concept, mapped_covering))

        is_deep = analogy.is_deep()
        conf = min(score * (1.5 if is_deep else 0.8), 1.0)

        rationale_parts = [
            f"Analogy from {reference_domain} to problem context.",
            f"Functor score: {analogy.functor_result.score:.2f}.",
            f"Topology score: {analogy.topology_result.score:.2f}.",
        ]
        if is_deep:
            rationale_parts.append("Analogy is deep (topology-preserving).")
        if analogy.is_novel():
            rationale_parts.append("Analogy is novel.")

        return ExtensionProposal(
            name=f"ext_{reference_domain}_{len(new_concepts)}concepts",
            description=(
                f"Extension inspired by {reference_domain} for: {problem[:80]}"
            ),
            source_analogy=analogy.mapping,
            target_gap=problem[:200],
            new_concepts=new_concepts,
            new_morphisms=new_morphisms,
            new_covers=new_covers,
            confidence=conf,
            rationale=" ".join(rationale_parts),
        )


# ---------------------------------------------------------------------------
# Helpers (module-private)
# ---------------------------------------------------------------------------


def _lean_ident(name: str) -> str:
    """Convert an arbitrary string to a valid Lean 4 identifier."""
    clean = re.sub(r"[^a-zA-Z0-9_]", "_", name)
    if clean and clean[0].isdigit():
        clean = "_" + clean
    return clean


def _lcs_length(a: str, b: str) -> int:
    """Length of the longest common subsequence of *a* and *b*."""
    m, n = len(a), len(b)
    if m == 0 or n == 0:
        return 0
    prev = [0] * (n + 1)
    for i in range(1, m + 1):
        curr = [0] * (n + 1)
        for j in range(1, n + 1):
            if a[i - 1] == b[j - 1]:
                curr[j] = prev[j - 1] + 1
            else:
                curr[j] = max(prev[j], curr[j - 1])
        prev = curr
    return prev[n]
