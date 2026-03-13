"""Stalk computation and germ-level equivalence.

In sheaf theory, the **stalk** F_p at a point p is the colimit:

    F_p = colim_{p ∈ U} F(U)

Its elements are **germs**: equivalence classes of local sections,
where two sections σ ∈ F(U) and τ ∈ F(V) represent the same germ
if they agree on some common neighbourhood W ⊆ U ∩ V.

This module provides:

1. ``Germ`` — a section quotiented by agreement-on-neighbourhoods.
2. ``Stalk`` — the colimit object F_p with all germs.
3. ``StalkEquivalenceChecker`` — two presheaves are isomorphic iff
   their stalks are isomorphic at every point.
4. ``GermMorphism`` — induced maps on stalks from presheaf morphisms.
5. ``StalkFunctor`` — the stalk functor Γ_p : Psh(S) → Set realized
   with predicates tracking the refinement structure.

The *key theorem* this module implements is:

    **A morphism η: F → G of sheaves is an isomorphism iff
    η_p : F_p → G_p is an isomorphism for all points p.**

This gives an alternative characterisation of equivalence that is
sometimes more efficient: instead of checking gluing globally, we
check isomorphism stalk-by-stalk.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf
from deppy.core.site import ConcreteMorphism, SiteCategory
from deppy.types.refinement import (
    ConjunctionPred,
    DisjunctionPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    FalsePred,
    VarPred,
)
from deppy.types.dependent import IdentityType
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    TransportWitness,
    TransitivityProof,
    SymmetryProof,
)

from deppy.equivalence._protocols import (
    EquivalenceVerdict,
    EquivalenceStrength,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.predicates import BiimplicationPred


# ═══════════════════════════════════════════════════════════════════════════════
# Germ — an equivalence class of local sections
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class Germ:
    """A germ [σ, U] at point p.

    Two germs [σ, U] and [τ, V] are equal if there exists W ⊆ U ∩ V
    with p ∈ W such that σ|_W = τ|_W.

    Attributes:
        point:        The point p (a SiteId in our model).
        section:      The representative local section σ ∈ F(U).
        neighbourhood: The open set U.
        predicate:    The refinement predicate of σ restricted to
                      the neighbourhood of p.
    """
    point: SiteId
    section: LocalSection
    neighbourhood: SiteId
    predicate: Predicate

    def agrees_with(self, other: "Germ") -> Predicate:
        """Return a predicate that is true iff the two germs are equal.

        Equality: ∃ W ⊆ U ∩ V with p ∈ W : σ|_W = τ|_W.
        We encode this as bi-implication of the predicates
        (since restriction preserves the predicate structure).
        """
        return ConjunctionPred(conjuncts=(
            ImplicationPred(antecedent=self.predicate, consequent=other.predicate),
            ImplicationPred(antecedent=other.predicate, consequent=self.predicate),
        ))

    @property
    def carrier_type(self) -> Any:
        return self.section.carrier_type


# ═══════════════════════════════════════════════════════════════════════════════
# Stalk — the colimit F_p = colim_{p ∈ U} F(U)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class Stalk:
    """The stalk F_p of a presheaf F at point p.

    F_p = colim_{p ∈ U} F(U) = { [σ, U] | σ ∈ F(U), p ∈ U } / ~

    where ~ is the germ equivalence relation.

    Attributes:
        point:  The point p.
        germs:  Representatives of germ equivalence classes.
        presheaf: The source presheaf F.
    """
    point: SiteId
    germs: List[Germ] = field(default_factory=list)
    presheaf: Optional[ConcretePresheaf] = None

    @property
    def is_empty(self) -> bool:
        return len(self.germs) == 0

    @property
    def carrier_types(self) -> List[Any]:
        """All carrier types represented in the stalk."""
        return [g.carrier_type for g in self.germs]

    @property
    def combined_predicate(self) -> Predicate:
        """The disjunction of all germ predicates.

        This represents "some germ at p is valid", i.e.
        the stalk is non-empty in the refinement sense.
        """
        preds = [g.predicate for g in self.germs]
        if not preds:
            return FalsePred()
        if len(preds) == 1:
            return preds[0]
        return DisjunctionPred(disjuncts=tuple(preds))


# ═══════════════════════════════════════════════════════════════════════════════
# Stalk functor  Γ_p : Psh(S) → Set
# ═══════════════════════════════════════════════════════════════════════════════


class StalkFunctor:
    """Compute stalks of presheaves.

    The stalk functor Γ_p at a point p sends a presheaf F to the
    set F_p = colim_{p ∈ U} F(U).

    In our computational model, a "point" is a SiteId, and the
    "neighbourhoods of p" are the sites U such that there is a
    morphism p → U (or p ∈ U in the topological sense, meaning
    p refines U or there is a restriction from U to p).

    Parameters:
        site_category:  The site category S with its morphisms.
    """

    def __init__(self, site_category: SiteCategory) -> None:
        self._category = site_category

    def stalk_at(
        self,
        presheaf: ConcretePresheaf,
        point: SiteId,
    ) -> Stalk:
        """Compute F_p.

        Collects all sections of F at neighbourhoods of p and
        quotiented by the germ equivalence relation.
        """
        neighbourhoods = self._neighbourhoods_of(point)
        raw_germs: List[Germ] = []

        for nbhd in neighbourhoods:
            sections = presheaf.sections_at(nbhd)
            for section in sections:
                pred = self._extract_predicate(section)
                raw_germs.append(Germ(
                    point=point,
                    section=section,
                    neighbourhood=nbhd,
                    predicate=pred,
                ))

        # Quotient by germ equivalence: group germs that agree
        equivalence_classes = self._quotient_germs(raw_germs)

        return Stalk(
            point=point,
            germs=equivalence_classes,
            presheaf=presheaf,
        )

    def all_stalks(
        self,
        presheaf: ConcretePresheaf,
    ) -> Dict[SiteId, Stalk]:
        """Compute stalks at all points (sites) of the presheaf."""
        return {
            site: self.stalk_at(presheaf, site)
            for site in presheaf.site_ids()
        }

    def stalk_map(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        morphism_components: Dict[SiteId, Any],
        point: SiteId,
    ) -> "GermMorphism":
        """Compute the induced map η_p : F_p → G_p from a presheaf morphism.

        If η: F → G, then η_p([σ, U]) = [η_U(σ), U].
        """
        stalk_f = self.stalk_at(presheaf_f, point)
        stalk_g = self.stalk_at(presheaf_g, point)

        germ_maps: Dict[int, int] = {}  # index in stalk_f → index in stalk_g
        evidence: Dict[int, Predicate] = {}

        for i, germ_f in enumerate(stalk_f.germs):
            nbhd = germ_f.neighbourhood
            comp = morphism_components.get(nbhd)
            if comp is None:
                continue

            # Apply the morphism component to find the image germ
            if hasattr(comp, "transform"):
                image_section = comp.transform(germ_f.section)
            else:
                continue

            image_pred = self._extract_predicate(image_section)

            # Find matching germ in stalk_g
            best_match = self._find_matching_germ(
                stalk_g.germs, image_pred, nbhd,
            )
            if best_match is not None:
                germ_maps[i] = best_match
                # Evidence: the predicate of the image agrees with g
                g_pred = stalk_g.germs[best_match].predicate
                evidence[i] = ConjunctionPred(conjuncts=(
                    ImplicationPred(antecedent=image_pred, consequent=g_pred),
                    ImplicationPred(antecedent=g_pred, consequent=image_pred),
                ))

        return GermMorphism(
            source=stalk_f,
            target=stalk_g,
            germ_map=germ_maps,
            evidence=evidence,
            point=point,
        )

    # ── Internal ──────────────────────────────────────────────────────────

    def _neighbourhoods_of(self, point: SiteId) -> List[SiteId]:
        """All sites U such that point ∈ U.

        In our site category, this means U = point or there is a
        morphism from point to U.
        """
        nbhds: Set[SiteId] = {point}

        # Sites reachable via morphisms from point (point refines U)
        for morph in self._category.outgoing(point):
            nbhds.add(morph.target)

        # Also sites with morphisms to point (U covers point)
        for morph in [m for m in self._category.morphisms if m.target == point]:
            nbhds.add(morph.source)

        return list(nbhds)

    def _quotient_germs(self, germs: List[Germ]) -> List[Germ]:
        """Quotient a list of germs by the equivalence relation.

        Two germs are equivalent if their predicates are bi-implicative.
        We use a simple union-find on predicate structure.
        """
        if not germs:
            return []

        classes: List[List[Germ]] = []
        assigned = [False] * len(germs)

        for i, germ_i in enumerate(germs):
            if assigned[i]:
                continue

            current_class = [germ_i]
            assigned[i] = True

            for j in range(i + 1, len(germs)):
                if assigned[j]:
                    continue
                germ_j = germs[j]

                # Syntactic check: if predicates are structurally equal,
                # they represent the same germ
                if self._predicates_equivalent(germ_i.predicate, germ_j.predicate):
                    current_class.append(germ_j)
                    assigned[j] = True

            classes.append(current_class)

        # Return one representative per class
        return [cls[0] for cls in classes]

    def _predicates_equivalent(self, p: Predicate, q: Predicate) -> bool:
        """Genuine predicate equivalence via the three-tier engine.

        Uses structural AST walk → algebraic normalisation → Z3 solver
        from ``predicate_eq`` rather than repr() comparison.
        """
        from deppy.equivalence.predicate_eq import predicates_equivalent, PredicateRelation
        result = predicates_equivalent(p, q, use_solver=True)
        return result.relation == PredicateRelation.EQUIVALENT

    def _find_matching_germ(
        self,
        germs: List[Germ],
        pred: Predicate,
        nbhd: SiteId,
    ) -> Optional[int]:
        """Find a germ in the list whose predicate matches."""
        for i, germ in enumerate(germs):
            if self._predicates_equivalent(pred, germ.predicate):
                return i
        # Fallback: match by neighbourhood
        for i, germ in enumerate(germs):
            if germ.neighbourhood == nbhd:
                return i
        return 0 if germs else None

    def _extract_predicate(self, section: LocalSection) -> Predicate:
        ct = section.carrier_type
        if isinstance(ct, RefinementType) and ct.predicate is not None:
            return ct.predicate
        return VarPred(var_name=f"section_{section.site_id.name}")


# ═══════════════════════════════════════════════════════════════════════════════
# GermMorphism — induced map on stalks
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class GermMorphism:
    """An induced map η_p: F_p → G_p on stalks.

    Attributes:
        source:   Stalk F_p
        target:   Stalk G_p
        germ_map: Maps germ indices in F_p to germ indices in G_p
        evidence: Per-germ evidence predicates
        point:    The point p
    """
    source: Stalk
    target: Stalk
    germ_map: Dict[int, int] = field(default_factory=dict)
    evidence: Dict[int, Predicate] = field(default_factory=dict)
    point: Optional[SiteId] = None

    @property
    def is_injective(self) -> bool:
        """η_p is injective iff the germ_map is injective."""
        values = list(self.germ_map.values())
        return len(values) == len(set(values))

    @property
    def is_surjective(self) -> bool:
        """η_p is surjective iff every germ in G_p is in the image."""
        image = set(self.germ_map.values())
        return all(i in image for i in range(len(self.target.germs)))

    @property
    def is_isomorphism(self) -> bool:
        """η_p is an iso iff injective + surjective."""
        return self.is_injective and self.is_surjective

    @property
    def is_total(self) -> bool:
        """η_p is total iff every germ in F_p has an image."""
        return len(self.germ_map) == len(self.source.germs)

    def injectivity_evidence(self) -> Predicate:
        """Predicate witnessing injectivity.

        Conjoins: for all i ≠ j, germ_map(i) ≠ germ_map(j).
        Encoded as pairwise distinctness of image predicates.
        """
        conjuncts: List[Predicate] = []
        indices = list(self.germ_map.keys())
        for a_idx in range(len(indices)):
            for b_idx in range(a_idx + 1, len(indices)):
                i, j = indices[a_idx], indices[b_idx]
                img_i = self.germ_map[i]
                img_j = self.germ_map[j]
                if img_i == img_j:
                    return FalsePred()  # not injective
                # The germs at img_i and img_j are distinct
                g_i = self.target.germs[img_i] if img_i < len(self.target.germs) else None
                g_j = self.target.germs[img_j] if img_j < len(self.target.germs) else None
                if g_i is not None and g_j is not None:
                    # Distinctness: ¬(pred_i ⟺ pred_j)
                    conjuncts.append(
                        DisjunctionPred(disjuncts=(
                            ImplicationPred(
                                antecedent=g_i.predicate,
                                consequent=g_j.predicate,
                            ).negate(),
                            ImplicationPred(
                                antecedent=g_j.predicate,
                                consequent=g_i.predicate,
                            ).negate(),
                        ))
                    )
        if not conjuncts:
            return TruePred()
        return ConjunctionPred(conjuncts=tuple(conjuncts))

    def surjectivity_evidence(self) -> Predicate:
        """Predicate witnessing surjectivity.

        Conjoins: for every g-germ, some f-germ maps to it.
        """
        image = set(self.germ_map.values())
        conjuncts: List[Predicate] = []

        for j in range(len(self.target.germs)):
            if j not in image:
                return FalsePred()  # not surjective
            # Find a preimage
            preimage_indices = [i for i, img in self.germ_map.items() if img == j]
            if preimage_indices:
                preimage_preds = [
                    self.evidence.get(i, TruePred()) for i in preimage_indices
                ]
                conjuncts.append(
                    DisjunctionPred(disjuncts=tuple(preimage_preds))
                    if len(preimage_preds) > 1
                    else preimage_preds[0]
                )

        if not conjuncts:
            return TruePred()
        return ConjunctionPred(conjuncts=tuple(conjuncts))

    def combined_evidence(self) -> Predicate:
        """All evidence for this germ morphism."""
        all_evidence = list(self.evidence.values())
        if not all_evidence:
            return TruePred()
        if len(all_evidence) == 1:
            return all_evidence[0]
        return ConjunctionPred(conjuncts=tuple(all_evidence))


# ═══════════════════════════════════════════════════════════════════════════════
# Stalk equivalence checker
# ═══════════════════════════════════════════════════════════════════════════════


class StalkEquivalenceChecker:
    """Check presheaf isomorphism via stalks.

    **Theorem:** A morphism η: F → G of sheaves on a site S is an
    isomorphism if and only if for every point p of S, the induced
    map η_p: F_p → G_p is a bijection.

    This gives an *alternative* to the global descent approach:
    instead of checking gluing conditions + H¹ triviality, we
    check that stalks are isomorphic point-by-point.

    The checker produces:
    - Per-point verdicts with injectivity/surjectivity evidence
    - An overall verdict
    - Counterexample germs where isomorphism fails
    """

    def __init__(self, site_category: SiteCategory) -> None:
        self._category = site_category
        self._stalk_functor = StalkFunctor(site_category)

    def check_stalkwise(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        morphism_components: Optional[Dict[SiteId, Any]] = None,
    ) -> StalkEquivalenceResult:
        """Check whether F and G are stalk-wise isomorphic.

        If *morphism_components* is given, it should be the components
        of a presheaf morphism η: F → G.  Otherwise, a default
        identity-like morphism is constructed from matching sites.
        """
        all_points = set(presheaf_f.site_ids()) | set(presheaf_g.site_ids())

        point_results: Dict[SiteId, PointStalkResult] = {}
        all_iso = True

        for point in all_points:
            stalk_f = self._stalk_functor.stalk_at(presheaf_f, point)
            stalk_g = self._stalk_functor.stalk_at(presheaf_g, point)

            # Build germ morphism
            if morphism_components is not None:
                germ_morph = self._stalk_functor.stalk_map(
                    presheaf_f, presheaf_g, morphism_components, point,
                )
            else:
                germ_morph = self._default_germ_morphism(stalk_f, stalk_g, point)

            is_iso = germ_morph.is_isomorphism
            if not is_iso:
                all_iso = False

            point_results[point] = PointStalkResult(
                point=point,
                stalk_f=stalk_f,
                stalk_g=stalk_g,
                germ_morphism=germ_morph,
                is_isomorphism=is_iso,
                injectivity_evidence=germ_morph.injectivity_evidence(),
                surjectivity_evidence=germ_morph.surjectivity_evidence(),
            )

        verdict = EquivalenceVerdict.EQUIVALENT if all_iso else EquivalenceVerdict.INEQUIVALENT

        return StalkEquivalenceResult(
            verdict=verdict,
            point_results=point_results,
            all_isomorphic=all_iso,
        )

    def _default_germ_morphism(
        self,
        stalk_f: Stalk,
        stalk_g: Stalk,
        point: SiteId,
    ) -> GermMorphism:
        """Build a default germ morphism by matching predicates."""
        germ_map: Dict[int, int] = {}
        evidence: Dict[int, Predicate] = {}
        used_g: Set[int] = set()

        for i, germ_f in enumerate(stalk_f.germs):
            best_j: Optional[int] = None
            best_pred: Optional[Predicate] = None

            for j, germ_g in enumerate(stalk_g.germs):
                if j in used_g:
                    continue
                agree = germ_f.agrees_with(germ_g)
                # Prefer exact match
                from deppy.equivalence.predicate_eq import predicates_equivalent, PredicateRelation
                if predicates_equivalent(germ_f.predicate, germ_g.predicate).relation == PredicateRelation.EQUIVALENT:
                    best_j = j
                    best_pred = agree
                    break
                # Accept agreement predicate
                if best_j is None:
                    best_j = j
                    best_pred = agree

            if best_j is not None:
                germ_map[i] = best_j
                evidence[i] = best_pred or TruePred()
                used_g.add(best_j)

        return GermMorphism(
            source=stalk_f,
            target=stalk_g,
            germ_map=germ_map,
            evidence=evidence,
            point=point,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Result types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class PointStalkResult:
    """Result of stalk comparison at a single point."""
    point: SiteId
    stalk_f: Stalk
    stalk_g: Stalk
    germ_morphism: GermMorphism
    is_isomorphism: bool
    injectivity_evidence: Predicate
    surjectivity_evidence: Predicate

    @property
    def is_injective(self) -> bool:
        return self.germ_morphism.is_injective

    @property
    def is_surjective(self) -> bool:
        return self.germ_morphism.is_surjective

    @property
    def counterexample_germs(self) -> List[Germ]:
        """Germs in G_p not in the image of η_p (surjectivity failures)."""
        image = set(self.germ_morphism.germ_map.values())
        return [
            g for i, g in enumerate(self.stalk_g.germs)
            if i not in image
        ]


@dataclass
class StalkEquivalenceResult:
    """Result of a stalk-wise equivalence check."""
    verdict: EquivalenceVerdict
    point_results: Dict[SiteId, PointStalkResult] = field(default_factory=dict)
    all_isomorphic: bool = False

    @property
    def failing_points(self) -> List[SiteId]:
        """Points where stalk isomorphism fails."""
        return [
            p for p, r in self.point_results.items()
            if not r.is_isomorphism
        ]

    @property
    def total_germs_f(self) -> int:
        return sum(len(r.stalk_f.germs) for r in self.point_results.values())

    @property
    def total_germs_g(self) -> int:
        return sum(len(r.stalk_g.germs) for r in self.point_results.values())
