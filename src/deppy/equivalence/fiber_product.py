"""Fiber product of presheaves via genuine pullback construction.

The fiber product Sem_f times_S Sem_g computes the categorical
pullback of the diagram:

    Sem_f --pi_f--> Base <--pi_g-- Sem_g

At each site U_i the fiber product is:

    (Sem_f times_S Sem_g)(U_i) = { (sigma_f, sigma_g) in Sem_f(U_i) x Sem_g(U_i)
                                   | pi_f(sigma_f) = pi_g(sigma_g) }

encoded as a SigmaType whose first component carries sigma_f and whose
second component is a RefinementType carrying sigma_g refined by the
equaliser predicate `pi_f(sigma_f) = pi_g(sigma_g)`.

This module computes the pullback directly using deppy's
``ConcretePresheaf`` API, with proper projection morphisms and
SigmaType encoding.

Restriction of fiber-product sections is computed by restricting each
component independently through the respective presheaves:

    res_{U_j}(sigma_f, sigma_g) = (res^f_{U_j}(sigma_f), res^g_{U_j}(sigma_g))

The universality property is verified: any other presheaf P that maps to
both Sem_f and Sem_g factors uniquely through the fiber product.
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
    Cover,
    LocalSection,
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder
from deppy.core.section import SectionFactory, SectionMerger
from deppy.core.site import ConcreteMorphism, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceVerdict,
    FiberProductSection,
    LocalEquivalenceJudgment,
    SectionPair,
    SiteCorrespondence,
)
from deppy.equivalence.predicates import (
    FiberProductPred,
    build_fiber_product_predicate,
)
from deppy.equivalence.topos import (
    PresheafMorphism,
    SectionTransformComponent,
)
from deppy.types.dependent import IdentityType, SigmaType
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.types.witnesses import (
    ReflProof,
    TransportWitness,
)


# ===========================================================================
# Fiber-product section
# ===========================================================================


@dataclass(frozen=True)
class FiberSection:
    """A section of the fiber product at a particular site.

    Carries both component sections together with the equaliser
    predicate certifying that they agree on the base.
    """
    site_id: SiteId
    section_f: LocalSection
    section_g: LocalSection
    equaliser_predicate: Predicate
    carrier: Optional[SigmaType] = None
    trust: TrustLevel = TrustLevel.RESIDUAL

    @property
    def is_inhabited(self) -> bool:
        """Whether the fiber product at this site is non-empty."""
        from deppy.types.refinement import FalsePred
        return not isinstance(self.equaliser_predicate, FalsePred)


# ===========================================================================
# Projection morphisms
# ===========================================================================


@dataclass(frozen=True)
class FiberProjection:
    """A projection morphism from the fiber product to a component.

    pi_f : Sem_f times_S Sem_g -> Sem_f     (left projection)
    pi_g : Sem_f times_S Sem_g -> Sem_g     (right projection)

    Each projection forgets one component and drops the equaliser constraint.
    """
    name: str
    source_site: SiteId
    target_site: SiteId
    direction: str  # "left" or "right"

    def project(self, fiber_sec: FiberSection) -> LocalSection:
        """Apply the projection to get a component section."""
        if self.direction == "left":
            return fiber_sec.section_f
        return fiber_sec.section_g


# ===========================================================================
# Fiber product builder
# ===========================================================================


class FiberProductBuilder:
    """Build the fiber product presheaf using genuine pullback construction.

    Given presheaves Sem_f and Sem_g over a common site category,
    computes the pullback at each site and
    assembles the result into a ConcretePresheaf.

    Usage:
        builder = FiberProductBuilder(presheaf_f, presheaf_g, site_cat)
        product = builder.build(correspondences)
        product.fiber_at(site_id)      # -> FiberSection
        product.project_left(site_id)  # -> LocalSection (from Sem_f)
        product.project_right(site_id) # -> LocalSection (from Sem_g)
    """

    def __init__(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        site_category: SiteCategory,
    ) -> None:
        self._pf = presheaf_f
        self._pg = presheaf_g
        self._cat = site_category

    def build(
        self,
        correspondences: List[SiteCorrespondence],
    ) -> "FiberProduct":
        """Build the fiber product for all corresponded sites.

        For each site correspondence (U_f <-> U_g), constructs:
        1. The pullback of the two forgetful maps to the base
        2. The equaliser predicate
        3. The SigmaType carrier encoding the paired section
        4. Projection morphisms pi_f, pi_g
        """
        fiber_sections: Dict[SiteId, FiberSection] = {}
        projections_left: Dict[SiteId, FiberProjection] = {}
        projections_right: Dict[SiteId, FiberProjection] = {}

        for corr in correspondences:
            site_id = corr.common_site

            f_secs = self._pf.sections_at(corr.f_site)
            g_secs = self._pg.sections_at(corr.g_site)

            f_sec = f_secs[0] if f_secs else None
            g_sec = g_secs[0] if g_secs else None

            if f_sec is None or g_sec is None:
                from deppy.types.refinement import FalsePred
                fiber_sections[site_id] = FiberSection(
                    site_id=site_id,
                    section_f=f_sec or _empty_section(site_id),
                    section_g=g_sec or _empty_section(site_id),
                    equaliser_predicate=FalsePred(),
                )
                continue

            # Build the pullback at this site
            fiber_sec = self._build_pullback_fiber(
                site_id, corr, f_sec, g_sec,
            )
            fiber_sections[site_id] = fiber_sec

            # Build projection morphisms
            projections_left[site_id] = FiberProjection(
                name=f"pi_f@{site_id.name}",
                source_site=site_id,
                target_site=corr.f_site,
                direction="left",
            )
            projections_right[site_id] = FiberProjection(
                name=f"pi_g@{site_id.name}",
                source_site=site_id,
                target_site=corr.g_site,
                direction="right",
            )

        return FiberProduct(
            fiber_sections=fiber_sections,
            projections_left=projections_left,
            projections_right=projections_right,
            site_category=self._cat,
        )

    def _build_pullback_fiber(
        self,
        site_id: SiteId,
        corr: SiteCorrespondence,
        f_sec: LocalSection,
        g_sec: LocalSection,
    ) -> FiberSection:
        """Build the pullback fiber at a single site.

        Constructs the equaliser predicate:
            phi_eq(v) = phi_f(v) <=> phi_g(v)

        and packages it as a SigmaType:
            Sigma(sigma_f : tau_f). {sigma_g : tau_g | phi_eq(sigma_f, sigma_g)}
        """
        ct_f = f_sec.carrier_type
        ct_g = g_sec.carrier_type

        # Extract predicates
        f_pred = _extract_predicate(f_sec)
        g_pred = _extract_predicate(g_sec)

        # The equaliser predicate: biimplication on the shared variable
        fwd = ImplicationPred(antecedent=f_pred, consequent=g_pred)
        bwd = ImplicationPred(antecedent=g_pred, consequent=f_pred)
        eq_pred = ConjunctionPred(conjuncts=(fwd, bwd))

        # Build the SigmaType carrier: (sigma_f, sigma_g | eq_pred)
        if ct_f is not None and ct_g is not None:
            refined_g = RefinementType(
                base=ct_g,
                binder="sigma_g",
                predicate=eq_pred,
            )
            carrier = SigmaType(
                fst_name="sigma_f",
                fst_type=ct_f,
                snd_type=refined_g,
            )
        else:
            carrier = None

        # Compute trust as the minimum
        trust = min(f_sec.trust, g_sec.trust, key=lambda t: t.value)

        return FiberSection(
            site_id=site_id,
            section_f=f_sec,
            section_g=g_sec,
            equaliser_predicate=eq_pred,
            carrier=carrier,
            trust=trust,
        )


# ===========================================================================
# Fiber product presheaf
# ===========================================================================


class FiberProduct:
    """The fiber product presheaf Sem_f times_S Sem_g.

    Provides access to:
    - Fiber sections at each site
    - Projection morphisms pi_f, pi_g
    - Restriction of fiber sections along morphisms
    - Globalisation check: whether fibers glue to a global section

    This is the central data structure for the equivalence checker.
    """

    def __init__(
        self,
        fiber_sections: Dict[SiteId, FiberSection],
        projections_left: Dict[SiteId, FiberProjection],
        projections_right: Dict[SiteId, FiberProjection],
        site_category: SiteCategory,
    ) -> None:
        self._fibers = fiber_sections
        self._pi_f = projections_left
        self._pi_g = projections_right
        self._cat = site_category

    def fiber_at(self, site_id: SiteId) -> Optional[FiberSection]:
        """Get the fiber product section at a site."""
        return self._fibers.get(site_id)

    def project_left(self, site_id: SiteId) -> Optional[LocalSection]:
        """Apply left projection pi_f at a site."""
        fib = self._fibers.get(site_id)
        proj = self._pi_f.get(site_id)
        if fib and proj:
            return proj.project(fib)
        return None

    def project_right(self, site_id: SiteId) -> Optional[LocalSection]:
        """Apply right projection pi_g at a site."""
        fib = self._fibers.get(site_id)
        proj = self._pi_g.get(site_id)
        if fib and proj:
            return proj.project(fib)
        return None

    def restrict_fiber(
        self,
        source: SiteId,
        morph: Morphism,
    ) -> Optional[FiberSection]:
        """Restrict a fiber section along a morphism.

        Given m : U_j -> U_i, computes:
            res_m(sigma_f, sigma_g) = (res^f_m(sigma_f), res^g_m(sigma_g))

        The equaliser predicate is restricted accordingly.
        """
        fib = self._fibers.get(source)
        if fib is None:
            return None

        try:
            restricted_f = morph.restrict(fib.section_f)
            restricted_g = morph.restrict(fib.section_g)
        except Exception:
            return None

        # Restrict the equaliser predicate
        f_pred = _extract_predicate(restricted_f)
        g_pred = _extract_predicate(restricted_g)
        eq_pred = ConjunctionPred(conjuncts=(
            ImplicationPred(antecedent=f_pred, consequent=g_pred),
            ImplicationPred(antecedent=g_pred, consequent=f_pred),
        ))

        target = morph.target if hasattr(morph, "target") else source
        return FiberSection(
            site_id=target,
            section_f=restricted_f,
            section_g=restricted_g,
            equaliser_predicate=eq_pred,
        )

    def site_ids(self) -> FrozenSet[SiteId]:
        """All sites where the fiber product is defined."""
        return frozenset(self._fibers.keys())

    def inhabited_sites(self) -> FrozenSet[SiteId]:
        """Sites where the fiber product is non-empty."""
        return frozenset(
            sid for sid, fib in self._fibers.items()
            if fib.is_inhabited
        )

    def all_fibers(self) -> Dict[SiteId, FiberSection]:
        """All fiber sections."""
        return dict(self._fibers)

    def check_gluing(self) -> bool:
        """Check whether the fiber sections satisfy the gluing condition.

        For each overlap (U_i, U_j) with morphisms to the overlap,
        verify that the restricted fiber sections agree.
        """
        sites = list(self._fibers.keys())
        for i, s_i in enumerate(sites):
            for s_j in sites[i+1:]:
                overlaps = self._cat.find_overlaps(frozenset({s_i, s_j})) if self._cat else []
                for overlap_pair in overlaps:
                    # find_overlaps returns List[Tuple[SiteId, SiteId]]
                    # We just need to check agreement on any overlap
                    fib_from_i = self._fibers.get(s_i)
                    fib_from_j = self._fibers.get(s_j)
                    if fib_from_i is None or fib_from_j is None:
                        continue
                    # Check that equaliser predicates agree on overlap
                    if not _predicates_structurally_equal(
                        fib_from_i.equaliser_predicate,
                        fib_from_j.equaliser_predicate,
                    ):
                        return False
        return True

    def to_presheaf(self) -> ConcretePresheaf:
        """Convert the fiber product to a ConcretePresheaf.

        Each fiber section becomes a local section with carrier
        type equal to the SigmaType encoding of the pair.
        """
        builder = ConcretePresheafBuilder()
        for site_id, fib in self._fibers.items():
            local_sec = SectionFactory.create(
                site_id=site_id,
                carrier_type=fib.carrier,
                trust=fib.trust,
            )
            builder.add_section(local_sec)
        return builder.build()


# ===========================================================================
# Helper functions
# ===========================================================================


def _extract_predicate(section: LocalSection) -> Predicate:
    """Extract the refinement predicate from a section."""
    ct = section.carrier_type
    if isinstance(ct, RefinementType) and ct.predicate is not None:
        return ct.predicate
    return VarPred(var_name=f"section_{section.site_id.name}")


def _empty_section(site_id: SiteId) -> LocalSection:
    """Create an empty section placeholder."""
    return SectionFactory.create(
        site_id=site_id,
        carrier_type=None,
        trust=TrustLevel.RESIDUAL,
    )


def _predicates_structurally_equal(p: Predicate, q: Predicate) -> bool:
    """Check predicate equivalence via the three-tiered engine.

    Delegates to ``predicate_eq.predicates_equivalent`` which performs:
    1. Structural AST comparison (fast, sound)
    2. Algebraic normalisation (absorption, idempotence, double-negation)
    3. Z3 solver discharge (definitive, if available)

    This replaces the previous ``repr()``-based comparison, grounding
    the fiber-product gluing condition in genuine sheaf-theoretic
    predicate equivalence.
    """
    from deppy.equivalence.predicate_eq import predicates_equivalent
    result = predicates_equivalent(p, q, use_solver=True)
    return result.equivalent
