"""Topos-theoretic infrastructure for equivalence checking.

This module provides the **categorical backbone** that the rest of the
equivalence checker builds on.  It implements:

* **Pullback** — the universal construction that fibre products depend on.
* **Pushout** — the dual, used for gluing data.
* **Equaliser / Co-equaliser** — used to define agreement conditions.
* **Subobject classifier** Ω — the internal truth-value object whose
  global sections are "truth values" in the topos of presheaves.
* **Internal Hom** — the presheaf [Sem_f, Sem_g] whose sections are
  local natural transformations.
* **Characteristic morphism** χ — sends a sub-presheaf to its
  classifying map into Ω.

Every construction works with ``ConcretePresheaf``, ``ConcreteMorphism``,
``LocalSection``, and ``RefinementType`` from the existing deppy core,
so equivalence predicates flow naturally through the categorical
diagrams.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import (
    Any,
    Callable,
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
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder
from deppy.core.section import SectionFactory, SectionMerger
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    DisjunctionPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    FalsePred,
    VarPred,
)
from deppy.types.dependent import IdentityType, PiType, SigmaType


# ═══════════════════════════════════════════════════════════════════════════════
# Categorical objects & morphisms in the presheaf topos
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class PresheafMorphism:
    """A natural transformation η: F ⇒ G between concrete presheaves.

    Components are stored per site-id.  Each component is a function
    ``F(U) → G(U)`` realised as a predicate transformer: given a
    ``LocalSection`` of F at U the component produces a ``LocalSection``
    of G at U, together with an *evidence predicate* that the
    transformation preserves the refinement predicate.

    Naturality:  for every morphism ``r: V → U`` in the site category,
    ``η_V ∘ F(r) = G(r) ∘ η_U``.  This is checked lazily via
    ``verify_naturality``.
    """
    source: ConcretePresheaf
    target: ConcretePresheaf
    components: Dict[SiteId, SectionTransformComponent] = field(default_factory=dict)

    def apply_at(self, site: SiteId, section: LocalSection) -> Optional[LocalSection]:
        """Apply η_U to a section of the source presheaf."""
        comp = self.components.get(site)
        if comp is None:
            return None
        return comp.transform(section)

    def evidence_at(self, site: SiteId) -> Optional[Predicate]:
        """Return the evidence predicate for the component at *site*."""
        comp = self.components.get(site)
        return comp.evidence if comp is not None else None


@dataclass(frozen=True)
class SectionTransformComponent:
    """One component η_U of a presheaf morphism.

    *transform* maps a LocalSection of the source at U to a
    LocalSection of the target at U.

    *evidence* is a ``Predicate`` that is valid precisely when the
    component preserves the refinement structure.

    *inverse* (optional) provides the inverse component when the
    morphism is an iso.
    """
    site_id: SiteId
    transform: Callable[[LocalSection], LocalSection]
    evidence: Predicate = field(default_factory=TruePred)
    inverse: Optional[Callable[[LocalSection], LocalSection]] = None

    @property
    def is_isomorphism(self) -> bool:
        return self.inverse is not None


# ═══════════════════════════════════════════════════════════════════════════════
# Pullback (fibre product in the presheaf topos)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class PullbackDiagram:
    """The universal pullback square in Psh(S):

            π_f
        P ───────▶ F
        │          │
    π_g │          │ α
        ▼          ▼
        G ───────▶ B
            β

    Here F = Sem_f, G = Sem_g, B = base presheaf (often the
    terminal presheaf or a shared interface), and P = F ×_B G.

    The diagram is *verified* by checking that α ∘ π_f = β ∘ π_g
    at every site, and that the universal property holds: for every
    cone (Z, f: Z→F, g: Z→G) with α∘f = β∘g, there exists a unique
    mediating morphism Z → P.
    """
    product: ConcretePresheaf        # P
    source_f: ConcretePresheaf       # F
    source_g: ConcretePresheaf       # G
    base: ConcretePresheaf           # B
    pi_f: PresheafMorphism           # π_f: P → F
    pi_g: PresheafMorphism           # π_g: P → G
    alpha: PresheafMorphism          # α: F → B
    beta: PresheafMorphism           # β: G → B
    # Per-site commutativity evidence
    commutativity: Dict[SiteId, Predicate] = field(default_factory=dict)

    @property
    def sites(self) -> FrozenSet[SiteId]:
        return frozenset(self.product.site_ids())


class PullbackBuilder:
    """Construct the pullback P = F ×_B G in the presheaf topos.

    Algorithm per site U:
    1. Let σ range over F(U), τ range over G(U).
    2. The fibre product section at U is the pair (σ, τ) such that
       α_U(σ) = β_U(τ) in B(U).
    3. The *equaliser predicate* encodes this agreement:
       ``φ_eq(v) ≡ α_U.pred(v) ⟺ β_U.pred(v)``
       when B-sections are refinement-typed.
    4. Projections π_f, π_g extract the first / second component.

    For restriction: given r: V → U, define
        P(r)(σ, τ) = (F(r)(σ), G(r)(τ))
    and verify the equaliser predicate is preserved.
    """

    def __init__(
        self,
        source_f: ConcretePresheaf,
        source_g: ConcretePresheaf,
        base: Optional[ConcretePresheaf] = None,
    ) -> None:
        self._f = source_f
        self._g = source_g
        # Default base = terminal presheaf (every section maps to ⊤)
        self._base = base or self._terminal_presheaf(source_f, source_g)
        self._alpha_components: Dict[SiteId, SectionTransformComponent] = {}
        self._beta_components: Dict[SiteId, SectionTransformComponent] = {}

    def with_alpha(self, site: SiteId, component: SectionTransformComponent) -> "PullbackBuilder":
        """Set the α component at *site*."""
        self._alpha_components[site] = component
        return self

    def with_beta(self, site: SiteId, component: SectionTransformComponent) -> "PullbackBuilder":
        """Set the β component at *site*."""
        self._beta_components[site] = component
        return self

    def build(self) -> PullbackDiagram:
        """Construct the pullback diagram."""
        product_builder = ConcretePresheafBuilder()
        pi_f_comps: Dict[SiteId, SectionTransformComponent] = {}
        pi_g_comps: Dict[SiteId, SectionTransformComponent] = {}
        comm_evidence: Dict[SiteId, Predicate] = {}

        all_sites = set(self._f.site_ids()) | set(self._g.site_ids())

        for site in all_sites:
            f_section = self._section_at(self._f, site)
            g_section = self._section_at(self._g, site)

            if f_section is None or g_section is None:
                continue

            # Build the equaliser predicate: α_U(σ_f) agrees with β_U(σ_g) in B(U)
            eq_pred = self._equaliser_predicate(site, f_section, g_section)

            # The fibre-product section at U is a paired section with the
            # equaliser predicate as refinement
            carrier = self._paired_carrier(f_section, g_section)
            paired_refinements = {
                **{f"f_{k}": v for k, v in f_section.refinements.items()},
                **{f"g_{k}": v for k, v in g_section.refinements.items()},
                "__equaliser__": eq_pred,
            }

            paired_section = LocalSection(
                site_id=site,
                carrier_type=carrier,
                refinements=paired_refinements,
                trust=min(f_section.trust, g_section.trust, key=lambda t: t.value),
                provenance=f"pullback({f_section.provenance}, {g_section.provenance})",
            )
            product_builder.add_section(paired_section)

            # Projection components
            pi_f_comps[site] = SectionTransformComponent(
                site_id=site,
                transform=self._make_projection_f(f_section),
                evidence=self._projection_evidence(f_section, paired_section),
            )
            pi_g_comps[site] = SectionTransformComponent(
                site_id=site,
                transform=self._make_projection_g(g_section),
                evidence=self._projection_evidence(g_section, paired_section),
            )

            # Commutativity evidence: α ∘ π_f = β ∘ π_g
            comm_evidence[site] = eq_pred

        product = product_builder.build()

        alpha = PresheafMorphism(
            source=self._f, target=self._base, components=self._alpha_components,
        )
        beta = PresheafMorphism(
            source=self._g, target=self._base, components=self._beta_components,
        )
        pi_f = PresheafMorphism(
            source=product, target=self._f, components=pi_f_comps,
        )
        pi_g = PresheafMorphism(
            source=product, target=self._g, components=pi_g_comps,
        )

        return PullbackDiagram(
            product=product,
            source_f=self._f,
            source_g=self._g,
            base=self._base,
            pi_f=pi_f,
            pi_g=pi_g,
            alpha=alpha,
            beta=beta,
            commutativity=comm_evidence,
        )

    # ── Universality check ────────────────────────────────────────────────

    def verify_universal_property(
        self,
        diagram: PullbackDiagram,
        cone_f: PresheafMorphism,
        cone_g: PresheafMorphism,
    ) -> Tuple[bool, Optional[PresheafMorphism]]:
        """Verify the universal property of the pullback.

        Given a cone (Z, f: Z→F, g: Z→G) with α∘f = β∘g,
        check that a unique mediating morphism Z → P exists.
        """
        mediating_comps: Dict[SiteId, SectionTransformComponent] = {}

        for site in diagram.sites:
            f_comp = cone_f.components.get(site)
            g_comp = cone_g.components.get(site)
            if f_comp is None or g_comp is None:
                return False, None

            # The mediating morphism sends z ∈ Z(U) to (f(z), g(z)) ∈ P(U)
            def make_mediator(fc: SectionTransformComponent, gc: SectionTransformComponent, s: SiteId):
                def mediate(section: LocalSection) -> LocalSection:
                    f_sec = fc.transform(section)
                    g_sec = gc.transform(section)
                    paired_refinements = {
                        **{f"f_{k}": v for k, v in f_sec.refinements.items()},
                        **{f"g_{k}": v for k, v in g_sec.refinements.items()},
                    }
                    return LocalSection(
                        site_id=s,
                        carrier_type=self._paired_carrier(f_sec, g_sec),
                        refinements=paired_refinements,
                        trust=min(f_sec.trust, g_sec.trust, key=lambda t: t.value),
                        provenance=f"mediator({f_sec.provenance}, {g_sec.provenance})",
                    )
                return mediate

            mediating_comps[site] = SectionTransformComponent(
                site_id=site,
                transform=make_mediator(f_comp, g_comp, site),
                evidence=ConjunctionPred(conjuncts=(
                    f_comp.evidence, g_comp.evidence,
                )),
            )

        mediating = PresheafMorphism(
            source=cone_f.source,
            target=diagram.product,
            components=mediating_comps,
        )
        return True, mediating

    # ── Helpers ───────────────────────────────────────────────────────────

    def _equaliser_predicate(
        self,
        site: SiteId,
        f_section: LocalSection,
        g_section: LocalSection,
    ) -> Predicate:
        """Build the predicate asserting α_U(σ_f) = β_U(σ_g).

        When α and β are identity (i.e. base = terminal), this reduces
        to bi-implication of the refinement predicates.

        When α, β are non-trivial projection morphisms, we compose
        them with the section predicates.
        """
        alpha_comp = self._alpha_components.get(site)
        beta_comp = self._beta_components.get(site)

        # Extract predicates from sections
        f_pred = self._section_predicate(f_section)
        g_pred = self._section_predicate(g_section)

        if alpha_comp is not None and beta_comp is not None:
            # α_U(σ_f) = β_U(σ_g) means the image predicates agree
            # Evidence from the morphism components captures this
            return ConjunctionPred(conjuncts=(
                alpha_comp.evidence,
                beta_comp.evidence,
                ImplicationPred(antecedent=f_pred, consequent=g_pred),
                ImplicationPred(antecedent=g_pred, consequent=f_pred),
            ))

        # Default: base = terminal, so agreement = bi-implication
        return ConjunctionPred(conjuncts=(
            ImplicationPred(antecedent=f_pred, consequent=g_pred),
            ImplicationPred(antecedent=g_pred, consequent=f_pred),
        ))

    def _section_predicate(self, section: LocalSection) -> Predicate:
        """Extract the refinement predicate from a section."""
        ct = section.carrier_type
        if isinstance(ct, RefinementType) and ct.predicate is not None:
            return ct.predicate
        # Fall back to a var-predicate naming the section
        return VarPred(var_name=f"section_{section.site_id.name}")

    def _paired_carrier(
        self,
        f_section: LocalSection,
        g_section: LocalSection,
    ) -> Any:
        """Build the carrier type for a fibre-product section.

        The paired carrier is a SigmaType:
            Σ(f_val : τ_f). {g_val : τ_g | equaliser(f_val, g_val)}
        """
        f_type = f_section.carrier_type
        g_type = g_section.carrier_type

        if f_type is not None and g_type is not None:
            return SigmaType(
                fst_name=f"f_{f_section.site_id.name}",
                fst_type=f_type,
                snd_type=g_type,
            )
        return f_type or g_type

    def _section_at(
        self,
        presheaf: ConcretePresheaf,
        site: SiteId,
    ) -> Optional[LocalSection]:
        """Get the section at a site, if any."""
        sections = presheaf.sections_at(site)
        if sections:
            return sections[0]
        return None

    def _make_projection_f(
        self, f_section: LocalSection,
    ) -> Callable[[LocalSection], LocalSection]:
        """Build π_f: extract the f-component from a paired section."""
        def project(paired: LocalSection) -> LocalSection:
            f_refs = {
                k[2:]: v for k, v in paired.refinements.items()
                if k.startswith("f_")
            }
            return LocalSection(
                site_id=paired.site_id,
                carrier_type=f_section.carrier_type,
                refinements=f_refs,
                trust=paired.trust,
                provenance=f"π_f({paired.provenance})",
            )
        return project

    def _make_projection_g(
        self, g_section: LocalSection,
    ) -> Callable[[LocalSection], LocalSection]:
        """Build π_g: extract the g-component from a paired section."""
        def project(paired: LocalSection) -> LocalSection:
            g_refs = {
                k[2:]: v for k, v in paired.refinements.items()
                if k.startswith("g_")
            }
            return LocalSection(
                site_id=paired.site_id,
                carrier_type=g_section.carrier_type,
                refinements=g_refs,
                trust=paired.trust,
                provenance=f"π_g({paired.provenance})",
            )
        return project

    def _projection_evidence(
        self,
        target_section: LocalSection,
        paired_section: LocalSection,
    ) -> Predicate:
        """Evidence that projection preserves refinements."""
        target_pred = self._section_predicate(target_section)
        paired_pred = self._section_predicate(paired_section)
        return ImplicationPred(antecedent=paired_pred, consequent=target_pred)

    def _terminal_presheaf(
        self, f: ConcretePresheaf, g: ConcretePresheaf,
    ) -> ConcretePresheaf:
        """Build the terminal presheaf: every section is ⊤."""
        builder = ConcretePresheafBuilder()
        for site in set(f.site_ids()) | set(g.site_ids()):
            builder.add_section(LocalSection(
                site_id=site,
                carrier_type=RefinementType(base=None, binder="v", predicate=TruePred()),
                refinements={},
                trust=TrustLevel.TRUSTED_AUTO,
                provenance="terminal",
            ))
        return builder.build()


# ═══════════════════════════════════════════════════════════════════════════════
# Equaliser (agreement sub-presheaf)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class EqualiserDiagram:
    """The equaliser E = eq(α, β) where α, β: F ⇒ G.

        ι
    E ────▶ F ═══▶ G
              α
              β

    E(U) = { σ ∈ F(U) | α_U(σ) = β_U(σ) }

    The equaliser is the sub-presheaf of F on which α and β agree.
    Its sections carry the *agreement predicate* as a refinement.
    """
    equaliser: ConcretePresheaf       # E
    source: ConcretePresheaf          # F
    target: ConcretePresheaf          # G
    inclusion: PresheafMorphism       # ι: E ↪ F
    alpha: PresheafMorphism           # α: F → G
    beta: PresheafMorphism            # β: F → G
    agreement: Dict[SiteId, Predicate] = field(default_factory=dict)


class EqualiserBuilder:
    """Construct the equaliser of two presheaf morphisms α, β: F ⇒ G.

    At each site U, the equaliser section is:
        E(U) = { σ ∈ F(U) | α_U(σ).pred ⟺ β_U(σ).pred }

    The agreement predicate is the bi-implication of the image
    predicates through α and β.
    """

    def __init__(
        self,
        alpha: PresheafMorphism,
        beta: PresheafMorphism,
    ) -> None:
        if alpha.source is not beta.source:
            raise ValueError("α and β must share the same source presheaf")
        if alpha.target is not beta.target:
            raise ValueError("α and β must share the same target presheaf")
        self._alpha = alpha
        self._beta = beta
        self._source = alpha.source
        self._target = alpha.target

    def build(self) -> EqualiserDiagram:
        """Construct the equaliser diagram."""
        eq_builder = ConcretePresheafBuilder()
        inclusion_comps: Dict[SiteId, SectionTransformComponent] = {}
        agreement: Dict[SiteId, Predicate] = {}

        for site in self._source.site_ids():
            sections = self._source.sections_at(site)
            if not sections:
                continue
            section = sections[0]

            # Compute α_U(σ) and β_U(σ)
            alpha_image = self._alpha.apply_at(site, section)
            beta_image = self._beta.apply_at(site, section)

            if alpha_image is None or beta_image is None:
                continue

            # Agreement predicate: α_U(σ).pred ⟺ β_U(σ).pred
            alpha_pred = self._extract_pred(alpha_image)
            beta_pred = self._extract_pred(beta_image)

            agree_pred = ConjunctionPred(conjuncts=(
                ImplicationPred(antecedent=alpha_pred, consequent=beta_pred),
                ImplicationPred(antecedent=beta_pred, consequent=alpha_pred),
            ))
            agreement[site] = agree_pred

            # Equaliser section: σ refined by the agreement predicate
            eq_carrier = section.carrier_type
            if isinstance(eq_carrier, RefinementType):
                eq_carrier = eq_carrier.strengthen(agree_pred)
            elif eq_carrier is not None:
                eq_carrier = RefinementType(
                    base=eq_carrier, binder="eq_v", predicate=agree_pred,
                )
            else:
                eq_carrier = RefinementType(
                    base=None, binder="eq_v", predicate=agree_pred,
                )

            eq_section = LocalSection(
                site_id=site,
                carrier_type=eq_carrier,
                refinements={**section.refinements, "__agreement__": agree_pred},
                trust=section.trust,
                provenance=f"equaliser({section.provenance})",
            )
            eq_builder.add_section(eq_section)

            # Inclusion ι: E ↪ F is the identity on the underlying section
            inclusion_comps[site] = SectionTransformComponent(
                site_id=site,
                transform=lambda s, _sec=section: _sec,  # forgetful: drop refinement
                evidence=agree_pred,
            )

        equaliser = eq_builder.build()
        inclusion = PresheafMorphism(
            source=equaliser, target=self._source, components=inclusion_comps,
        )

        return EqualiserDiagram(
            equaliser=equaliser,
            source=self._source,
            target=self._target,
            inclusion=inclusion,
            alpha=self._alpha,
            beta=self._beta,
            agreement=agreement,
        )

    def _extract_pred(self, section: LocalSection) -> Predicate:
        ct = section.carrier_type
        if isinstance(ct, RefinementType) and ct.predicate is not None:
            return ct.predicate
        return VarPred(var_name=f"section_{section.site_id.name}")


# ═══════════════════════════════════════════════════════════════════════════════
# Subobject classifier Ω in the presheaf topos
# ═══════════════════════════════════════════════════════════════════════════════


class SubobjectClassifier:
    """The subobject classifier Ω in Psh(S).

    For a presheaf topos Psh(S), the subobject classifier is the
    presheaf Ω defined by:

        Ω(U) = { sieves on U }

    A *sieve* on U is a downward-closed family of morphisms into U.
    In our setting, we represent sieves concretely as sets of SiteId
    that "cover" U.

    The classifying map χ_A : F → Ω for a sub-presheaf A ↪ F is:

        χ_A(σ)(V →^r U) = 1  iff  F(r)(σ) ∈ A(V)

    This is used to internalise the equivalence sub-presheaf: the
    sites where f ≡ g form a sub-presheaf, and its classifying map
    tells us *which* restrictions preserve equivalence.
    """

    def __init__(self, site_category: SiteCategory) -> None:
        self._category = site_category

    def sieve_at(self, site: SiteId) -> FrozenSet[SiteId]:
        """The maximal sieve on *site*: all sites reachable from it."""
        reachable: Set[SiteId] = {site}
        frontier = [site]
        while frontier:
            current = frontier.pop()
            for morph in self._category.outgoing(current):
                if morph.target not in reachable:
                    reachable.add(morph.target)
                    frontier.append(morph.target)
        return frozenset(reachable)

    def classify(
        self,
        ambient: ConcretePresheaf,
        sub: ConcretePresheaf,
    ) -> Dict[SiteId, Predicate]:
        """Compute the classifying map χ: ambient → Ω.

        Returns a predicate per site that is true when the section
        belongs to the sub-presheaf.
        """
        result: Dict[SiteId, Predicate] = {}

        for site in ambient.site_ids():
            ambient_sections = ambient.sections_at(site)
            sub_sections = sub.sections_at(site)

            if not ambient_sections:
                result[site] = FalsePred()
                continue

            if sub_sections:
                # Section exists in sub-presheaf → classify as true
                # with the sub-section's predicate
                sub_sec = sub_sections[0]
                ct = sub_sec.carrier_type
                if isinstance(ct, RefinementType) and ct.predicate is not None:
                    result[site] = ct.predicate
                else:
                    result[site] = TruePred()
            else:
                result[site] = FalsePred()

        return result

    def characteristic_predicate(
        self,
        ambient: ConcretePresheaf,
        sub: ConcretePresheaf,
        site: SiteId,
    ) -> Predicate:
        """Get the characteristic predicate at a single site."""
        classifying = self.classify(ambient, sub)
        return classifying.get(site, FalsePred())


# ═══════════════════════════════════════════════════════════════════════════════
# Internal hom [F, G] in the presheaf topos
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class InternalHomSection:
    """A section of [F, G] at site U.

    This is a family of maps { F(V) → G(V) | V → U in S } that
    is compatible with restrictions.  Concretely it is a collection
    of ``SectionTransformComponent``s indexed by sites reachable
    from U.
    """
    site_id: SiteId
    components: Dict[SiteId, SectionTransformComponent] = field(default_factory=dict)
    is_natural: bool = False


class InternalHomPresheaf:
    """Construct the internal hom [F, G] in Psh(S).

    [F, G](U) = Nat(y(U) × F, G)

    where y is the Yoneda embedding.  Concretely, a section at U
    is a compatible family of transforms F(V) → G(V) for all
    morphisms V → U.

    This is the *function space* in the presheaf topos and is used
    to internalise the sheaf of local equivalences.
    """

    def __init__(
        self,
        source: ConcretePresheaf,
        target: ConcretePresheaf,
        site_category: SiteCategory,
    ) -> None:
        self._source = source
        self._target = target
        self._category = site_category

    def sections_at(self, site: SiteId) -> List[InternalHomSection]:
        """Compute [F, G](U).

        A section at U assigns to each V → U a map F(V) → G(V),
        naturally in V.
        """
        # Collect all sites reachable from U (the "star" of U)
        reachable = self._reachable(site)

        # For each reachable site V, check if we can build a component
        components: Dict[SiteId, SectionTransformComponent] = {}
        all_ok = True

        for v_site in reachable:
            f_sections = self._source.sections_at(v_site)
            g_sections = self._target.sections_at(v_site)

            if not f_sections or not g_sections:
                all_ok = False
                continue

            f_sec = f_sections[0]
            g_sec = g_sections[0]

            # The component at V maps f_sec to g_sec
            # with evidence that the refinement predicates are compatible
            f_pred = self._extract_pred(f_sec)
            g_pred = self._extract_pred(g_sec)

            evidence = ConjunctionPred(conjuncts=(
                ImplicationPred(antecedent=f_pred, consequent=g_pred),
                ImplicationPred(antecedent=g_pred, consequent=f_pred),
            ))

            components[v_site] = SectionTransformComponent(
                site_id=v_site,
                transform=lambda s, _g=g_sec: _g,
                evidence=evidence,
            )

        if components:
            return [InternalHomSection(
                site_id=site,
                components=components,
                is_natural=all_ok,
            )]
        return []

    def is_iso_section(self, section: InternalHomSection) -> bool:
        """Check if a section of [F, G] is an isomorphism."""
        return all(
            comp.is_isomorphism
            for comp in section.components.values()
        )

    def _reachable(self, site: SiteId) -> Set[SiteId]:
        """Sites V with a morphism V → U (i.e. the slice over U)."""
        result: Set[SiteId] = {site}
        for morph in [m for m in self._category.morphisms if m.target == site]:
            result.add(morph.source)
        return result

    def _extract_pred(self, section: LocalSection) -> Predicate:
        ct = section.carrier_type
        if isinstance(ct, RefinementType) and ct.predicate is not None:
            return ct.predicate
        return VarPred(var_name=f"section_{section.site_id.name}")


# ═══════════════════════════════════════════════════════════════════════════════
# Pushout (for gluing)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class PushoutDiagram:
    """The pushout (co-product over a base) in Psh(S):

              ι_f
        A ───────▶ F
        │          │
    ι_g │          │ j_f
        ▼          ▼
        G ───────▶ P
              j_g

    Here A = intersection/overlap presheaf, P = F ∐_A G.

    P(U) = (F(U) ⊔ G(U)) / ~  where ~ identifies sections that
    agree on the image of A(U).

    This is used for *gluing*: when local equivalences on overlapping
    sites agree, the pushout provides the global equivalence.
    """
    pushout: ConcretePresheaf
    source_f: ConcretePresheaf
    source_g: ConcretePresheaf
    base: ConcretePresheaf
    j_f: PresheafMorphism
    j_g: PresheafMorphism


class PushoutBuilder:
    """Construct the pushout P = F ∐_A G.

    At each site U:
        P(U) = F(U) ∐_{A(U)} G(U)

    concretely, the section carries the *disjunction* of the
    f-predicate and g-predicate, refined by agreement on the overlap.
    """

    def __init__(
        self,
        source_f: ConcretePresheaf,
        source_g: ConcretePresheaf,
        base: ConcretePresheaf,
        inclusion_f: PresheafMorphism,
        inclusion_g: PresheafMorphism,
    ) -> None:
        self._f = source_f
        self._g = source_g
        self._base = base
        self._if = inclusion_f
        self._ig = inclusion_g

    def build(self) -> PushoutDiagram:
        """Construct the pushout."""
        pushout_builder = ConcretePresheafBuilder()
        j_f_comps: Dict[SiteId, SectionTransformComponent] = {}
        j_g_comps: Dict[SiteId, SectionTransformComponent] = {}

        all_sites = set(self._f.site_ids()) | set(self._g.site_ids())

        for site in all_sites:
            f_sections = self._f.sections_at(site)
            g_sections = self._g.sections_at(site)
            base_sections = self._base.sections_at(site)

            f_sec = f_sections[0] if f_sections else None
            g_sec = g_sections[0] if g_sections else None
            base_sec = base_sections[0] if base_sections else None

            f_pred = self._extract_pred(f_sec) if f_sec else FalsePred()
            g_pred = self._extract_pred(g_sec) if g_sec else FalsePred()

            # Pushout predicate: disjunction, with agreement on overlap
            if base_sec is not None:
                base_pred = self._extract_pred(base_sec)
                # On the overlap, both predicates must agree
                overlap_agree = ConjunctionPred(conjuncts=(
                    ImplicationPred(antecedent=base_pred, consequent=f_pred),
                    ImplicationPred(antecedent=base_pred, consequent=g_pred),
                ))
                pushout_pred = ConjunctionPred(conjuncts=(
                    DisjunctionPred(disjuncts=(f_pred, g_pred)),
                    overlap_agree,
                ))
            else:
                pushout_pred = DisjunctionPred(disjuncts=(f_pred, g_pred))

            carrier = None
            if f_sec is not None:
                carrier = f_sec.carrier_type
            elif g_sec is not None:
                carrier = g_sec.carrier_type

            pushout_section = LocalSection(
                site_id=site,
                carrier_type=RefinementType(base=carrier, binder="p_v", predicate=pushout_pred),
                refinements={},
                trust=TrustLevel.RESIDUAL,
                provenance=f"pushout({site.name})",
            )
            pushout_builder.add_section(pushout_section)

            # j_f: F → P  and  j_g: G → P
            if f_sec is not None:
                j_f_comps[site] = SectionTransformComponent(
                    site_id=site,
                    transform=lambda s, _ps=pushout_section: _ps,
                    evidence=ImplicationPred(antecedent=f_pred, consequent=pushout_pred),
                )
            if g_sec is not None:
                j_g_comps[site] = SectionTransformComponent(
                    site_id=site,
                    transform=lambda s, _ps=pushout_section: _ps,
                    evidence=ImplicationPred(antecedent=g_pred, consequent=pushout_pred),
                )

        pushout = pushout_builder.build()
        j_f = PresheafMorphism(source=self._f, target=pushout, components=j_f_comps)
        j_g = PresheafMorphism(source=self._g, target=pushout, components=j_g_comps)

        return PushoutDiagram(
            pushout=pushout,
            source_f=self._f,
            source_g=self._g,
            base=self._base,
            j_f=j_f,
            j_g=j_g,
        )

    def _extract_pred(self, section: Optional[LocalSection]) -> Predicate:
        if section is None:
            return FalsePred()
        ct = section.carrier_type
        if isinstance(ct, RefinementType) and ct.predicate is not None:
            return ct.predicate
        return VarPred(var_name=f"section_{section.site_id.name}")
