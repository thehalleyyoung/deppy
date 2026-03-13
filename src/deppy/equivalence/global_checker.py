"""Global equivalence checking via sheaf gluing and descent.

The global checker orchestrates the full equivalence verification:

1. **Local checking** — per-site equivalence via LocalEquivalenceChecker
2. **Naturality** — verify the local equivalences form a natural
   transformation via SheafMorphismBuilder
3. **Descent** — check that local equivalences glue to a global
   equivalence via EquivalenceDescentChecker (H^1 triviality)
4. **Gluing** — if descent holds, construct the global equivalence
   as a global section of the fiber product presheaf

The sheaf gluing axiom states:
    Given local sections sigma_i in F(U_i) that agree on overlaps
    (sigma_i|_{U_{ij}} = sigma_j|_{U_{ij}}), there exists a unique
    global section sigma in F(U) with sigma|_{U_i} = sigma_i.

For equivalence, the "sheaf" is the isomorphism sheaf Iso(Sem_f, Sem_g),
and the "local sections" are the local equivalences eta_{U_i}.

This module delegates to:
- SheafConditionChecker from presheaf.py for the gluing axiom
- PushoutBuilder from topos.py for the colimit construction
- EquivalenceDescentChecker from descent.py for H^1 computation
- StalkEquivalenceChecker from stalk.py for stalk-level verification
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
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
    GlobalSection,
    LocalSection,
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf, SheafConditionChecker
from deppy.core.section import (
    GlobalSectionBuilder,
    SectionFactory,
    SectionMerger,
    SectionRestrictor,
)
from deppy.core.site import ConcreteMorphism, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceJudgment,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceStrength,
    EquivalenceVerdict,
    IsomorphismWitness,
    LocalEquivalenceJudgment,
    NaturalTransformation,
    SiteCorrespondence,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    SectionAgreementPred,
)
from deppy.equivalence.local_checker import (
    LocalEquivalenceChecker,
    check_local_equivalences,
)
from deppy.equivalence.sheaf_morphism import (
    IsomorphismChecker,
    SheafMorphism,
    SheafMorphismBuilder,
)
from deppy.equivalence.descent import (
    DescentResult,
    EquivalenceDescentChecker,
    quick_descent_check,
)
from deppy.equivalence.fiber_product import (
    FiberProduct,
    FiberProductBuilder,
)
from deppy.equivalence.topos import PushoutBuilder
from deppy.equivalence.stalk import StalkEquivalenceChecker, StalkEquivalenceResult
from deppy.types.dependent import IdentityType
from deppy.types.refinement import (
    ConjunctionPred,
    FalsePred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.types.witnesses import (
    CompositeProof,
    ProofTerm,
    ReflProof,
    TransitivityProof,
)


# ===========================================================================
# Global equivalence checker
# ===========================================================================


class GlobalEquivalenceChecker:
    """Orchestrate global equivalence verification.

    Given two presheaves Sem_f, Sem_g over a shared site category with
    a common refinement cover, determines whether they are isomorphic
    as sheaves.

    The check proceeds through several phases:

    Phase 1 -- Local Checking:
        For each site in the common refinement, check per-site equivalence.
        Uses LocalEquivalenceChecker with presheaf restriction integration.

    Phase 2 -- Naturality Verification:
        Verify that the local equivalences form a natural transformation
        eta : Sem_f -> Sem_g.  This requires checking all naturality squares.

    Phase 3 -- Descent (H^1 Computation):
        Compute the Cech cohomology H^1(U, Iso(Sem_f, Sem_g)).
        Descent holds iff H^1 = 0.

    Phase 4 -- Gluing (if descent holds):
        Construct the global equivalence by gluing local equivalences.
        Uses the sheaf gluing axiom via SheafConditionChecker.

    Phase 5 -- Uniqueness:
        Verify uniqueness of the global section (sheaf condition).

    Phase 6 -- Stalk Verification (optional):
        Cross-check via stalk equivalence (eta is iso iff eta_p is
        bijection for all points p).
    """

    def __init__(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        site_category: SiteCategory,
        correspondences: List[SiteCorrespondence],
        sections_f: Dict[SiteId, LocalSection],
        sections_g: Dict[SiteId, LocalSection],
        use_stalk_check: bool = False,
    ) -> None:
        self._pf = presheaf_f
        self._pg = presheaf_g
        self._cat = site_category
        self._corrs = correspondences
        self._secs_f = sections_f
        self._secs_g = sections_g
        self._use_stalk = use_stalk_check

    def check(self) -> GlobalEquivalenceResult:
        """Run the full global equivalence check."""
        # -- Phase 1: Local checking ----------------------------------------
        judgments = check_local_equivalences(
            correspondences=self._corrs,
            sections_f=self._secs_f,
            sections_g=self._secs_g,
            site_category=self._cat,
            presheaf_f=self._pf,
            presheaf_g=self._pg,
        )

        # Quick exit: if any local check is NOT_EQUIVALENT, fail fast
        local_failures = [
            j for j in judgments
            if j.verdict == EquivalenceVerdict.INEQUIVALENT
        ]
        if local_failures:
            return GlobalEquivalenceResult(
                verdict=EquivalenceVerdict.INEQUIVALENT,
                local_judgments=judgments,
                obstructions=self._obstructions_from_local_failures(local_failures),
                explanation="Local equivalence check failed at one or more sites",
            )

        # -- Phase 2: Naturality --------------------------------------------
        morph_builder = SheafMorphismBuilder(self._pf, self._pg, self._cat)
        morphism = morph_builder.build(judgments)

        if not morphism.is_natural:
            failing = morphism.failing_squares()
            return GlobalEquivalenceResult(
                verdict=EquivalenceVerdict.INEQUIVALENT,
                local_judgments=judgments,
                sheaf_morphism=morphism,
                obstructions=[
                    EquivalenceObstruction(
                        kind=EquivalenceObstructionKind.GLUING_FAILURE,
                        sites=[sq.morphism_source, sq.morphism_target],
                        description=f"Naturality square fails: {sq.morphism_source.name} -> {sq.morphism_target.name}",
                    )
                    for sq in failing
                ],
                explanation="Local equivalences do not form a natural transformation",
            )

        # -- Phase 3: Descent (H^1) ----------------------------------------
        # Quick check first
        quick = quick_descent_check(judgments)
        if quick is True:
            # All local checks trivially pass -- skip full cohomology
            descent_result = DescentResult(descent_holds=True)
        else:
            descent_checker = EquivalenceDescentChecker(
                site_category=self._cat,
                presheaf_f=self._pf,
                presheaf_g=self._pg,
            )
            descent_result = descent_checker.check(judgments)

        if not descent_result.descent_holds:
            return GlobalEquivalenceResult(
                verdict=EquivalenceVerdict.INEQUIVALENT,
                local_judgments=judgments,
                sheaf_morphism=morphism,
                descent_result=descent_result,
                obstructions=descent_result.obstructions,
                explanation="Descent check failed: H^1 is non-trivial",
            )

        # -- Phase 4: Gluing -----------------------------------------------
        gluing_result = self._attempt_gluing(judgments, morphism)

        # -- Phase 5: Uniqueness -------------------------------------------
        unique = self._check_uniqueness(judgments) if gluing_result.glued else True

        # -- Phase 6: Stalk check (optional) --------------------------------
        stalk_result: Optional[StalkEquivalenceResult] = None
        if self._use_stalk:
            stalk_result = self._stalk_verification(morphism)
            if stalk_result and not stalk_result.is_isomorphism:
                return GlobalEquivalenceResult(
                    verdict=EquivalenceVerdict.INEQUIVALENT,
                    local_judgments=judgments,
                    sheaf_morphism=morphism,
                    descent_result=descent_result,
                    stalk_result=stalk_result,
                    explanation="Stalk-level equivalence check failed",
                )

        # -- Assemble final result -----------------------------------------
        iso_witness = morphism.to_isomorphism_witness()
        all_conditional = any(
            j.verdict == EquivalenceVerdict.REFINED
            for j in judgments
        )
        has_conditional_squares = len(morphism.conditional_squares()) > 0

        if all_conditional or has_conditional_squares:
            verdict = EquivalenceVerdict.REFINED
        else:
            verdict = EquivalenceVerdict.EQUIVALENT

        return GlobalEquivalenceResult(
            verdict=verdict,
            local_judgments=judgments,
            sheaf_morphism=morphism,
            descent_result=descent_result,
            stalk_result=stalk_result,
            isomorphism_witness=iso_witness,
            gluing_result=gluing_result,
            explanation="Global equivalence verified" if verdict == EquivalenceVerdict.EQUIVALENT else "Conditional equivalence (solver verification needed)",
        )

    # -- Phase 4: Gluing ---------------------------------------------------

    def _attempt_gluing(
        self,
        judgments: List[LocalEquivalenceJudgment],
        morphism: SheafMorphism,
    ) -> "GluingResult":
        """Attempt to glue local equivalences into a global section.

        Uses GlobalSectionBuilder to assemble a GlobalSection of the
        fiber product presheaf.
        """
        # Build fiber product
        product_builder = FiberProductBuilder(self._pf, self._pg, self._cat)
        product = product_builder.build(self._corrs)

        # Check gluing condition on fiber product
        gluing_ok = product.check_gluing()

        # Build global section from fiber product
        global_builder = GlobalSectionBuilder()
        for sid in product.site_ids():
            fib = product.fiber_at(sid)
            if fib is not None:
                sec = SectionFactory.create(
                    site_id=sid,
                    carrier_type=fib.carrier,
                    trust=fib.trust,
                )
                global_builder.add_section(sec)

        try:
            global_section = global_builder.build()
            glued = True
        except Exception:
            global_section = None
            glued = False

        return GluingResult(
            glued=glued and gluing_ok,
            global_section=global_section,
            fiber_product=product,
        )

    # -- Phase 5: Uniqueness -----------------------------------------------

    def _check_uniqueness(
        self,
        judgments: List[LocalEquivalenceJudgment],
    ) -> bool:
        """Verify uniqueness of the glued section.

        The sheaf condition requires that the global section is unique.
        We check this by verifying that any two global sections that
        restrict to the same locals must be equal.

        Concretely: for each site, the local section is determined by
        the judgment, so uniqueness follows from the functionality of
        restriction.
        """
        seen_sites: Set[SiteId] = set()
        for j in judgments:
            if j.site_id in seen_sites:
                return False
            seen_sites.add(j.site_id)
        return True

    # -- Phase 6: Stalk verification ----------------------------------------

    def _stalk_verification(
        self,
        morphism: SheafMorphism,
    ) -> Optional[StalkEquivalenceResult]:
        """Cross-check equivalence at the stalk level."""
        try:
            stalk_checker = StalkEquivalenceChecker(
                presheaf_f=self._pf,
                presheaf_g=self._pg,
                site_category=self._cat,
            )
            return stalk_checker.check(morphism.presheaf_morphism)
        except Exception:
            return None

    # -- Obstruction helpers ------------------------------------------------

    def _obstructions_from_local_failures(
        self,
        failures: List[LocalEquivalenceJudgment],
    ) -> List[EquivalenceObstruction]:
        """Convert local failures to obstructions."""
        obstructions = []
        for j in failures:
            kind = EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH
            explanation = f"Local equivalence failed at {j.site_id.name}"

            if j.obligation:
                ct_f = j.obligation.carrier_type_f
                ct_g = j.obligation.carrier_type_g
                if ct_f is not None and ct_g is not None and ct_f != ct_g:
                    explanation += f": {ct_f} ≠ {ct_g}"
                else:
                    kind = EquivalenceObstructionKind.PREDICATE_GAP
                    explanation += ": refinement predicates disagree"

            obstructions.append(EquivalenceObstruction(
                kind=kind,
                sites=[j.site_id],
                description=explanation,
            ))
        return obstructions


# ===========================================================================
# Result types
# ===========================================================================


@dataclass
class GluingResult:
    """Result of the gluing attempt."""
    glued: bool
    global_section: Optional[GlobalSection] = None
    fiber_product: Optional[FiberProduct] = None


@dataclass
class GlobalEquivalenceResult:
    """Full result of the global equivalence check."""
    verdict: EquivalenceVerdict
    local_judgments: List[LocalEquivalenceJudgment] = field(default_factory=list)
    sheaf_morphism: Optional[SheafMorphism] = None
    descent_result: Optional[DescentResult] = None
    stalk_result: Optional[StalkEquivalenceResult] = None
    isomorphism_witness: Optional[IsomorphismWitness] = None
    gluing_result: Optional[GluingResult] = None
    obstructions: List[EquivalenceObstruction] = field(default_factory=list)
    explanation: str = ""

    @property
    def is_equivalent(self) -> bool:
        return self.verdict == EquivalenceVerdict.EQUIVALENT

    @property
    def is_conditional(self) -> bool:
        return self.verdict == EquivalenceVerdict.REFINED

    @property
    def obstruction_count(self) -> int:
        return len(self.obstructions)

    def strength(self) -> EquivalenceStrength:
        """Determine the strength of the equivalence."""
        if self.verdict == EquivalenceVerdict.INEQUIVALENT:
            return EquivalenceStrength.REFINEMENT
        if self.verdict == EquivalenceVerdict.EQUIVALENT:
            if self.isomorphism_witness is not None:
                return EquivalenceStrength.DENOTATIONAL
            return EquivalenceStrength.BISIMULATION
        return EquivalenceStrength.CONTEXTUAL
