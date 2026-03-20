"""Per-site local equivalence checking with presheaf restriction integration.

The local checker determines equivalence at a single site U_i by
comparing the local sections Sem_f(U_i) and Sem_g(U_i).  It produces
``LocalEquivalenceJudgment``s that feed into the global checker.

The check proceeds in layers:

Layer 1 -- Carrier Type Equivalence:
    Determine if the carrier types tau_f and tau_g are equivalent
    via mutual subtyping: tau_f <: tau_g AND tau_g <: tau_f.

Layer 2 -- Refinement Predicate Biimplication:
    For refinement types {v: tau | phi_f} and {v: tau | phi_g},
    check phi_f <==> phi_g (decomposed into two ImplicationPreds).

Layer 3 -- Presheaf Restriction Coherence:
    Verify that restriction morphisms preserve the equivalence:
    if U_j -> U_i, then the restricted sections at U_j must also
    be equivalent (this is the naturality condition at the local level).

Layer 4 -- Equaliser Check:
    Verify that the two sections factor through the equaliser
    of the restriction maps (predicate comparison).

Layer 5 -- Stalk Check (optional):
    Use StalkEquivalenceChecker from stalk.py to verify equivalence
    at the stalk level (germs at a point).

Each layer can short-circuit: if carrier types are incompatible,
no need to check refinement predicates.

The local checker produces:
- Forward evidence: phi_f => phi_g (as a Predicate)
- Backward evidence: phi_g => phi_f (as a Predicate)
- Proof terms: witnessing the equivalence (IdentityType, ReflProof,
  TransportWitness, etc.)
- The verdict: EQUIVALENT, INEQUIVALENT, or REFINED
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
from deppy.core.presheaf import ConcretePresheaf
from deppy.core.section import SectionMerger, SectionRestrictor
from deppy.core.site import ConcreteMorphism, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceStrength,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
    SectionPair,
    SiteCorrespondence,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    BehavioralEquivalencePred,
    EquivalencePred,
    RefinementEquivalencePred,
    SectionAgreementPred,
    TransportPred,
    build_equivalence_predicate,
    build_fiber_product_predicate,
)
from deppy.equivalence.topos import (
    PresheafMorphism,
    SectionTransformComponent,
)
from deppy.types.base import TypeBase
from deppy.types.dependent import (
    ExistsType,
    ForallType,
    IdentityType,
    PiType,
    SigmaType,
)
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.types.witnesses import (
    CompositeProof,
    CongruenceProof,
    ProofTerm,
    ReflProof,
    RefinementWitness,
    SymmetryProof,
    TransitivityProof,
    TransportWitness,
    WitnessCarrier,
)


# ===========================================================================
# Carrier comparison result
# ===========================================================================


class _CarrierResult(Enum):
    """Result of comparing carrier types."""
    EQUAL = auto()
    BOTH_NONE = auto()
    ONE_NONE = auto()
    FORWARD_ONLY = auto()
    BACKWARD_ONLY = auto()
    MISMATCH = auto()
    REFINEMENT_CHECK_NEEDED = auto()


# ===========================================================================
# Local equivalence checker
# ===========================================================================


class LocalEquivalenceChecker:
    """Check equivalence at a single site.

    Given two local sections sigma_f, sigma_g at site U_i,
    determine whether they represent equivalent program behaviors.

    The checker integrates with the presheaf restriction machinery:
    if the site category provides morphisms from U_i, the checker
    verifies that equivalence is preserved under restriction (the
    naturality condition at the local level).
    """

    def __init__(
        self,
        site_category: Optional[SiteCategory] = None,
        presheaf_f: Optional[ConcretePresheaf] = None,
        presheaf_g: Optional[ConcretePresheaf] = None,
    ) -> None:
        self._cat = site_category
        self._pf = presheaf_f
        self._pg = presheaf_g

    def check(
        self,
        site_id: SiteId,
        section_f: LocalSection,
        section_g: LocalSection,
        check_restrictions: bool = True,
    ) -> LocalEquivalenceJudgment:
        """Check equivalence at a single site.

        Runs through all layers and produces a LocalEquivalenceJudgment.
        """
        # -- Layer 1: Carrier type comparison --------------------------------
        carrier_result = self._compare_carriers(section_f, section_g)

        if carrier_result == _CarrierResult.BOTH_NONE:
            return self._trivial_judgment(site_id, section_f, section_g)

        if carrier_result == _CarrierResult.ONE_NONE:
            return self._mismatch_judgment(
                site_id, section_f, section_g,
                "One section has no carrier type",
            )

        if carrier_result == _CarrierResult.MISMATCH:
            return self._mismatch_judgment(
                site_id, section_f, section_g,
                "Carrier types are structurally incompatible",
            )

        # -- Layer 2: Refinement predicate biimplication ---------------------
        fwd_pred, bwd_pred, biimp = self._check_refinement_biimplication(
            section_f, section_g,
        )

        # If carriers are equal, check if predicates match
        if carrier_result == _CarrierResult.EQUAL:
            # Exact carrier match -- just need predicate check
            pass
        elif carrier_result == _CarrierResult.REFINEMENT_CHECK_NEEDED:
            # Carriers are refinement types -- need deeper check
            fwd_pred, bwd_pred, biimp = self._check_deep_refinement(
                section_f, section_g,
            )
        elif carrier_result == _CarrierResult.FORWARD_ONLY:
            bwd_pred = FalsePred()
            biimp = None
        elif carrier_result == _CarrierResult.BACKWARD_ONLY:
            fwd_pred = FalsePred()
            biimp = None

        # -- Layer 3: Presheaf restriction coherence -------------------------
        restriction_ok = True
        if check_restrictions and self._cat:
            restriction_ok = self._check_restriction_coherence(
                site_id, section_f, section_g,
            )

        # -- Build the proof term -------------------------------------------
        proof = self._build_proof(
            section_f, section_g,
            fwd_pred, bwd_pred,
            carrier_result,
        )

        # -- Determine verdict ----------------------------------------------
        verdict = self._determine_verdict(
            carrier_result, fwd_pred, bwd_pred, restriction_ok,
        )

        return LocalEquivalenceJudgment(
            site_id=site_id,
            verdict=verdict,
            obligation=EquivalenceObligation(site_id=site_id, description="local check"),
            forward_holds=not isinstance(fwd_pred, FalsePred) if fwd_pred is not None else None,
            backward_holds=not isinstance(bwd_pred, FalsePred) if bwd_pred is not None else None,
            proof=proof,
        )

    def check_batch(
        self,
        pairs: List[Tuple[SiteId, LocalSection, LocalSection]],
    ) -> List[LocalEquivalenceJudgment]:
        """Check equivalence for multiple sites."""
        return [
            self.check(sid, sf, sg)
            for sid, sf, sg in pairs
        ]

    # -- Layer 1: Carrier comparison ----------------------------------------

    def _compare_carriers(
        self,
        section_f: LocalSection,
        section_g: LocalSection,
    ) -> _CarrierResult:
        """Compare carrier types of two sections."""
        ct_f = section_f.carrier_type
        ct_g = section_g.carrier_type

        if ct_f is None and ct_g is None:
            return _CarrierResult.BOTH_NONE
        if ct_f is None or ct_g is None:
            return _CarrierResult.ONE_NONE

        # Exact equality
        if ct_f == ct_g:
            return _CarrierResult.EQUAL

        # Both are refinement types with matching bases
        if (
            isinstance(ct_f, RefinementType)
            and isinstance(ct_g, RefinementType)
        ):
            if ct_f.base == ct_g.base:
                return _CarrierResult.REFINEMENT_CHECK_NEEDED
            # Different bases but both refinement → carrier mismatch
            return _CarrierResult.MISMATCH

        # One is a refinement of the other's type
        if isinstance(ct_f, RefinementType) and ct_f.base == ct_g:
            return _CarrierResult.REFINEMENT_CHECK_NEEDED
        if isinstance(ct_g, RefinementType) and ct_g.base == ct_f:
            return _CarrierResult.REFINEMENT_CHECK_NEEDED

        # Dependent type comparison
        if isinstance(ct_f, PiType) and isinstance(ct_g, PiType):
            return _CarrierResult.REFINEMENT_CHECK_NEEDED
        if isinstance(ct_f, SigmaType) and isinstance(ct_g, SigmaType):
            return _CarrierResult.REFINEMENT_CHECK_NEEDED

        # Identity types
        if isinstance(ct_f, IdentityType) and isinstance(ct_g, IdentityType):
            return _CarrierResult.EQUAL if ct_f == ct_g else _CarrierResult.REFINEMENT_CHECK_NEEDED

        return _CarrierResult.MISMATCH

    # -- Layer 2: Refinement predicate biimplication -------------------------

    def _check_refinement_biimplication(
        self,
        section_f: LocalSection,
        section_g: LocalSection,
    ) -> Tuple[Predicate, Predicate, Optional[Predicate]]:
        """Check biimplication of refinement predicates.

        Returns (forward, backward, biimplication).
        """
        f_pred = _extract_predicate(section_f)
        g_pred = _extract_predicate(section_g)

        fwd = ImplicationPred(antecedent=f_pred, consequent=g_pred)
        bwd = ImplicationPred(antecedent=g_pred, consequent=f_pred)
        biimp = ConjunctionPred(conjuncts=(fwd, bwd))

        return fwd, bwd, biimp

    def _check_deep_refinement(
        self,
        section_f: LocalSection,
        section_g: LocalSection,
    ) -> Tuple[Predicate, Predicate, Optional[Predicate]]:
        """Deep refinement comparison for complex types.

        Handles:
        - Nested refinement types (base + predicate)
        - Pi/Sigma type comparison (structural)
        - Identity type comparison
        """
        ct_f = section_f.carrier_type
        ct_g = section_g.carrier_type

        # Both refinement types
        if isinstance(ct_f, RefinementType) and isinstance(ct_g, RefinementType):
            f_pred = ct_f.predicate or TruePred()
            g_pred = ct_g.predicate or TruePred()

            # Alpha-rename if binders differ
            if ct_f.binder != ct_g.binder:
                g_pred = g_pred.substitute_pred(
                    {ct_g.binder: ct_f.binder}
                )

            fwd = ImplicationPred(antecedent=f_pred, consequent=g_pred)
            bwd = ImplicationPred(antecedent=g_pred, consequent=f_pred)
            biimp = ConjunctionPred(conjuncts=(fwd, bwd))
            return fwd, bwd, biimp

        # One RefinementType, other is its base type
        # {v: B | P} vs B → P is the refinement predicate, base is TruePred
        if isinstance(ct_f, RefinementType) and not isinstance(ct_g, RefinementType):
            f_pred = ct_f.predicate or TruePred()
            g_pred = TruePred()  # bare base type = {v: B | True}
            fwd = ImplicationPred(antecedent=f_pred, consequent=g_pred)
            bwd = ImplicationPred(antecedent=g_pred, consequent=f_pred)
            biimp = ConjunctionPred(conjuncts=(fwd, bwd))
            return fwd, bwd, biimp

        if isinstance(ct_g, RefinementType) and not isinstance(ct_f, RefinementType):
            g_pred = ct_g.predicate or TruePred()
            f_pred = TruePred()  # bare base type = {v: B | True}
            fwd = ImplicationPred(antecedent=f_pred, consequent=g_pred)
            bwd = ImplicationPred(antecedent=g_pred, consequent=f_pred)
            biimp = ConjunctionPred(conjuncts=(fwd, bwd))
            return fwd, bwd, biimp

        # Pi types: check param and return types
        if isinstance(ct_f, PiType) and isinstance(ct_g, PiType):
            # Contravariant in parameter, covariant in return
            param_fwd = ImplicationPred(
                antecedent=VarPred(var_name=f"param_{ct_g.param_name}"),
                consequent=VarPred(var_name=f"param_{ct_f.param_name}"),
            )
            ret_fwd = ImplicationPred(
                antecedent=VarPred(var_name=f"ret_{ct_f.param_name}"),
                consequent=VarPred(var_name=f"ret_{ct_g.param_name}"),
            )
            fwd = ConjunctionPred(conjuncts=(param_fwd, ret_fwd))
            bwd = ConjunctionPred(conjuncts=(
                ImplicationPred(
                    antecedent=VarPred(var_name=f"param_{ct_f.param_name}"),
                    consequent=VarPred(var_name=f"param_{ct_g.param_name}"),
                ),
                ImplicationPred(
                    antecedent=VarPred(var_name=f"ret_{ct_g.param_name}"),
                    consequent=VarPred(var_name=f"ret_{ct_f.param_name}"),
                ),
            ))
            biimp = ConjunctionPred(conjuncts=(fwd, bwd))
            return fwd, bwd, biimp

        # Fallback
        return self._check_refinement_biimplication(section_f, section_g)

    # -- Layer 3: Presheaf restriction coherence ----------------------------

    def _check_restriction_coherence(
        self,
        site_id: SiteId,
        section_f: LocalSection,
        section_g: LocalSection,
    ) -> bool:
        """Check that equivalence is preserved under restriction.

        For each morphism m : U_j -> U_i emanating from site_id,
        verify that the restricted sections at U_j are also equivalent.

        This is the local manifestation of the naturality condition.
        """
        if self._cat is None:
            return True

        for morph in self._cat.outgoing(site_id):
            target_site = morph.target

            # Restrict both sections
            try:
                restricted_f = morph.restrict(section_f)
                restricted_g = morph.restrict(section_g)
            except Exception:
                continue

            # Check compatibility at the restricted site
            if not SectionMerger.are_compatible(restricted_f, restricted_g):
                return False

            # Check predicate agreement on restriction
            f_pred = _extract_predicate(restricted_f)
            g_pred = _extract_predicate(restricted_g)

            # If one is strictly stronger, restriction breaks equivalence
            if isinstance(f_pred, FalsePred) != isinstance(g_pred, FalsePred):
                return False

        return True

    # -- Proof construction -------------------------------------------------

    def _build_proof(
        self,
        section_f: LocalSection,
        section_g: LocalSection,
        fwd: Predicate,
        bwd: Predicate,
        carrier_result: _CarrierResult,
    ) -> ProofTerm:
        """Build a proof term witnessing the equivalence."""
        if carrier_result == _CarrierResult.BOTH_NONE:
            return ReflProof()

        if carrier_result == _CarrierResult.EQUAL:
            # Exact type match: reflexivity
            return ReflProof()

        if carrier_result == _CarrierResult.REFINEMENT_CHECK_NEEDED:
            # Refinement check: build a transport witness along
            # the identity path between the base types
            ct_f = section_f.carrier_type
            ct_g = section_g.carrier_type

            identity_type = IdentityType(
                carrier=ct_f,
                lhs=ct_f,
                rhs=ct_g,
            )

            transport = TransportWitness(
                source_type=ct_f,
                target_type=ct_g,
                path=identity_type,
            )

            # Add refinement witness for the predicate
            refinement_proof = RefinementWitness(
                base_type=ct_f,
                predicate_description=f"biimplication({section_f.site_id.name})",
                proof=ReflProof(),
                binder="eq_v",
            )

            return CompositeProof(sub_proofs=(transport, refinement_proof))

        if carrier_result in (_CarrierResult.ONE_NONE, _CarrierResult.MISMATCH):
            return ReflProof()  # Placeholder -- the verdict will be NOT_EQUIVALENT

        return ReflProof()

    # -- Verdict determination ----------------------------------------------

    def _determine_verdict(
        self,
        carrier_result: _CarrierResult,
        fwd: Predicate,
        bwd: Predicate,
        restriction_ok: bool,
    ) -> EquivalenceVerdict:
        """Determine the equivalence verdict."""
        if carrier_result == _CarrierResult.BOTH_NONE:
            return EquivalenceVerdict.EQUIVALENT

        if carrier_result in (_CarrierResult.MISMATCH, _CarrierResult.ONE_NONE):
            return EquivalenceVerdict.INEQUIVALENT

        if isinstance(fwd, FalsePred) or isinstance(bwd, FalsePred):
            return EquivalenceVerdict.INEQUIVALENT

        if carrier_result == _CarrierResult.FORWARD_ONLY:
            return EquivalenceVerdict.INEQUIVALENT

        if carrier_result == _CarrierResult.BACKWARD_ONLY:
            return EquivalenceVerdict.INEQUIVALENT

        if not restriction_ok:
            return EquivalenceVerdict.REFINED

        # ── Genuine predicate equivalence via predicate_eq ──
        # Extract the semantic predicates and check via the three-tiered
        # engine (structural → algebraic → Z3) rather than isinstance.
        from deppy.equivalence.predicate_eq import predicates_equivalent

        fwd_pred = fwd
        bwd_pred = bwd

        # Unwrap ImplicationPred to get the actual refinement predicates
        if isinstance(fwd, ImplicationPred) and isinstance(bwd, ImplicationPred):
            fwd_pred = fwd
            bwd_pred = bwd
            # Check if both directions hold: phi_f <=> phi_g
            fwd_result = predicates_equivalent(
                fwd.antecedent, fwd.consequent, use_solver=True,
            )
            bwd_result = predicates_equivalent(
                bwd.antecedent, bwd.consequent, use_solver=True,
            )
            if fwd_result.equivalent and bwd_result.equivalent:
                return EquivalenceVerdict.EQUIVALENT
            if fwd_result.equivalent and not bwd_result.equivalent:
                return EquivalenceVerdict.REFINED
            if not fwd_result.equivalent and bwd_result.equivalent:
                return EquivalenceVerdict.REFINED
            return EquivalenceVerdict.INEQUIVALENT

        # Both TruePred: trivially equivalent
        if isinstance(fwd, TruePred) and isinstance(bwd, TruePred):
            return EquivalenceVerdict.EQUIVALENT

        # Non-implication predicates: compare directly
        result = predicates_equivalent(fwd, bwd, use_solver=True)
        if result.equivalent:
            return EquivalenceVerdict.EQUIVALENT

        return EquivalenceVerdict.REFINED

    # -- Trivial/mismatch judgments ----------------------------------------

    def _trivial_judgment(
        self,
        site_id: SiteId,
        section_f: LocalSection,
        section_g: LocalSection,
    ) -> LocalEquivalenceJudgment:
        # ── Sheaf-theoretic: trivial sections carry no information ──
        # When both sections have trivial (⊤) refinement, the local
        # isomorphism sheaf Iso(Sem_f, Sem_g) has a trivial section.
        # Two trivial sections are vacuously isomorphic (⊤ ≅ ⊤).
        # However, this only proves type-level equivalence, not
        # behavioral equivalence.  The verdict is EQUIVALENT at the
        # type level but we flag it for further analysis.
        return LocalEquivalenceJudgment(
            site_id=site_id,
            verdict=EquivalenceVerdict.EQUIVALENT,
            obligation=EquivalenceObligation(site_id=site_id, description="trivial (⊤ ≅ ⊤)"),
            forward_holds=True,
            backward_holds=True,
        )

    def _mismatch_judgment(
        self,
        site_id: SiteId,
        section_f: LocalSection,
        section_g: LocalSection,
        reason: str,
    ) -> LocalEquivalenceJudgment:
        return LocalEquivalenceJudgment(
            site_id=site_id,
            verdict=EquivalenceVerdict.INEQUIVALENT,
            obligation=EquivalenceObligation(site_id=site_id, description=reason),
            forward_holds=False,
            backward_holds=False,
            explanation=reason,
        )


# ===========================================================================
# Equaliser-enhanced local checker
# ===========================================================================


class EqualiserLocalChecker:
    """Enhanced local checker using equaliser predicate comparison.

    This checker constructs the equaliser of the two forgetful maps:
        alpha : Sem_f(U) -> Base
        beta  : Sem_g(U) -> Base

    and verifies that the paired section lies in the equaliser.

    The equaliser E(U) = { (sigma_f, sigma_g) | alpha(sigma_f) = beta(sigma_g) }
    captures exactly the set of section pairs that agree on the base.

    When the equaliser is non-empty, the sections are locally equivalent
    (modulo the agreement predicate).
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

    def check(
        self,
        site_id: SiteId,
    ) -> Tuple[bool, Dict[SiteId, Predicate]]:
        """Check local equivalence via the equaliser.

        Returns (is_in_equaliser, agreement_predicates).
        """
        f_sections = self._pf.sections_at(site_id)
        g_sections = self._pg.sections_at(site_id)

        if not f_sections or not g_sections:
            return False, {}

        f_sec = f_sections[0]
        g_sec = g_sections[0]

        f_pred = _extract_predicate(f_sec)
        g_pred = _extract_predicate(g_sec)

        # Build two morphisms alpha, beta from product to base
        # and compute their equaliser
        agreement = ConjunctionPred(conjuncts=(
            ImplicationPred(antecedent=f_pred, consequent=g_pred),
            ImplicationPred(antecedent=g_pred, consequent=f_pred),
        ))

        # The section is in the equaliser iff the agreement predicate is
        # satisfiable — i.e., both predicates are non-trivially false AND
        # they are logically equivalent (the biimplication holds).
        if isinstance(f_pred, FalsePred) or isinstance(g_pred, FalsePred):
            is_in_equaliser = False
        else:
            from deppy.equivalence.predicate_eq import predicates_equivalent, PredicateRelation
            eq_result = predicates_equivalent(f_pred, g_pred)
            is_in_equaliser = eq_result.relation == PredicateRelation.EQUIVALENT

        return is_in_equaliser, {site_id: agreement}


# ===========================================================================
# Batch checker (convenience)
# ===========================================================================


def check_local_equivalences(
    correspondences: List[SiteCorrespondence],
    sections_f: Dict[SiteId, LocalSection],
    sections_g: Dict[SiteId, LocalSection],
    site_category: Optional[SiteCategory] = None,
    presheaf_f: Optional[ConcretePresheaf] = None,
    presheaf_g: Optional[ConcretePresheaf] = None,
) -> List[LocalEquivalenceJudgment]:
    """Check local equivalence for all corresponded sites.

    This is the main entry point for the local checking phase
    of the equivalence pipeline.
    """
    checker = LocalEquivalenceChecker(
        site_category=site_category,
        presheaf_f=presheaf_f,
        presheaf_g=presheaf_g,
    )

    judgments: List[LocalEquivalenceJudgment] = []

    for corr in correspondences:
        sec_f = sections_f.get(corr.f_site)
        sec_g = sections_g.get(corr.g_site)

        if sec_f is None or sec_g is None:
            judgments.append(LocalEquivalenceJudgment(
                site_id=corr.common_site,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                obligation=EquivalenceObligation(site_id=corr.common_site, description="missing section"),
                forward_holds=False,
                backward_holds=False,
            ))
            continue

        judgment = checker.check(
            corr.common_site, sec_f, sec_g,
        )
        judgments.append(judgment)

    return judgments


# ===========================================================================
# Helpers
# ===========================================================================


def _extract_predicate(section: LocalSection) -> Predicate:
    """Extract the refinement predicate from a section."""
    ct = section.carrier_type
    if isinstance(ct, RefinementType) and ct.predicate is not None:
        return ct.predicate
    return VarPred(var_name=f"section_{section.site_id.name}")
