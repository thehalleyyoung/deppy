"""Descent data and Cech cohomology for equivalence via cohomology.py.

Descent theory provides the obstruction-theoretic framework for
deciding whether local equivalences glue to a global equivalence.

Given local isomorphisms eta_{U_i} : Sem_f(U_i) ~> Sem_g(U_i),
the transition functions on overlaps U_{ij} = U_i cap U_j are:

    g_{ij} = eta_{U_j}|_{U_{ij}} . (eta_{U_i}|_{U_{ij}})^{-1}

These form a Cech 1-cocycle in C^1(U, Iso(Sem_f, Sem_g)).
The cocycle condition on triple overlaps U_{ijk} is:

    g_{ij} . g_{jk} = g_{ik}

The equivalence descends (i.e., local equivalences glue to a global
one) if and only if this cocycle is a coboundary: [g] = 0 in H^1.

This module delegates the actual cohomological computation to
``CechCohomologyComputer`` from ``cohomology.py``, which computes
the full Cech complex C^0 -> C^1 -> C^2 and the groups
H^0, H^1 with proper kernel/image/quotient formation.

Workflow:
1. Build transition functions from local judgments (the 1-cochain)
2. Feed to CechCohomologyComputer for H^1 computation
3. If H^1 = 0, descent holds => global equivalence
4. If H^1 != 0, extract obstructions from non-trivial classes
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
    CechCochainData,
    CohomologyClass,
    Cover,
    DescentDatum,
    LocalSection,
    Morphism,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf
from deppy.core.section import SectionMerger, SectionRestrictor
from deppy.core.site import ConcreteMorphism, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceCochainData,
    EquivalenceCohomologyClass,
    EquivalenceDescentDatum,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
    SectionPair,
    SiteCorrespondence,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    SectionAgreementPred,
)
from deppy.equivalence.cohomology import (
    CechCohomologyComputer,
    CechCohomologyResult,
    CochainElement,
    CochainGroup,
    CoboundaryOperator,
    extract_obstructions_from_h1,
)
from deppy.types.dependent import IdentityType, SigmaType
from deppy.types.refinement import (
    ConjunctionPred,
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
    ProofTerm,
    ReflProof,
    SymmetryProof,
    TransitivityProof,
    TransportWitness,
)


# ===========================================================================
# Transition function computation
# ===========================================================================


@dataclass(frozen=True)
class TransitionFunction:
    """Transition function g_{ij} on overlap U_i cap U_j.

    g_{ij} = eta_j|_{U_{ij}} . (eta_i|_{U_{ij}})^{-1}

    Encoded as a predicate: the composition of the forward evidence
    at j with the backward evidence at i, restricted to the overlap.
    """
    site_i: SiteId
    site_j: SiteId
    predicate: Predicate
    is_identity: bool = False
    proof_term: Optional[ProofTerm] = None


class TransitionFunctionBuilder:
    """Compute transition functions from local equivalence judgments.

    For each pair of overlapping sites (U_i, U_j), computes:

        g_{ij} = eta_j . eta_i^{-1}

    restricted to the overlap U_{ij}.
    """

    def __init__(
        self,
        site_category: SiteCategory,
        presheaf_f: Optional[ConcretePresheaf] = None,
        presheaf_g: Optional[ConcretePresheaf] = None,
    ) -> None:
        self._cat = site_category
        self._pf = presheaf_f
        self._pg = presheaf_g

    def build(
        self,
        judgments: List[LocalEquivalenceJudgment],
    ) -> List[TransitionFunction]:
        """Compute all transition functions from local judgments."""
        judgment_map: Dict[SiteId, LocalEquivalenceJudgment] = {
            j.site_id: j for j in judgments
        }
        transitions: List[TransitionFunction] = []
        seen: Set[FrozenSet[SiteId]] = set()

        sites = list(judgment_map.keys())

        for i, s_i in enumerate(sites):
            for s_j in sites[i+1:]:
                pair = frozenset({s_i, s_j})
                if pair in seen:
                    continue
                seen.add(pair)

                # Check if sites overlap
                overlaps = self._cat.find_overlaps(frozenset({s_i, s_j}))
                if not overlaps:
                    continue

                j_i = judgment_map[s_i]
                j_j = judgment_map[s_j]

                tf = self._compute_transition(s_i, s_j, j_i, j_j)
                transitions.append(tf)

        return transitions

    def _compute_transition(
        self,
        s_i: SiteId,
        s_j: SiteId,
        j_i: LocalEquivalenceJudgment,
        j_j: LocalEquivalenceJudgment,
    ) -> TransitionFunction:
        """Compute g_{ij} = eta_j . eta_i^{-1}.

        eta_i^{-1} is the backward evidence at i.
        eta_j is the forward evidence at j.
        Their composition is encoded as conjunction.
        """
        # Extract evidence from the obligation's predicates
        fwd_j = (j_j.obligation.forward_predicate
                 if j_j.obligation and j_j.obligation.forward_predicate
                 else TruePred())
        bwd_i = (j_i.obligation.backward_predicate
                 if j_i.obligation and j_i.obligation.backward_predicate
                 else TruePred())

        # g_{ij} = fwd_j . bwd_i (function composition = conjunction)
        transition_pred = ConjunctionPred(conjuncts=(bwd_i, fwd_j))

        # Check if it's the identity
        is_identity = (
            isinstance(fwd_j, TruePred) and isinstance(bwd_i, TruePred)
        )

        # Build proof term
        if j_i.proof and j_j.proof:
            proof = TransitivityProof(
                left=SymmetryProof(inner=j_i.proof),
                right=j_j.proof,
            )
        else:
            proof = ReflProof()

        return TransitionFunction(
            site_i=s_i,
            site_j=s_j,
            predicate=transition_pred,
            is_identity=is_identity,
            proof_term=proof,
        )


# ===========================================================================
# Descent datum builder
# ===========================================================================


class DescentDatumBuilder:
    """Build a DescentDatum from local judgments.

    Assembles:
    - The local sections (from the fiber product)
    - The transition isomorphisms (from transition functions)
    """

    def __init__(
        self,
        site_category: SiteCategory,
    ) -> None:
        self._cat = site_category

    def build(
        self,
        judgments: List[LocalEquivalenceJudgment],
    ) -> DescentDatum:
        """Build a DescentDatum.

        The sections map is the collection of local equivalence witnesses.
        The transition_isos map records the transition functions.
        """
        sections: Dict[SiteId, LocalSection] = {}
        for j in judgments:
            # Extract carrier types from the obligation (which records both programs)
            carrier_f = (j.obligation.carrier_type_f
                         if j.obligation and j.obligation.carrier_type_f
                         else None)
            carrier_g = (j.obligation.carrier_type_g
                         if j.obligation and j.obligation.carrier_type_g
                         else None)

            if carrier_f is not None:
                # Build an IdentityType encoding f(U) = g(U) as the descent section
                carrier = IdentityType(
                    carrier=carrier_f,
                    lhs=carrier_f,
                    rhs=carrier_g if carrier_g else carrier_f,
                )
                from deppy.core.section import SectionFactory
                sections[j.site_id] = SectionFactory.create(
                    site_id=j.site_id,
                    carrier_type=carrier,
                )

        transition_builder = TransitionFunctionBuilder(self._cat)
        transitions = transition_builder.build(judgments)

        transition_isos: Dict[Tuple[SiteId, SiteId], Any] = {}
        for tf in transitions:
            transition_isos[(tf.site_i, tf.site_j)] = {
                "predicate": tf.predicate,
                "is_identity": tf.is_identity,
                "proof": tf.proof_term,
            }

        return DescentDatum(
            sections=sections,
            transition_isos=transition_isos,
        )


# ===========================================================================
# Cech cohomology delegation
# ===========================================================================


class EquivalenceDescentChecker:
    """Check whether local equivalences descend to a global equivalence.

    Delegates to CechCohomologyComputer from cohomology.py to compute
    the full Cech complex and H^1 group.

    Descent holds iff H^1(U, Iso(Sem_f, Sem_g)) = 0.
    """

    def __init__(
        self,
        site_category: SiteCategory,
        presheaf_f: Optional[ConcretePresheaf] = None,
        presheaf_g: Optional[ConcretePresheaf] = None,
    ) -> None:
        self._cat = site_category
        self._pf = presheaf_f
        self._pg = presheaf_g

    def check(
        self,
        judgments: List[LocalEquivalenceJudgment],
    ) -> DescentResult:
        """Check descent via Cech cohomology.

        Steps:
        1. Build the Cech complex from local judgments
        2. Compute H^0 (global sections of the equivalence sheaf)
        3. Compute H^1 (obstructions to descent)
        4. If H^1 = 0, descent holds
        5. If H^1 != 0, extract and classify obstructions
        """
        sites = [j.site_id for j in judgments]
        judgment_dict = {j.site_id: j for j in judgments}

        # Compute pairwise overlaps from the site category
        overlaps = self._cat.find_overlaps(frozenset(sites))

        # Build C^0 from local equivalence judgments
        computer = CechCohomologyComputer(
            judgments=judgment_dict,
            overlaps=overlaps,
        )

        # Compute the Čech cohomology
        cohomology_result = computer.compute()

        # Determine descent
        h1_trivial = cohomology_result.h1_trivial

        # Extract obstructions from H^1 if non-trivial
        obstructions: List[EquivalenceObstruction] = []
        if not h1_trivial:
            obstructions = extract_obstructions_from_h1(
                cohomology_result,
            )

        # Build descent datum
        datum_builder = DescentDatumBuilder(self._cat)
        datum = datum_builder.build(judgments)

        return DescentResult(
            descent_holds=h1_trivial,
            h0_sections=cohomology_result.h0,
            h1_group=cohomology_result.h1,
            obstructions=obstructions,
            descent_datum=datum,
            cohomology_result=cohomology_result,
        )


# ===========================================================================
# Descent result
# ===========================================================================


@dataclass
class DescentResult:
    """Result of the descent check."""
    descent_holds: bool
    h0_sections: Optional[CochainGroup] = None
    h1_group: Optional[CochainGroup] = None
    obstructions: List[EquivalenceObstruction] = field(default_factory=list)
    descent_datum: Optional[DescentDatum] = None
    cohomology_result: Optional[CechCohomologyResult] = None

    @property
    def has_obstructions(self) -> bool:
        return len(self.obstructions) > 0

    @property
    def obstruction_count(self) -> int:
        return len(self.obstructions)


# ===========================================================================
# Quick check: skip cohomology if all local checks pass trivially
# ===========================================================================


def quick_descent_check(
    judgments: List[LocalEquivalenceJudgment],
) -> Optional[bool]:
    """Quick check: if all local judgments are EQUIVALENT with
    TruePred evidence, descent trivially holds (no obstruction possible).

    Returns None if the quick check is inconclusive and the full
    cohomological computation is needed.
    """
    for j in judgments:
        if j.verdict != EquivalenceVerdict.EQUIVALENT:
            return None
        # Check that both directions hold via the obligation predicates
        fwd = (j.obligation.forward_predicate
               if j.obligation and j.obligation.forward_predicate
               else None)
        bwd = (j.obligation.backward_predicate
               if j.obligation and j.obligation.backward_predicate
               else None)
        if fwd is not None and not isinstance(fwd, TruePred):
            return None
        if bwd is not None and not isinstance(bwd, TruePred):
            return None
    return True


# ===========================================================================
# Cocycle condition checker (direct, without full H^1)
# ===========================================================================


class CocycleConditionChecker:
    """Direct cocycle condition check on transition functions.

    For each triple overlap (i, j, k), verifies:
        g_{ij} . g_{jk} = g_{ik}

    This is a quicker alternative to the full H^1 computation
    when we only need to know if the cocycle condition holds.
    """

    def __init__(self, site_category: SiteCategory) -> None:
        self._cat = site_category

    def check(
        self,
        transitions: List[TransitionFunction],
    ) -> CocycleResult:
        """Check the cocycle condition on all triples."""
        tf_map: Dict[FrozenSet[SiteId], TransitionFunction] = {
            frozenset({tf.site_i, tf.site_j}): tf
            for tf in transitions
        }

        sites = set()
        for tf in transitions:
            sites.add(tf.site_i)
            sites.add(tf.site_j)

        site_list = sorted(sites, key=lambda s: s.name)
        failures: List[CocycleFailure] = []

        for a_idx, s_i in enumerate(site_list):
            for b_idx in range(a_idx + 1, len(site_list)):
                s_j = site_list[b_idx]
                for c_idx in range(b_idx + 1, len(site_list)):
                    s_k = site_list[c_idx]

                    g_ij = tf_map.get(frozenset({s_i, s_j}))
                    g_jk = tf_map.get(frozenset({s_j, s_k}))
                    g_ik = tf_map.get(frozenset({s_i, s_k}))

                    if g_ij is None or g_jk is None or g_ik is None:
                        continue

                    # Check: g_ij . g_jk = g_ik
                    lhs = ConjunctionPred(conjuncts=(
                        g_ij.predicate, g_jk.predicate,
                    ))
                    rhs = g_ik.predicate

                    from deppy.equivalence.predicate_eq import check_cocycle_identity, PredicateRelation
                    cocycle_result = check_cocycle_identity(
                        g_ij.predicate, g_jk.predicate, g_ik.predicate,
                    )
                    if cocycle_result.relation == PredicateRelation.EQUIVALENT:
                        continue
                    if g_ij.is_identity and g_jk.is_identity and g_ik.is_identity:
                        continue

                    failures.append(CocycleFailure(
                        site_i=s_i, site_j=s_j, site_k=s_k,
                        lhs_predicate=lhs,
                        rhs_predicate=rhs,
                    ))

        return CocycleResult(
            cocycle_holds=len(failures) == 0,
            failures=failures,
        )


@dataclass(frozen=True)
class CocycleFailure:
    """A failure of the cocycle condition at a triple overlap."""
    site_i: SiteId
    site_j: SiteId
    site_k: SiteId
    lhs_predicate: Predicate
    rhs_predicate: Predicate


@dataclass
class CocycleResult:
    """Result of the cocycle condition check."""
    cocycle_holds: bool
    failures: List[CocycleFailure] = field(default_factory=list)
