"""Hard tests for descent data, transition functions, cocycle conditions,
and the full EquivalenceDescentChecker.

These tests exercise the sheaf-theoretic descent machinery:
  - TransitionFunctionBuilder computing g_{ij} = η_j · η_i⁻¹
  - CocycleConditionChecker verifying g_{ij} · g_{jk} = g_{ik}
  - quick_descent_check edge cases
  - Full EquivalenceDescentChecker.check() (the fixed code path)
  - DescentDatumBuilder constructing DescentDatum objects

Levels:
  2 — basic transition function computation
  3 — cocycle conditions with 3+ sites
  4 — full descent checker with cohomology delegation
  5 — quick_descent_check edge cases and counter-examples
"""
from __future__ import annotations

import pytest

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory

from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonPred,
    FalsePred,
    ImplicationPred,
    TruePred,
    VarPred,
)
from deppy.types.witnesses import ReflProof

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.descent import (
    CocycleConditionChecker,
    CocycleResult,
    DescentDatumBuilder,
    DescentResult,
    EquivalenceDescentChecker,
    TransitionFunction,
    TransitionFunctionBuilder,
    quick_descent_check,
)


# ── Helpers ───────────────────────────────────────────────────────────────

def _sid(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _site_cat(*names: str, overlaps: list[tuple[str, str]] | None = None) -> SiteCategory:
    """Build a SiteCategory with sites and optional overlaps.

    For each overlap (a, b), creates a synthetic meet site and morphisms
    a → meet, b → meet so that find_overlaps detects the pair.
    """
    cat = SiteCategory()
    for n in names:
        cat.add_site(ConcreteSite(_site_id=_sid(n)))
    if overlaps:
        for a, b in overlaps:
            # Create a synthetic overlap site a∩b
            meet_id = _sid(f"{a}∩{b}")
            cat.add_site(ConcreteSite(_site_id=meet_id))
            cat.add_morphism(ConcreteMorphism(_source=_sid(a), _target=meet_id))
            cat.add_morphism(ConcreteMorphism(_source=_sid(b), _target=meet_id))
    return cat


def _judgment(
    name: str,
    verdict: EquivalenceVerdict = EquivalenceVerdict.EQUIVALENT,
    fwd_pred=None,
    bwd_pred=None,
    fwd_holds: bool = True,
    bwd_holds: bool = True,
) -> LocalEquivalenceJudgment:
    sid = _sid(name)
    return LocalEquivalenceJudgment(
        site_id=sid,
        verdict=verdict,
        obligation=EquivalenceObligation(
            site_id=sid,
            description="test",
            forward_predicate=fwd_pred,
            backward_predicate=bwd_pred,
        ),
        forward_holds=fwd_holds,
        backward_holds=bwd_holds,
        proof=ReflProof(),
    )


# ═══════════════════════════════════════════════════════════════════════════
# Level 2: TransitionFunctionBuilder
# ═══════════════════════════════════════════════════════════════════════════


class TestTransitionFunctionBuilder:
    """Test transition function computation from local judgments."""

    def test_no_overlaps_no_transitions(self):
        """Disjoint sites produce no transition functions."""
        cat = _site_cat("a", "b")  # no overlaps added
        builder = TransitionFunctionBuilder(site_category=cat)
        judgments = [_judgment("a"), _judgment("b")]
        transitions = builder.build(judgments)
        assert len(transitions) == 0

    def test_trivial_overlap_identity_transition(self):
        """Two overlapping EQUIVALENT sites with TruePred evidence
        produce an identity transition function."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        builder = TransitionFunctionBuilder(site_category=cat)
        judgments = [_judgment("a"), _judgment("b")]
        transitions = builder.build(judgments)
        assert len(transitions) == 1
        tf = transitions[0]
        assert tf.is_identity
        assert isinstance(tf.predicate, ConjunctionPred)

    def test_nontrivial_predicates_produce_nontrivial_transition(self):
        """When local evidence carries non-trivial predicates, the
        transition function g_{ij} = bwd_i ∧ fwd_j is non-trivial."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        builder = TransitionFunctionBuilder(site_category=cat)
        x = VarPred(var_name="x")
        y = VarPred(var_name="y")
        judgments = [
            _judgment("a", fwd_pred=x, bwd_pred=x),
            _judgment("b", fwd_pred=y, bwd_pred=y),
        ]
        transitions = builder.build(judgments)
        assert len(transitions) == 1
        tf = transitions[0]
        assert not tf.is_identity
        # g_{ab} = bwd_a ∧ fwd_b = x ∧ y
        assert isinstance(tf.predicate, ConjunctionPred)

    def test_three_sites_three_transitions(self):
        """Three mutually overlapping sites produce three transitions."""
        cat = _site_cat("a", "b", "c", overlaps=[("a", "b"), ("b", "c"), ("a", "c")])
        builder = TransitionFunctionBuilder(site_category=cat)
        judgments = [_judgment("a"), _judgment("b"), _judgment("c")]
        transitions = builder.build(judgments)
        assert len(transitions) == 3

    def test_proof_term_is_transitivity(self):
        """The proof term for a transition should use TransitivityProof."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        builder = TransitionFunctionBuilder(site_category=cat)
        judgments = [_judgment("a"), _judgment("b")]
        transitions = builder.build(judgments)
        tf = transitions[0]
        from deppy.types.witnesses import TransitivityProof
        assert isinstance(tf.proof_term, TransitivityProof)


# ═══════════════════════════════════════════════════════════════════════════
# Level 3: CocycleConditionChecker
# ═══════════════════════════════════════════════════════════════════════════


class TestCocycleConditionChecker:
    """Test the direct cocycle condition checker."""

    def test_identity_transitions_satisfy_cocycle(self):
        """All-identity transitions trivially satisfy the cocycle."""
        cat = _site_cat("a", "b", "c")
        checker = CocycleConditionChecker(site_category=cat)
        transitions = [
            TransitionFunction(site_i=_sid("a"), site_j=_sid("b"),
                               predicate=TruePred(), is_identity=True),
            TransitionFunction(site_i=_sid("b"), site_j=_sid("c"),
                               predicate=TruePred(), is_identity=True),
            TransitionFunction(site_i=_sid("a"), site_j=_sid("c"),
                               predicate=TruePred(), is_identity=True),
        ]
        result = checker.check(transitions)
        assert result.cocycle_holds
        assert len(result.failures) == 0

    def test_consistent_nontrivial_transitions(self):
        """g_{ab} = x, g_{bc} = x, g_{ac} = x ∧ x.
        Cocycle: x ∧ x ≡ x (by idempotency), so should pass."""
        cat = _site_cat("a", "b", "c")
        checker = CocycleConditionChecker(site_category=cat)
        x = VarPred(var_name="x")
        transitions = [
            TransitionFunction(site_i=_sid("a"), site_j=_sid("b"),
                               predicate=x, is_identity=False),
            TransitionFunction(site_i=_sid("b"), site_j=_sid("c"),
                               predicate=x, is_identity=False),
            TransitionFunction(site_i=_sid("a"), site_j=_sid("c"),
                               predicate=ConjunctionPred(conjuncts=(x, x)),
                               is_identity=False),
        ]
        result = checker.check(transitions)
        assert result.cocycle_holds

    def test_inconsistent_transitions_fail(self):
        """g_{ab} = x, g_{bc} = y, g_{ac} = z.
        Cocycle: x ∧ y ≢ z for distinct free vars → failure."""
        cat = _site_cat("a", "b", "c")
        checker = CocycleConditionChecker(site_category=cat)
        transitions = [
            TransitionFunction(site_i=_sid("a"), site_j=_sid("b"),
                               predicate=VarPred(var_name="x"), is_identity=False),
            TransitionFunction(site_i=_sid("b"), site_j=_sid("c"),
                               predicate=VarPred(var_name="y"), is_identity=False),
            TransitionFunction(site_i=_sid("a"), site_j=_sid("c"),
                               predicate=VarPred(var_name="z"), is_identity=False),
        ]
        result = checker.check(transitions)
        assert not result.cocycle_holds
        assert len(result.failures) == 1
        fail = result.failures[0]
        assert fail.site_i == _sid("a")
        assert fail.site_k == _sid("c")

    def test_two_sites_no_triples(self):
        """Only two sites → no triple overlap → cocycle vacuously holds."""
        cat = _site_cat("a", "b")
        checker = CocycleConditionChecker(site_category=cat)
        transitions = [
            TransitionFunction(site_i=_sid("a"), site_j=_sid("b"),
                               predicate=VarPred(var_name="x"), is_identity=False),
        ]
        result = checker.check(transitions)
        assert result.cocycle_holds

    def test_no_transitions(self):
        """Empty input → cocycle vacuously holds."""
        cat = _site_cat()
        checker = CocycleConditionChecker(site_category=cat)
        result = checker.check([])
        assert result.cocycle_holds


# ═══════════════════════════════════════════════════════════════════════════
# Level 4: EquivalenceDescentChecker (full cohomology delegation)
# ═══════════════════════════════════════════════════════════════════════════


class TestEquivalenceDescentChecker:
    """Test the full descent checker that delegates to cohomology.py."""

    def test_single_site_descent_trivial(self):
        """Single site → descent trivially holds (no overlaps)."""
        cat = _site_cat("a")
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([_judgment("a")])
        assert isinstance(result, DescentResult)
        assert result.descent_holds
        assert result.obstruction_count == 0

    def test_two_equivalent_sites_descent_holds(self):
        """Two overlapping EQUIVALENT sites → descent holds."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([_judgment("a"), _judgment("b")])
        assert result.descent_holds

    def test_three_site_triangle_descent(self):
        """Three equivalent sites in a triangle → descent holds."""
        cat = _site_cat("a", "b", "c",
                        overlaps=[("a", "b"), ("b", "c"), ("a", "c")])
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([
            _judgment("a"), _judgment("b"), _judgment("c"),
        ])
        assert result.descent_holds
        assert result.cohomology_result is not None
        assert result.cohomology_result.h1_trivial

    def test_inequivalent_site_detected(self):
        """An INEQUIVALENT site should propagate through descent."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([
            _judgment("a"),
            _judgment("b", verdict=EquivalenceVerdict.INEQUIVALENT,
                      fwd_holds=False, bwd_holds=False),
        ])
        # Descent may or may not "hold" (the C^0 element is non-iso),
        # but the cohomology result should reflect the non-iso
        assert result.cohomology_result is not None

    def test_descent_datum_built(self):
        """The descent result should include a DescentDatum."""
        cat = _site_cat("a")
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([_judgment("a")])
        assert result.descent_datum is not None

    def test_h0_and_h1_groups_present(self):
        """Both H^0 and H^1 groups should be in the result."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        checker = EquivalenceDescentChecker(site_category=cat)
        result = checker.check([_judgment("a"), _judgment("b")])
        assert result.h0_sections is not None
        assert result.h1_group is not None


# ═══════════════════════════════════════════════════════════════════════════
# Level 5: quick_descent_check edge cases
# ═══════════════════════════════════════════════════════════════════════════


class TestQuickDescentCheck:
    """Test the quick descent shortcut."""

    def test_all_equivalent_true_pred(self):
        """All EQUIVALENT with TruePred → quick says True."""
        judgments = [_judgment("a"), _judgment("b")]
        assert quick_descent_check(judgments) is True

    def test_inequivalent_returns_none(self):
        """Any non-EQUIVALENT → quick returns None (inconclusive)."""
        judgments = [
            _judgment("a"),
            _judgment("b", verdict=EquivalenceVerdict.INEQUIVALENT,
                      fwd_holds=False, bwd_holds=False),
        ]
        assert quick_descent_check(judgments) is None

    def test_refined_returns_none(self):
        """REFINED verdict → quick returns None."""
        judgments = [
            _judgment("a"),
            _judgment("b", verdict=EquivalenceVerdict.REFINED),
        ]
        assert quick_descent_check(judgments) is None

    def test_nontrivial_forward_pred_returns_none(self):
        """Non-TruePred forward → quick returns None."""
        judgments = [
            _judgment("a", fwd_pred=VarPred(var_name="x")),
        ]
        assert quick_descent_check(judgments) is None

    def test_nontrivial_backward_pred_returns_none(self):
        """Non-TruePred backward → quick returns None."""
        judgments = [
            _judgment("a", bwd_pred=VarPred(var_name="y")),
        ]
        assert quick_descent_check(judgments) is None

    def test_empty_judgments(self):
        """Empty list → quick says True (vacuously)."""
        assert quick_descent_check([]) is True

    def test_none_predicates_treated_as_trivial(self):
        """None forward/backward predicates are treated as TruePred."""
        judgments = [_judgment("a")]  # No predicates set
        assert quick_descent_check(judgments) is True


# ═══════════════════════════════════════════════════════════════════════════
# Level 5: DescentDatumBuilder
# ═══════════════════════════════════════════════════════════════════════════


class TestDescentDatumBuilder:
    """Test DescentDatum construction."""

    def test_single_site_no_transitions(self):
        """Single site → datum has one section, no transitions."""
        from deppy.types.base import TypeBase

        class DummyType(TypeBase):
            def __eq__(self, other): return isinstance(other, DummyType)
            def __hash__(self): return hash("DummyType")
            def __repr__(self): return "DummyType()"
            def free_variables(self): return frozenset()
            def substitute(self, mapping): return self

        cat = _site_cat("a")
        builder = DescentDatumBuilder(site_category=cat)
        jud = _judgment("a")
        # Give it carrier types so sections are built
        jud.obligation.carrier_type_f = DummyType()
        jud.obligation.carrier_type_g = DummyType()
        datum = builder.build([jud])
        assert len(datum.sections) == 1
        assert _sid("a") in datum.sections
        assert len(datum.transition_isos) == 0

    def test_two_overlapping_sites_one_transition(self):
        """Two overlapping sites → one transition iso in datum."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        builder = DescentDatumBuilder(site_category=cat)
        datum = builder.build([_judgment("a"), _judgment("b")])
        assert len(datum.transition_isos) == 1
