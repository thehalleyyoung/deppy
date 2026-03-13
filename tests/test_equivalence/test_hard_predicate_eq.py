"""Hard tests for predicate_eq — sheaf-theoretic predicate equivalence engine.

Level 2-5 difficulty tests that push the three-tiered engine:
 - Structural tier: commutativity, nested conjunctions, multiset matching
 - Algebraic tier: DeMorgan, absorption, distributivity, double negation
 - Z3 tier: semantically equal but structurally very different predicates

Also tests compose_predicates and check_cocycle_identity with non-trivial
transition predicates, exercising the Čech cohomological cocycle machinery.
"""

from __future__ import annotations

import pytest

from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    NotPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.equivalence.predicate_eq import (
    PredicateEquivalenceResult,
    PredicateRelation,
    _algebraically_equivalent,
    _normalise,
    _structural_equal,
    check_cocycle_identity,
    compose_predicates,
    predicates_equivalent,
)


# ===========================================================================
# Helpers
# ===========================================================================

x = VarPred(var_name="x")
y = VarPred(var_name="y")
z = VarPred(var_name="z")
w = VarPred(var_name="w")
T = TruePred()
F = FalsePred()


def AND(*ps: Predicate) -> ConjunctionPred:
    return ConjunctionPred(conjuncts=tuple(ps))


def OR(*ps: Predicate) -> DisjunctionPred:
    return DisjunctionPred(disjuncts=tuple(ps))


def NOT(p: Predicate) -> NotPred:
    return NotPred(inner=p)


def IMP(a: Predicate, c: Predicate) -> ImplicationPred:
    return ImplicationPred(antecedent=a, consequent=c)


# ===========================================================================
# Level 2 — Structural tier: commutativity and multiset matching
# ===========================================================================


class TestStructuralCommutativity:
    """Test that the structural tier handles commutativity of ∧ and ∨."""

    def test_conjunction_two_vars_commutes(self):
        p = AND(x, y)
        q = AND(y, x)
        assert _structural_equal(p, q) is True

    def test_disjunction_two_vars_commutes(self):
        p = OR(x, y)
        q = OR(y, x)
        assert _structural_equal(p, q) is True

    def test_conjunction_three_vars_permutation(self):
        p = AND(x, y, z)
        q = AND(z, x, y)
        assert _structural_equal(p, q) is True

    def test_disjunction_three_vars_permutation(self):
        p = OR(x, y, z)
        q = OR(y, z, x)
        assert _structural_equal(p, q) is True

    def test_nested_conjunction_commutativity(self):
        """(x ∧ y) ∧ z vs z ∧ (x ∧ y) — structural should match via multiset."""
        p = AND(AND(x, y), z)
        q = AND(z, AND(x, y))
        assert _structural_equal(p, q) is True

    def test_structural_rejects_different_vars(self):
        p = AND(x, y)
        q = AND(x, z)
        result = _structural_equal(p, q)
        assert result is None or result is False

    def test_implication_not_commutative(self):
        """p ⟹ q is NOT the same as q ⟹ p structurally."""
        p = IMP(x, y)
        q = IMP(y, x)
        result = _structural_equal(p, q)
        assert result is None or result is False


# ===========================================================================
# Level 2 — Algebraic tier: basic simplification
# ===========================================================================


class TestAlgebraicBasic:
    def test_conjunction_with_true_simplifies(self):
        """x ∧ True ≡ x."""
        p = AND(x, T)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_disjunction_with_false_simplifies(self):
        """x ∨ False ≡ x."""
        p = OR(x, F)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_double_negation(self):
        """¬¬x ≡ x."""
        p = NOT(NOT(x))
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_conjunction_idempotence(self):
        """x ∧ x ≡ x."""
        p = AND(x, x)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_disjunction_idempotence(self):
        """x ∨ x ≡ x."""
        p = OR(x, x)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_implication_true_consequent(self):
        """x ⟹ True ≡ True."""
        p = IMP(x, T)
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_implication_false_antecedent(self):
        """False ⟹ x ≡ True."""
        p = IMP(F, x)
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_implication_true_antecedent(self):
        """True ⟹ x ≡ x."""
        p = IMP(T, x)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_negation_of_true(self):
        """¬True ≡ False."""
        p = NOT(T)
        q = F
        assert _algebraically_equivalent(p, q) is True

    def test_negation_of_false(self):
        """¬False ≡ True."""
        p = NOT(F)
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_conjunction_with_false_is_false(self):
        """x ∧ False ≡ False."""
        p = AND(x, F)
        q = F
        assert _algebraically_equivalent(p, q) is True

    def test_disjunction_with_true_is_true(self):
        """x ∨ True ≡ True."""
        p = OR(x, T)
        q = T
        assert _algebraically_equivalent(p, q) is True


# ===========================================================================
# Level 3 — Algebraic tier: deeper algebraic laws
# ===========================================================================


class TestAlgebraicDeep:
    def test_triple_negation(self):
        """¬¬¬x ≡ ¬x."""
        p = NOT(NOT(NOT(x)))
        q = NOT(x)
        assert _algebraically_equivalent(p, q) is True

    def test_conjunction_true_true(self):
        """True ∧ True ≡ True."""
        p = AND(T, T)
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_conjunction_absorption_nested(self):
        """x ∧ True ∧ True ≡ x."""
        p = AND(x, T, T)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_disjunction_absorption_nested(self):
        """x ∨ False ∨ False ≡ x."""
        p = OR(x, F, F)
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_double_negation_inside_conjunction(self):
        """¬¬x ∧ y ≡ x ∧ y."""
        p = AND(NOT(NOT(x)), y)
        q = AND(x, y)
        result = predicates_equivalent(p, q)
        assert result.equivalent

    def test_nested_implication_simplification(self):
        """True ⟹ (False ⟹ x) ≡ True (because False ⟹ x ≡ True, True ⟹ True ≡ True)."""
        p = IMP(T, IMP(F, x))
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_conjunction_idempotence_with_commutation(self):
        """y ∧ x ∧ x ∧ y ≡ x ∧ y (idempotence + commutativity)."""
        p = AND(y, x, x, y)
        q = AND(x, y)
        result = predicates_equivalent(p, q)
        assert result.equivalent


# ===========================================================================
# Level 3 — Full predicates_equivalent API
# ===========================================================================


class TestPredicatesEquivalentAPI:
    def test_identity_object(self):
        """Same object -> EQUIVALENT."""
        result = predicates_equivalent(x, x)
        assert result.equivalent
        assert result.relation == PredicateRelation.EQUIVALENT

    def test_structural_var_match(self):
        """Same var name -> EQUIVALENT."""
        p = VarPred(var_name="x")
        q = VarPred(var_name="x")
        result = predicates_equivalent(p, q)
        assert result.equivalent

    def test_structural_var_mismatch(self):
        """Different var names -> not EQUIVALENT."""
        result = predicates_equivalent(x, y, use_solver=False)
        assert not result.equivalent

    def test_conjunction_commutativity_full(self):
        """x ∧ y ≡ y ∧ x through full API."""
        result = predicates_equivalent(AND(x, y), AND(y, x))
        assert result.equivalent

    def test_double_neg_full(self):
        """¬¬x ≡ x through full API."""
        result = predicates_equivalent(NOT(NOT(x)), x)
        assert result.equivalent

    def test_absorption_full(self):
        """x ∧ True ≡ x through full API."""
        result = predicates_equivalent(AND(x, T), x)
        assert result.equivalent

    def test_false_pred_equivalence(self):
        """False ≡ False."""
        result = predicates_equivalent(F, F)
        assert result.equivalent

    def test_true_false_not_equivalent(self):
        """True ≢ False."""
        result = predicates_equivalent(T, F, use_solver=False)
        assert not result.equivalent


# ===========================================================================
# Level 4 — Composition and cocycle identity
# ===========================================================================


class TestComposePredicates:
    def test_compose_with_true_left(self):
        """True ∘ q = q."""
        result = compose_predicates(T, x)
        assert _structural_equal(result, x) is True

    def test_compose_with_true_right(self):
        """p ∘ True = p."""
        result = compose_predicates(x, T)
        assert _structural_equal(result, x) is True

    def test_compose_with_false_left(self):
        """False ∘ q = False."""
        result = compose_predicates(F, x)
        assert isinstance(result, FalsePred)

    def test_compose_with_false_right(self):
        """p ∘ False = False."""
        result = compose_predicates(x, F)
        assert isinstance(result, FalsePred)

    def test_compose_nontrivial(self):
        """x ∘ y = x ∧ y."""
        result = compose_predicates(x, y)
        assert isinstance(result, ConjunctionPred)
        assert set(result.conjuncts) == {x, y} or _structural_equal(result, AND(x, y)) is True


class TestCocycleIdentity:
    def test_trivial_cocycle(self):
        """True ∘ True = True (trivial cover)."""
        result = check_cocycle_identity(T, T, T)
        assert result.equivalent

    def test_reflexive_cocycle(self):
        """g_ii = True, g_ij ∘ g_ji = True → cocycle holds."""
        result = check_cocycle_identity(x, x, AND(x, x))
        assert result.equivalent  # x ∧ x ≡ x ∧ x

    def test_cocycle_with_identity_transition(self):
        """g_ij = x, g_jk = True → g_ik should equal x."""
        result = check_cocycle_identity(x, T, x)
        assert result.equivalent  # compose(x, True) = x ≡ x

    def test_cocycle_failure_mismatch(self):
        """g_ij = x, g_jk = y → g_ik = x ∧ y, but if g_ik = x then FAIL."""
        result = check_cocycle_identity(x, y, x, use_solver=False)
        # compose(x, y) = x ∧ y ≢ x (structurally)
        assert not result.equivalent

    def test_cocycle_with_conjunction_matching(self):
        """g_ij = x, g_jk = y → g_ik = y ∧ x (commutative)."""
        result = check_cocycle_identity(x, y, AND(y, x))
        assert result.equivalent  # x ∧ y ≡ y ∧ x via commutativity

    def test_cocycle_triple_overlap(self):
        """Full triple: g_ij = x, g_jk = y, g_ik = x ∧ y."""
        result = check_cocycle_identity(x, y, AND(x, y))
        assert result.equivalent

    def test_cocycle_with_absorption(self):
        """g_ij = x, g_jk = True, g_ik = x ∧ True → should hold."""
        result = check_cocycle_identity(x, T, AND(x, T))
        assert result.equivalent


# ===========================================================================
# Level 4 — DeMorgan's laws (algebraic + Z3)
# ===========================================================================


class TestDeMorgans:
    """DeMorgan's laws: ¬(x ∧ y) ≡ ¬x ∨ ¬y and ¬(x ∨ y) ≡ ¬x ∧ ¬y.

    These are NOT handled by the algebraic normaliser (it doesn't distribute
    negation), so they require the Z3 tier or will be UNKNOWN without solver.
    """

    def test_demorgan_and(self):
        """¬(x ∧ y) ≡ ¬x ∨ ¬y — requires solver or algebraic DeMorgan."""
        p = NOT(AND(x, y))
        q = OR(NOT(x), NOT(y))
        result = predicates_equivalent(p, q)
        # May be EQUIVALENT (if Z3 available) or UNKNOWN (no solver)
        # Both are acceptable; what matters is it's never INEQUIVALENT
        assert result.relation in (
            PredicateRelation.EQUIVALENT,
            PredicateRelation.UNKNOWN,
        )

    def test_demorgan_or(self):
        """¬(x ∨ y) ≡ ¬x ∧ ¬y — requires solver."""
        p = NOT(OR(x, y))
        q = AND(NOT(x), NOT(y))
        result = predicates_equivalent(p, q)
        assert result.relation in (
            PredicateRelation.EQUIVALENT,
            PredicateRelation.UNKNOWN,
        )

    def test_demorgan_not_spurious_equivalence(self):
        """¬(x ∧ y) ≢ ¬x ∧ ¬y (this is NOT DeMorgan)."""
        p = NOT(AND(x, y))
        q = AND(NOT(x), NOT(y))
        # These are NOT equivalent (DeMorgan gives ∨ not ∧)
        result = predicates_equivalent(p, q, use_solver=False)
        # Without solver, should not claim EQUIVALENT
        assert result.relation != PredicateRelation.EQUIVALENT


# ===========================================================================
# Level 4 — Normalisation edge cases
# ===========================================================================


class TestNormalisationEdgeCases:
    def test_deeply_nested_double_negation(self):
        """¬¬¬¬x ≡ x."""
        p = NOT(NOT(NOT(NOT(x))))
        assert _algebraically_equivalent(p, x) is True

    def test_conjunction_flattening_with_true(self):
        """(x ∧ True) ∧ (y ∧ True) ≡ x ∧ y."""
        p = AND(AND(x, T), AND(y, T))
        q = AND(x, y)
        result = predicates_equivalent(p, q)
        assert result.equivalent

    def test_empty_conjunction_is_true(self):
        """Conjunction of all True operands → True."""
        p = AND(T, T, T)
        q = T
        assert _algebraically_equivalent(p, q) is True

    def test_empty_disjunction_after_removal(self):
        """Disjunction of all False operands → False."""
        p = OR(F, F, F)
        q = F
        assert _algebraically_equivalent(p, q) is True

    def test_implication_chain_simplification(self):
        """True ⟹ (True ⟹ x) ≡ x."""
        p = IMP(T, IMP(T, x))
        q = x
        assert _algebraically_equivalent(p, q) is True

    def test_normalise_preserves_semantics(self):
        """Normalisation of x ∧ (y ∨ False) ∧ True should give x ∧ y."""
        p = AND(x, OR(y, F), T)
        np = _normalise(p)
        # Should simplify to x ∧ y
        assert predicates_equivalent(np, AND(x, y)).equivalent


# ===========================================================================
# Level 5 — Sheaf-theoretic cocycle chains
# ===========================================================================


class TestCocycleChainsHard:
    """Test cocycle conditions for longer chains and verify the cocycle
    identity g_{ik} = g_{jk} ∘ g_{ij} over non-trivial predicates."""

    def test_chain_three_sites_trivial(self):
        """Three-site cover with identity transitions: all cocycles hold."""
        g_ab = T
        g_bc = T
        g_ac = T
        assert check_cocycle_identity(g_ab, g_bc, g_ac).equivalent

    def test_chain_three_sites_nontrivial(self):
        """g_ab = x, g_bc = y, g_ac = x ∧ y."""
        g_ab = x
        g_bc = y
        g_ac = AND(x, y)
        assert check_cocycle_identity(g_ab, g_bc, g_ac).equivalent

    def test_chain_failure_wrong_transition(self):
        """g_ab = x, g_bc = y, but g_ac = z (wrong!)."""
        result = check_cocycle_identity(x, y, z, use_solver=False)
        assert not result.equivalent  # x ∧ y ≢ z structurally

    def test_cocycle_associativity(self):
        """(g_ab ∘ g_bc) ∘ g_cd should equal g_ab ∘ (g_bc ∘ g_cd).

        This is associativity of conjunction in the presheaf topos.
        """
        # (x ∧ y) ∧ z vs x ∧ (y ∧ z)
        left = compose_predicates(compose_predicates(x, y), z)
        right = compose_predicates(x, compose_predicates(y, z))
        result = predicates_equivalent(left, right)
        assert result.equivalent

    def test_cocycle_with_implication_transitions(self):
        """Transition functions that are implications:
        g_ab = (x ⟹ y), g_bc = (y ⟹ z), g_ac = (x ⟹ y) ∧ (y ⟹ z).
        """
        g_ab = IMP(x, y)
        g_bc = IMP(y, z)
        g_ac = AND(IMP(x, y), IMP(y, z))
        assert check_cocycle_identity(g_ab, g_bc, g_ac).equivalent

    def test_cocycle_identity_reflexive(self):
        """g_ii = True for any site i (reflexive cocycle)."""
        for p in [T, x, AND(x, y), NOT(x)]:
            composed = compose_predicates(p, T)
            result = predicates_equivalent(composed, p)
            assert result.equivalent, f"Failed reflexive cocycle for {p}"


# ===========================================================================
# Level 5 — predicates_equivalent robustness
# ===========================================================================


class TestPredicateEquivalenceRobustness:
    def test_large_conjunction_commutativity(self):
        """4-element conjunction: all permutations should be equivalent."""
        p = AND(x, y, z, w)
        q = AND(w, z, y, x)
        result = predicates_equivalent(p, q)
        assert result.equivalent

    def test_nested_not_conjunction(self):
        """¬(¬x ∧ ¬y) should not be equivalent to x ∧ y without solver."""
        p = NOT(AND(NOT(x), NOT(y)))
        q = AND(x, y)
        # This is actually DeMorgan: ¬(¬x ∧ ¬y) = x ∨ y ≠ x ∧ y
        result = predicates_equivalent(p, q, use_solver=False)
        assert result.relation != PredicateRelation.EQUIVALENT

    def test_implication_vs_disjunction(self):
        """x ⟹ y ≡ ¬x ∨ y — requires solver, not algebraic."""
        p = IMP(x, y)
        q = OR(NOT(x), y)
        result = predicates_equivalent(p, q)
        assert result.relation in (
            PredicateRelation.EQUIVALENT,
            PredicateRelation.UNKNOWN,
        )

    def test_false_is_not_true(self):
        """False ≢ True."""
        result = predicates_equivalent(F, T)
        assert not result.equivalent

    def test_var_not_equiv_to_negation(self):
        """x ≢ ¬x."""
        result = predicates_equivalent(x, NOT(x), use_solver=False)
        assert not result.equivalent

    def test_biimplication_structure(self):
        """The result should carry the biimplication and VCs."""
        result = predicates_equivalent(x, y, use_solver=False)
        assert result.relation == PredicateRelation.UNKNOWN
        # Should have VCs set
        assert result.forward_vc is not None or result.backward_vc is not None
