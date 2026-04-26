"""Tests for ``deppy.lean.predicate_canon``.

This module backs the round-2 cohomology fix that compares
predicate values for equality (rather than just simplex membership)
to compute ``H^k`` correctly.
"""
from __future__ import annotations

from deppy.lean.predicate_canon import (
    canonicalize_predicate,
    matches_pattern,
    predicates_equivalent,
)


class TestCanonicalize:
    def test_empty(self):
        assert canonicalize_predicate("") == ""

    def test_strips_whitespace(self):
        assert canonicalize_predicate("  P  →  Q  ") == "P → Q"

    def test_collapses_internal_whitespace(self):
        assert canonicalize_predicate("P     →    Q") == "P → Q"

    def test_outer_parens_stripped(self):
        assert canonicalize_predicate("(P → Q)") == "P → Q"
        assert canonicalize_predicate("((P → Q))") == "P → Q"

    def test_outer_parens_kept_when_not_outermost(self):
        # ``(P) → (Q)`` — the outer parens are NOT around the whole
        # expression (each is around one operand).
        assert (
            canonicalize_predicate("(P) → (Q)")
            == "(P) → (Q)"
        )

    def test_arrow_normalisation(self):
        assert canonicalize_predicate("P -> Q") == "P → Q"
        assert canonicalize_predicate("P => Q") == "P → Q"
        assert canonicalize_predicate("P→Q") == "P → Q"

    def test_and_normalisation(self):
        assert canonicalize_predicate("A and B") == "A ∧ B"
        assert canonicalize_predicate("A && B") == "A ∧ B"

    def test_or_normalisation(self):
        assert canonicalize_predicate("A or B") == "A ∨ B"
        assert canonicalize_predicate("A || B") == "A ∨ B"

    def test_eq_normalisation(self):
        assert canonicalize_predicate("a == b") == "a = b"
        assert canonicalize_predicate("a != b") == "a ≠ b"
        assert canonicalize_predicate("a <= b") == "a ≤ b"
        assert canonicalize_predicate("a >= b") == "a ≥ b"

    def test_negation_normalisation(self):
        assert "¬" in canonicalize_predicate("not P")
        assert "¬" in canonicalize_predicate("!P")

    def test_commutative_and_sorts(self):
        # ``B ∧ A`` and ``A ∧ B`` canonicalise the same.
        assert (
            canonicalize_predicate("B ∧ A")
            == canonicalize_predicate("A ∧ B")
        )

    def test_commutative_or_sorts(self):
        assert (
            canonicalize_predicate("B ∨ A")
            == canonicalize_predicate("A ∨ B")
        )


class TestEquivalent:
    def test_identical(self):
        assert predicates_equivalent("P → Q", "P → Q")

    def test_whitespace_irrelevant(self):
        assert predicates_equivalent("P → Q", "  P→Q  ")

    def test_outer_parens_irrelevant(self):
        assert predicates_equivalent("(P → Q)", "P → Q")

    def test_operator_aliases_match(self):
        assert predicates_equivalent("P -> Q", "P → Q")
        assert predicates_equivalent("a == b", "a = b")
        assert predicates_equivalent("A and B", "A ∧ B")

    def test_distinct_predicates(self):
        assert not predicates_equivalent("P → Q", "Q → P")

    def test_inner_parens_distinguished(self):
        # "(P) → (Q)" and "P → Q" — the inner parens are part of
        # the structure (group operands).  Both canonicalise to
        # the same form because the strip-outer-parens function
        # only removes parens that wrap the *entire* expression.
        # But the inner parens themselves stay.
        c1 = canonicalize_predicate("(P) → (Q)")
        c2 = canonicalize_predicate("P → Q")
        # These are NOT equal — the parens around individual
        # operands are preserved.
        assert c1 != c2


class TestMatchesPattern:
    def test_simple_pattern(self):
        bindings: dict[str, str] = {}
        assert matches_pattern(
            "(safe(f)) → (safe(g))",
            "({P}) → ({Q})",
            bindings,
        )
        # Bindings captured.
        assert bindings.get("P") == "safe(f)"
        assert bindings.get("Q") == "safe(g)"

    def test_no_match(self):
        assert not matches_pattern(
            "P → Q ∧ R",
            "{P} ∨ {Q}",
        )

    def test_pattern_with_normalisation(self):
        # Pattern uses Python ``->`` but text uses Lean ``→`` —
        # canonicalisation makes them equivalent.
        bindings: dict[str, str] = {}
        assert matches_pattern(
            "x = 0",
            "{V} == 0",
            bindings,
        )
        assert bindings.get("V") == "x"
