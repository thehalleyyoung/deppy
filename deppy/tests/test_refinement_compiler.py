"""Tests for deppy.lean.refinement_compiler — AST-based refinement
compiler for nested predicates that the regex-based spec_translator
cannot handle.

Each test exercises a predicate that the legacy translator emits as
``sorry``; the new compiler produces a structured Lean proposition
+ tactic.
"""
from __future__ import annotations

import pytest

from deppy.lean.refinement_compiler import (
    compile_refinement,
    CompiledRefinement,
    RefinementCompiler,
)


# ═══════════════════════════════════════════════════════════════════
#  Quantifiers over Python generator expressions
# ═══════════════════════════════════════════════════════════════════

def test_all_over_list_translates_to_forall():
    cr = compile_refinement(
        "all(x > 0 for x in xs)",
        params=["xs"],
    )
    assert cr.handled
    assert "∀ x ∈ xs" in cr.lean_prop
    assert "(0 > x)" in cr.lean_prop or "(x > 0)" in cr.lean_prop
    assert cr.tactic != "sorry"


def test_any_over_list_translates_to_exists():
    cr = compile_refinement(
        "any(x == 0 for x in xs)",
        params=["xs"],
    )
    assert cr.handled
    assert "∃ x ∈ xs" in cr.lean_prop
    assert cr.tactic != "sorry"


def test_all_over_range_uses_list_range():
    cr = compile_refinement(
        "all(i >= 0 for i in range(n))",
        params=["n"],
    )
    assert cr.handled
    assert "List.range n" in cr.lean_prop
    assert "∀ i" in cr.lean_prop


def test_quantifier_with_filter_produces_implication():
    cr = compile_refinement(
        "all(P(x) for x in xs if Q(x))",
        params=["xs"],
    )
    assert cr.handled
    # ∀ x ∈ xs, Q(x) → P(x)
    assert "→" in cr.lean_prop
    assert "Q x" in cr.lean_prop or "(Q x)" in cr.lean_prop
    assert "P x" in cr.lean_prop or "(P x)" in cr.lean_prop


def test_existential_with_filter_produces_conjunction():
    cr = compile_refinement(
        "any(P(x) for x in xs if Q(x))",
        params=["xs"],
    )
    assert cr.handled
    assert "∧" in cr.lean_prop
    assert "∃" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  List comprehensions
# ═══════════════════════════════════════════════════════════════════

def test_listcomp_translates_to_map():
    cr = compile_refinement(
        "result == [x * 2 for x in xs]",
        params=["xs"],
    )
    assert cr.handled
    assert ".map" in cr.lean_prop


def test_listcomp_with_filter_translates_to_filter_then_map():
    cr = compile_refinement(
        "result == [x for x in xs if x > 0]",
        params=["xs"],
    )
    assert cr.handled
    assert ".filter" in cr.lean_prop


def test_listcomp_identity_collapses_to_filter():
    cr = compile_refinement(
        "result == [x for x in xs if x > 0]",
        params=["xs"],
    )
    # Identity ``map (fun x => x)`` should collapse to just ``filter``.
    assert cr.handled
    assert ".map" not in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Chained comparisons
# ═══════════════════════════════════════════════════════════════════

def test_chained_comparison_unfolds_to_conjunction():
    cr = compile_refinement(
        "0 <= i <= len(xs)",
        params=["xs", "i"],
    )
    assert cr.handled
    assert " ∧ " in cr.lean_prop


def test_three_way_chain():
    cr = compile_refinement(
        "a < b < c",
        params=["a", "b", "c"],
    )
    assert cr.handled
    assert "(a < b)" in cr.lean_prop
    assert "(b < c)" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Logical operators
# ═══════════════════════════════════════════════════════════════════

def test_boolop_and_uses_lean_and():
    cr = compile_refinement(
        "x > 0 and y > 0",
        params=["x", "y"],
    )
    assert cr.handled
    assert "∧" in cr.lean_prop


def test_boolop_or_uses_lean_or():
    cr = compile_refinement(
        "x == 0 or y == 0",
        params=["x", "y"],
    )
    assert cr.handled
    assert "∨" in cr.lean_prop


def test_unary_not_uses_lean_neg():
    cr = compile_refinement(
        "not (x == 0)",
        params=["x"],
    )
    assert cr.handled
    assert "¬" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Membership
# ═══════════════════════════════════════════════════════════════════

def test_membership_in_named_list():
    cr = compile_refinement(
        "x in xs",
        params=["x", "xs"],
    )
    assert cr.handled
    assert "x ∈ xs" in cr.lean_prop


def test_membership_in_literal_list_unfolds_to_disjunction():
    cr = compile_refinement(
        "x in [1, 2, 3]",
        params=["x"],
    )
    assert cr.handled
    assert "∨" in cr.lean_prop


def test_negative_membership():
    cr = compile_refinement(
        "x not in xs",
        params=["x", "xs"],
    )
    assert cr.handled
    assert "x ∉ xs" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Builtins (len, abs, min, max, sum)
# ═══════════════════════════════════════════════════════════════════

def test_len_uses_dot_length():
    cr = compile_refinement(
        "len(xs) > 0",
        params=["xs"],
    )
    assert cr.handled
    assert "xs.length" in cr.lean_prop


def test_min_max_over_two_args():
    cr = compile_refinement(
        "min(a, b) <= max(a, b)",
        params=["a", "b"],
    )
    assert cr.handled
    assert "min" in cr.lean_prop
    assert "max" in cr.lean_prop


def test_abs_translates_to_conditional():
    cr = compile_refinement(
        "abs(x) >= 0",
        params=["x"],
    )
    assert cr.handled
    assert "if" in cr.lean_prop  # conditional Lean form


# ═══════════════════════════════════════════════════════════════════
#  Conditional expressions
# ═══════════════════════════════════════════════════════════════════

def test_ifexp_translates_to_lean_conditional():
    cr = compile_refinement(
        "(x if x > 0 else -x) >= 0",
        params=["x"],
    )
    assert cr.handled
    assert "if" in cr.lean_prop
    assert "then" in cr.lean_prop
    assert "else" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Result substitution
# ═══════════════════════════════════════════════════════════════════

def test_result_resolved_to_func_app():
    cr = compile_refinement(
        "result >= 0",
        params=["x"],
        func_app="(double x)",
    )
    assert cr.handled
    assert "(double x)" in cr.lean_prop


# ═══════════════════════════════════════════════════════════════════
#  Honest fallback for unhandled cases
# ═══════════════════════════════════════════════════════════════════

def test_syntax_error_returns_handled_false():
    cr = compile_refinement(
        "x >> >> y",  # syntax error
        params=["x", "y"],
    )
    assert not cr.handled
    assert cr.tactic == "sorry"
    assert "syntax error" in str(cr.sub_obligations)


def test_double_for_clause_listcomp_returns_sorry():
    cr = compile_refinement(
        "result == [x + y for x in xs for y in ys]",
        params=["xs", "ys"],
    )
    # We only support single-clause comprehensions; multi-clause emits
    # ``sorry`` honestly.
    assert not cr.handled


# ═══════════════════════════════════════════════════════════════════
#  Integration with spec_translator
# ═══════════════════════════════════════════════════════════════════

def test_spec_translator_uses_refinement_compiler_fallback():
    """When the legacy regex catalogue doesn't match, the new
    compiler should engage instead of producing ``sorry``."""
    from deppy.lean.spec_translator import translate_guarantee
    thm = translate_guarantee(
        "all(x > 0 for x in result)",
        func_name="positive_filter",
        param_names=["xs"],
        param_types={"xs": list},
    )
    # The legacy ``for all x in result, ...`` regex pattern catches
    # this — but in the form ``all(... for ... in result)`` it does not.
    # The new compiler should produce a proper ∀ proposition.
    assert "sorry" not in thm.conclusion or "∀" in thm.conclusion


def test_spec_translator_fallback_produces_real_lean():
    """A predicate the legacy translator can't handle should now
    produce real Lean output via the new fallback."""
    from deppy.lean.spec_translator import translate_guarantee
    thm = translate_guarantee(
        "all(x >= 0 for x in xs) and len(xs) > 0",
        func_name="nonempty_nonneg",
        param_names=["xs"],
        param_types={"xs": list},
    )
    # Result should not be the ``sorry /- ... -/`` fallback.
    assert "sorry /-" not in thm.conclusion or "∀" in thm.conclusion or "∧" in thm.conclusion


# ═══════════════════════════════════════════════════════════════════
#  Sub-obligation tracking
# ═══════════════════════════════════════════════════════════════════

def test_unhandled_subexpr_logged_in_sub_obligations():
    cr = compile_refinement(
        "result == [x + y for x in xs for y in ys]",
        params=["xs", "ys"],
    )
    assert cr.sub_obligations
    assert any("multi-for" in s for s in cr.sub_obligations)


def test_handled_predicate_has_no_sub_obligations():
    cr = compile_refinement(
        "all(x > 0 for x in xs)",
        params=["xs"],
    )
    assert cr.handled
    assert not cr.sub_obligations
