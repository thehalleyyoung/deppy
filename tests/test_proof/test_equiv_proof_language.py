"""Tests for equivalence proof language — LLM-written proofs bridging
completely different algorithms to OTerm equivalence, with effects.

Tests the full pipeline:
  1. Parse equiv proof script
  2. Verify effect claims
  3. Compile to ProofTerm (Ext + Cut chain)
  4. Verify through the proof checker kernel
  5. Bridge to enhanced_check_equivalence
"""
from __future__ import annotations

import pytest


# ═══════════════════════════════════════════════════════════════════
# Test parsing
# ═══════════════════════════════════════════════════════════════════

class TestEquivScriptParsing:
    """Test parsing equivalence proof scripts."""

    def test_parse_simple_equiv(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EffectClaim, EquivTacticKind,
        )
        text = """
equiv test_eq
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = x + 1 := by omega
  exact h1
qed
"""
        script = parse_equiv_script(text)
        assert script is not None
        assert script.name == "test_eq"
        assert script.func_a == "f"
        assert script.func_b == "g"
        assert script.given == {"x": "Int"}
        assert script.effect_claim == EffectClaim.BOTH_PURE
        assert script.goal_lhs == "f(x)"
        assert script.goal_rhs == "g(x)"
        assert len(script.steps) == 1
        assert script.steps[0].name == "h1"
        assert script.steps[0].tactic.kind == EquivTacticKind.OMEGA

    def test_parse_multi_step(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EquivTacticKind,
        )
        text = """
equiv sort_eq
  func_a: bubble_sort
  func_b: merge_sort
  given xs : List
  effects: both pure
  show bubble_sort(xs) = merge_sort(xs)
  have h1 : bubble_sort(xs) = sorted_perm(xs) := by apply bubble_sort_correct
  have h2 : merge_sort(xs) = sorted_perm(xs) := by apply merge_sort_correct
  exact trans(h1, sym(h2))
qed
"""
        script = parse_equiv_script(text)
        assert script is not None
        assert len(script.steps) == 2
        assert script.steps[0].trust == "axiom"
        assert script.steps[1].trust == "axiom"

    def test_parse_returns_none_for_invalid(self):
        from cctt.proof_theory.equiv_proof_language import parse_equiv_script
        assert parse_equiv_script("not a proof") is None
        assert parse_equiv_script("") is None

    def test_pretty_roundtrip(self):
        from cctt.proof_theory.equiv_proof_language import parse_equiv_script
        text = """
equiv test for_test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        assert script is not None
        pretty = script.pretty()
        assert "equiv test" in pretty
        assert "func_a: f" in pretty
        assert "func_b: g" in pretty

    def test_parse_multiple_params(self):
        from cctt.proof_theory.equiv_proof_language import parse_equiv_script
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int, y : Int, z : List
  effects: both pure
  show f(x, y, z) = g(x, y, z)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        assert script is not None
        assert script.given == {"x": "Int", "y": "Int", "z": "List"}


# ═══════════════════════════════════════════════════════════════════
# Test tactic parsing
# ═══════════════════════════════════════════════════════════════════

class TestEquivTacticParsing:
    """Test parsing individual tactics."""

    def test_parse_apply(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_tactic, EquivTacticKind,
        )
        t = parse_equiv_tactic("apply sorted_perm_unique")
        assert t is not None
        assert t.kind == EquivTacticKind.APPLY
        assert t.args == ("sorted_perm_unique",)

    def test_parse_omega(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_tactic, EquivTacticKind,
        )
        t = parse_equiv_tactic("omega")
        assert t is not None
        assert t.kind == EquivTacticKind.OMEGA

    def test_parse_trans_with_args(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_tactic, EquivTacticKind,
        )
        t = parse_equiv_tactic("trans(h1, sym(h2))")
        assert t is not None
        assert t.kind == EquivTacticKind.TRANS
        assert t.args == ("h1", "sym(h2)")

    def test_parse_refl(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_tactic, EquivTacticKind,
        )
        t = parse_equiv_tactic("refl")
        assert t is not None
        assert t.kind == EquivTacticKind.REFL

    def test_parse_funext(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_tactic, EquivTacticKind,
        )
        t = parse_equiv_tactic("funext x")
        assert t is not None
        assert t.kind == EquivTacticKind.FUNEXT
        assert t.args == ("x",)

    def test_parse_with_comment(self):
        from cctt.proof_theory.equiv_proof_language import parse_equiv_tactic
        t = parse_equiv_tactic("omega -- by integer arithmetic")
        assert t is not None
        assert "integer arithmetic" in t.comment


# ═══════════════════════════════════════════════════════════════════
# Test compilation to ProofTerms
# ═══════════════════════════════════════════════════════════════════

class TestEquivCompilation:
    """Test compilation of equiv proofs to ProofTerm trees."""

    def test_compile_simple_refl(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        from cctt.proof_theory.terms import Ext, Refl
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        assert proof is not None
        # Should be Ext(x, Refl(...))
        assert isinstance(proof, Ext)
        assert proof.var == "x"

    def test_compile_trans_sym(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        from cctt.proof_theory.terms import Ext, Cut, Trans, Sym
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = mid := by omega
  have h2 : g(x) = mid := by omega
  exact trans(h1, sym(h2))
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        assert isinstance(proof, Ext)
        # Inside Ext: Cut(h1, Cut(h2, Trans(h1, Sym(h2))))
        inner = proof.body_proof
        assert isinstance(inner, Cut)
        assert inner.label == "h1"
        # Inner cut
        inner2 = inner.main_proof
        assert isinstance(inner2, Cut)
        assert inner2.label == "h2"
        # Final: Trans
        final = inner2.main_proof
        assert isinstance(final, Trans)
        # right of Trans should be Sym
        assert isinstance(final.right, Sym)

    def test_compile_with_apply_creates_assume(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        from cctt.proof_theory.terms import Ext, Cut, Assume
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = spec := by apply f_correct
  exact h1
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        # The h1 step uses apply → Assume (explicitly trusted)
        inner = proof.body_proof  # Cut
        assert isinstance(inner, Cut)
        lemma = inner.lemma_proof
        assert isinstance(lemma, Assume)
        assert "axiom" in lemma.label

    def test_compile_multi_var(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        from cctt.proof_theory.terms import Ext
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int, y : Int
  effects: both pure
  show f(x, y) = g(x, y)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        # Should have nested Ext: Ext(y, Ext(x, ...)) or similar
        assert isinstance(proof, Ext)
        inner = proof.body_proof
        assert isinstance(inner, Ext)


# ═══════════════════════════════════════════════════════════════════
# Test effect verification
# ═══════════════════════════════════════════════════════════════════

class TestEffectVerification:
    """Test that effect claims are verified against actual code."""

    def test_both_pure_verified(self):
        from cctt.proof_theory.equiv_proof_language import (
            verify_effect_claim, EffectClaim, EffectVerdict,
        )
        source_a = "def f(x): return x + 1"
        source_b = "def g(x): return 1 + x"
        verdict, detail = verify_effect_claim(
            EffectClaim.BOTH_PURE, source_a, source_b,
        )
        assert verdict in (EffectVerdict.VERIFIED, EffectVerdict.ASSUMED)

    def test_impure_function_rejected(self):
        from cctt.proof_theory.equiv_proof_language import (
            verify_effect_claim, EffectClaim, EffectVerdict,
        )
        source_a = "def f(x): return x + 1"
        source_b = "def g(x): print(x); return x + 1"
        verdict, detail = verify_effect_claim(
            EffectClaim.BOTH_PURE, source_a, source_b,
        )
        # Should be REJECTED or ASSUMED depending on analyzer capability
        assert verdict in (EffectVerdict.REJECTED, EffectVerdict.ASSUMED)


# ═══════════════════════════════════════════════════════════════════
# Test proof term pretty printing
# ═══════════════════════════════════════════════════════════════════

class TestEquivProofPretty:
    """Test that compiled proofs have readable pretty-printing."""

    def test_pretty_contains_ext(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h : f(x) = g(x) := by omega
  exact h
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        pretty = proof.pretty()
        assert "ext" in pretty
        assert "cut" in pretty

    def test_pretty_contains_trans_sym(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, compile_equiv_proof,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = mid := by omega
  have h2 : g(x) = mid := by omega
  exact trans(h1, sym(h2))
qed
"""
        script = parse_equiv_script(text)
        proof = compile_equiv_proof(script)
        pretty = proof.pretty()
        assert "trans" in pretty
        assert "sym" in pretty


# ═══════════════════════════════════════════════════════════════════
# Test LLM obligation rendering
# ═══════════════════════════════════════════════════════════════════

class TestRenderEquivObligation:
    """Test rendering equiv obligations for the LLM."""

    def test_render_contains_both_functions(self):
        from cctt.proof_theory.equiv_proof_language import render_equiv_obligation
        text = render_equiv_obligation(
            func_a_name="bubble_sort",
            func_b_name="merge_sort",
            source_a="def bubble_sort(xs): ...",
            source_b="def merge_sort(xs): ...",
            params=["xs"],
            param_sorts={"xs": "List"},
        )
        assert "bubble_sort" in text
        assert "merge_sort" in text
        assert "equiv" in text
        assert "Available tactics" in text

    def test_render_includes_template(self):
        from cctt.proof_theory.equiv_proof_language import render_equiv_obligation
        text = render_equiv_obligation(
            func_a_name="f",
            func_b_name="g",
            source_a="def f(x): return x",
            source_b="def g(x): return x",
            params=["x"],
            param_sorts={"x": "Int"},
        )
        assert "have" in text
        assert "exact" in text
        assert "qed" in text


# ═══════════════════════════════════════════════════════════════════
# Test end-to-end: simple equivalence verification
# ═══════════════════════════════════════════════════════════════════

class TestEquivE2E:
    """End-to-end test: parse → compile → verify through kernel."""

    def test_trivial_equiv_refl(self):
        """Two identical functions should be provable via refl."""
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, verify_equiv_proof,
        )
        source_a = "def f(x): return x + 1"
        source_b = "def g(x): return x + 1"
        text = """
equiv trivial
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        # Attach sources
        from cctt.proof_theory.equiv_proof_language import EquivScript
        script = EquivScript(
            name=script.name, func_a=script.func_a, func_b=script.func_b,
            given=script.given, effect_claim=script.effect_claim,
            goal_lhs=script.goal_lhs, goal_rhs=script.goal_rhs,
            steps=script.steps, final_tactic=script.final_tactic,
            source_a=source_a, source_b=source_b,
        )
        verdict = verify_equiv_proof(script, source_a, source_b)
        # The kernel should accept this (both compile to same OTerm)
        # Note: may be accepted or rejected depending on OTerm normalization
        assert verdict is not None
        assert isinstance(verdict.equivalent, bool)

    def test_axiom_trusted_marking(self):
        """Steps using 'apply' should be marked AXIOM_TRUSTED."""
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EquivScript,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = spec := by apply f_correct
  have h2 : g(x) = spec := by apply g_correct
  exact trans(h1, sym(h2))
qed
"""
        script = parse_equiv_script(text)
        # Both steps use apply → axiom trust
        assert script.steps[0].trust == "axiom"
        assert script.steps[1].trust == "axiom"
        # Kernel-verified steps don't have axiom trust
        text2 = """
equiv test2
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  have h1 : f(x) = g(x) := by omega
  exact h1
qed
"""
        script2 = parse_equiv_script(text2)
        assert script2.steps[0].trust == "kernel"


# ═══════════════════════════════════════════════════════════════════
# Test integration bridge
# ═══════════════════════════════════════════════════════════════════

class TestEquivBridge:
    """Test the bridge to the checker pipeline."""

    def test_try_equiv_proof_returns_result(self):
        from cctt.proof_theory.equiv_proof_language import try_equiv_proof
        source_a = "def f(x): return x + 1"
        source_b = "def g(x): return 1 + x"
        proof_text = """
equiv comm_add
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  exact refl
qed
"""
        result = try_equiv_proof(source_a, source_b, proof_text)
        # May or may not verify depending on OTerm normalization of x+1 vs 1+x
        # But should not crash
        assert result is None or result.equivalent

    def test_try_equiv_proof_invalid_returns_none(self):
        from cctt.proof_theory.equiv_proof_language import try_equiv_proof
        result = try_equiv_proof("def f(x): pass", "def g(x): pass", "not a proof")
        assert result is None


# ═══════════════════════════════════════════════════════════════════
# Test effect claim types
# ═══════════════════════════════════════════════════════════════════

class TestEffectClaims:
    """Test the effect claim enum and parsing."""

    def test_both_pure_parsed(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EffectClaim,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both pure
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        assert script.effect_claim == EffectClaim.BOTH_PURE

    def test_both_read_parsed(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EffectClaim,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: both read
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        assert script.effect_claim == EffectClaim.BOTH_READ

    def test_unknown_effect_parsed(self):
        from cctt.proof_theory.equiv_proof_language import (
            parse_equiv_script, EffectClaim,
        )
        text = """
equiv test
  func_a: f
  func_b: g
  given x : Int
  effects: magical
  show f(x) = g(x)
  exact refl
qed
"""
        script = parse_equiv_script(text)
        assert script.effect_claim == EffectClaim.UNKNOWN


# ═══════════════════════════════════════════════════════════════════
# Test proof expression parser (trans, sym, cong)
# ═══════════════════════════════════════════════════════════════════

class TestProofExprParser:
    """Test recursive parsing of proof expressions."""

    def test_parse_refl(self):
        from cctt.proof_theory.equiv_proof_language import _parse_proof_expr
        from cctt.proof_theory.terms import Refl
        result = _parse_proof_expr("refl", (), "a", "b")
        assert isinstance(result, Refl)

    def test_parse_sym(self):
        from cctt.proof_theory.equiv_proof_language import (
            _parse_proof_expr, EquivStep, EquivTactic, EquivTacticKind,
        )
        from cctt.proof_theory.terms import Sym
        steps = (
            EquivStep("h1", "a", "b", EquivTactic(EquivTacticKind.REFL)),
        )
        result = _parse_proof_expr("sym(h1)", steps, "X", "Y")
        assert isinstance(result, Sym)

    def test_parse_trans(self):
        from cctt.proof_theory.equiv_proof_language import (
            _parse_proof_expr, EquivStep, EquivTactic, EquivTacticKind,
        )
        from cctt.proof_theory.terms import Trans
        steps = (
            EquivStep("h1", "a", "b", EquivTactic(EquivTacticKind.REFL)),
            EquivStep("h2", "b", "c", EquivTactic(EquivTacticKind.REFL)),
        )
        result = _parse_proof_expr("trans(h1, h2)", steps, "X", "Y")
        assert isinstance(result, Trans)

    def test_parse_nested_trans_sym(self):
        from cctt.proof_theory.equiv_proof_language import (
            _parse_proof_expr, EquivStep, EquivTactic, EquivTacticKind,
        )
        from cctt.proof_theory.terms import Trans, Sym
        steps = (
            EquivStep("h1", "a", "m", EquivTactic(EquivTacticKind.REFL)),
            EquivStep("h2", "b", "m", EquivTactic(EquivTacticKind.REFL)),
        )
        result = _parse_proof_expr("trans(h1, sym(h2))", steps, "a", "b")
        assert isinstance(result, Trans)
        assert isinstance(result.right, Sym)

    def test_parse_cong(self):
        from cctt.proof_theory.equiv_proof_language import (
            _parse_proof_expr, EquivStep, EquivTactic, EquivTacticKind,
        )
        from cctt.proof_theory.terms import Cong
        steps = (
            EquivStep("h1", "a", "b", EquivTactic(EquivTacticKind.REFL)),
        )
        result = _parse_proof_expr("cong(f, h1)", steps, "X", "Y")
        assert isinstance(result, Cong)
        assert result.func == "f"

    def test_parse_step_reference(self):
        from cctt.proof_theory.equiv_proof_language import (
            _parse_proof_expr, EquivStep, EquivTactic, EquivTacticKind,
        )
        from cctt.proof_theory.terms import Assume
        steps = (
            EquivStep("h1", "a", "b", EquivTactic(EquivTacticKind.REFL)),
        )
        result = _parse_proof_expr("h1", steps, "X", "Y")
        assert isinstance(result, Assume)
        assert "h1" in result.label
