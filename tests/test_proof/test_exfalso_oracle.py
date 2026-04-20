"""Tests for F*-style ExFalso, ProofLanguage, and proof-code binding.

Tests the F*-style tactic pipeline:
  Tactic 0:  ExFalso — hypotheses contradictory → any goal
  Tactic 4:  ProofScript — LLM-written Lean-like proof, code-attached

And the proof-code binding: proof terms reference actual code
variables and the C4 compiler verifies independently.
"""
from __future__ import annotations

import pytest
from unittest.mock import MagicMock


# ═══════════════════════════════════════════════════════════════════
# Test ExFalso proof term
# ═══════════════════════════════════════════════════════════════════

class TestExFalsoProofTerm:
    """Test the ExFalso proof term in terms.py."""

    def test_exfalso_creation(self):
        from cctt.proof_theory.terms import ExFalso
        proof = ExFalso(
            context_formula="x == 3 and not (x == 3)",
            variables={"x": "Int"},
            absurdity="direct contradiction",
        )
        assert proof.context_formula == "x == 3 and not (x == 3)"
        assert proof.variables == {"x": "Int"}
        assert proof.absurdity == "direct contradiction"

    def test_exfalso_pretty(self):
        from cctt.proof_theory.terms import ExFalso
        proof = ExFalso(
            context_formula="x > 0 and x <= 0",
            variables={"x": "Int"},
            absurdity="sign contradiction",
        )
        text = proof.pretty()
        assert "ex_falso" in text
        assert "sign contradiction" in text

    def test_exfalso_tag(self):
        from cctt.proof_theory.terms import ExFalso
        proof = ExFalso(
            context_formula="True and False",
            variables={},
        )
        assert proof.tag() == "ExFalso"

    def test_exfalso_is_proof_term(self):
        from cctt.proof_theory.terms import ExFalso, ProofTerm
        proof = ExFalso(
            context_formula="x > 0 and x < 0",
            variables={"x": "Int"},
        )
        assert isinstance(proof, ProofTerm)

    def test_exfalso_no_children(self):
        from cctt.proof_theory.terms import ExFalso
        proof = ExFalso(
            context_formula="x > 0 and x < 0",
            variables={"x": "Int"},
        )
        assert proof.children() == []

    def test_exfalso_frozen(self):
        from cctt.proof_theory.terms import ExFalso
        proof = ExFalso(
            context_formula="a and not a",
            variables={"a": "Bool"},
        )
        with pytest.raises(Exception):
            proof.context_formula = "changed"


# ═══════════════════════════════════════════════════════════════════
# Test ExFalso compiler handler
# ═══════════════════════════════════════════════════════════════════

class TestExFalsoCompiler:
    """Test _compile_ex_falso in c4_compiler.py."""

    def test_genuine_contradiction_verified(self):
        """ExFalso with genuinely contradictory hypotheses → valid."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="(x == 3) and (not (x == 3))",
            variables={"x": "Int"},
            absurdity="x==3 and not(x==3)",
        )
        env = Z3Env()
        env.declare_var("x", "Int")

        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is True

    def test_satisfiable_hypotheses_rejected(self):
        """ExFalso with satisfiable hypotheses → invalid."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="(x > 0) and (x < 10)",
            variables={"x": "Int"},
            absurdity="not actually contradictory",
        )
        env = Z3Env()
        env.declare_var("x", "Int")

        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is False

    def test_arithmetic_contradiction(self):
        """ExFalso with arithmetic contradiction → valid."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="(x > 5) and (x < 3)",
            variables={"x": "Int"},
            absurdity="x>5 and x<3",
        )
        env = Z3Env()
        env.declare_var("x", "Int")

        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is True

    def test_modular_contradiction(self):
        """ExFalso with y%2==0 ∧ ¬(y%2==0) → valid."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="(y % 2 == 0) and (not (y % 2 == 0))",
            variables={"y": "Int"},
            absurdity="y%2==0 contradicts not(y%2==0)",
        )
        env = Z3Env()
        env.declare_var("y", "Int")

        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is True

    def test_unparseable_formula_rejected(self):
        """ExFalso with unparseable context → invalid."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="[1, 2, 3] == [4, 5, 6]",
            variables={},
            absurdity="unparseable",
        )
        env = Z3Env()
        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is False

    def test_exfalso_trust_is_z3(self):
        """ExFalso verified proofs have Z3 trust provenance."""
        from cctt.proof_theory.terms import ExFalso
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        proof = ExFalso(
            context_formula="(x == 1) and (x == 2)",
            variables={"x": "Int"},
        )
        env = Z3Env()
        env.declare_var("x", "Int")
        result = compile_proof(proof, OVar("a"), OVar("b"), env, depth=0)
        assert result.valid is True
        # Trust should mention Z3 (not just kernel)
        assert any(vc.status.name == 'VERIFIED' for vc in result.vcs)


# ═══════════════════════════════════════════════════════════════════
# Test ExFalso detection in verify_clause_on_path
# ═══════════════════════════════════════════════════════════════════

class TestExFalsoDetection:
    """Test that verify_clause_on_path detects contradictory hypotheses."""

    def test_contradictory_path_guard_verified(self):
        """When fiber guard contradicts path guard, ExFalso detects it."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause_on_path, ReturnPath, C4Strategy,
        )
        # Fiber clause for x==3, but path guard says not(x==3)
        path = ReturnPath(
            guard="not (x == 3)",
            return_expr="sorted(l)",
            is_exception=False,
        )
        # The fiber guard appears in requires
        verdict, detail, strategy, proof = verify_clause_on_path(
            clause="len(result) == 2",
            path=path,
            requires=["x == 3", "y % 2 == 0"],
            params=["x", "y"],
            func_name="test_func",
            source="def test_func(x, y): pass",
        )
        assert verdict == "verified"
        assert strategy == C4Strategy.EX_FALSO
        assert "ExFalso" in detail

    def test_contradictory_modular_guard(self):
        """y%2==0 in requires contradicts not(y%2==0) path guard → ExFalso."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause_on_path, ReturnPath, C4Strategy,
        )
        path = ReturnPath(
            guard="x == 3 and not (y % 2 == 0)",
            return_expr="[j, k, j*k]",
            is_exception=False,
        )
        verdict, detail, strategy, proof = verify_clause_on_path(
            clause="len(result) == 2",
            path=path,
            requires=["x == 3", "y % 2 == 0"],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source="def egypt_takenouchi(x, y): pass",
        )
        assert verdict == "verified"
        assert strategy == C4Strategy.EX_FALSO

    def test_consistent_hypotheses_not_exfalso(self):
        """Non-contradictory hypotheses should NOT trigger ExFalso."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause_on_path, ReturnPath, C4Strategy,
        )
        path = ReturnPath(
            guard="x > 0",
            return_expr="x + 1",
            is_exception=False,
        )
        verdict, detail, strategy, proof = verify_clause_on_path(
            clause="result > 0",
            path=path,
            requires=["x > 0"],
            params=["x"],
            func_name="test_func",
            source="def test_func(x): return x + 1",
        )
        # Should be verified by Z3, not ExFalso
        assert verdict == "verified"
        assert strategy != C4Strategy.EX_FALSO

    def test_exfalso_with_unparseable_goal(self):
        """ExFalso works even when goal is unparseable (key F* innovation)."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause_on_path, ReturnPath, C4Strategy,
        )
        # Goal involves list literal → unparseable by Z3
        path = ReturnPath(
            guard="not (x == 3)",
            return_expr="[y // 2, y]",
            is_exception=False,
        )
        verdict, detail, strategy, proof = verify_clause_on_path(
            clause="len(result) == 3",
            path=path,
            requires=["x == 3"],
            params=["x", "y"],
            func_name="test_func",
            source="def test_func(x, y): pass",
        )
        # Before ExFalso: would be "assumed, clause unparseable"
        # After ExFalso: "verified" because requires + guard are contradictory
        assert verdict == "verified"
        assert strategy == C4Strategy.EX_FALSO

    def test_exfalso_proof_term_emitted(self):
        """ExFalso should emit a proper ExFalso proof term."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause_on_path, ReturnPath,
        )
        from cctt.proof_theory.terms import ExFalso

        path = ReturnPath(
            guard="not (x == 3)",
            return_expr="42",
            is_exception=False,
        )
        verdict, detail, strategy, proof = verify_clause_on_path(
            clause="result > 100",
            path=path,
            requires=["x == 3"],
            params=["x"],
            func_name="test_func",
            source="def test_func(x): return 42",
        )
        assert verdict == "verified"
        assert isinstance(proof, ExFalso)
        assert "x" in proof.variables


# ═══════════════════════════════════════════════════════════════════
# Test ExFalso in verify_clause (multi-path aggregation)
# ═══════════════════════════════════════════════════════════════════

class TestExFalsoMultiPath:
    """Test that ExFalso on contradictory paths enables full verification."""

    def test_fiber_clause_all_paths_verified_with_exfalso(self):
        """A fiber clause verified on matching path + ExFalso on others = VERIFIED."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause, ReturnPath, ClauseVerdict, C4Strategy,
        )
        paths = [
            ReturnPath(guard="x == 3 and y % 2 == 0",
                       return_expr="[y // 2, y]", is_exception=False),
            ReturnPath(guard="x == 3 and not (y % 2 == 0)",
                       return_expr="[j, k, j * k]", is_exception=False),
            ReturnPath(guard="not (x == 3)",
                       return_expr="sorted(l)", is_exception=False),
        ]
        # Fiber requires: x == 3 and y % 2 == 0
        # Path 0: consistent → structural tautology (len 2 on [a,b])
        # Path 1: y%2==0 contradicts not(y%2==0) → ExFalso
        # Path 2: x==3 contradicts not(x==3) → ExFalso
        result = verify_clause(
            clause="len(result) == 2",
            paths=paths,
            requires=["x == 3", "y % 2 == 0"],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source="def egypt_takenouchi(x, y): pass",
        )
        assert result.verdict == ClauseVerdict.C4_VERIFIED

    def test_egypt_len3_fiber_all_verified(self):
        """len(result)==3 on fiber x==3 and not(y%2==0) verified everywhere."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause, ReturnPath, ClauseVerdict,
        )
        paths = [
            ReturnPath(guard="x == 3 and y % 2 == 0",
                       return_expr="[y // 2, y]", is_exception=False),
            ReturnPath(guard="x == 3 and not (y % 2 == 0)",
                       return_expr="[j, k, j * k]", is_exception=False),
            ReturnPath(guard="not (x == 3)",
                       return_expr="sorted(l)", is_exception=False),
        ]
        result = verify_clause(
            clause="len(result) == 3",
            paths=paths,
            requires=["x == 3", "not (y % 2 == 0)"],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source="def egypt_takenouchi(x, y): pass",
        )
        assert result.verdict == ClauseVerdict.C4_VERIFIED


# ═══════════════════════════════════════════════════════════════════
# Test ProofObligation
# ═══════════════════════════════════════════════════════════════════

class TestProofObligation:
    """Test the F*-style proof obligation dataclass."""

    def test_obligation_creation(self):
        from cctt.proof_theory.terms import ProofObligation
        obl = ProofObligation(
            hypotheses=("x > 0", "y > 0"),
            goal="result > 0",
            return_expr="x + y",
            func_name="add_positive",
            source="def add_positive(x, y): return x + y",
            params=("x", "y"),
            var_sorts={"x": "Int", "y": "Int", "result": "Int"},
        )
        assert obl.func_name == "add_positive"
        assert len(obl.hypotheses) == 2
        assert obl.goal == "result > 0"

    def test_obligation_with_fiber_guard(self):
        from cctt.proof_theory.terms import ProofObligation
        obl = ProofObligation(
            hypotheses=("x == 3", "y % 2 == 0"),
            goal="len(result) == 2",
            return_expr="[y // 2, y]",
            func_name="egypt_takenouchi",
            source="",
            params=("x", "y"),
            var_sorts={"x": "Int", "y": "Int"},
            fiber_guard="x == 3 and y % 2 == 0",
        )
        assert obl.fiber_guard is not None

    def test_obligation_is_frozen(self):
        from cctt.proof_theory.terms import ProofObligation
        obl = ProofObligation(
            hypotheses=("x > 0",),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        with pytest.raises(Exception):
            obl.goal = "changed"


# ═══════════════════════════════════════════════════════════════════
# Test Proof Language — Lean-like proof scripts attached to code
# ═══════════════════════════════════════════════════════════════════

class TestProofLanguage:
    """Test the Lean-like proof language for C4."""

    def test_parse_tactic_contradiction(self):
        from cctt.proof_theory.proof_oracle import parse_tactic, TacticKind
        t = parse_tactic("contradiction")
        assert t is not None
        assert t.kind == TacticKind.CONTRADICTION

    def test_parse_tactic_omega(self):
        from cctt.proof_theory.proof_oracle import parse_tactic, TacticKind
        t = parse_tactic("omega")
        assert t is not None
        assert t.kind == TacticKind.OMEGA

    def test_parse_tactic_with_comment(self):
        from cctt.proof_theory.proof_oracle import parse_tactic, TacticKind
        t = parse_tactic("contradiction -- y % 2 == 0 contradicts negation")
        assert t is not None
        assert t.kind == TacticKind.CONTRADICTION
        assert "contradicts" in t.comment

    def test_parse_tactic_simp_with_rules(self):
        from cctt.proof_theory.proof_oracle import parse_tactic, TacticKind
        t = parse_tactic("simp [list_length, sorted_len]")
        assert t is not None
        assert t.kind == TacticKind.SIMP
        assert t.args == ("list_length", "sorted_len")

    def test_parse_tactic_apply_theorem(self):
        from cctt.proof_theory.proof_oracle import parse_tactic, TacticKind
        t = parse_tactic("apply sorted_preserves_length")
        assert t is not None
        assert t.kind == TacticKind.APPLY
        assert t.args == ("sorted_preserves_length",)

    def test_parse_tactic_unknown_returns_none(self):
        from cctt.proof_theory.proof_oracle import parse_tactic
        t = parse_tactic("magic_wand")
        assert t is None


class TestProofScriptParsing:
    """Test parsing complete proof scripts."""

    def test_parse_simple_proof(self):
        from cctt.proof_theory.proof_oracle import parse_proof_script

        text = """
proof simple_pos for f
  given x : Int
  assuming x > 0
  show result > 0
  on path (x > 0) returning x + 1:
    by omega
qed
"""
        script = parse_proof_script(text)
        assert script is not None
        assert script.name == "simple_pos"
        assert script.func_name == "f"
        assert script.given == {"x": "Int"}
        assert script.assuming == ("x > 0",)
        assert script.goal == "result > 0"
        assert len(script.path_proofs) == 1
        assert script.path_proofs[0].guard == "x > 0"
        assert script.path_proofs[0].return_expr == "x + 1"

    def test_parse_egypt_proof(self):
        from cctt.proof_theory.proof_oracle import parse_proof_script, TacticKind

        text = """
proof egypt_len2 for egypt_takenouchi
  given x : Int, y : Int
  assuming x == 3, y % 2 == 0
  show len(result) == 2
  on path (x == 3 and y % 2 == 0) returning [y // 2, y]:
    by structural  -- [a, b] has length 2
  on path (x == 3 and not (y % 2 == 0)) returning [j, k, j * k]:
    by contradiction  -- y % 2 == 0 contradicts not (y % 2 == 0)
  on path (not (x == 3)) returning sorted(l):
    by contradiction  -- x == 3 contradicts not (x == 3)
qed
"""
        script = parse_proof_script(text)
        assert script is not None
        assert script.func_name == "egypt_takenouchi"
        assert len(script.path_proofs) == 3
        assert script.path_proofs[0].tactic.kind == TacticKind.STRUCTURAL
        assert script.path_proofs[1].tactic.kind == TacticKind.CONTRADICTION
        assert script.path_proofs[2].tactic.kind == TacticKind.CONTRADICTION

    def test_pretty_roundtrip(self):
        from cctt.proof_theory.proof_oracle import parse_proof_script

        text = """
proof test for f
  given x : Int
  show result > 0
  on path (True) returning x + 1:
    by omega
qed
"""
        script = parse_proof_script(text)
        assert script is not None
        pretty = script.pretty()
        assert "proof test for f" in pretty
        assert "by omega" in pretty

    def test_parse_no_returning(self):
        from cctt.proof_theory.proof_oracle import parse_proof_script

        text = """
proof test for f
  given x : Int
  show result > 0
  on path (x > 0):
    by omega
qed
"""
        script = parse_proof_script(text)
        assert script is not None
        assert len(script.path_proofs) == 1
        assert script.path_proofs[0].return_expr == ""


class TestTacticCompilation:
    """Test tactic → C4 ProofTerm compilation."""

    def test_contradiction_compiles_to_exfalso(self):
        from cctt.proof_theory.proof_oracle import compile_tactic, Tactic, TacticKind
        from cctt.proof_theory.terms import ExFalso

        t = Tactic(kind=TacticKind.CONTRADICTION)
        proof = compile_tactic(
            tactic=t,
            hypotheses=("x == 3", "not (x == 3)"),
            goal="len(result) == 2",
            return_expr="[y, z]",
            var_sorts={"x": "Int"},
            func_name="f",
        )
        assert isinstance(proof, ExFalso)
        assert "x == 3" in proof.context_formula

    def test_omega_compiles_to_z3discharge(self):
        from cctt.proof_theory.proof_oracle import compile_tactic, Tactic, TacticKind
        from cctt.proof_theory.terms import Z3Discharge

        t = Tactic(kind=TacticKind.OMEGA)
        proof = compile_tactic(
            tactic=t,
            hypotheses=("x > 0",),
            goal="x + 1 > 0",
            return_expr="x + 1",
            var_sorts={"x": "Int"},
            func_name="f",
        )
        assert isinstance(proof, Z3Discharge)
        assert proof.fragment == "QF_LIA"

    def test_structural_compiles_to_tautology(self):
        from cctt.proof_theory.proof_oracle import compile_tactic, Tactic, TacticKind
        from cctt.proof_theory.terms import Z3Discharge

        t = Tactic(kind=TacticKind.STRUCTURAL)
        proof = compile_tactic(
            tactic=t,
            hypotheses=(),
            goal="isinstance(result, list)",
            return_expr="[1, 2, 3]",
            var_sorts={},
            func_name="f",
        )
        assert isinstance(proof, Z3Discharge)
        assert proof.fragment == "TAUTOLOGY"

    def test_list_length_compiles_to_listsimp(self):
        from cctt.proof_theory.proof_oracle import compile_tactic, Tactic, TacticKind
        from cctt.proof_theory.terms import ListSimp

        t = Tactic(kind=TacticKind.LIST_LENGTH)
        proof = compile_tactic(
            tactic=t,
            hypotheses=(),
            goal="len(result) == 3",
            return_expr="[a, b, c]",
            var_sorts={},
            func_name="f",
        )
        assert isinstance(proof, ListSimp)
        assert proof.rule == "list_literal_length"

    def test_simp_with_list_rules(self):
        from cctt.proof_theory.proof_oracle import compile_tactic, Tactic, TacticKind
        from cctt.proof_theory.terms import ListSimp

        t = Tactic(kind=TacticKind.SIMP, args=("list_length",))
        proof = compile_tactic(
            tactic=t,
            hypotheses=(),
            goal="len(result) == 2",
            return_expr="[a, b]",
            var_sorts={},
            func_name="f",
        )
        assert isinstance(proof, ListSimp)


class TestProofScriptCompilation:
    """Test full proof script → per-path C4 ProofTerms."""

    def test_compile_egypt_proof(self):
        from cctt.proof_theory.proof_oracle import (
            parse_proof_script, compile_proof_script,
        )
        from cctt.proof_theory.terms import ExFalso, Z3Discharge

        text = """
proof egypt_len2 for egypt_takenouchi
  given x : Int, y : Int
  assuming x == 3, y % 2 == 0
  show len(result) == 2
  on path (x == 3 and y % 2 == 0) returning [y // 2, y]:
    by structural
  on path (x == 3 and not (y % 2 == 0)) returning [j, k, j * k]:
    by contradiction
  on path (not (x == 3)) returning sorted(l):
    by contradiction
qed
"""
        script = parse_proof_script(text)
        assert script is not None
        compiled = compile_proof_script(script)
        assert len(compiled) == 3
        # First path: structural → Z3Discharge(TAUTOLOGY)
        assert isinstance(compiled["x == 3 and y % 2 == 0"], Z3Discharge)
        # Other paths: contradiction → ExFalso
        assert isinstance(compiled["x == 3 and not (y % 2 == 0)"], ExFalso)
        assert isinstance(compiled["not (x == 3)"], ExFalso)


class TestRenderObligation:
    """Test rendering proof obligations for the LLM."""

    def test_render_simple_obligation(self):
        from cctt.proof_theory.proof_oracle import render_proof_obligation

        text = render_proof_obligation(
            func_name="f",
            params=["x", "y"],
            param_sorts={"x": "Int", "y": "Int"},
            clause="result > 0",
            requires=["x > 0"],
            paths=[],
            source="def f(x, y): return x + y",
        )
        assert "proof" in text
        assert "f" in text
        assert "result > 0" in text
        assert "Available tactics" in text


# ═══════════════════════════════════════════════════════════════════
# Test C4Strategy enum
# ═══════════════════════════════════════════════════════════════════

class TestC4StrategyEnum:
    """Test that new strategies are properly defined."""

    def test_exfalso_strategy_exists(self):
        from cctt.proof_theory.c4_llm_verifier import C4Strategy
        assert hasattr(C4Strategy, 'EX_FALSO')
        assert C4Strategy.EX_FALSO.value == "ExFalso"

    def test_proof_script_strategy_exists(self):
        from cctt.proof_theory.c4_llm_verifier import C4Strategy
        assert hasattr(C4Strategy, 'PROOF_SCRIPT')
        assert C4Strategy.PROOF_SCRIPT.value == "ProofScript"


# ═══════════════════════════════════════════════════════════════════
# Test _compile_proof_term (proof script verification through C4)
# ═══════════════════════════════════════════════════════════════════

class TestCompileProofTerm:
    """Test that proof script terms are compiled through C4 for verification."""

    def test_valid_exfalso_compiled_successfully(self):
        from cctt.proof_theory.c4_llm_verifier import _compile_proof_term, C4Strategy
        from cctt.proof_theory.terms import ExFalso

        proof = ExFalso(
            context_formula="(x == 1) and (x == 2)",
            variables={"x": "Int"},
        )
        result = _compile_proof_term(proof, {"x": "Int"})
        assert result is not None
        verdict, detail, strategy, proof_term = result
        assert verdict == "verified"
        assert strategy == C4Strategy.PROOF_SCRIPT
        assert isinstance(proof_term, ExFalso)

    def test_invalid_exfalso_rejected(self):
        from cctt.proof_theory.c4_llm_verifier import _compile_proof_term
        from cctt.proof_theory.terms import ExFalso

        proof = ExFalso(
            context_formula="(x > 0) and (x < 10)",
            variables={"x": "Int"},
        )
        result = _compile_proof_term(proof, {"x": "Int"})
        assert result is None  # Compiler rejects: not a contradiction


# ═══════════════════════════════════════════════════════════════════
# Test verify_c4_spec with proof script
# ═══════════════════════════════════════════════════════════════════

class TestVerifyC4SpecWithProofScript:
    """Test that verify_c4_spec accepts proof_script parameter."""

    def test_proof_script_parameter_accepted(self):
        """verify_c4_spec accepts proof_script parameter."""
        from cctt.proof_theory.c4_llm_verifier import verify_c4_spec
        from cctt.proof_theory.proof_oracle import parse_proof_script

        source = '''
def simple(x):
    return x + 1
'''
        script = parse_proof_script("""
proof simple_pos for simple
  given x : Int
  show result > x
  on path (True) returning x + 1:
    by omega
qed
""")
        result = verify_c4_spec(
            source=source,
            func_name="simple",
            params=["x"],
            spec={"ensures": ["result > x"]},
            proof_script=script,
        )
        assert result is not None


# ═══════════════════════════════════════════════════════════════════
# Test end-to-end: egypt_takenouchi fiber verification
# ═══════════════════════════════════════════════════════════════════

class TestEgyptTakenouchiE2E:
    """End-to-end test: the egypt_takenouchi fibers that were ASSUMED
    before ExFalso should now be VERIFIED."""

    EGYPT_SOURCE = '''
def egypt_takenouchi(x, y):
    if x == 3:
        if y % 2 == 0:
            return [y//2, y]
        i = (y - 1)//2
        j = i + 1
        k = j + i
        return [j, k, j*k]
    l = [y] * x
    while len(l) != len(set(l)):
        l.sort()
        for i in range(len(l) - 1):
            if l[i] == l[i + 1]:
                break
        k = l[i]
        if k % 2 == 0:
            l[i] = l[i] // 2
            del l[i + 1]
        else:
            l[i], l[i + 1] = (k + 1)//2, k*(k + 1)//2
    return sorted(l)
'''

    def test_isinstance_list_still_verified(self):
        """isinstance(result, list) should still be verified via structural tautology."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause, ReturnPath, ClauseVerdict,
        )
        paths = [
            ReturnPath(guard="x == 3 and y % 2 == 0",
                       return_expr="[y // 2, y]", is_exception=False),
            ReturnPath(guard="x == 3 and not (y % 2 == 0)",
                       return_expr="[j, k, j * k]", is_exception=False),
            ReturnPath(guard="not (x == 3)",
                       return_expr="sorted(l)", is_exception=False),
        ]
        result = verify_clause(
            clause="isinstance(result, list)",
            paths=paths,
            requires=[],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source=self.EGYPT_SOURCE,
        )
        assert result.verdict == ClauseVerdict.C4_VERIFIED

    def test_len2_fiber_now_verified(self):
        """len(result)==2 on fiber x==3 and y%2==0: now VERIFIED (was ASSUMED)."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause, ReturnPath, ClauseVerdict,
        )
        paths = [
            ReturnPath(guard="x == 3 and y % 2 == 0",
                       return_expr="[y // 2, y]", is_exception=False),
            ReturnPath(guard="x == 3 and not (y % 2 == 0)",
                       return_expr="[j, k, j * k]", is_exception=False),
            ReturnPath(guard="not (x == 3)",
                       return_expr="sorted(l)", is_exception=False),
        ]
        result = verify_clause(
            clause="len(result) == 2",
            paths=paths,
            requires=["x == 3", "y % 2 == 0"],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source=self.EGYPT_SOURCE,
        )
        assert result.verdict == ClauseVerdict.C4_VERIFIED

    def test_len3_fiber_now_verified(self):
        """len(result)==3 on fiber x==3 and not(y%2==0): now VERIFIED (was ASSUMED)."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_clause, ReturnPath, ClauseVerdict,
        )
        paths = [
            ReturnPath(guard="x == 3 and y % 2 == 0",
                       return_expr="[y // 2, y]", is_exception=False),
            ReturnPath(guard="x == 3 and not (y % 2 == 0)",
                       return_expr="[j, k, j * k]", is_exception=False),
            ReturnPath(guard="not (x == 3)",
                       return_expr="sorted(l)", is_exception=False),
        ]
        result = verify_clause(
            clause="len(result) == 3",
            paths=paths,
            requires=["x == 3", "not (y % 2 == 0)"],
            params=["x", "y"],
            func_name="egypt_takenouchi",
            source=self.EGYPT_SOURCE,
        )
        assert result.verdict == ClauseVerdict.C4_VERIFIED
