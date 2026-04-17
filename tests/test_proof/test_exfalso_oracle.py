"""Tests for F*-style ExFalso, ProofOracle, and proof-code binding.

Tests the F*-style tactic pipeline:
  Tactic 0:  ExFalso — hypotheses contradictory → any goal
  Tactic 4:  ProofOracle — LLM/automated proof term generation

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
# Test ProofOracle
# ═══════════════════════════════════════════════════════════════════

class TestProofOracle:
    """Test the proof oracle framework."""

    def test_mock_oracle_returns_none(self):
        from cctt.proof_theory.proof_oracle import MockProofOracle
        from cctt.proof_theory.terms import ProofObligation

        oracle = MockProofOracle()
        obl = ProofObligation(
            hypotheses=("x > 0",),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        assert oracle.generate_proof(obl) is None

    def test_automated_oracle_detects_contradiction(self):
        from cctt.proof_theory.proof_oracle import AutomatedProofOracle
        from cctt.proof_theory.terms import ProofObligation, ExFalso

        oracle = AutomatedProofOracle()
        obl = ProofObligation(
            hypotheses=("x == 3", "not (x == 3)"),
            goal="len(result) == 999",  # doesn't matter — contradiction
            return_expr="[1, 2, 3]",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        proof = oracle.generate_proof(obl)
        assert proof is not None
        assert isinstance(proof, ExFalso)

    def test_automated_oracle_no_contradiction(self):
        from cctt.proof_theory.proof_oracle import AutomatedProofOracle
        from cctt.proof_theory.terms import ProofObligation

        oracle = AutomatedProofOracle()
        obl = ProofObligation(
            hypotheses=("x > 0", "x < 10"),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        proof = oracle.generate_proof(obl)
        assert proof is None  # Not a contradiction, can't auto-prove

    def test_llm_oracle_falls_back_to_automated(self):
        from cctt.proof_theory.proof_oracle import LLMProofOracle
        from cctt.proof_theory.terms import ProofObligation, ExFalso

        oracle = LLMProofOracle(spec_oracle=None)
        obl = ProofObligation(
            hypotheses=("x > 10", "x < 5"),
            goal="anything",
            return_expr="42",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        proof = oracle.generate_proof(obl)
        assert isinstance(proof, ExFalso)

    def test_llm_oracle_no_proof_without_llm(self):
        from cctt.proof_theory.proof_oracle import LLMProofOracle
        from cctt.proof_theory.terms import ProofObligation

        oracle = LLMProofOracle(spec_oracle=None)
        obl = ProofObligation(
            hypotheses=("x > 0",),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        proof = oracle.generate_proof(obl)
        # No contradiction, no LLM → None
        assert proof is None


# ═══════════════════════════════════════════════════════════════════
# Test proof JSON parsing
# ═══════════════════════════════════════════════════════════════════

class TestProofJsonParsing:
    """Test parse_proof_json for LLM-generated proof terms."""

    def test_parse_exfalso_json(self):
        from cctt.proof_theory.proof_oracle import parse_proof_json
        from cctt.proof_theory.terms import ProofObligation, ExFalso

        obl = ProofObligation(
            hypotheses=("x > 0",),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        data = {
            "tactic": "ExFalso",
            "context_formula": "x > 0 and x < 0",
            "variables": {"x": "Int"},
            "absurdity": "test contradiction",
        }
        proof = parse_proof_json(data, obl)
        assert isinstance(proof, ExFalso)
        assert proof.context_formula == "x > 0 and x < 0"

    def test_parse_z3discharge_json(self):
        from cctt.proof_theory.proof_oracle import parse_proof_json
        from cctt.proof_theory.terms import ProofObligation, Z3Discharge

        obl = ProofObligation(
            hypotheses=("x > 0",),
            goal="result > 0",
            return_expr="x",
            func_name="f",
            source="",
            params=("x",),
            var_sorts={"x": "Int"},
        )
        data = {
            "tactic": "Z3Discharge",
            "formula": "x > 0",
            "fragment": "QF_LIA",
        }
        proof = parse_proof_json(data, obl)
        assert isinstance(proof, Z3Discharge)

    def test_parse_listsim_json(self):
        from cctt.proof_theory.proof_oracle import parse_proof_json
        from cctt.proof_theory.terms import ProofObligation, ListSimp

        obl = ProofObligation(
            hypotheses=(),
            goal="len(result) == 3",
            return_expr="[1, 2, 3]",
            func_name="f",
            source="",
            params=(),
            var_sorts={},
        )
        data = {
            "tactic": "ListSimp",
            "rule": "literal_len",
            "target": "len([1,2,3]) == 3",
        }
        proof = parse_proof_json(data, obl)
        assert isinstance(proof, ListSimp)

    def test_parse_unknown_tactic_returns_none(self):
        from cctt.proof_theory.proof_oracle import parse_proof_json
        from cctt.proof_theory.terms import ProofObligation

        obl = ProofObligation(
            hypotheses=(),
            goal="result > 0",
            return_expr="1",
            func_name="f",
            source="",
            params=(),
            var_sorts={},
        )
        data = {"tactic": "MagicWand"}
        proof = parse_proof_json(data, obl)
        assert proof is None


# ═══════════════════════════════════════════════════════════════════
# Test C4Strategy enum
# ═══════════════════════════════════════════════════════════════════

class TestC4StrategyEnum:
    """Test that new strategies are properly defined."""

    def test_exfalso_strategy_exists(self):
        from cctt.proof_theory.c4_llm_verifier import C4Strategy
        assert hasattr(C4Strategy, 'EX_FALSO')
        assert C4Strategy.EX_FALSO.value == "ExFalso"

    def test_proof_oracle_strategy_exists(self):
        from cctt.proof_theory.c4_llm_verifier import C4Strategy
        assert hasattr(C4Strategy, 'PROOF_ORACLE')
        assert C4Strategy.PROOF_ORACLE.value == "ProofOracle"


# ═══════════════════════════════════════════════════════════════════
# Test _compile_oracle_proof
# ═══════════════════════════════════════════════════════════════════

class TestCompileOracleProof:
    """Test that oracle proofs are compiled through C4 for verification."""

    def test_valid_exfalso_compiled_successfully(self):
        from cctt.proof_theory.c4_llm_verifier import _compile_oracle_proof, C4Strategy
        from cctt.proof_theory.terms import ExFalso

        proof = ExFalso(
            context_formula="(x == 1) and (x == 2)",
            variables={"x": "Int"},
        )
        result = _compile_oracle_proof(proof, {"x": "Int"})
        assert result is not None
        verdict, detail, strategy, proof_term = result
        assert verdict == "verified"
        assert strategy == C4Strategy.PROOF_ORACLE
        assert isinstance(proof_term, ExFalso)

    def test_invalid_exfalso_rejected(self):
        from cctt.proof_theory.c4_llm_verifier import _compile_oracle_proof
        from cctt.proof_theory.terms import ExFalso

        proof = ExFalso(
            context_formula="(x > 0) and (x < 10)",
            variables={"x": "Int"},
        )
        result = _compile_oracle_proof(proof, {"x": "Int"})
        assert result is None  # Compiler rejects: not a contradiction


# ═══════════════════════════════════════════════════════════════════
# Test verify_c4_spec with proof oracle
# ═══════════════════════════════════════════════════════════════════

class TestVerifyC4SpecWithOracle:
    """Test that verify_c4_spec passes proof_oracle through."""

    def test_oracle_parameter_accepted(self):
        """verify_c4_spec accepts proof_oracle parameter."""
        from cctt.proof_theory.c4_llm_verifier import verify_c4_spec
        from cctt.proof_theory.proof_oracle import AutomatedProofOracle

        source = '''
def simple(x):
    return x + 1
'''
        oracle = AutomatedProofOracle()
        result = verify_c4_spec(
            source=source,
            func_name="simple",
            params=["x"],
            spec={"ensures": ["result > x"]},
            proof_oracle=oracle,
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
