"""Tests for c4_llm_verifier — C4-native spec validation and verification."""
from __future__ import annotations

import pytest
from cctt.proof_theory.c4_llm_verifier import (
    validate_c4_clause,
    validate_c4_spec,
    extract_return_paths,
    verify_clause_on_path,
    verify_clause,
    verify_c4_spec,
    check_path_exhaustiveness,
    ClauseVerdict,
    C4Strategy,
    ReturnPath,
    C4SpecVerdict,
    build_c4_spec_prompt,
    _infer_result_sort,
    _is_boolean_tautology,
    _inject_builtin_axioms,
    C4_SPEC_SYSTEM_PROMPT,
)


# ═══════════════════════════════════════════════════════════════════
# Clause Validation
# ═══════════════════════════════════════════════════════════════════

class TestValidateClause:
    """Test that the validator accepts C4 and rejects non-C4."""

    def test_simple_comparison(self):
        ok, _ = validate_c4_clause("result >= 0", {"x", "result"})
        assert ok

    def test_arithmetic(self):
        ok, _ = validate_c4_clause("result == x + y", {"x", "y", "result"})
        assert ok

    def test_boolean_connective(self):
        ok, _ = validate_c4_clause("result >= 0 and result <= x", {"x", "result"})
        assert ok

    def test_builtin_function(self):
        ok, _ = validate_c4_clause("result == abs(x)", {"x", "result"})
        assert ok

    def test_isinstance(self):
        ok, _ = validate_c4_clause("isinstance(result, int)", {"x", "result"})
        assert ok

    def test_conditional(self):
        ok, _ = validate_c4_clause("result == x if x > 0 else result == -x",
                                    {"x", "result"})
        assert ok

    def test_len(self):
        ok, _ = validate_c4_clause("len(result) == len(x)", {"x", "result"})
        assert ok

    def test_reject_english(self):
        ok, reason = validate_c4_clause("returns a non-negative number", {"x", "result"})
        assert not ok
        assert "English" in reason or "unknown" in reason.lower()

    def test_reject_method_call(self):
        ok, reason = validate_c4_clause("q.is_zero is not True", {"q", "result"})
        assert not ok

    def test_reject_comprehension(self):
        ok, reason = validate_c4_clause(
            "all(result[i] <= result[i+1] for i in range(len(result)-1))",
            {"result"},
        )
        assert not ok

    def test_reject_subscript(self):
        ok, reason = validate_c4_clause("result[0] == x", {"x", "result"})
        assert not ok

    def test_reject_unknown_variable(self):
        ok, reason = validate_c4_clause("result == z + 1", {"x", "result"})
        assert not ok
        assert "unknown" in reason.lower()

    def test_reject_non_builtin_function(self):
        ok, reason = validate_c4_clause("result == sorted(x)", {"x", "result"})
        assert not ok

    def test_reject_is_operator(self):
        ok, reason = validate_c4_clause("result is S.NaN", {"result"})
        assert not ok

    def test_empty_clause(self):
        ok, _ = validate_c4_clause("", {"result"})
        assert not ok

    def test_negation(self):
        ok, _ = validate_c4_clause("not (result == 0)", {"result"})
        assert ok

    def test_chained_comparison(self):
        ok, _ = validate_c4_clause("0 <= result <= x", {"x", "result"})
        assert ok

    def test_self_attribute(self):
        ok, _ = validate_c4_clause("result >= 0", {"self", "result"})
        assert ok

    def test_max_min(self):
        ok, _ = validate_c4_clause("result == max(x, y)", {"x", "y", "result"})
        assert ok


class TestValidateSpec:
    """Test full spec validation."""

    def test_valid_spec(self):
        spec = {
            "requires": ["x > 0"],
            "ensures": ["result >= 0", "result == abs(x)"],
            "fibers": [
                {"name": "pos", "guard": "x >= 0", "ensures": ["result == x"]},
            ],
        }
        ok, errors = validate_c4_spec(spec, ["x"])
        assert ok, errors

    def test_invalid_ensures(self):
        spec = {
            "ensures": ["result.is_integer()"],  # method call
        }
        ok, errors = validate_c4_spec(spec, ["x"])
        assert not ok
        assert len(errors) >= 1

    def test_invalid_fiber_guard(self):
        spec = {
            "fibers": [
                {"name": "bad", "guard": "x.is_positive", "ensures": ["result > 0"]},
            ],
        }
        ok, errors = validate_c4_spec(spec, ["x"])
        assert not ok

    def test_invalid_returns_expr(self):
        spec = {
            "returns_expr": "sorted(lst)",
        }
        ok, errors = validate_c4_spec(spec, ["lst"])
        assert not ok


# ═══════════════════════════════════════════════════════════════════
# Path Extraction
# ═══════════════════════════════════════════════════════════════════

class TestPathExtraction:
    """Test extracting return paths from source."""

    def test_simple_return(self):
        source = "def f(x):\n    return x + 1"
        paths = extract_return_paths(source, "f")
        assert len(paths) == 1
        assert paths[0].guard == "True"
        assert "x + 1" in paths[0].return_expr

    def test_conditional_return(self):
        source = """\
def abs_val(x):
    if x >= 0:
        return x
    else:
        return -x
"""
        paths = extract_return_paths(source, "abs_val")
        assert len(paths) == 2
        guards = {p.guard for p in paths}
        assert any("x >= 0" in g for g in guards)
        assert any("not" in g for g in guards)

    def test_nested_conditions(self):
        source = """\
def classify(x):
    if x > 0:
        return 1
    elif x < 0:
        return -1
    else:
        return 0
"""
        paths = extract_return_paths(source, "classify")
        assert len(paths) == 3

    def test_exception_path(self):
        source = """\
def safe_div(x, y):
    if y == 0:
        raise ValueError("div by zero")
    return x // y
"""
        paths = extract_return_paths(source, "safe_div")
        assert any(p.is_exception for p in paths)
        assert any(not p.is_exception for p in paths)

    def test_no_return(self):
        source = "def f(x):\n    pass"
        paths = extract_return_paths(source, "f")
        # Should get implicit None return
        assert len(paths) >= 1

    def test_wrong_function_name(self):
        source = "def f(x):\n    return x"
        paths = extract_return_paths(source, "g")
        assert len(paths) == 0


# ═══════════════════════════════════════════════════════════════════
# Clause Verification
# ═══════════════════════════════════════════════════════════════════

class TestClauseVerification:
    """Test Z3-based clause verification per path."""

    def test_verified_simple(self):
        """result == x + 1 should be verified when return is x + 1."""
        path = ReturnPath(guard="True", return_expr="x + 1")
        verdict, detail, _strat, _proof = verify_clause_on_path(
            "result == x + 1", path, [], ["x"])
        assert verdict == "verified"

    def test_verified_nonnegative(self):
        """result >= 0 should be verified when return is x * x."""
        path = ReturnPath(guard="True", return_expr="x * x")
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result >= 0", path, [], ["x"])
        assert verdict == "verified"

    def test_failed_contradiction(self):
        """result == x should fail when return is x + 1."""
        path = ReturnPath(guard="True", return_expr="x + 1")
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result == x", path, [], ["x"])
        assert verdict == "failed"

    def test_assumed_uninterpreted(self):
        """With axioms, abs(x) == max(x, -x) is now provable."""
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result == max(x, -x)", path, [], ["x"])
        # axiom injection makes this provable: abs definition + max semantics
        assert verdict == "verified"

    def test_guarded_path(self):
        """Under guard x >= 0, result == x is verified for return x."""
        path = ReturnPath(guard="x >= 0", return_expr="x")
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result >= 0", path, [], ["x"])
        assert verdict == "verified"

    def test_requires_as_hypothesis(self):
        """Requires should be used as hypotheses."""
        path = ReturnPath(guard="True", return_expr="x")
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result > 0", path, ["x > 0"], ["x"])
        assert verdict == "verified"

    def test_exception_path_assumed(self):
        """Exception paths don't apply to postconditions."""
        path = ReturnPath(guard="y == 0", return_expr="raise(ValueError)",
                         is_exception=True)
        verdict, _, _strat, _proof = verify_clause_on_path(
            "result >= 0", path, [], ["y"])
        assert verdict == "assumed"


class TestFullClauseVerification:
    """Test verify_clause across ALL paths."""

    def test_verified_on_all_paths(self):
        paths = [
            ReturnPath(guard="x >= 0", return_expr="x"),
            ReturnPath(guard="x < 0", return_expr="-x"),
        ]
        result = verify_clause("result >= 0", paths, [], ["x"])
        assert result.verdict == ClauseVerdict.C4_VERIFIED

    def test_failed_on_one_path(self):
        paths = [
            ReturnPath(guard="x >= 0", return_expr="x"),
            ReturnPath(guard="x < 0", return_expr="x"),  # wrong! x < 0 means result < 0
        ]
        result = verify_clause("result >= 0", paths, [], ["x"])
        assert result.verdict == ClauseVerdict.C4_FAILED

    def test_mixed_paths(self):
        paths = [
            ReturnPath(guard="x >= 0", return_expr="x"),
            ReturnPath(guard="x < 0", return_expr="abs(x)"),  # uninterpreted
        ]
        result = verify_clause("result >= 0", paths, [], ["x"])
        # First path verified, second assumed → overall assumed
        assert result.verdict in (ClauseVerdict.C4_ASSUMED, ClauseVerdict.C4_VERIFIED)


# ═══════════════════════════════════════════════════════════════════
# Path Exhaustiveness
# ═══════════════════════════════════════════════════════════════════

class TestExhaustiveness:
    """Test path coverage under requires."""

    def test_exhaustive_unconditional(self):
        paths = [ReturnPath(guard="True", return_expr="x")]
        result = check_path_exhaustiveness(paths, [], ["x"])
        assert result == "verified"

    def test_exhaustive_complement(self):
        paths = [
            ReturnPath(guard="x >= 0", return_expr="x"),
            ReturnPath(guard="x < 0", return_expr="-x"),
        ]
        result = check_path_exhaustiveness(paths, [], ["x"])
        assert result == "verified"

    def test_not_exhaustive(self):
        paths = [
            ReturnPath(guard="x > 0", return_expr="x"),
            # Missing: x == 0 and x < 0
        ]
        result = check_path_exhaustiveness(paths, [], ["x"])
        assert result == "failed"

    def test_exhaustive_under_requires(self):
        paths = [
            ReturnPath(guard="x > 0", return_expr="x"),
        ]
        # Under requires x > 0, the single guard covers everything
        result = check_path_exhaustiveness(paths, ["x > 0"], ["x"])
        assert result == "verified"


# ═══════════════════════════════════════════════════════════════════
# Full Pipeline: verify_c4_spec
# ═══════════════════════════════════════════════════════════════════

class TestVerifyC4Spec:
    """Test the full C4 verification pipeline."""

    def test_abs_val_fully_verified(self):
        source = """\
def abs_val(x):
    if x >= 0:
        return x
    else:
        return -x
"""
        spec = {
            "requires": [],
            "ensures": ["result >= 0"],
            "fibers": [
                {"name": "pos", "guard": "x >= 0", "ensures": ["result == x"]},
                {"name": "neg", "guard": "x < 0", "ensures": ["result == -x"]},
            ],
        }
        verdict = verify_c4_spec(source, "abs_val", ["x"], spec)
        # result >= 0 should be C4_VERIFIED across both paths
        assert verdict.n_failed == 0
        assert verdict.n_rejected == 0
        # At least the global ensures should be verified
        global_clauses = [c for c in verdict.clause_results
                         if not c.clause.startswith("[fiber:")]
        assert any(c.verdict == ClauseVerdict.C4_VERIFIED for c in global_clauses)

    def test_wrong_spec_detected(self):
        source = "def inc(x):\n    return x + 1"
        spec = {
            "ensures": ["result == x"],  # wrong!
        }
        verdict = verify_c4_spec(source, "inc", ["x"], spec)
        assert verdict.n_failed >= 1

    def test_non_c4_clause_rejected(self):
        source = "def f(x):\n    return x"
        spec = {
            "ensures": ["result == x", "q.is_positive"],  # second is not C4
        }
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        assert verdict.n_rejected >= 1
        # First clause should still be verified
        verified_clauses = [c for c in verdict.clause_results
                           if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert len(verified_clauses) >= 1

    def test_exhaustiveness_checked(self):
        source = """\
def abs_val(x):
    if x >= 0:
        return x
    else:
        return -x
"""
        spec = {"ensures": ["result >= 0"]}
        verdict = verify_c4_spec(source, "abs_val", ["x"], spec)
        assert verdict.exhaustiveness == "verified"

    def test_empty_spec(self):
        source = "def f(x):\n    return x"
        spec = {"ensures": [], "requires": []}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        assert verdict.n_verified == 0
        assert verdict.n_failed == 0

    def test_add_function(self):
        source = "def add(a, b):\n    return a + b"
        spec = {
            "ensures": ["result == a + b"],
            "returns_expr": "a + b",
        }
        verdict = verify_c4_spec(source, "add", ["a", "b"], spec)
        assert verdict.n_verified >= 1
        assert verdict.n_failed == 0

    def test_clamp_with_fibers(self):
        source = """\
def clamp(x, lo, hi):
    if x < lo:
        return lo
    elif x > hi:
        return hi
    else:
        return x
"""
        spec = {
            "requires": ["lo <= hi"],
            "ensures": ["result >= lo", "result <= hi"],
            "fibers": [
                {"name": "below", "guard": "x < lo", "ensures": ["result == lo"]},
                {"name": "above", "guard": "x > hi", "ensures": ["result == hi"]},
                {"name": "mid", "guard": "x >= lo and x <= hi", "ensures": ["result == x"]},
            ],
        }
        verdict = verify_c4_spec(source, "clamp", ["x", "lo", "hi"], spec)
        assert verdict.n_failed == 0

    def test_verdict_json_serializable(self):
        source = "def f(x):\n    return x + 1"
        spec = {"ensures": ["result > x"]}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        j = verdict.to_json()
        assert "n_verified" in j
        assert "summary" in j
        assert j["func_name"] == "f"


# ═══════════════════════════════════════════════════════════════════
# Integration with baseline_prove
# ═══════════════════════════════════════════════════════════════════

class TestBaselineProveIntegration:
    """Test that baseline_prove uses C4 verification when oracle present."""

    def test_baseline_prove_without_oracle(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )
        defn = Definition(
            name="inc", qualname="test.inc",
            kind=DefKind.FUNCTION, lineno=1, end_lineno=2,
            source="def inc(x):\n    return x + 1",
            docstring="", params=["x"],
            return_annotation=None, decorators=[],
            class_name=None, module_path="test",
        )
        result = baseline_prove(defn, "test")
        assert result.annotation is not None

    def test_baseline_prove_with_mock_oracle(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )
        from cctt.proof_theory.spec_oracle import MockLLMOracle

        defn = Definition(
            name="abs", qualname="test.abs",
            kind=DefKind.FUNCTION, lineno=1, end_lineno=4,
            source="def abs(x):\n    if x >= 0:\n        return x\n    return -x",
            docstring="", params=["x"],
            return_annotation=None, decorators=[],
            class_name=None, module_path="test",
        )
        result = baseline_prove(defn, "test", spec_oracle=MockLLMOracle())
        assert result.annotation is not None
        spec = result.annotation.formal_spec
        assert spec is not None
        # Should have C4 verdict information
        intent_data = spec.get("intent_spec", {})
        if intent_data:
            c4v = intent_data.get("c4_verdict")
            if c4v:
                assert "n_verified" in c4v
                assert "n_failed" in c4v


# ═══════════════════════════════════════════════════════════════════
# Prompt Generation
# ═══════════════════════════════════════════════════════════════════

class TestPromptGeneration:
    """Test the C4 spec prompt."""

    def test_prompt_includes_c4_grammar(self):
        assert "Z3" in C4_SPEC_SYSTEM_PROMPT
        assert "FORBIDDEN" in C4_SPEC_SYSTEM_PROMPT
        assert "Method calls" in C4_SPEC_SYSTEM_PROMPT or "method" in C4_SPEC_SYSTEM_PROMPT.lower()

    def test_build_prompt_includes_source(self):
        prompt = build_c4_spec_prompt(
            "def f(x):\n    return x + 1", "f", ["x"], "increment x")
        assert "def f(x)" in prompt
        assert "f" in prompt
        assert "x" in prompt

    def test_build_prompt_no_docstring(self):
        prompt = build_c4_spec_prompt("def f(x): return x", "f", ["x"])
        assert "def f(x)" in prompt


# ═══════════════════════════════════════════════════════════════════
# Tactics: Sort Inference, Axiom Injection, Tautology Detection
# ═══════════════════════════════════════════════════════════════════

class TestSortInference:
    """Test that sorts are inferred from function names and annotations."""

    def test_is_predicate_returns_bool(self):
        assert _infer_result_sort("is_positive", "") == "Bool"
        assert _infer_result_sort("_eval_is_integer", "") == "Bool"
        assert _infer_result_sort("has_key", "") == "Bool"

    def test_regular_function_returns_int(self):
        assert _infer_result_sort("compute", "") == "Int"
        assert _infer_result_sort("add", "") == "Int"

    def test_annotation_overrides(self):
        src = "def f(x) -> bool:\n    return True"
        assert _infer_result_sort("f", src) == "Bool"

    def test_float_annotation(self):
        src = "def f(x) -> float:\n    return 1.0"
        assert _infer_result_sort("f", src) == "Real"


class TestTautologyDetection:
    """Test that boolean tautologies are detected."""

    def test_bool_exhaustion(self):
        r = _is_boolean_tautology("result == True or result == False", "Bool")
        assert r is not None
        assert "tautology" in r

    def test_not_tautology_for_int(self):
        r = _is_boolean_tautology("result == True or result == False", "Int")
        assert r is None

    def test_isinstance_bool(self):
        r = _is_boolean_tautology("isinstance(result, bool)", "Bool")
        assert r is not None


class TestAxiomInjection:
    """Test that builtin axioms enable verification via LibraryAxiom strategy."""

    def test_abs_nonneg_verified(self):
        """With abs axiom, result >= 0 for abs(x) should be verified."""
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _, strat, _proof = verify_clause_on_path(
            "result >= 0", path, [], ["x"],
            func_name="my_abs", source="def my_abs(x): return abs(x)")
        assert verdict == "verified"
        assert strat == C4Strategy.LIBRARY_AXIOM

    def test_max_ge_both(self):
        """With max axioms, max(x,y) >= x should be verified."""
        path = ReturnPath(guard="True", return_expr="max(x, y)")
        verdict, _, strat, _proof = verify_clause_on_path(
            "result >= x", path, [], ["x", "y"],
            func_name="my_max",
            source="def my_max(x, y): return max(x, y)")
        assert verdict == "verified"
        assert strat == C4Strategy.LIBRARY_AXIOM

    def test_len_nonneg(self):
        """With len axiom, len(x) >= 0 should be verified."""
        path = ReturnPath(guard="True", return_expr="len(x)")
        verdict, _, strat, _proof = verify_clause_on_path(
            "result >= 0", path, [], ["x"],
            func_name="my_len", source="def my_len(x): return len(x)")
        assert verdict == "verified"
        assert strat == C4Strategy.LIBRARY_AXIOM


class TestBoolPredicateVerification:
    """Test that is_* functions get Bool sort and verify accordingly."""

    def test_is_predicate_bool_tautology_verified(self):
        """_eval_is_integer with result == True or result == False
        should be verified via Tautology strategy."""
        source = "def _eval_is_integer(self):\n    return True"
        spec = {"ensures": ["result == True or result == False"]}
        verdict = verify_c4_spec(source, "_eval_is_integer", [], spec)
        assert verdict.n_verified >= 1
        assert verdict.n_failed == 0
        # Check strategy is Tautology
        verified_clauses = [c for c in verdict.clause_results
                           if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert any(c.strategy == C4Strategy.TAUTOLOGY for c in verified_clauses)

    def test_is_positive_bool(self):
        source = "def is_positive(x):\n    return x > 0"
        spec = {"ensures": ["result == True or result == False"]}
        verdict = verify_c4_spec(source, "is_positive", ["x"], spec)
        assert verdict.n_verified >= 1


class TestC4StrategyLabeling:
    """Test that each verified clause is labeled with its C4 strategy."""

    def test_z3_discharge_simple(self):
        """Direct Z3 proof should use Z3_DISCHARGE strategy."""
        path = ReturnPath(guard="True", return_expr="x + 1")
        verdict, _, strat, _proof = verify_clause_on_path(
            "result == x + 1", path, [], ["x"])
        assert verdict == "verified"
        assert strat == C4Strategy.Z3_DISCHARGE

    def test_cases_split_multipath(self):
        """Multi-path function should use CasesSplit strategy."""
        source = "def f(x):\n    if x >= 0:\n        return x\n    else:\n        return -x"
        spec = {"ensures": ["result >= 0"]}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        verified = [c for c in verdict.clause_results
                   if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert len(verified) >= 1
        assert verified[0].strategy == C4Strategy.CASES_SPLIT

    def test_refinement_descent_fibers(self):
        """Fiber clauses should use RefinementDescent strategy."""
        source = "def f(x):\n    if x >= 0:\n        return x\n    else:\n        return -x"
        spec = {
            "ensures": ["result >= 0"],
            "fibers": [
                {"name": "pos", "guard": "x >= 0", "ensures": ["result == x"]},
                {"name": "neg", "guard": "x < 0", "ensures": ["result == -x"]},
            ],
        }
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        fiber_verified = [c for c in verdict.clause_results
                         if c.verdict == ClauseVerdict.C4_VERIFIED
                         and c.clause.startswith("[fiber:")]
        assert len(fiber_verified) >= 2
        assert all(c.strategy == C4Strategy.REFINEMENT_DESCENT
                   for c in fiber_verified)

    def test_library_axiom_abs(self):
        """abs(x) == max(x, -x) should use LIBRARY_AXIOM strategy."""
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _, strat, _proof = verify_clause_on_path(
            "result == max(x, -x)", path, [], ["x"])
        assert verdict == "verified"
        assert strat == C4Strategy.LIBRARY_AXIOM

    def test_strategy_in_json(self):
        """Strategy should appear in JSON output."""
        source = "def f(x):\n    return x + 1"
        spec = {"ensures": ["result > x"]}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        j = verdict.to_json()
        clauses = j["clauses"]
        assert len(clauses) >= 1
        assert "strategy" in clauses[0]
        assert clauses[0]["strategy"] is not None


# ═══════════════════════════════════════════════════════════════════
# Dependency Topological Sort
# ═══════════════════════════════════════════════════════════════════

class TestDependencyTopoSort:
    """Test call graph + topological sort for proof ordering."""

    def test_leaf_functions_first(self):
        """Leaf functions (no internal calls) should be in level 0."""
        from cctt.proof_theory.library_proof_orchestrator import (
            build_call_graph, topological_sort_definitions,
            Definition, DefKind,
        )
        d1 = Definition(name="helper", qualname="m.helper",
                       kind=DefKind.FUNCTION, lineno=1, end_lineno=2,
                       source="def helper(x):\n    return x + 1",
                       docstring="", params=["x"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        d2 = Definition(name="main", qualname="m.main",
                       kind=DefKind.FUNCTION, lineno=3, end_lineno=4,
                       source="def main(x):\n    return helper(x) * 2",
                       docstring="", params=["x"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        graph = build_call_graph([d1, d2])
        assert graph["helper"] == set()  # leaf
        assert "helper" in graph["main"]  # main calls helper

        levels = topological_sort_definitions([d1, d2], graph)
        assert len(levels) >= 2
        level0_names = {d.name for d in levels[0]}
        assert "helper" in level0_names  # leaf first
        # main must be in a later level
        remaining_names = {d.name for lvl in levels[1:] for d in lvl}
        assert "main" in remaining_names

    def test_independent_functions_same_level(self):
        """Functions with no mutual dependencies are in the same level."""
        from cctt.proof_theory.library_proof_orchestrator import (
            build_call_graph, topological_sort_definitions,
            Definition, DefKind,
        )
        defs = []
        for name in ["a", "b", "c"]:
            defs.append(Definition(
                name=name, qualname=f"m.{name}",
                kind=DefKind.FUNCTION, lineno=1, end_lineno=2,
                source=f"def {name}(x):\n    return x",
                docstring="", params=["x"],
                return_annotation=None, decorators=[],
                class_name=None, module_path="m"))
        graph = build_call_graph(defs)
        levels = topological_sort_definitions(defs, graph)
        assert len(levels) == 1  # all independent → one level
        assert len(levels[0]) == 3

    def test_mutual_recursion_same_level(self):
        """Mutually recursive functions should be in the same SCC level."""
        from cctt.proof_theory.library_proof_orchestrator import (
            build_call_graph, topological_sort_definitions,
            Definition, DefKind,
        )
        d1 = Definition(name="even", qualname="m.even",
                       kind=DefKind.FUNCTION, lineno=1, end_lineno=3,
                       source="def even(n):\n    if n == 0: return True\n    return odd(n - 1)",
                       docstring="", params=["n"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        d2 = Definition(name="odd", qualname="m.odd",
                       kind=DefKind.FUNCTION, lineno=4, end_lineno=6,
                       source="def odd(n):\n    if n == 0: return False\n    return even(n - 1)",
                       docstring="", params=["n"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        graph = build_call_graph([d1, d2])
        assert "odd" in graph["even"]
        assert "even" in graph["odd"]

        levels = topological_sort_definitions([d1, d2], graph)
        # Mutually recursive → same level
        scc_level = [l for l in levels if len(l) == 2]
        assert len(scc_level) == 1
        names = {d.name for d in scc_level[0]}
        assert names == {"even", "odd"}

    def test_chain_dependency(self):
        """A→B→C should produce 3 levels."""
        from cctt.proof_theory.library_proof_orchestrator import (
            build_call_graph, topological_sort_definitions,
            Definition, DefKind,
        )
        dc = Definition(name="c", qualname="m.c",
                       kind=DefKind.FUNCTION, lineno=1, end_lineno=2,
                       source="def c(x):\n    return x",
                       docstring="", params=["x"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        db = Definition(name="b", qualname="m.b",
                       kind=DefKind.FUNCTION, lineno=3, end_lineno=4,
                       source="def b(x):\n    return c(x) + 1",
                       docstring="", params=["x"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        da = Definition(name="a", qualname="m.a",
                       kind=DefKind.FUNCTION, lineno=5, end_lineno=6,
                       source="def a(x):\n    return b(x) * 2",
                       docstring="", params=["x"],
                       return_annotation=None, decorators=[],
                       class_name=None, module_path="m")
        graph = build_call_graph([da, db, dc])
        levels = topological_sort_definitions([da, db, dc], graph)
        assert len(levels) == 3
        level_names = [[d.name for d in l] for l in levels]
        assert level_names[0] == ["c"]  # leaf
        assert level_names[1] == ["b"]  # depends on c
        assert level_names[2] == ["a"]  # depends on b

    def test_call_graph_ignores_external(self):
        """Calls to names not in definitions should be ignored."""
        from cctt.proof_theory.library_proof_orchestrator import (
            build_call_graph, Definition, DefKind,
        )
        d = Definition(name="f", qualname="m.f",
                      kind=DefKind.FUNCTION, lineno=1, end_lineno=2,
                      source="def f(x):\n    return len(x) + abs(x)",
                      docstring="", params=["x"],
                      return_annotation=None, decorators=[],
                      class_name=None, module_path="m")
        graph = build_call_graph([d])
        assert graph["f"] == set()  # len, abs are external


# ═══════════════════════════════════════════════════════════════════
# Proof Term Emission
# ═══════════════════════════════════════════════════════════════════

class TestProofTermEmission:
    """Test that verified clauses emit ProofTerms that compile through C4."""

    def test_z3_discharge_emits_proof(self):
        """Z3Discharge tactic should emit a Z3Discharge ProofTerm."""
        from cctt.proof_theory.terms import Z3Discharge as Z3DischargeTerm
        path = ReturnPath(guard="True", return_expr="x + 1")
        verdict, _, strat, proof = verify_clause_on_path(
            "result == x + 1", path, [], ["x"])
        assert verdict == "verified"
        assert proof is not None
        assert isinstance(proof, Z3DischargeTerm)
        assert "result == x + 1" in proof.formula

    def test_tautology_emits_z3discharge(self):
        """Tautologies should emit Z3Discharge (not Refl, per rubber-duck review)."""
        from cctt.proof_theory.terms import Z3Discharge as Z3DischargeTerm
        path = ReturnPath(guard="True", return_expr="True")
        verdict, _, strat, proof = verify_clause_on_path(
            "result == True or result == False", path, [], [])
        assert verdict == "verified"
        assert proof is not None
        assert isinstance(proof, Z3DischargeTerm)
        # Fragment is set by the Z3 solver, not necessarily 'TAUTOLOGY'
        assert proof.fragment in ('TAUTOLOGY', 'QF_LIA')

    def test_library_axiom_emits_proof(self):
        """LibraryAxiom tactic should emit a LibraryAxiom ProofTerm."""
        from cctt.proof_theory.library_axioms import LibraryAxiom as LibAxiomTerm
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _, strat, proof = verify_clause_on_path(
            "result >= 0", path, [], ["x"])
        assert verdict == "verified"
        assert proof is not None
        assert isinstance(proof, LibAxiomTerm)
        assert proof.library == 'builtins'

    def test_failed_emits_no_proof(self):
        """Failed verification should emit no ProofTerm."""
        path = ReturnPath(guard="True", return_expr="x - 1")
        verdict, _, _, proof = verify_clause_on_path(
            "result == x + 1", path, [], ["x"])
        assert verdict == "failed"
        assert proof is None

    def test_assumed_emits_no_proof(self):
        """Assumed verification should emit no ProofTerm."""
        path = ReturnPath(guard="True", return_expr="foo(x)")
        verdict, _, _, proof = verify_clause_on_path(
            "result > 0", path, [], ["x"])
        assert verdict == "assumed"
        assert proof is None

    def test_cases_split_emits_cases_proof(self):
        """Multi-path verification should emit CasesSplit ProofTerm."""
        from cctt.proof_theory.terms import CasesSplit as CasesSplitTerm
        source = "def f(x):\n    if x >= 0:\n        return x\n    else:\n        return -x"
        spec = {"ensures": ["result >= 0"]}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        assert verdict.n_verified >= 1
        verified = [c for c in verdict.clause_results if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert len(verified) >= 1
        assert verified[0].proof_term is not None
        assert isinstance(verified[0].proof_term, CasesSplitTerm)

    def test_verify_c4_spec_collects_proof_terms(self):
        """verify_c4_spec should collect emitted proofs and attempt compilation."""
        source = "def add(a, b):\n    return a + b"
        spec = {"ensures": ["result == a + b"]}
        verdict = verify_c4_spec(source, "add", ["a", "b"], spec)
        assert verdict.n_verified >= 1
        # Proof terms are collected even if compilation fails on Z3-internal formulas
        assert len(verdict.proof_terms) >= 1

    def test_clause_result_has_proof_goal(self):
        """ClauseResult should include a proof_goal string."""
        source = "def inc(x):\n    return x + 1"
        spec = {"ensures": ["result == x + 1"]}
        verdict = verify_c4_spec(source, "inc", ["x"], spec)
        verified = [c for c in verdict.clause_results if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert len(verified) >= 1
        assert verified[0].proof_goal != ""

    def test_compile_verdict_stored(self):
        """ClauseResult should have compile_verdict after compilation."""
        source = "def f(x):\n    return x"
        spec = {"ensures": ["result == x"]}
        verdict = verify_c4_spec(source, "f", ["x"], spec)
        verified = [c for c in verdict.clause_results if c.verdict == ClauseVerdict.C4_VERIFIED]
        assert len(verified) >= 1
        assert verified[0].compile_verdict is not None


# ═══════════════════════════════════════════════════════════════════
# F*-style ProofTerm Constructors
# ═══════════════════════════════════════════════════════════════════

class TestFStarProofTerms:
    """Test that the new F*-style proof terms compile correctly.

    For sub-proofs using Refl, we pass the same OTerm as both lhs and rhs
    so the Refl VC succeeds (definitional equality). For Z3Discharge
    sub-proofs, we use valid Python expressions (not => which is not Python).
    """

    def test_weakest_precondition_compiles(self):
        """WeakestPrecondition should compile through the C4 compiler."""
        from cctt.proof_theory.terms import WeakestPrecondition, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        # Use Refl for precondition (trivial case: f≡f)
        f = OVar("f")
        wp = WeakestPrecondition(
            statement_desc="x := x + 1",
            postcondition="x > 0",
            wp_formula="x + 1 > 0",
            precondition_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(wp, f, f, env, depth=0)
        assert result.valid
        assert any("WeakestPrecondition" in vc.rule for vc in result.vcs)

    def test_effect_frame_compiles(self):
        """EffectFrame should compile through the C4 compiler."""
        from cctt.proof_theory.terms import EffectFrame, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        ef = EffectFrame(
            frame_vars=("self_count",),
            function_desc="increment",
            preserved_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(ef, f, f, env, depth=0)
        assert result.valid
        assert any("EffectFrame" in vc.rule for vc in result.vcs)

    def test_exception_case_compiles(self):
        """ExceptionCase should compile through the C4 compiler."""
        from cctt.proof_theory.terms import ExceptionCase, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        ec = ExceptionCase(
            normal_proof=Refl(term=f),
            exception_proofs={
                "ValueError": Refl(term=f),
            },
        )
        env = Z3Env()
        result = compile_proof(ec, f, f, env, depth=0)
        assert result.valid
        assert any("ExceptionCase" in vc.rule for vc in result.vcs)

    def test_normalize_compiles(self):
        """Normalize should compile through the C4 compiler."""
        from cctt.proof_theory.terms import Normalize
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        n = Normalize(
            reduction_steps=("β", "δ", "arithmetic"),
            normal_form_desc="x + 1",
        )
        env = Z3Env()
        result = compile_proof(n, OVar("f"), OVar("g"), env, depth=0)
        assert result.valid
        assert any("Normalize" in vc.rule for vc in result.vcs)

    def test_dependent_match_compiles(self):
        """DependentMatch should compile through the C4 compiler."""
        from cctt.proof_theory.terms import DependentMatch, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        dm = DependentMatch(
            discriminant=OVar("x"),
            discriminant_type="type(x)",
            branches={
                "int": Refl(term=f),
                "float": Refl(term=f),
            },
        )
        env = Z3Env()
        result = compile_proof(dm, f, f, env, depth=0)
        assert result.valid
        assert any("DependentMatch" in vc.rule for vc in result.vcs)

    def test_lemma_app_compiles(self):
        """LemmaApp should compile through the C4 compiler."""
        from cctt.proof_theory.terms import LemmaApp, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        la = LemmaApp(
            lemma_name="add_comm",
            instantiation={"a": OVar("x"), "b": OVar("y")},
            lemma_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(la, f, f, env, depth=0)
        assert result.valid
        assert any("LemmaApp" in vc.rule for vc in result.vcs)

    def test_unfold_compiles(self):
        """Unfold should compile through the C4 compiler."""
        from cctt.proof_theory.terms import Unfold, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        u = Unfold(
            func_name="double",
            args=(OVar("x"),),
            inner_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(u, f, f, env, depth=0)
        assert result.valid
        assert any("Unfold" in vc.rule for vc in result.vcs)

    def test_assert_compiles(self):
        """Assert should compile through the C4 compiler."""
        from cctt.proof_theory.terms import Assert, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        a = Assert(
            assertion="x == x",
            assertion_proof=Refl(term=f),
            continuation=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(a, f, f, env, depth=0)
        assert result.valid
        assert any("Assert" in vc.rule for vc in result.vcs)


# ═══════════════════════════════════════════════════════════════════
# Compiler Field Mismatch Regression
# ═══════════════════════════════════════════════════════════════════

class TestCompilerFieldMismatches:
    """Regression tests ensuring compiler reads correct field names from terms.py.

    For each ProofTerm, we construct inputs where sub-proofs Refl will succeed:
    lhs == rhs for the OTerms passed to compile_proof.
    """

    def test_cong_uses_arg_proofs(self):
        """Cong compiler should read 'func' and 'arg_proofs'."""
        from cctt.proof_theory.terms import Cong, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar, OOp

        c = Cong(
            func="add",
            arg_proofs=(Refl(term=OVar("x")), Refl(term=OVar("y"))),
        )
        env = Z3Env()
        lhs = OOp("add", (OVar("x"), OVar("y")))
        rhs = OOp("add", (OVar("x"), OVar("y")))
        result = compile_proof(c, lhs, rhs, env, depth=0)
        assert result.valid
        assert any("Cong" in vc.rule for vc in result.vcs)

    def test_path_compose_uses_left_right(self):
        """PathCompose compiler should read 'left' and 'right'."""
        from cctt.proof_theory.terms import PathCompose, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        # Trivial case: a → a → a (Refl succeeds when lhs==rhs==middle)
        a = OVar("a")
        pc = PathCompose(
            left=Refl(term=a),
            right=Refl(term=a),
            middle=a,
        )
        env = Z3Env()
        result = compile_proof(pc, a, a, env, depth=0)
        assert result.valid
        assert any("PathCompose" in vc.rule for vc in result.vcs)

    def test_let_proof_uses_sub_proof(self):
        """LetProof compiler should read 'sub_proof' not 'bound_proof'."""
        from cctt.proof_theory.terms import LetProof, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        a = OVar("a")
        lp = LetProof(
            label="helper",
            sub_lhs=a,
            sub_rhs=a,
            sub_proof=Refl(term=a),
            body=Refl(term=a),
        )
        env = Z3Env()
        result = compile_proof(lp, a, a, env, depth=0)
        assert result.valid

    def test_ext_uses_body_proof(self):
        """Ext compiler should read 'body_proof' not 'proof'."""
        from cctt.proof_theory.terms import Ext, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        e = Ext(
            var="x",
            body_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(e, f, f, env, depth=0)
        assert result.valid
        assert any("FunExt" in vc.rule for vc in result.vcs)

    def test_simulation_uses_init_step_output(self):
        """Simulation compiler should read init/step/output proofs."""
        from cctt.proof_theory.terms import Simulation, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        s = Simulation(
            relation="R",
            init_proof=Refl(term=f),
            step_proof=Refl(term=f),
            output_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(s, f, f, env, depth=0)
        assert result.valid
        assert any("Simulation" in vc.rule for vc in result.vcs)

    def test_abstraction_refinement_uses_f_g(self):
        """AbstractionRefinement should read abstraction_f and abstraction_g."""
        from cctt.proof_theory.terms import AbstractionRefinement, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        ar = AbstractionRefinement(
            spec_name="sort",
            abstraction_f=Refl(term=f),
            abstraction_g=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(ar, f, f, env, depth=0)
        assert result.valid
        assert any("AbstractionRefinement" in vc.rule for vc in result.vcs)

    def test_functor_map_uses_compose_proof(self):
        """FunctorMap should read 'compose_proof' not 'inner_proof'."""
        from cctt.proof_theory.terms import FunctorMap, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        fm = FunctorMap(
            functor="map",
            compose_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(fm, f, f, env, depth=0)
        assert result.valid
        assert any("FunctorMap" in vc.rule for vc in result.vcs)

    def test_loop_invariant_uses_post_proof(self):
        """LoopInvariant should read 'preservation' and 'post_proof'."""
        from cctt.proof_theory.terms import LoopInvariant, Refl
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        f = OVar("f")
        li = LoopInvariant(
            invariant="count >= 0",
            init_proof=Refl(term=f),
            preservation=Refl(term=f),
            termination=Refl(term=f),
            post_proof=Refl(term=f),
        )
        env = Z3Env()
        result = compile_proof(li, f, f, env, depth=0)
        assert result.valid
        assert any("LoopInvariant" in vc.rule for vc in result.vcs)

    def test_library_contract_uses_function_name(self):
        """LibraryContract should read 'function_name' not 'function'."""
        from cctt.proof_theory.library_axioms import LibraryContract
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar

        lc = LibraryContract(
            library="numpy",
            function_name="linalg.solve",
            postcondition="A @ result == b",
        )
        env = Z3Env()
        result = compile_proof(lc, OVar("f"), OVar("g"), env, depth=0)
        assert result.valid


# ═══════════════════════════════════════════════════════════════════
# Expanded C4 Grammar
# ═══════════════════════════════════════════════════════════════════

class TestExpandedGrammar:
    """Test that the expanded C4 grammar accepts new constructs."""

    def test_none_comparison(self):
        """result != None should be valid C4."""
        ok, err = validate_c4_clause("result != None", {"result"})
        assert ok, f"result != None should be valid, got: {err}"

    def test_quantified_predicates(self):
        """all_of, is_sorted should be valid C4."""
        ok1, _ = validate_c4_clause("all_of(result, 0)", {"result"})
        assert ok1
        ok2, _ = validate_c4_clause("is_sorted(result)", {"result"})
        assert ok2

    def test_contains_predicate(self):
        """contains(result, x) should be valid C4."""
        ok, _ = validate_c4_clause("contains(result, x)", {"result", "x"})
        assert ok

    def test_isinstance_type_names(self):
        """isinstance(result, Expr) should be valid C4."""
        ok, err = validate_c4_clause("isinstance(result, Expr)", {"result"})
        assert ok, f"isinstance(result, Expr) should be valid, got: {err}"

    def test_c4_strategy_enum_expanded(self):
        """New strategies should exist in C4Strategy."""
        assert C4Strategy.WEAKEST_PRECONDITION.value == "WeakestPrecondition"
        assert C4Strategy.EFFECT_FRAME.value == "EffectFrame"
        assert C4Strategy.EXCEPTION_CASE.value == "ExceptionCase"
        assert C4Strategy.DEPENDENT_MATCH.value == "DependentMatch"
        assert C4Strategy.NORMALIZE.value == "Normalize"
        assert C4Strategy.UNFOLD.value == "Unfold"
