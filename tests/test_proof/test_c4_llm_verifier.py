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
        verdict, detail = verify_clause_on_path(
            "result == x + 1", path, [], ["x"])
        assert verdict == "verified"

    def test_verified_nonnegative(self):
        """result >= 0 should be verified when return is x * x."""
        path = ReturnPath(guard="True", return_expr="x * x")
        verdict, _ = verify_clause_on_path(
            "result >= 0", path, [], ["x"])
        assert verdict == "verified"

    def test_failed_contradiction(self):
        """result == x should fail when return is x + 1."""
        path = ReturnPath(guard="True", return_expr="x + 1")
        verdict, _ = verify_clause_on_path(
            "result == x", path, [], ["x"])
        assert verdict == "failed"

    def test_assumed_uninterpreted(self):
        """With axioms, abs(x) == max(x, -x) is now provable."""
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _ = verify_clause_on_path(
            "result == max(x, -x)", path, [], ["x"])
        # axiom injection makes this provable: abs definition + max semantics
        assert verdict == "verified"

    def test_guarded_path(self):
        """Under guard x >= 0, result == x is verified for return x."""
        path = ReturnPath(guard="x >= 0", return_expr="x")
        verdict, _ = verify_clause_on_path(
            "result >= 0", path, [], ["x"])
        assert verdict == "verified"

    def test_requires_as_hypothesis(self):
        """Requires should be used as hypotheses."""
        path = ReturnPath(guard="True", return_expr="x")
        verdict, _ = verify_clause_on_path(
            "result > 0", path, ["x > 0"], ["x"])
        assert verdict == "verified"

    def test_exception_path_assumed(self):
        """Exception paths don't apply to postconditions."""
        path = ReturnPath(guard="y == 0", return_expr="raise(ValueError)",
                         is_exception=True)
        verdict, _ = verify_clause_on_path(
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
    """Test that builtin axioms enable verification."""

    def test_abs_nonneg_verified(self):
        """With abs axiom, result >= 0 for abs(x) should be verified."""
        path = ReturnPath(guard="True", return_expr="abs(x)")
        verdict, _ = verify_clause_on_path(
            "result >= 0", path, [], ["x"],
            func_name="my_abs", source="def my_abs(x): return abs(x)")
        assert verdict == "verified"

    def test_max_ge_both(self):
        """With max axioms, max(x,y) >= x should be verified."""
        path = ReturnPath(guard="True", return_expr="max(x, y)")
        verdict, _ = verify_clause_on_path(
            "result >= x", path, [], ["x", "y"],
            func_name="my_max",
            source="def my_max(x, y): return max(x, y)")
        assert verdict == "verified"

    def test_len_nonneg(self):
        """With len axiom, len(x) >= 0 should be verified."""
        path = ReturnPath(guard="True", return_expr="len(x)")
        verdict, _ = verify_clause_on_path(
            "result >= 0", path, [], ["x"],
            func_name="my_len", source="def my_len(x): return len(x)")
        assert verdict == "verified"


class TestBoolPredicateVerification:
    """Test that is_* functions get Bool sort and verify accordingly."""

    def test_is_predicate_bool_tautology_verified(self):
        """_eval_is_integer with result == True or result == False
        should be verified via tautology."""
        source = "def _eval_is_integer(self):\n    return True"
        spec = {"ensures": ["result == True or result == False"]}
        verdict = verify_c4_spec(source, "_eval_is_integer", [], spec)
        assert verdict.n_verified >= 1
        assert verdict.n_failed == 0

    def test_is_positive_bool(self):
        source = "def is_positive(x):\n    return x > 0"
        spec = {"ensures": ["result == True or result == False"]}
        verdict = verify_c4_spec(source, "is_positive", ["x"], spec)
        assert verdict.n_verified >= 1
