"""Tests for the spec oracle — template and mock LLM spec generation."""
from __future__ import annotations

import pytest
from cctt.proof_theory.spec_oracle import (
    TemplateOracle, MockLLMOracle, LLMSpecOracle, upgrade_spec,
)
from cctt.proof_theory.spec_inference import (
    C4Spec, SpecSource, SpecStrength, infer_c4_spec,
)


class TestTemplateOracle:
    """Test pattern-based spec generation."""

    def setup_method(self):
        self.oracle = TemplateOracle()

    def _gen(self, source, name, params=None):
        params = params or []
        static = infer_c4_spec(source, name, params)
        return self.oracle.generate_spec(source, name, params, static)

    def test_identity_pattern(self):
        spec = self._gen("def f(x):\n    return x", "f", ["x"])
        assert spec.returns_expr == "x"
        assert "result == x" in spec.ensures

    def test_none_default_pattern(self):
        spec = self._gen(
            "def f(x, default=0):\n    return x if x is not None else default",
            "f", ["x", "default"],
        )
        # Static analyzer already gets returns_expr -> FORMAL, template skips
        assert spec.returns_expr == "x if x is not None else default"

    def test_container_wrap_list(self):
        spec = self._gen(
            "def to_list(x):\n    return list(x)",
            "to_list", ["x"],
        )
        # Static extracts returns_expr "list(x)" -> FORMAL
        assert spec.returns_expr == "list(x)" or "isinstance(result, list)" in spec.ensures

    def test_container_wrap_dict(self):
        spec = self._gen(
            "def to_dict(pairs):\n    return dict(pairs)",
            "to_dict", ["pairs"],
        )
        assert spec.returns_expr == "dict(pairs)" or "isinstance(result, dict)" in spec.ensures

    def test_boolean_predicate_all(self):
        spec = self._gen(
            "def all_positive(xs):\n    return all(x > 0 for x in xs)",
            "all_positive", ["xs"],
        )
        assert spec.returns_expr is not None or "isinstance(result, bool)" in spec.ensures

    def test_boolean_predicate_comparison(self):
        spec = self._gen(
            "def is_equal(a, b):\n    return a == b",
            "is_equal", ["a", "b"],
        )
        assert spec.returns_expr == "a == b" or "isinstance(result, bool)" in spec.ensures

    def test_length_preserving_listcomp(self):
        spec = self._gen(
            "def double_all(lst):\n    return [x * 2 for x in lst]",
            "double_all", ["lst"],
        )
        assert spec.is_formal

    def test_constructor_init(self):
        spec = self._gen(
            "def __init__(self, x, y):\n    self.x = x\n    self.y = y",
            "__init__", ["self", "x", "y"],
        )
        assert "self.x == x" in spec.ensures
        assert "self.y == y" in spec.ensures

    def test_getter_pattern(self):
        spec = self._gen(
            "def get_name(self):\n    return self.name",
            "get_name", ["self"],
        )
        assert spec.returns_expr == "self.name"

    def test_delegation_pattern(self):
        spec = self._gen(
            "def wrapper(x, y):\n    return compute(x, y)",
            "wrapper", ["x", "y"],
        )
        assert spec.returns_expr == "compute(x, y)"

    def test_no_upgrade_for_formal(self):
        # If static spec is already formal, don't change it
        static = C4Spec(
            ensures=["result >= 0", "result == abs(x)"],
            returns_expr="abs(x)",
            source=SpecSource.STATIC,
        )
        static.strength = static.classify_strength()
        result = self.oracle.generate_spec(
            "def f(x): return abs(x)", "f", ["x"], static,
        )
        assert result is static  # Unchanged

    def test_syntax_error_returns_static(self):
        static = C4Spec()
        result = self.oracle.generate_spec(
            "def bad(:\n    pass", "bad", [], static,
        )
        assert result is static


class TestMockLLMOracle:
    """Test deterministic mock LLM specs."""

    def setup_method(self):
        self.oracle = MockLLMOracle()

    def test_abs_spec(self):
        static = C4Spec()
        spec = self.oracle.generate_spec(
            "def abs(x): ...", "abs", ["x"], static,
        )
        assert "result >= 0" in spec.ensures
        assert "result == x or result == -x" in spec.ensures
        assert spec.source == SpecSource.LLM

    def test_sqrt_spec(self):
        static = C4Spec()
        spec = self.oracle.generate_spec(
            "def sqrt(x): ...", "sqrt", ["x"], static,
        )
        assert "result >= 0" in spec.ensures
        assert "x >= 0" in spec.requires

    def test_sorted_spec(self):
        static = C4Spec()
        spec = self.oracle.generate_spec(
            "def sorted(iterable): ...", "sorted", ["iterable"], static,
        )
        assert "isinstance(result, list)" in spec.ensures

    def test_factorial_spec(self):
        static = C4Spec()
        spec = self.oracle.generate_spec(
            "def factorial(n): ...", "factorial", ["n"], static,
        )
        assert "result >= 1" in spec.ensures
        assert "n >= 0" in spec.requires

    def test_unknown_function_returns_static(self):
        static = C4Spec(ensures=["isinstance(result, int)"])
        spec = self.oracle.generate_spec(
            "def custom_thing(x): ...", "custom_thing", ["x"], static,
        )
        assert spec is static

    def test_qualname_suffix_match(self):
        static = C4Spec()
        spec = self.oracle.generate_spec(
            "def gcd(a, b): ...", "gcd", ["a", "b"], static,
            qualname="math.gcd",
        )
        assert "result >= 0" in spec.ensures


class TestLLMSpecOracle:
    """Test LLM oracle with mock callback."""

    def test_with_callback(self):
        # Simulate LLM returning a spec response
        def fake_llm(prompt):
            return """```json
{
    "requires": ["x >= 0"],
    "ensures": ["result >= 0"],
    "returns_expr": "x ** 0.5",
    "fibers": []
}
```"""
        oracle = LLMSpecOracle(llm_call=fake_llm)
        static = C4Spec()
        spec = oracle.generate_spec(
            "def sqrt(x): return x ** 0.5", "sqrt", ["x"], static,
        )
        assert spec.source == SpecSource.LLM
        assert "result >= 0" in spec.ensures

    def test_without_callback(self):
        oracle = LLMSpecOracle(llm_call=None)
        static = C4Spec(ensures=["isinstance(result, float)"])
        spec = oracle.generate_spec(
            "def sqrt(x): ...", "sqrt", ["x"], static,
        )
        assert spec is static

    def test_callback_error_returns_static(self):
        def bad_llm(prompt):
            raise RuntimeError("API error")
        oracle = LLMSpecOracle(llm_call=bad_llm)
        static = C4Spec()
        spec = oracle.generate_spec(
            "def f(x): ...", "f", ["x"], static,
        )
        assert spec is static


class TestUpgradeSpec:
    """Test the top-level upgrade_spec function."""

    def test_upgrades_trivial(self):
        static = C4Spec()  # trivial
        upgraded = upgrade_spec(
            "def f(x):\n    return x", "f", ["x"], static,
        )
        # TemplateOracle should detect identity pattern
        assert "result == x" in upgraded.ensures

    def test_no_downgrade_formal(self):
        formal = C4Spec(
            ensures=["result == x * 2"],
            returns_expr="x * 2",
        )
        formal.strength = SpecStrength.FORMAL
        result = upgrade_spec(
            "def f(x): return x * 2", "f", ["x"], formal,
        )
        assert result is formal

    def test_uses_mock_oracle(self):
        static = C4Spec()
        upgraded = upgrade_spec(
            "def abs(x): ...", "abs", ["x"], static,
            oracle=MockLLMOracle(),
        )
        assert "result >= 0" in upgraded.ensures


class TestOracleWithOrchestrator:
    """Test that oracle integrates with baseline_prove."""

    def test_baseline_prove_uses_oracle(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )

        defn = Definition(
            name="get_name", qualname="mod.Person.get_name",
            kind=DefKind.METHOD,
            lineno=1, end_lineno=2,
            source="def get_name(self):\n    return self.name",
            docstring="",
            params=["self"],
            return_annotation=None,
            decorators=[],
            class_name="Person",
            module_path="mod",
        )

        result = baseline_prove(defn, "mod")
        assert result.annotation is not None
        # The template oracle should detect getter pattern
        spec = result.annotation.formal_spec
        assert spec is not None
        # Should have result == self.name or returns_expr
        has_getter = (
            spec.get("returns_expr") == "self.name"
            or "result == self.name" in spec.get("ensures", [])
        )
        assert has_getter, f"Expected getter spec, got: {spec}"

    def test_baseline_prove_init_constructor(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )

        defn = Definition(
            name="__init__", qualname="mod.Point.__init__",
            kind=DefKind.METHOD,
            lineno=1, end_lineno=3,
            source="def __init__(self, x, y):\n    self.x = x\n    self.y = y",
            docstring="",
            params=["self", "x", "y"],
            return_annotation=None,
            decorators=[],
            class_name="Point",
            module_path="mod",
        )

        result = baseline_prove(defn, "mod")
        assert result.annotation is not None
        spec = result.annotation.formal_spec
        assert spec is not None
        ensures = spec.get("ensures", [])
        assert "self.x == x" in ensures
        assert "self.y == y" in ensures
