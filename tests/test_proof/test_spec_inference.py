"""Tests for spec_inference.py — formal C4 spec generation.

Verifies that the static analyzer extracts REAL Python-expression specs
from source code (not English), and that spec quality is honestly classified.
"""
from __future__ import annotations

import json
import pytest
from cctt.proof_theory.spec_inference import (
    C4Spec, FiberClause, SpecSource, SpecStrength,
    StaticSpecAnalyzer, infer_c4_spec, parse_llm_spec_response,
    build_llm_spec_prompt,
)


class TestStaticSpecAnalyzer:
    """Test that static analysis extracts formal specs from Python AST."""

    def setup_method(self):
        self.analyzer = StaticSpecAnalyzer()

    # ── Return type annotations → ensures ─────────────────────

    def test_bool_return_type(self):
        src = '''
def is_positive(x: int) -> bool:
    return x > 0
'''
        spec = self.analyzer.infer(src, "is_positive")
        assert "isinstance(result, bool)" in spec.ensures
        assert spec.classify_strength() != SpecStrength.TRIVIAL

    def test_list_return_type(self):
        src = '''
def get_items(data) -> list[int]:
    return [x for x in data if x > 0]
'''
        spec = self.analyzer.infer(src, "get_items")
        assert any("isinstance(result, list)" in e for e in spec.ensures)

    def test_tuple_return_type(self):
        src = '''
def split(s: str) -> tuple[str, str]:
    i = s.index(',')
    return s[:i], s[i+1:]
'''
        spec = self.analyzer.infer(src, "split")
        assert "isinstance(result, tuple)" in spec.ensures
        assert "len(result) == 2" in spec.ensures

    # ── Parameter annotations → requires ─────────────────────

    def test_param_types(self):
        src = '''
def add(x: int, y: int) -> int:
    return x + y
'''
        spec = self.analyzer.infer(src, "add")
        assert "isinstance(x, int)" in spec.requires
        assert "isinstance(y, int)" in spec.requires

    # ── Assert → requires ────────────────────────────────────

    def test_assert_precondition(self):
        src = '''
def sqrt(x: float) -> float:
    assert x >= 0
    return x ** 0.5
'''
        spec = self.analyzer.infer(src, "sqrt")
        assert "x >= 0" in spec.requires

    # ── Fiber decomposition from if/elif ─────────────────────

    def test_isinstance_fibers(self):
        src = '''
def process(x):
    if isinstance(x, int):
        return x * 2
    elif isinstance(x, str):
        return x.upper()
    else:
        return str(x)
'''
        spec = self.analyzer.infer(src, "process")
        assert len(spec.fibers) >= 2
        names = [f.name for f in spec.fibers]
        assert "int" in names
        assert "str" in names
        # Check that fibers have per-case return expressions
        int_fiber = next(f for f in spec.fibers if f.name == "int")
        assert int_fiber.returns_expr == "x * 2"
        assert "isinstance(x, int)" in int_fiber.guard

    def test_value_dispatch_fibers(self):
        src = '''
def sign(x):
    if x > 0:
        return 1
    elif x < 0:
        return -1
    else:
        return 0
'''
        spec = self.analyzer.infer(src, "sign")
        assert len(spec.fibers) == 3
        pos = next(f for f in spec.fibers if f.name == "positive")
        assert pos.returns_expr == "1"
        neg = next(f for f in spec.fibers if f.name == "negative")
        assert neg.returns_expr == "-1"

    # ── Single return → returns_expr ─────────────────────────

    def test_single_return_expr(self):
        src = '''
def double(x: int) -> int:
    return x * 2
'''
        spec = self.analyzer.infer(src, "double")
        assert spec.returns_expr == "x * 2"
        assert spec.classify_strength() == SpecStrength.FORMAL

    def test_complex_return_not_extracted(self):
        """A single variable return is too opaque to be a useful spec."""
        src = '''
def compute(data):
    result = complex_operation(data)
    return result
'''
        spec = self.analyzer.infer(src, "compute")
        # Single variable return → not a useful spec
        assert spec.returns_expr is None

    # ── Raise → requires ─────────────────────────────────────

    def test_raise_precondition(self):
        src = '''
def divide(x, y):
    if y == 0:
        raise ValueError("division by zero")
    return x / y
'''
        spec = self.analyzer.infer(src, "divide")
        assert any("y == 0" in r or "not (y == 0)" in r for r in spec.requires)

    def test_raise_not_guard(self):
        src = '''
def safe(x):
    if not isinstance(x, int):
        raise TypeError("need int")
    return x + 1
'''
        spec = self.analyzer.infer(src, "safe")
        assert "isinstance(x, int)" in spec.requires

    # ── Class invariants ─────────────────────────────────────

    def test_class_invariants(self):
        src = '''
class Stack:
    def __init__(self):
        self._items = []
        self._size = 0
'''
        spec = self.analyzer.infer(src, "Stack")
        assert "hasattr(self, '_items')" in spec.invariants
        assert "hasattr(self, '_size')" in spec.invariants

    # ── Attribute access → requires ──────────────────────────

    def test_attr_requires(self):
        src = '''
def get_length(obj):
    return len(obj.items)
'''
        spec = self.analyzer.infer(src, "get_length")
        assert "hasattr(obj, 'items')" in spec.requires

    # ── Purity detection ─────────────────────────────────────

    def test_pure_function(self):
        src = '''
def add(x, y):
    return x + y
'''
        spec = self.analyzer.infer(src, "add")
        assert spec.purity is True

    def test_impure_global(self):
        src = '''
def increment():
    global counter
    counter += 1
'''
        spec = self.analyzer.infer(src, "increment")
        assert spec.purity is False


class TestC4SpecClassification:
    """Test that spec strength is classified honestly."""

    def test_trivial_spec(self):
        spec = C4Spec(source=SpecSource.STATIC)
        assert spec.classify_strength() == SpecStrength.TRIVIAL
        assert spec.is_trivial

    def test_partial_spec(self):
        spec = C4Spec(
            ensures=["isinstance(result, int)"],
            source=SpecSource.STATIC,
        )
        assert spec.classify_strength() == SpecStrength.PARTIAL

    def test_formal_spec_from_returns_expr(self):
        spec = C4Spec(
            returns_expr="x * 2",
            source=SpecSource.STATIC,
        )
        assert spec.classify_strength() == SpecStrength.FORMAL
        assert spec.is_formal

    def test_formal_spec_from_nontrivial_ensures(self):
        spec = C4Spec(
            ensures=["len(result) == len(input)", "result[0] <= result[-1]"],
            source=SpecSource.STATIC,
        )
        assert spec.classify_strength() == SpecStrength.FORMAL

    def test_formal_spec_from_fiber_returns(self):
        spec = C4Spec(
            fibers=[FiberClause(name="pos", guard="x > 0",
                                ensures=[], returns_expr="x")],
            source=SpecSource.STATIC,
        )
        assert spec.classify_strength() == SpecStrength.FORMAL


class TestC4SpecSerialization:
    """Test JSON round-trip."""

    def test_round_trip(self):
        spec = C4Spec(
            requires=["isinstance(x, int)", "x >= 0"],
            ensures=["isinstance(result, int)", "result >= x"],
            returns_expr="x * 2",
            fibers=[FiberClause(name="pos", guard="x > 0",
                                ensures=["result > 0"], returns_expr="x")],
            invariants=["hasattr(self, '_data')"],
            purity=True,
            source=SpecSource.STATIC,
        )
        d = spec.to_json()
        spec2 = C4Spec.from_json(d)
        assert spec2.requires == spec.requires
        assert spec2.ensures == spec.ensures
        assert spec2.returns_expr == spec.returns_expr
        assert len(spec2.fibers) == 1
        assert spec2.fibers[0].name == "pos"
        assert spec2.purity is True


class TestLLMSpecParsing:
    """Test parsing of LLM-generated spec responses."""

    def test_parse_clean_json(self):
        response = json.dumps({
            "requires": ["isinstance(x, int)"],
            "ensures": ["result >= 0"],
            "returns_expr": "abs(x)",
            "fibers": [],
            "pure": True,
        })
        spec = parse_llm_spec_response(response)
        assert spec.source == SpecSource.LLM
        assert spec.requires == ["isinstance(x, int)"]
        assert spec.returns_expr == "abs(x)"
        assert spec.classify_strength() == SpecStrength.FORMAL

    def test_parse_with_markdown_fences(self):
        response = '''```json
{"requires": ["x > 0"], "ensures": ["result > 0"]}
```'''
        spec = parse_llm_spec_response(response)
        assert spec.requires == ["x > 0"]

    def test_parse_garbage_returns_trivial(self):
        spec = parse_llm_spec_response("this is not json at all")
        assert spec.is_trivial

    def test_prompt_generation(self):
        system, user = build_llm_spec_prompt(
            source="def add(x, y): return x + y",
            qualname="mylib.add",
            library_name="mylib",
            docstring="Add two numbers.",
        )
        assert "Python boolean expression" in system
        assert "NEVER write English" in system
        assert "def add(x, y)" in user
        assert "mylib.add" in user


class TestPathRHS:
    """Test that C4Spec produces formal (non-English) path RHS."""

    def test_returns_expr_is_rhs(self):
        spec = C4Spec(returns_expr="x * 2")
        assert spec.path_rhs("f", ["x"]) == "x * 2"

    def test_ensures_as_rhs(self):
        spec = C4Spec(ensures=["result >= 0", "isinstance(result, int)"])
        rhs = spec.path_rhs("f", ["x"])
        assert "result >= 0" in rhs
        assert "isinstance(result, int)" in rhs
        assert "English" not in rhs  # no English!

    def test_unspecified_is_honest(self):
        spec = C4Spec()
        rhs = spec.path_rhs("f", ["x"])
        assert "<unspecified:f>" in rhs


class TestTopLevelAPI:
    """Test the infer_c4_spec top-level function."""

    def test_static_inference(self):
        src = '''
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    else:
        return -x
'''
        spec = infer_c4_spec(src, "abs_val", "mylib.abs_val")
        assert spec.source == SpecSource.STATIC
        assert "isinstance(x, int)" in spec.requires
        assert len(spec.fibers) == 2
        # The formal spec should have real Python expressions
        rhs = spec.path_rhs("abs_val", ["x"])
        assert "behaves correctly" not in rhs
        assert "expected output" not in rhs

    def test_llm_override(self):
        src = "def f(x): return x + 1"
        llm_json = json.dumps({
            "requires": ["isinstance(x, int)"],
            "ensures": ["result == x + 1"],
            "returns_expr": "x + 1",
        })
        spec = infer_c4_spec(src, "f", llm_response=llm_json)
        assert spec.source == SpecSource.LLM
        assert spec.returns_expr == "x + 1"

    def test_no_english_in_specs(self):
        """The whole point: specs must be formal, not English."""
        english_phrases = [
            "behaves correctly", "produces the expected output",
            "internal helper", "correctly constructs",
            "returns the .* attribute", "initializes the instance",
        ]
        src = '''
def _helper(data):
    result = []
    for x in data:
        result.append(x * 2)
    return result
'''
        spec = infer_c4_spec(src, "_helper", "mylib._helper")
        rhs = spec.path_rhs("_helper", ["data"])
        for phrase in english_phrases:
            assert phrase not in rhs, f"Found English '{phrase}' in spec RHS: {rhs}"


class TestFiberDecidability:
    """Test that fiber guards are classified for synergy integration."""

    def test_isinstance_is_structural(self):
        src = '''
def process(x):
    if isinstance(x, int):
        return x
    elif isinstance(x, str):
        return len(x)
'''
        spec = infer_c4_spec(src, "process")
        for f in spec.fibers:
            if "isinstance" in f.guard:
                assert f.decidability == "structural"

    def test_comparison_is_z3(self):
        src = '''
def classify(x):
    if x > 0:
        return 1
    elif x < 0:
        return -1
    else:
        return 0
'''
        spec = infer_c4_spec(src, "classify")
        for f in spec.fibers:
            if ">" in f.guard or "<" in f.guard:
                assert f.decidability == "z3"


class TestAnnotationIntegration:
    """Test that the orchestrator uses formal specs in annotations."""

    def test_annotation_carries_formal_spec(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )
        defn = Definition(
            name="double",
            qualname="test.double",
            kind=DefKind.FUNCTION,
            lineno=1, end_lineno=2,
            source="def double(x: int) -> int:\n    return x * 2\n",
            params=["x"],
            docstring="",
            return_annotation="int",
            decorators=[],
            class_name=None,
            module_path="test",
        )
        result = baseline_prove(defn, "test")
        ann = result.annotation
        assert ann is not None
        # The annotation should carry the formal spec
        assert ann.formal_spec is not None
        assert ann.spec_source == "static"
        # The formal spec should have real ensures
        fs = ann.formal_spec
        assert "requires" in fs or "ensures" in fs or "returns_expr" in fs

    def test_annotation_rhs_is_not_english(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )
        defn = Definition(
            name="negate",
            qualname="test.negate",
            kind=DefKind.FUNCTION,
            lineno=1, end_lineno=2,
            source="def negate(x: int) -> int:\n    return -x\n",
            params=["x"],
            docstring="",
            return_annotation="int",
            decorators=[],
            class_name=None,
            module_path="test",
        )
        result = baseline_prove(defn, "test")
        ann = result.annotation
        assert ann is not None
        # The path RHS should be formal
        rhs = ann.spec.rhs
        assert "behaves correctly" not in rhs
        assert "produces the expected output" not in rhs
        assert "-x" in rhs or "isinstance" in rhs  # real Python expression

    def test_trivial_function_gets_honest_label(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, Definition, DefKind,
        )
        defn = Definition(
            name="_private_thing",
            qualname="test._private_thing",
            kind=DefKind.FUNCTION,
            lineno=1, end_lineno=2,
            source="def _private_thing():\n    pass\n",
            params=[],
            docstring="",
            return_annotation="",
            decorators=[],
            class_name=None,
            module_path="test",
        )
        result = baseline_prove(defn, "test")
        ann = result.annotation
        assert ann is not None
        # A trivial function should either have formal_spec with strength=trivial
        # or an unspecified label
        if ann.formal_spec:
            assert ann.formal_spec.get("strength") in ("trivial", "partial")
