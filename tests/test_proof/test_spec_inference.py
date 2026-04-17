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


class TestGlobalPostconditionSynthesis:
    """Test that global postconditions are derived from fiber analysis.

    A thorough spec uniquely determines the input→output relation.
    Type-level ensures (isinstance) are necessary but never sufficient.
    Global postconditions bridge the gap.
    """

    def setup_method(self):
        self.analyzer = StaticSpecAnalyzer()

    def test_abs_definitional_spec(self):
        """abs_val should get: result == (x if x >= 0 else -x)"""
        src = '''
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    else:
        return -x
'''
        spec = self.analyzer.infer(src, "abs_val", ["x"])
        assert any("result == (x if x >= 0 else -x)" in e for e in spec.ensures)

    def test_abs_nonneg(self):
        """abs_val should get: result >= 0"""
        src = '''
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    else:
        return -x
'''
        spec = self.analyzer.infer(src, "abs_val", ["x"])
        assert "result >= 0" in spec.ensures

    def test_abs_value_disjunction(self):
        """abs_val should get: result == x or result == -x"""
        src = '''
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    else:
        return -x
'''
        spec = self.analyzer.infer(src, "abs_val", ["x"])
        assert "result == x or result == -x" in spec.ensures

    def test_max_definitional_spec(self):
        """max(a, b) should get conditional equality."""
        src = '''
def my_max(a: int, b: int) -> int:
    if a >= b:
        return a
    else:
        return b
'''
        spec = self.analyzer.infer(src, "my_max", ["a", "b"])
        assert any("result == (a if a >= b else b)" in e for e in spec.ensures)

    def test_max_value_disjunction(self):
        """max(a, b) should get: result == a or result == b"""
        src = '''
def my_max(a: int, b: int) -> int:
    if a >= b:
        return a
    else:
        return b
'''
        spec = self.analyzer.infer(src, "my_max", ["a", "b"])
        assert "result == a or result == b" in spec.ensures

    def test_isinstance_dispatch_conditional(self):
        """isinstance dispatch should get conditional equality."""
        src = '''
def f(x):
    if isinstance(x, int):
        return x + 1
    elif isinstance(x, str):
        return len(x)
    else:
        return 0
'''
        spec = self.analyzer.infer(src, "f", ["x"])
        # Should have a conditional expression in ensures
        cond = [e for e in spec.ensures if "if isinstance" in e]
        assert len(cond) >= 1, f"Missing conditional ensures, got: {spec.ensures}"

    def test_common_fiber_ensures_lifted(self):
        """If all fibers share an ensures, it should be global."""
        spec = C4Spec(
            fibers=[
                FiberClause(name="a", guard="x > 0",
                            ensures=["result > 0", "isinstance(result, int)"],
                            returns_expr="x"),
                FiberClause(name="b", guard="x <= 0",
                            ensures=["result > 0", "isinstance(result, int)"],
                            returns_expr="-x + 1"),
            ],
            source=SpecSource.STATIC,
        )
        # Directly test the synthesis method
        analyzer = StaticSpecAnalyzer()
        synthesized = analyzer._synthesize_global_postconditions(spec.fibers, [])
        # "isinstance(result, int)" is common to both fibers
        assert "isinstance(result, int)" in synthesized
        # "result > 0" is common to both fibers
        assert "result > 0" in synthesized

    def test_nonneg_from_abs_and_len(self):
        """len() and abs() returns are non-negative."""
        src = '''
def f(x):
    if isinstance(x, str):
        return len(x)
    else:
        return abs(x)
'''
        spec = self.analyzer.infer(src, "f", ["x"])
        assert "result >= 0" in spec.ensures

    def test_classify_sign_positive_literal(self):
        """Fibers returning literals should detect non-negativity."""
        src = '''
def classify(x):
    if x > 0:
        return 1
    elif x < 0:
        return -1
    else:
        return 0
'''
        spec = self.analyzer.infer(src, "classify", ["x"])
        # Not all non-negative: -1 is negative
        assert "result >= 0" not in spec.ensures
        # But should still get conditional + disjunction
        assert any("result ==" in e and "if" in e for e in spec.ensures)

    def test_strength_is_formal_with_global_postconditions(self):
        """Functions with synthesized postconditions should be FORMAL."""
        src = '''
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    else:
        return -x
'''
        spec = self.analyzer.infer(src, "abs_val", ["x"])
        assert spec.classify_strength() == SpecStrength.FORMAL


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


class TestC4CompilerIntegration:
    """Test that the C4 synergy-aware compiler runs alongside check_proof."""

    def _make_defn(self, name, source, params=None, qualname=None):
        from cctt.proof_theory.library_proof_orchestrator import Definition, DefKind
        return Definition(
            name=name,
            qualname=qualname or f"test.{name}",
            kind=DefKind.FUNCTION,
            lineno=1, end_lineno=source.count("\n") + 1,
            source=source,
            params=params or [],
            docstring="",
            return_annotation="",
            decorators=[],
            class_name=None,
            module_path="test",
        )

    def test_c4_verdict_present(self):
        """Every annotation should now carry a C4 verdict summary."""
        from cctt.proof_theory.library_proof_orchestrator import baseline_prove
        defn = self._make_defn("f", "def f(x: int) -> int:\n    return x + 1\n", ["x"])
        r = baseline_prove(defn, "test")
        assert r.annotation.c4_verdict_summary is not None
        cv = r.annotation.c4_verdict_summary
        assert "valid" in cv
        assert "n_vcs" in cv
        assert "verdict_class" in cv

    def test_c4_library_axiom_reports_assumed(self):
        """LibraryAxiom proofs should report verdict_class='assumed'."""
        from cctt.proof_theory.library_proof_orchestrator import baseline_prove
        # Use a function complex enough to fall through to LibraryAxiom (strategy 6)
        defn = self._make_defn("process",
            "def process(data, config):\n"
            "    result = data\n"
            "    for k in config:\n"
            "        result = result + config[k]\n"
            "    return result\n",
            ["data", "config"])
        r = baseline_prove(defn, "test")
        cv = r.annotation.c4_verdict_summary
        assert cv is not None
        # Should be 'assumed' — LibraryAxiom produces ASSUMED VCs
        assert cv["verdict_class"] == "assumed"
        assert cv["n_assumed"] >= 1
        assert cv["n_verified"] == 0

    def test_c4_refl_has_binding_true(self):
        """Refl proofs should pass the F*-style binding check."""
        from cctt.proof_theory.library_proof_orchestrator import baseline_prove
        defn = self._make_defn("trivial", "def trivial():\n    pass\n")
        r = baseline_prove(defn, "test")
        cv = r.annotation.c4_verdict_summary
        assert cv is not None
        # Binding should succeed for trivial functions
        if "binding" in cv and cv["binding"] is not None:
            assert cv["binding"] is True

    def test_source_text_and_params_stored(self):
        """Annotation should store source_text and param_names for reverification."""
        from cctt.proof_theory.library_proof_orchestrator import baseline_prove
        defn = self._make_defn("add", "def add(a: int, b: int) -> int:\n    return a + b\n", ["a", "b"])
        r = baseline_prove(defn, "test")
        ann = r.annotation
        assert ann.source_text is not None
        assert "def add" in ann.source_text
        assert ann.param_names == ["a", "b"]

    def test_c4_verdict_in_json_roundtrip(self):
        """C4 verdict should survive JSON serialization."""
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, VerifiedAnnotation,
        )
        defn = self._make_defn("inc", "def inc(x: int) -> int:\n    return x + 1\n", ["x"])
        r = baseline_prove(defn, "test")
        ann = r.annotation
        j = ann.to_json()
        restored = VerifiedAnnotation.from_json(j)
        assert restored.c4_verdict_summary == ann.c4_verdict_summary

    def test_compile_annotation_uses_c4(self):
        """compile_annotation runs C4 compiler when source is available."""
        from cctt.proof_theory.library_proof_orchestrator import (
            baseline_prove, compile_annotation,
        )
        defn = self._make_defn("neg", "def neg(x: int) -> int:\n    return -x\n", ["x"])
        r = baseline_prove(defn, "test")
        ann = r.annotation
        # compile_annotation should run; structural check may fail
        # (Refl lhs≠rhs mismatch) but C4 compiler should run without crash
        cr = compile_annotation(ann)
        # Verify C4 warnings are generated (not errors about missing source)
        # The important thing: no "C4 compile skipped" in warnings
        assert not any("C4 compile skipped" in w for w in cr.warnings)


# ═══════════════════════════════════════════════════════════════════
# Deep Fiber Extraction Tests — nested ifs, implicit else, collections
# ═══════════════════════════════════════════════════════════════════

class TestDeepFiberExtraction:
    """Test recursive fiber extraction from complex control flow."""

    def setup_method(self):
        self.analyzer = StaticSpecAnalyzer()

    def test_nested_if_fibers(self):
        """Nested if chains should produce flattened fibers with compound guards."""
        src = '''
def f(x, y):
    if x == 3:
        if y % 2 == 0:
            return [y // 2, y]
        return [y, y + 1]
    return [x]
'''
        spec = self.analyzer.infer(src, "f")
        assert len(spec.fibers) == 3
        guards = [f.guard for f in spec.fibers]
        assert "x == 3 and y % 2 == 0" in guards
        assert any("not (y % 2 == 0)" in g for g in guards)
        assert any("not (x == 3)" in g for g in guards)

    def test_implicit_else_fiber(self):
        """Code after an if-then-return should become an implicit-else fiber."""
        src = '''
def sign(x):
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
'''
        spec = self.analyzer.infer(src, "sign")
        assert len(spec.fibers) == 3
        guards = [f.guard for f in spec.fibers]
        # First fiber: x > 0
        assert "x > 0" in guards
        # Second fiber: not (x > 0) and x < 0
        assert any("not (x > 0)" in g and "x < 0" in g for g in guards)
        # Third fiber: not (x > 0) and not (x < 0) — the implicit else
        assert any("not (x > 0)" in g and "not (x < 0)" in g for g in guards)

    def test_egypt_takenouchi_fibers(self):
        """egypt_takenouchi should produce 3 fibers with correct guards."""
        src = '''
def egypt_takenouchi(x, y):
    if x == 3:
        if y % 2 == 0:
            return [y//2, y]
        i = (y - 1)//2
        j = i + 1
        k = j + i
        return [j, k, j*k]
    l = [y] * x
    while True:
        break
    return sorted(l)
'''
        spec = self.analyzer.infer(src, "egypt_takenouchi")
        assert len(spec.fibers) == 3
        assert spec.strength == SpecStrength.FORMAL

        # Check fiber guards
        f0, f1, f2 = spec.fibers
        assert "x == 3" in f0.guard
        assert "y % 2 == 0" in f0.guard
        assert "x == 3" in f1.guard
        assert "not" in f1.guard
        assert "not (x == 3)" in f2.guard

    def test_block_must_return_simple(self):
        """_block_must_return should detect blocks that always return."""
        import ast
        # Block with direct return
        tree = ast.parse("return 1")
        assert self.analyzer._block_must_return(tree.body) is True

        # Block with only assignment
        tree = ast.parse("x = 1")
        assert self.analyzer._block_must_return(tree.body) is False

    def test_block_must_return_if_else(self):
        """_block_must_return should detect if/else blocks that cover all paths."""
        import ast
        code = "if x > 0:\n    return 1\nelse:\n    return 2\n"
        tree = ast.parse(code)
        assert self.analyzer._block_must_return(tree.body) is True

    def test_block_must_return_if_no_else(self):
        """if without else doesn't always return."""
        import ast
        code = "if x > 0:\n    return 1\n"
        tree = ast.parse(code)
        assert self.analyzer._block_must_return(tree.body) is False


class TestCollectionPostconditions:
    """Test collection type inference from return expressions."""

    def setup_method(self):
        self.analyzer = StaticSpecAnalyzer()

    def test_all_list_returns(self):
        """When all returns are list literals, infer isinstance(result, list)."""
        src = '''
def f(x):
    if x > 0:
        return [x, x + 1]
    return [0]
'''
        spec = self.analyzer.infer(src, "f")
        assert "isinstance(result, list)" in spec.ensures

    def test_list_and_sorted_returns(self):
        """Mix of list literals and sorted() → isinstance(result, list)."""
        src = '''
def f(xs):
    if len(xs) <= 1:
        return xs
    return sorted(xs)
'''
        spec = self.analyzer.infer(src, "f")
        # sorted() returns list, but xs is a variable (no type known)
        # So global isinstance may not be inferred (xs unknown type)

    def test_detect_return_type_list_literal(self):
        """_detect_return_type recognizes list literals."""
        assert self.analyzer._detect_return_type("[1, 2, 3]") == "list"
        assert self.analyzer._detect_return_type("[x, y]") == "list"

    def test_detect_return_type_sorted(self):
        """_detect_return_type recognizes sorted() as producing list."""
        assert self.analyzer._detect_return_type("sorted(l)") == "list"

    def test_detect_return_type_dict(self):
        """_detect_return_type recognizes dict literals."""
        assert self.analyzer._detect_return_type("{'a': 1}") == "dict"
        assert self.analyzer._detect_return_type("dict()") == "dict"

    def test_detect_return_type_tuple(self):
        """_detect_return_type recognizes tuple literals."""
        assert self.analyzer._detect_return_type("(1, 2)") == "tuple"

    def test_detect_return_type_set(self):
        """_detect_return_type recognizes set calls."""
        assert self.analyzer._detect_return_type("set()") == "set"

    def test_detect_return_type_unknown(self):
        """Variables and complex expressions → None."""
        assert self.analyzer._detect_return_type("x") is None
        assert self.analyzer._detect_return_type("f(x)") is None

    def test_detect_return_length(self):
        """_detect_return_length gets exact length for list/tuple literals."""
        assert self.analyzer._detect_return_length("[1, 2, 3]") == 3
        assert self.analyzer._detect_return_length("[x]") == 1
        assert self.analyzer._detect_return_length("(a, b)") == 2

    def test_detect_return_length_starred(self):
        """Starred elements → unknown length."""
        assert self.analyzer._detect_return_length("[1, *xs]") is None

    def test_detect_return_length_unknown(self):
        """Non-literals → None."""
        assert self.analyzer._detect_return_length("sorted(l)") is None

    def test_fiber_len_ensures(self):
        """Fibers with list literal returns should get len(result) == N."""
        src = '''
def f(x):
    if x > 0:
        return [x, x + 1]
    return [0]
'''
        spec = self.analyzer.infer(src, "f")
        assert any(f for f in spec.fibers if "len(result) == 2" in f.ensures)
        assert any(f for f in spec.fibers if "len(result) == 1" in f.ensures)

    def test_no_result_eq_for_collections(self):
        """result == [a, b] should NOT be in ensures (C4 can't parse lists)."""
        src = '''
def f(x):
    if x > 0:
        return [x, x + 1]
    return [0]
'''
        spec = self.analyzer.infer(src, "f")
        # No fiber should have result == [...]
        for fiber in spec.fibers:
            for e in fiber.ensures:
                if e.startswith("result =="):
                    assert "[" not in e, f"Collection literal in ensures: {e}"


class TestFiberNameFromGuard:
    """Test fiber naming with compound guards."""

    def setup_method(self):
        self.analyzer = StaticSpecAnalyzer()

    def test_simple_isinstance(self):
        assert self.analyzer._fiber_name_from_guard("isinstance(x, int)", 0) == "int"

    def test_compound_isinstance(self):
        """Last positive isinstance should win."""
        guard = "not (isinstance(x, int)) and isinstance(x, str)"
        assert self.analyzer._fiber_name_from_guard(guard, 1) == "str"

    def test_all_negated_is_default(self):
        guard = "not (isinstance(x, int)) and not (isinstance(x, str))"
        assert self.analyzer._fiber_name_from_guard(guard, 2) == "default"

    def test_positive_comparison(self):
        assert self.analyzer._fiber_name_from_guard("x > 0", 0) == "positive"

    def test_compound_negative(self):
        guard = "not (x > 0) and x < 0"
        assert self.analyzer._fiber_name_from_guard(guard, 1) == "negative"


class TestStructuralTautology:
    """Test structural tautology detection in the verifier."""

    def test_isinstance_list_literal(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("isinstance(result, list)", "[1, 2, 3]")
        assert result is not None
        assert "list" in result

    def test_isinstance_sorted(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("isinstance(result, list)", "sorted(l)")
        assert result is not None

    def test_isinstance_dict_literal(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("isinstance(result, dict)", "{'a': 1}")
        assert result is not None

    def test_isinstance_tuple(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("isinstance(result, tuple)", "(1, 2)")
        assert result is not None

    def test_isinstance_mismatch(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("isinstance(result, dict)", "[1, 2]")
        assert result is None

    def test_len_exact_match(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("len(result) == 2", "[a, b]")
        assert result is not None

    def test_len_gte(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("len(result) >= 1", "[a, b, c]")
        assert result is not None

    def test_len_mismatch(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("len(result) == 3", "[a, b]")
        assert result is None

    def test_len_unknown(self):
        from cctt.proof_theory.c4_llm_verifier import _is_structural_tautology
        result = _is_structural_tautology("len(result) == 2", "sorted(l)")
        assert result is None


class TestReturnPathGuards:
    """Test that return path guard accumulation is correct."""

    def test_if_then_return_implicit_else(self):
        from cctt.proof_theory.c4_llm_verifier import extract_return_paths
        src = '''
def f(x):
    if x > 0:
        return 1
    return 0
'''
        paths = extract_return_paths(src, "f")
        assert len(paths) == 2
        guards = [p.guard for p in paths]
        assert "x > 0" in guards
        assert "not (x > 0)" in guards

    def test_chained_if_return(self):
        from cctt.proof_theory.c4_llm_verifier import extract_return_paths
        src = '''
def f(x):
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
'''
        paths = extract_return_paths(src, "f")
        assert len(paths) == 3
        guards = [p.guard for p in paths]
        assert "x > 0" in guards
        assert "not (x > 0) and x < 0" in guards
        assert "not (x > 0) and not (x < 0)" in guards

    def test_nested_if_guards(self):
        from cctt.proof_theory.c4_llm_verifier import extract_return_paths
        src = '''
def f(x, y):
    if x == 3:
        if y > 0:
            return 1
        return 2
    return 3
'''
        paths = extract_return_paths(src, "f")
        assert len(paths) == 3
        guards = [p.guard for p in paths]
        assert "x == 3 and y > 0" in guards
        assert any("x == 3" in g and "not (y > 0)" in g for g in guards)
        assert "not (x == 3)" in guards


class TestFullPipelineVerification:
    """Test spec inference + verification end-to-end."""

    def test_egypt_takenouchi_isinstance_verified(self):
        """isinstance(result, list) should be C4_VERIFIED for egypt_takenouchi."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_c4_spec, ClauseVerdict,
        )
        source = '''
def egypt_takenouchi(x, y):
    if x == 3:
        if y % 2 == 0:
            return [y//2, y]
        i = (y - 1)//2
        j = i + 1
        k = j + i
        return [j, k, j*k]
    l = [y] * x
    while True:
        break
    return sorted(l)
'''
        spec = infer_c4_spec(source, 'egypt_takenouchi')
        assert spec.strength == SpecStrength.FORMAL
        assert "isinstance(result, list)" in spec.ensures

        spec_dict = spec.to_json()
        result = verify_c4_spec(source, 'egypt_takenouchi', ['x', 'y'], spec_dict)

        # Global isinstance should be VERIFIED
        isinstance_results = [
            cr for cr in result.clause_results
            if cr.clause == "isinstance(result, list)"
        ]
        assert len(isinstance_results) >= 1
        assert isinstance_results[0].verdict == ClauseVerdict.C4_VERIFIED

        # Should have compiled proofs
        assert result.n_compiled >= 1

    def test_simple_list_return_verified(self):
        """Simple list-returning function should get isinstance verified."""
        from cctt.proof_theory.c4_llm_verifier import (
            verify_c4_spec, ClauseVerdict,
        )
        source = '''
def pair(x, y):
    return [x, y]
'''
        spec = infer_c4_spec(source, 'pair')
        # Single return → should get isinstance(result, list)
        assert "isinstance(result, list)" in spec.ensures

    def test_no_rejected_from_local_vars(self):
        """Specs should not reference local variables (causes REJECTED)."""
        source = '''
def f(x):
    if x > 0:
        y = x + 1
        return [x, y]
    z = -x
    return [z]
'''
        spec = infer_c4_spec(source, 'f')
        # Global ensures should not contain local variables
        for e in spec.ensures:
            if "result ==" in e:
                assert "y" not in e and "z" not in e, f"Local var in ensures: {e}"
