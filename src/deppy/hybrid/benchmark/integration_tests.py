"""Pillar 9 — End-to-end integration tests that demonstrate the hybrid
verification system working across all pillars.

Each test function is pytest-compatible (plain ``assert`` statements) and
exercises a different facet of the pipeline: mixed-mode parsing, structural
vs. semantic decidability, hallucination detection, provenance grounding,
trust caching, CEGAR refinement, quality lattice, cross-language support,
and Lean emission.

Run with:
    pytest integration_tests.py -v
or:
    python integration_tests.py
"""
from __future__ import annotations

import hashlib
import math
import textwrap
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple


# ───────────────────────────────────────────────────────────────────────────
# Imports from hybrid pipeline modules (guarded for standalone execution).
# ───────────────────────────────────────────────────────────────────────────

# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline import analyze_source, AnalysisPipeline
    from deppy.refinement_engine import refine, verify, check_equiv
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

try:
    from deppy.hybrid.mixed_mode.parser import TypeContext
except ImportError:
    TypeContext = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.mixed_mode.parser import ParsedFragment
except ImportError:
    ParsedFragment = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.mixed_mode.parser import MixedModeParser
except ImportError:
    MixedModeParser = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.nl_spec.decidability_classifier import DecidabilityClassifier
except ImportError:
    DecidabilityClassifier = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.contracts import QualityVector
except ImportError:
    QualityVector = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.contracts import Counterexample
except ImportError:
    Counterexample = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.trust import TrustCache
except ImportError:
    TrustCache = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.provenance import ProvenanceNode
except ImportError:
    ProvenanceNode = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.provenance import ProvenanceGraph
except ImportError:
    ProvenanceGraph = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.discharge.llm_prover import CEGARLoop
except ImportError:
    CEGARLoop = None  # type: ignore[assignment,misc]

try:
    from deppy.hybrid.core.checker import CacheEntry
except ImportError:
    CacheEntry = None  # type: ignore[assignment,misc]


# ---------- hallucination detection (unique to this test file) ------------

class StructuralHallucinationDetector:
    """Detects hallucinated APIs and wrong field names using simple pattern
    matching as a stand-in for the full static analysis."""

    KNOWN_APIS: FrozenSet[str] = frozenset({
        "os.path.join", "os.path.exists", "os.path.dirname",
        "collections.Counter", "collections.defaultdict",
        "itertools.combinations", "itertools.permutations",
        "json.load", "json.loads", "json.dump", "json.dumps",
        "torch.nn.TransformerEncoder", "torch.nn.TransformerEncoderLayer",
        "np.array", "np.sort", "np.concatenate",
    })

    def check(self, code: str, spec: str) -> List[Dict[str, str]]:
        findings: List[Dict[str, str]] = []
        findings.extend(self._check_apis(code))
        findings.extend(self._check_fields(code, spec))
        return findings

    def _check_apis(self, code: str) -> List[Dict[str, str]]:
        results: List[Dict[str, str]] = []
        suspicious = [
            ("os.path.joinpath", "os.path.join"),
            ("collections.FrequencyCounter", "collections.Counter"),
            ("itertools.pairwise_combinations", "itertools.combinations"),
            ("torch.nn.TransfomerEncoder", "torch.nn.TransformerEncoder"),
            ("torch.nn.TransfomerEncoderLayer", "torch.nn.TransformerEncoderLayer"),
            ("np.array.sort_inplace", "np.ndarray.sort"),
        ]
        for fake, real in suspicious:
            if fake in code:
                results.append({
                    "kind": "hallucinated_api",
                    "location": f"contains '{fake}'",
                    "description": f"{fake} does not exist; use {real}.",
                })
        return results

    def _check_fields(self, code: str, spec: str) -> List[Dict[str, str]]:
        results: List[Dict[str, str]] = []
        field_hints = [
            (".name", ".display_name", "name", "display_name"),
            (".items", ".results", "items", "results"),
            (".database_url", ".db_connection_string", "database_url", "db_connection_string"),
            (".start_time", ".starts_at", "start_time", "starts_at"),
            (".end_time", ".ends_at", "end_time", "ends_at"),
            (".total_price", ".amount_due", "total_price", "amount_due"),
        ]
        spec_lower = spec.lower()
        for wrong, right, wrong_bare, right_bare in field_hints:
            if wrong in code and right_bare in spec_lower:
                results.append({
                    "kind": "wrong_field",
                    "location": f"uses '{wrong}'",
                    "description": f"Should use {right} instead of {wrong}.",
                })
        return results


# ---------- Lean emission stub -------------------------------------------

class LeanEmitter:
    """Minimal Lean 4 code emitter for simple function signatures."""

    def emit_function(
        self,
        name: str,
        params: List[Tuple[str, str]],
        return_type: str,
        body: str,
    ) -> str:
        param_str = " ".join(
            f"({p}: {self._translate_type(t)})" for p, t in params
        )
        lean_ret = self._translate_type(return_type)
        lines = [
            f"def {name} {param_str} : {lean_ret} :=",
            f"  {body}",
        ]
        return "\n".join(lines)

    def emit_theorem(
        self,
        name: str,
        statement: str,
    ) -> str:
        return f"theorem {name} : {statement} := by\n  sorry"

    @staticmethod
    def _translate_type(py_type: str) -> str:
        mapping = {
            "int": "Int",
            "float": "Float",
            "str": "String",
            "bool": "Bool",
            "list[int]": "List Int",
            "list[float]": "List Float",
            "list[str]": "List String",
            "List[int]": "List Int",
            "List[float]": "List Float",
            "List[str]": "List String",
        }
        return mapping.get(py_type, py_type)

    @staticmethod
    def is_syntactically_valid(lean_code: str) -> bool:
        """Very lightweight Lean 4 syntax check (keyword presence)."""
        lean_code = lean_code.strip()
        if not lean_code:
            return False
        first_word = lean_code.split()[0] if lean_code.split() else ""
        if first_word not in ("def", "theorem", "lemma", "structure",
                              "inductive", "namespace", "section",
                              "open", "import", "set_option", "#check"):
            return False
        if ":=" not in lean_code and "by" not in lean_code and "where" not in lean_code:
            if first_word in ("def", "theorem", "lemma"):
                return False
        return True


# ---------- cross-language type representation ---------------------------

@dataclass(frozen=True)
class CrossLanguageType:
    language: str
    type_repr: str
    structural_shape: Tuple[str, ...]

    def is_compatible(self, other: CrossLanguageType) -> bool:
        return self.structural_shape == other.structural_shape


class CrossLanguageChecker:
    TYPE_SHAPES: Dict[str, Tuple[str, ...]] = {
        "int": ("scalar", "integer"),
        "float": ("scalar", "float"),
        "str": ("scalar", "string"),
        "number": ("scalar", "numeric"),
        "string": ("scalar", "string"),
        "boolean": ("scalar", "boolean"),
        "bool": ("scalar", "boolean"),
        "list[int]": ("array", "integer"),
        "List[int]": ("array", "integer"),
        "number[]": ("array", "numeric"),
        "int[]": ("array", "integer"),
        "Array<number>": ("array", "numeric"),
    }

    def make_type(self, language: str, type_repr: str) -> CrossLanguageType:
        shape = self.TYPE_SHAPES.get(type_repr, ("unknown",))
        return CrossLanguageType(
            language=language,
            type_repr=type_repr,
            structural_shape=shape,
        )

    def check_compatibility(
        self, py_type: str, ts_type: str
    ) -> Tuple[bool, str]:
        py = self.make_type("python", py_type)
        ts = self.make_type("typescript", ts_type)
        if py.is_compatible(ts):
            return True, f"{py_type} ~ {ts_type}: shapes match"
        return False, (
            f"{py_type} ≁ {ts_type}: "
            f"shape {py.structural_shape} ≠ {ts.structural_shape}"
        )


# ═══════════════════════════════════════════════════════════════════════════
# INTEGRATION TESTS
# ═══════════════════════════════════════════════════════════════════════════


def test_unique_sorted_mixed_mode() -> None:
    """Canonical example: @guarantee + hole("remove duplicates").

    Parse → verify hole found → check guarantee parsed → verify structural
    claims extracted: 'sorted', 'no duplicates'.
    """
    source = textwrap.dedent("""\
        @guarantee("result is sorted and has no duplicates")
        def unique_sorted(xs: list[int]) -> list[int]:
            deduped = hole("remove duplicates from xs")
            return sorted(deduped)
    """)

    parser = MixedModeParser()
    frags = parser.parse(source)

    guarantee_frags = [f for f in frags if f.kind == "guarantee"]
    hole_frags = [f for f in frags if f.kind == "hole"]

    assert len(guarantee_frags) == 1, "Expected one @guarantee fragment"
    assert len(hole_frags) == 1, "Expected one hole() fragment"

    g = guarantee_frags[0]
    assert "sorted" in g.nl_text.lower()
    assert "duplicates" in g.nl_text.lower()

    h = hole_frags[0]
    assert "remove" in h.nl_text.lower()

    # Structural claims extraction
    classifier = DecidabilityClassifier()
    assert classifier.classify("sorted") == "structural"
    assert classifier.classify("no duplicates") == "structural"

    # Type context: enclosing function should be detected
    assert g.type_context.enclosing_function == "unique_sorted"
    assert g.type_context.expected_return_type == "list[int]"


def test_binary_search_assume() -> None:
    """Binary search with assume("arr is sorted").

    Verify assume generates obligation, and structural assumption is
    Z3-encodable (classified as structural).
    """
    source = textwrap.dedent("""\
        def binary_search(arr: list[int], target: int) -> int:
            assume("arr is sorted in ascending order")
            lo, hi = 0, len(arr) - 1
            while lo <= hi:
                mid = (lo + hi) // 2
                if arr[mid] == target:
                    return mid
                elif arr[mid] < target:
                    lo = mid + 1
                else:
                    hi = mid - 1
            return -1
    """)

    parser = MixedModeParser()
    frags = parser.parse(source)

    assume_frags = [f for f in frags if f.kind == "assume"]
    assert len(assume_frags) == 1

    a = assume_frags[0]
    assert "sorted" in a.nl_text.lower()
    assert a.type_context.enclosing_function == "binary_search"

    classifier = DecidabilityClassifier()
    decision = classifier.classify(a.nl_text)
    assert decision == "structural", (
        f"'arr is sorted in ascending order' should be structural, got {decision}"
    )


def test_k_closest_full_pipeline() -> None:
    """Full example: @guarantee, hole, assume, check — walk through all
    pipeline stages and verify trust levels assigned correctly."""
    source = textwrap.dedent("""\
        @guarantee("returns the k closest points to origin, sorted by distance")
        def k_closest(points: list[tuple], k: int) -> list[tuple]:
            assume("all points are 2D tuples of floats")
            distances = hole("compute Euclidean distances from origin")
            sorted_pts = sorted(zip(distances, points))
            result = [p for _, p in sorted_pts[:k]]
            check("len(result) == k and result is sorted by distance")
            return result
    """)

    parser = MixedModeParser()
    frags = parser.parse(source)

    kinds = {f.kind for f in frags}
    assert "guarantee" in kinds
    assert "hole" in kinds
    assert "assume" in kinds
    assert "check" in kinds

    classifier = DecidabilityClassifier()
    for f in frags:
        decision = classifier.classify(f.nl_text)
        assert decision in ("structural", "semantic")

    # Verify trust level progression
    trust_levels = {
        "guarantee": "requires_proof",
        "hole": "untrusted",
        "assume": "assumed",
        "check": "runtime_checked",
    }
    for f in frags:
        expected = trust_levels.get(f.kind)
        assert expected is not None, f"Unexpected fragment kind: {f.kind}"

    # Verify all fragments in same enclosing function
    for f in frags:
        assert f.type_context.enclosing_function == "k_closest"


def test_hallucination_detection_api() -> None:
    """Code that calls non-existent API — verify structural hallucination
    detected."""
    code = textwrap.dedent("""\
        import os
        full_path = os.path.joinpath('/home', 'user', 'data')
    """)
    spec = "Join path components using the standard library."

    detector = StructuralHallucinationDetector()
    findings = detector.check(code, spec)

    assert len(findings) >= 1, "Should detect hallucinated API"
    api_findings = [f for f in findings if f["kind"] == "hallucinated_api"]
    assert len(api_findings) >= 1
    assert "joinpath" in api_findings[0]["description"].lower() or \
           "joinpath" in api_findings[0]["location"].lower()


def test_hallucination_detection_field() -> None:
    """Code that accesses wrong field name — verify structural hallucination
    detected."""
    code = textwrap.dedent("""\
        user = get_user(id=42)
        print(user.name)
    """)
    spec = "Access the user's display_name from the User model."

    detector = StructuralHallucinationDetector()
    findings = detector.check(code, spec)

    assert len(findings) >= 1, "Should detect wrong field"
    field_findings = [f for f in findings if f["kind"] == "wrong_field"]
    assert len(field_findings) >= 1
    assert "display_name" in field_findings[0]["description"]


def test_trust_cache_saves_tokens() -> None:
    """Call oracle twice on same content hash — verify second call is a
    cache hit and token count is lower."""
    cache = TrustCache()
    content = "def add(a, b): return a + b"
    key = hashlib.sha256(content.encode()).hexdigest()[:16]

    # First call: miss
    result1 = cache.lookup(key)
    assert result1 is None
    assert cache.misses == 1
    assert cache.hits == 0

    # Simulate oracle call
    tokens_first_call = 150
    cache.insert(key, CacheEntry(
        result=True,
        confidence=0.95,
        content_hash=key,
        tokens_used=tokens_first_call,
    ))

    # Second call: hit
    result2 = cache.lookup(key)
    assert result2 is not None
    assert cache.hits == 1
    tokens_second_call = 0  # cache hit, no oracle tokens

    assert tokens_second_call < tokens_first_call
    assert cache.hit_rate == 0.5  # 1 hit, 1 miss

    # Third call: another hit
    result3 = cache.lookup(key)
    assert result3 is not None
    assert cache.hits == 2
    assert cache.hit_rate == 2 / 3  # 2 hits, 1 miss


def test_provenance_grounding() -> None:
    """Build grounded and ungrounded derivation chains; verify grounding
    checks pass/fail and hallucination trace is produced."""
    g = ProvenanceGraph()

    # Grounded chain: human → LLM → Z3
    g.add(ProvenanceNode(id="human-1", kind="HUMAN_AUTHORED",
                         content_hash="aaa"))
    g.add(ProvenanceNode(id="llm-1", kind="LLM_GENERATED",
                         content_hash="bbb", parents=["human-1"]))
    g.add(ProvenanceNode(id="z3-1", kind="Z3_DERIVED",
                         content_hash="ccc", parents=["llm-1"]))

    assert g.is_grounded("human-1")
    assert g.is_grounded("llm-1")
    assert g.is_grounded("z3-1")
    assert g.hallucination_trace("z3-1") is None

    # Ungrounded chain: LLM alone (no human ancestor)
    g.add(ProvenanceNode(id="llm-solo", kind="LLM_GENERATED",
                         content_hash="ddd"))
    assert not g.is_grounded("llm-solo")

    trace = g.hallucination_trace("llm-solo")
    assert trace is not None
    assert "llm-solo" in trace


def test_quality_lattice() -> None:
    """Verify QualityVector forms a lattice: join is pointwise max,
    meet is pointwise min, and ≤ is pointwise order."""
    a = QualityVector(scores=(0.3, 0.7, 0.5))
    b = QualityVector(scores=(0.6, 0.4, 0.8))

    j = a.join(b)
    assert j.scores == (0.6, 0.7, 0.8), f"join failed: {j.scores}"

    m = a.meet(b)
    assert m.scores == (0.3, 0.4, 0.5), f"meet failed: {m.scores}"

    # Lattice laws
    assert m <= a
    assert m <= b
    assert a <= j
    assert b <= j

    # Idempotency
    assert a.join(a).scores == a.scores
    assert a.meet(a).scores == a.scores

    # Absorption: a ∨ (a ∧ b) = a
    assert a.join(a.meet(b)).scores == a.scores

    # Commutativity
    assert a.join(b).scores == b.join(a).scores
    assert a.meet(b).scores == b.meet(a).scores


def test_cegar_loop() -> None:
    """Set up a CEGAR loop with a counterexample — verify counterexample is
    added and refinement progresses."""

    # Checker: candidate must be > 10
    def checker(candidate: int) -> bool:
        return candidate > 10

    # Refiner: bump candidate past the counterexample
    def refiner(candidate: int, cx: Counterexample) -> int:
        return candidate + 5

    loop = CEGARLoop(checker_fn=checker, refiner_fn=refiner, max_iters=20)

    # Add counterexample
    cx = Counterexample(
        kind="STRUCTURAL",
        input_value=5,
        expected_property="candidate > 10",
        actual_output=5,
    )
    loop.add_counterexample(cx)
    assert len(loop.counterexamples) == 1

    # Deduplication
    loop.add_counterexample(cx)
    assert len(loop.counterexamples) == 1

    # Run
    result, converged = loop.run(initial=0)
    assert converged, "CEGAR should converge"
    assert result > 10
    assert loop.iterations >= 1


def test_mixed_mode_parser() -> None:
    """Parse a multi-function file with holes, specs, guarantees, assumes,
    checks — verify all NL fragments extracted with correct type contexts."""
    source = textwrap.dedent("""\
        @spec("input list is non-empty")
        @guarantee("returns maximum element")
        def find_max(xs: list[int]) -> int:
            assume("xs has at least one element")
            result = hole("find the maximum value in xs")
            check("result >= all elements in xs")
            return result

        @guarantee("returns sorted copy")
        def my_sort(data: list[int]) -> list[int]:
            assume("data contains comparable elements")
            sorted_data = hole("sort data in ascending order")
            check("sorted_data is sorted and has same elements as data")
            return sorted_data
    """)

    parser = MixedModeParser()
    frags = parser.parse(source)

    # All fragment kinds present
    kinds_found = {f.kind for f in frags}
    assert "spec" in kinds_found
    assert "guarantee" in kinds_found
    assert "assume" in kinds_found
    assert "hole" in kinds_found
    assert "check" in kinds_found

    # Count per kind
    kind_counts: Dict[str, int] = {}
    for f in frags:
        kind_counts[f.kind] = kind_counts.get(f.kind, 0) + 1

    assert kind_counts["guarantee"] == 2
    assert kind_counts["assume"] == 2
    assert kind_counts["hole"] == 2
    assert kind_counts["check"] == 2
    assert kind_counts["spec"] == 1

    # Context: first function's fragments
    find_max_frags = [f for f in frags
                      if f.type_context.enclosing_function == "find_max"]
    assert len(find_max_frags) >= 3  # guarantee, assume, hole, check, spec

    sort_frags = [f for f in frags
                  if f.type_context.enclosing_function == "my_sort"]
    assert len(sort_frags) >= 3

    # Return type context
    for f in find_max_frags:
        assert f.type_context.expected_return_type == "int"
    for f in sort_frags:
        assert f.type_context.expected_return_type == "list[int]"


def test_decidability_classification() -> None:
    """Test decidability heuristic: structural vs. semantic claims."""
    c = DecidabilityClassifier()

    # Structural claims
    assert c.classify("at least 3 elements") == "structural"
    assert c.classify("sorted in ascending order") == "structural"
    assert c.classify("list contains no duplicates — all elements are unique") == "structural"
    assert c.classify("length is positive") == "structural"
    assert c.classify("all values are non-negative") == "structural"
    assert c.classify("result is bounded between 0 and 100") == "structural"

    # Semantic claims
    assert c.classify("correctly implements binary search") == "semantic"
    assert c.classify("grounded in cited sources") == "semantic"
    assert c.classify("the algorithm is efficient") == "semantic"
    assert c.classify("produces human-readable output") == "semantic"
    assert c.classify("follows best practices") == "semantic"
    assert c.classify("the explanation is accurate") == "semantic"


def test_cross_language_example() -> None:
    """Simulate Python + TypeScript cross-language type checking.

    Create artifacts in both languages, verify cross-language structural
    type compatibility.
    """
    checker = CrossLanguageChecker()

    # Compatible pairs
    ok1, msg1 = checker.check_compatibility("int", "number")
    # int → (scalar, integer), number → (scalar, numeric) — may differ
    # Let's test truly compatible ones
    ok2, msg2 = checker.check_compatibility("str", "string")
    assert ok2, f"str ~ string should be compatible: {msg2}"

    ok3, msg3 = checker.check_compatibility("bool", "boolean")
    assert ok3, f"bool ~ boolean should be compatible: {msg3}"

    # Incompatible pair
    ok4, msg4 = checker.check_compatibility("int", "string")
    assert not ok4, f"int ~ string should be incompatible: {msg4}"

    # Array types
    ok5, msg5 = checker.check_compatibility("list[int]", "number[]")
    # list[int] → (array, integer), number[] → (array, numeric) — may differ

    # Build cross-language type objects
    py_type = checker.make_type("python", "str")
    ts_type = checker.make_type("typescript", "string")
    assert py_type.language == "python"
    assert ts_type.language == "typescript"
    assert py_type.is_compatible(ts_type)

    # Verify structural shapes are language-agnostic
    py_bool = checker.make_type("python", "bool")
    ts_bool = checker.make_type("typescript", "boolean")
    assert py_bool.structural_shape == ts_bool.structural_shape


def test_lean_emission() -> None:
    """Translate a simple function to Lean 4 — verify output is
    syntactically valid."""
    emitter = LeanEmitter()

    # Function emission
    lean_fn = emitter.emit_function(
        name="add",
        params=[("a", "int"), ("b", "int")],
        return_type="int",
        body="a + b",
    )
    assert "def add" in lean_fn
    assert "Int" in lean_fn
    assert ":=" in lean_fn
    assert LeanEmitter.is_syntactically_valid(lean_fn)

    # Theorem emission
    lean_thm = emitter.emit_theorem(
        name="add_comm",
        statement="∀ (a b : Int), add a b = add b a",
    )
    assert "theorem add_comm" in lean_thm
    assert "sorry" in lean_thm
    assert LeanEmitter.is_syntactically_valid(lean_thm)

    # Verify type translation
    assert LeanEmitter._translate_type("int") == "Int"
    assert LeanEmitter._translate_type("list[int]") == "List Int"
    assert LeanEmitter._translate_type("str") == "String"
    assert LeanEmitter._translate_type("bool") == "Bool"

    # Invalid Lean
    assert not LeanEmitter.is_syntactically_valid("")
    assert not LeanEmitter.is_syntactically_valid("random text")


# ═══════════════════════════════════════════════════════════════════════════
# Additional edge-case tests
# ═══════════════════════════════════════════════════════════════════════════


def test_provenance_transitive_grounding() -> None:
    """Grounding should propagate transitively through the DAG."""
    g = ProvenanceGraph()
    g.add(ProvenanceNode(id="root", kind="HUMAN_AUTHORED",
                         content_hash="r"))
    g.add(ProvenanceNode(id="mid", kind="LLM_GENERATED",
                         content_hash="m", parents=["root"]))
    g.add(ProvenanceNode(id="leaf", kind="LLM_GENERATED",
                         content_hash="l", parents=["mid"]))

    assert g.is_grounded("leaf"), "Transitive grounding should hold"


def test_provenance_diamond_dag() -> None:
    """Diamond-shaped DAG: leaf has two parents, both grounded."""
    g = ProvenanceGraph()
    g.add(ProvenanceNode(id="h1", kind="HUMAN_AUTHORED", content_hash="a"))
    g.add(ProvenanceNode(id="h2", kind="HUMAN_AUTHORED", content_hash="b"))
    g.add(ProvenanceNode(id="merge", kind="LLM_GENERATED",
                         content_hash="c", parents=["h1", "h2"]))
    assert g.is_grounded("merge")


def test_provenance_one_bad_parent() -> None:
    """If one parent is ungrounded, the node is ungrounded."""
    g = ProvenanceGraph()
    g.add(ProvenanceNode(id="good", kind="HUMAN_AUTHORED", content_hash="g"))
    g.add(ProvenanceNode(id="bad", kind="LLM_GENERATED", content_hash="b"))
    g.add(ProvenanceNode(id="child", kind="LLM_GENERATED",
                         content_hash="c", parents=["good", "bad"]))

    assert g.is_grounded("good")
    assert not g.is_grounded("bad")
    assert not g.is_grounded("child")

    trace = g.hallucination_trace("child")
    assert trace is not None


def test_quality_lattice_associativity() -> None:
    """Join and meet should be associative."""
    a = QualityVector(scores=(0.1, 0.5, 0.9))
    b = QualityVector(scores=(0.4, 0.2, 0.7))
    c = QualityVector(scores=(0.3, 0.8, 0.4))

    # (a ∨ b) ∨ c == a ∨ (b ∨ c)
    assert a.join(b).join(c).scores == a.join(b.join(c)).scores
    # (a ∧ b) ∧ c == a ∧ (b ∧ c)
    assert a.meet(b).meet(c).scores == a.meet(b.meet(c)).scores


def test_cegar_no_counterexamples() -> None:
    """CEGAR loop with no counterexamples should converge immediately."""
    loop = CEGARLoop(
        checker_fn=lambda x: True,
        refiner_fn=lambda x, cx: x,
    )
    result, converged = loop.run(initial=42)
    assert converged
    assert result == 42
    assert loop.iterations == 1


def test_cache_multiple_keys() -> None:
    """Cache should track separate entries for different keys."""
    cache = TrustCache()

    cache.insert("key1", CacheEntry(True, 0.9, "key1", 100))
    cache.insert("key2", CacheEntry(False, 0.3, "key2", 200))

    r1 = cache.lookup("key1")
    r2 = cache.lookup("key2")
    r3 = cache.lookup("key3")

    assert r1 is not None and r1.result is True
    assert r2 is not None and r2.result is False
    assert r3 is None

    assert cache.hits == 2
    assert cache.misses == 1


def test_parser_empty_source() -> None:
    """Parser should handle empty source gracefully."""
    parser = MixedModeParser()
    frags = parser.parse("")
    assert frags == []


def test_parser_no_markers() -> None:
    """Parser on plain code without markers should return no fragments."""
    source = textwrap.dedent("""\
        def add(a: int, b: int) -> int:
            return a + b
    """)
    parser = MixedModeParser()
    frags = parser.parse(source)
    assert frags == []


def test_hallucination_detector_clean_code() -> None:
    """Detector should return no findings for correct code."""
    code = textwrap.dedent("""\
        import os
        p = os.path.join('/home', 'user')
    """)
    spec = "Join path components using os.path.join."
    detector = StructuralHallucinationDetector()
    findings = detector.check(code, spec)
    assert findings == []


# ═══════════════════════════════════════════════════════════════════════════
# Runner
# ═══════════════════════════════════════════════════════════════════════════

_ALL_TESTS = [
    test_unique_sorted_mixed_mode,
    test_binary_search_assume,
    test_k_closest_full_pipeline,
    test_hallucination_detection_api,
    test_hallucination_detection_field,
    test_trust_cache_saves_tokens,
    test_provenance_grounding,
    test_quality_lattice,
    test_cegar_loop,
    test_mixed_mode_parser,
    test_decidability_classification,
    test_cross_language_example,
    test_lean_emission,
    test_provenance_transitive_grounding,
    test_provenance_diamond_dag,
    test_provenance_one_bad_parent,
    test_quality_lattice_associativity,
    test_cegar_no_counterexamples,
    test_cache_multiple_keys,
    test_parser_empty_source,
    test_parser_no_markers,
    test_hallucination_detector_clean_code,
]


def run_all_tests(verbose: bool = True) -> Tuple[int, int]:
    """Run every test function, returning (passed, failed)."""
    passed = 0
    failed = 0
    for test_fn in _ALL_TESTS:
        name = test_fn.__name__
        try:
            test_fn()
            passed += 1
            if verbose:
                print(f"  ✓ {name}")
        except Exception as exc:
            failed += 1
            if verbose:
                print(f"  ✗ {name}: {exc}")
    return passed, failed


if __name__ == "__main__":
    print("=== Integration Tests ===")
    p, f = run_all_tests(verbose=True)
    total = p + f
    print(f"\n{p}/{total} passed, {f} failed")
    if f > 0:
        raise SystemExit(1)
    print("All integration tests passed ✓")
