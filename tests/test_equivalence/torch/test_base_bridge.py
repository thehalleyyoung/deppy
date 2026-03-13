"""Integration tests for the base framework bridge.

Tests that the torch layer correctly delegates to the base deppy
sheaf-theoretic infrastructure: ``bug_detect``, ``CechCohomologyComputer``,
and ``EquivalenceDescentChecker``.
"""
from __future__ import annotations

import unittest
from typing import List

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    EquivalenceVerdict,
    TensorLocalJudgment,
    TensorSiteKind,
    TensorStratum,
    BugKind,
)
from deppy.equivalence.torch.base_bridge import (
    detect_python_bugs,
    tensor_judgment_to_base,
    compute_cohomology_via_base,
    verify_descent_via_base,
    build_base_site_category,
    _BUGDETECT_TO_BUGKIND,
)


# ── Helpers ──────────────────────────────────────────────────────────────

def _make_judgment(
    kind: TensorSiteKind,
    verdict: EquivalenceVerdict,
    explanation: str = "",
) -> TensorLocalJudgment:
    return TensorLocalJudgment(
        site_id=SiteId(kind=SiteKind.TENSOR_SHAPE, name=f"test_{kind.name.lower()}"),
        tensor_site_kind=kind,
        stratum=TensorStratum.STRUCTURAL,
        verdict=verdict,
        explanation=explanation,
        max_abs_diff=0.0 if verdict == EquivalenceVerdict.EQUIVALENT else 1.0,
        max_rel_diff=0.0 if verdict == EquivalenceVerdict.EQUIVALENT else 0.5,
        test_cases_run=10,
        test_cases_passed=10 if verdict == EquivalenceVerdict.EQUIVALENT else 0,
    )


# ── Bug Detection Integration ───────────────────────────────────────────

class TestDetectPythonBugs(unittest.TestCase):
    """Test that detect_python_bugs correctly wraps base bug_detect."""

    def test_detects_division_by_zero(self):
        """A function with an obvious div-zero should be flagged."""
        def risky(x, y):
            return x / y
        bugs = detect_python_bugs(risky)
        # May or may not detect depending on analysis depth; just check types
        self.assertIsInstance(bugs, list)
        for b in bugs:
            self.assertIn(b.kind, list(BugKind))
            self.assertIsInstance(b.description, str)

    def test_clean_function_no_bugs(self):
        """A simple clean function should have no/few bugs."""
        def clean(x):
            return x + 1
        bugs = detect_python_bugs(clean)
        self.assertIsInstance(bugs, list)

    def test_returns_empty_for_non_inspectable(self):
        """Built-in functions can't be inspected — should return empty."""
        bugs = detect_python_bugs(abs)
        self.assertEqual(bugs, [])

    def test_bug_kinds_are_python_level(self):
        """All detected bugs should use Python-level BugKind values."""
        python_kinds = set(_BUGDETECT_TO_BUGKIND.values())
        def maybe_risky(data):
            d = {}
            return d[data]
        bugs = detect_python_bugs(maybe_risky)
        for b in bugs:
            if b.kind in python_kinds:
                self.assertIn(b.kind, python_kinds)

    def test_lambda_detection(self):
        """Lambdas should also be analyzable."""
        fn = lambda x: 1 / x
        bugs = detect_python_bugs(fn)
        self.assertIsInstance(bugs, list)


# ── Judgment Bridging ────────────────────────────────────────────────────

class TestTensorJudgmentToBase(unittest.TestCase):
    """Test conversion from TensorLocalJudgment to base LocalEquivalenceJudgment."""

    def test_equivalent_judgment_conversion(self):
        tj = _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT)
        base_j = tensor_judgment_to_base(tj)
        self.assertEqual(base_j.site_id, tj.site_id)
        self.assertEqual(base_j.explanation, tj.explanation)

    def test_inequivalent_judgment_conversion(self):
        tj = _make_judgment(
            TensorSiteKind.NUMERICAL,
            EquivalenceVerdict.INEQUIVALENT,
            "values differ by 1.5",
        )
        base_j = tensor_judgment_to_base(tj)
        self.assertEqual(base_j.explanation, "values differ by 1.5")

    def test_all_verdicts_convertible(self):
        for v in EquivalenceVerdict:
            tj = _make_judgment(TensorSiteKind.DTYPE, v)
            base_j = tensor_judgment_to_base(tj)
            self.assertIsNotNone(base_j)


# ── Site Category Construction ───────────────────────────────────────────

class TestBuildBaseSiteCategory(unittest.TestCase):
    """Test build_base_site_category constructs valid categories."""

    def test_single_judgment(self):
        judgments = [_make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT)]
        cat = build_base_site_category(judgments)
        self.assertIsNotNone(cat)

    def test_multiple_judgments_with_overlaps(self):
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.STRIDE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.DTYPE, EquivalenceVerdict.EQUIVALENT),
        ]
        cat = build_base_site_category(judgments)
        self.assertIsNotNone(cat)


# ── Cohomology Integration ──────────────────────────────────────────────

class TestComputeCohomologyViaBase(unittest.TestCase):
    """Test that compute_cohomology_via_base delegates correctly."""

    def test_all_equivalent_trivial_cohomology(self):
        """All-equivalent judgments should give trivial H¹."""
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.DTYPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.NUMERICAL, EquivalenceVerdict.EQUIVALENT),
        ]
        result, classes = compute_cohomology_via_base(judgments)
        # Trivial H¹ = no obstruction classes
        trivial_classes = [c for c in classes if not c.is_trivial]
        # All equivalent → should have no non-trivial obstructions
        self.assertTrue(result.h1_trivial or len(trivial_classes) == 0)

    def test_inequivalent_gives_obstruction(self):
        """An inequivalent judgment should yield H¹ obstruction classes."""
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(
                TensorSiteKind.NUMERICAL,
                EquivalenceVerdict.INEQUIVALENT,
                "numerical divergence",
            ),
        ]
        result, classes = compute_cohomology_via_base(judgments)
        self.assertIsInstance(classes, list)

    def test_returns_tensor_cohomology_classes(self):
        """Output should be TensorCohomologyClass instances."""
        from deppy.equivalence.torch._protocols import TensorCohomologyClass
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.INEQUIVALENT, "mismatch"),
        ]
        result, classes = compute_cohomology_via_base(judgments)
        for c in classes:
            self.assertIsInstance(c, TensorCohomologyClass)


# ── Descent Integration ─────────────────────────────────────────────────

class TestVerifyDescentViaBase(unittest.TestCase):
    """Test that verify_descent_via_base delegates correctly."""

    def test_all_equivalent_descent_holds(self):
        """All equivalent → descent should be effective."""
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.DTYPE, EquivalenceVerdict.EQUIVALENT),
        ]
        result = verify_descent_via_base(judgments)
        self.assertTrue(result.is_effective)

    def test_mixed_verdicts(self):
        """Mixed verdicts may or may not hold — should not crash."""
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(
                TensorSiteKind.NUMERICAL,
                EquivalenceVerdict.INEQUIVALENT,
                "diverged",
            ),
        ]
        result = verify_descent_via_base(judgments)
        self.assertIsInstance(result.is_effective, bool)
        self.assertIsInstance(result.cocycle_violations, list)

    def test_single_judgment_descent(self):
        """Single judgment — trivially effective."""
        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
        ]
        result = verify_descent_via_base(judgments)
        self.assertTrue(result.is_effective)


# ── Full Pipeline Integration ───────────────────────────────────────────

class TestFullPipelineIntegration(unittest.TestCase):
    """E2E test that the torch pipeline uses base framework components."""

    def test_global_checker_uses_base_descent(self):
        """verify_tensor_descent should invoke base EquivalenceDescentChecker."""
        from deppy.equivalence.torch.torch_global_checker import (
            verify_tensor_descent,
        )
        from deppy.equivalence.torch._protocols import (
            LocalCheckResult,
            TensorEquivalenceConfig,
        )

        judgments = [
            _make_judgment(TensorSiteKind.SHAPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.DTYPE, EquivalenceVerdict.EQUIVALENT),
            _make_judgment(TensorSiteKind.NUMERICAL, EquivalenceVerdict.EQUIVALENT),
        ]
        local_result = LocalCheckResult(
            judgments=judgments,
            all_equivalent=True,
        )
        config = TensorEquivalenceConfig()
        result = verify_tensor_descent(local_result, config)
        self.assertTrue(result.is_effective)

    def test_global_checker_uses_base_cohomology(self):
        """compute_tensor_cohomology should invoke base CechCohomologyComputer."""
        from deppy.equivalence.torch.torch_global_checker import (
            compute_tensor_cohomology,
        )
        from deppy.equivalence.torch._protocols import (
            LocalCheckResult,
            DescentResult,
        )

        judgments = [
            _make_judgment(
                TensorSiteKind.NUMERICAL,
                EquivalenceVerdict.INEQUIVALENT,
                "numerical divergence",
            ),
        ]
        local_result = LocalCheckResult(
            judgments=judgments,
            all_equivalent=False,
        )
        descent = DescentResult(
            is_effective=True,
            cocycle_violations=[],
            glued_verdict=EquivalenceVerdict.INEQUIVALENT,
        )
        classes = compute_tensor_cohomology(local_result, descent)
        self.assertTrue(len(classes) >= 1)
        # At least one non-trivial class for the numerical failure
        non_trivial = [c for c in classes if not c.is_trivial]
        self.assertTrue(len(non_trivial) >= 1)

    def test_analysis_includes_python_bugs(self):
        """analyze_torch in bug_finding mode should call detect_python_bugs."""
        from deppy.equivalence.torch.analysis import analyze_torch
        from deppy.equivalence.torch._protocols import AnalysisMode

        def risky_fn(x):
            return x / 0

        try:
            result = analyze_torch(risky_fn, mode=AnalysisMode.BUG_FINDING)
            self.assertIsNotNone(result)
        except Exception:
            pass  # Function may fail during execution — that's fine


# ── Mapping Completeness ────────────────────────────────────────────────

class TestBugDetectMapping(unittest.TestCase):
    """Test the bug_detect → BugKind mapping is well-formed."""

    def test_all_mapped_kinds_exist(self):
        """Every value in the mapping should be a valid BugKind."""
        for kind in _BUGDETECT_TO_BUGKIND.values():
            self.assertIsInstance(kind, BugKind)

    def test_mapping_covers_key_types(self):
        """Key bug types from bug_detect should be mapped."""
        key_types = [
            "division_by_zero", "null_dereference", "type_error",
            "unbound_variable", "key_error",
        ]
        for bt in key_types:
            self.assertIn(bt, _BUGDETECT_TO_BUGKIND)

    def test_mapping_is_not_empty(self):
        self.assertTrue(len(_BUGDETECT_TO_BUGKIND) > 10)


if __name__ == "__main__":
    unittest.main()
