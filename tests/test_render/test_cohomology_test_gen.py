"""Tests for deppy.render.cohomology_test_gen — H¹-targeted test generation."""

from __future__ import annotations

import pytest

from deppy.render.cohomology_test_gen import (
    TargetedTest,
    TestGenerationResult,
    generate_targeted_tests,
)


# ── TargetedTest dataclass ───────────────────────────────────────────────────

class TestTargetedTest:
    def test_creation(self):
        t = TargetedTest(
            test_name="test_null_boundary",
            code="assert f(None) is not None",
            target_conjunct="result is not None",
            target_site=0,
            boundary_description="None input",
            h1_class=0,
        )
        assert t.test_name == "test_null_boundary"
        assert t.priority == 1.0

    def test_format(self):
        t = TargetedTest(
            test_name="test_x",
            code="assert f(0) > 0",
            target_conjunct="x > 0",
            target_site=1,
            boundary_description="zero boundary",
            h1_class=0,
        )
        formatted = t.format()
        assert "zero boundary" in formatted
        assert "assert" in formatted


# ── TestGenerationResult ─────────────────────────────────────────────────────

class TestTestGenerationResult:
    def test_empty(self):
        result = TestGenerationResult(function_name="f")
        assert len(result.tests) == 0
        summary = result.summary()
        assert "f" in summary

    def test_with_tests(self):
        result = TestGenerationResult(
            function_name="f",
            tests=[
                TargetedTest(
                    test_name="t1", code="pass", target_conjunct="x",
                    target_site=0, boundary_description="", h1_class=0,
                ),
            ],
            h1_classes_targeted=1,
            total_h1_classes=2,
        )
        assert len(result.tests) == 1
        assert result.h1_classes_targeted == 1


# ── Mock objects for SpecVerificationResult ──────────────────────────────────

class _MockCoverSite:
    def __init__(self, conjunct_idx=0, path_idx=0):
        self.conjunct_idx = conjunct_idx
        self.path_idx = path_idx


class _MockConjunct:
    def __init__(self, source="x > 0"):
        self.source = source


class _MockCover:
    def __init__(self, sites=None):
        self.sites = sites or []


class _MockDecomp:
    def __init__(self, conjuncts=None):
        self.conjuncts = conjuncts or []


class _MockVCResult:
    def __init__(self, proved=True, method="z3"):
        self.proved = proved
        self.method = method


class _MockImplAnalysis:
    pass


class _MockSpecResult:
    def __init__(self, n_proved=2, n_inconclusive=1, n_total=3):
        self.function_name = "my_func"
        self.spec_name = "my_spec"
        self.n_vcs_proved = n_proved
        self.n_vcs_total = n_total
        sites = []
        conjuncts = []
        vc_results = []
        for i in range(n_total):
            sites.append(_MockCoverSite(conjunct_idx=i))
            conjuncts.append(_MockConjunct(f"pred_{i}(result)"))
            proved = i < n_proved
            vc_results.append(_MockVCResult(proved=proved, method="z3" if proved else "inconclusive"))
        self.cover = _MockCover(sites)
        self.spec_decomposition = _MockDecomp(conjuncts)
        self.vc_results = vc_results
        self.impl_analysis = _MockImplAnalysis()


# ── generate_targeted_tests ──────────────────────────────────────────────────

class TestGenerateTargetedTests:
    def test_all_proved_generates_no_tests(self):
        result = _MockSpecResult(n_proved=3, n_inconclusive=0, n_total=3)
        gen = generate_targeted_tests(result)
        assert isinstance(gen, TestGenerationResult)
        assert len(gen.tests) == 0

    def test_inconclusive_generates_tests(self):
        result = _MockSpecResult(n_proved=1, n_inconclusive=2, n_total=3)
        gen = generate_targeted_tests(result)
        assert len(gen.tests) >= 1
        assert gen.inconclusive_sites >= 1

    def test_max_tests_limit(self):
        result = _MockSpecResult(n_proved=0, n_inconclusive=5, n_total=5)
        gen = generate_targeted_tests(result, max_tests=2)
        assert len(gen.tests) <= 2

    def test_test_has_code(self):
        result = _MockSpecResult(n_proved=1, n_inconclusive=1, n_total=2)
        gen = generate_targeted_tests(result)
        if gen.tests:
            t = gen.tests[0]
            assert t.code != ""
            assert t.test_name != ""

    def test_no_cover_handled(self):
        result = _MockSpecResult()
        result.cover = None
        gen = generate_targeted_tests(result)
        assert isinstance(gen, TestGenerationResult)
        # Without cover, the generator may still use vc_results directly

    def test_no_decomposition_handled(self):
        result = _MockSpecResult()
        result.spec_decomposition = None
        gen = generate_targeted_tests(result)
        assert isinstance(gen, TestGenerationResult)

    def test_coverage_metric(self):
        result = _MockSpecResult(n_proved=2, n_inconclusive=1, n_total=3)
        gen = generate_targeted_tests(result)
        assert gen.coverage_before == pytest.approx(2 / 3, abs=0.01)
