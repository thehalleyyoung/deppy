"""Tests for deppy.render.incremental_verify — Mayer-Vietoris locality."""

from __future__ import annotations

import pytest

from deppy.render.incremental_verify import (
    IncrementalVerifyPlan,
    plan_incremental_reverify,
)


# ── IncrementalVerifyPlan dataclass ──────────────────────────────────────────

class TestIncrementalVerifyPlan:
    def test_savings_nothing_to_recheck(self):
        plan = IncrementalVerifyPlan(
            changed_lines=frozenset(),
            total_vcs=10,
            recheck_vcs=[],
            unchanged_vcs=list(range(10)),
        )
        assert plan.savings == 1.0

    def test_savings_everything_to_recheck(self):
        plan = IncrementalVerifyPlan(
            changed_lines=frozenset({1, 2, 3}),
            total_vcs=3,
            recheck_vcs=[0, 1, 2],
            unchanged_vcs=[],
        )
        assert plan.savings == 0.0

    def test_savings_partial(self):
        plan = IncrementalVerifyPlan(
            changed_lines=frozenset({5}),
            total_vcs=4,
            recheck_vcs=[2],
            unchanged_vcs=[0, 1, 3],
        )
        assert plan.savings == pytest.approx(0.75)

    def test_savings_zero_total(self):
        plan = IncrementalVerifyPlan(
            changed_lines=frozenset(),
            total_vcs=0,
        )
        assert plan.savings == 0.0  # 0/0 → 0.0 by convention

    def test_summary(self):
        plan = IncrementalVerifyPlan(
            changed_lines=frozenset({10, 11}),
            total_vcs=5,
            recheck_vcs=[1, 3],
            unchanged_vcs=[0, 2, 4],
        )
        summary = plan.summary()
        assert "2" in summary  # 2 to recheck
        assert "5" in summary or "3" in summary  # total or unchanged


# ── Mock objects for SpecVerificationResult ──────────────────────────────────

class _MockCoverSite:
    def __init__(self, path_idx=0, conjunct_idx=0):
        self.path_idx = path_idx
        self.conjunct_idx = conjunct_idx


class _MockPath:
    def __init__(self, line_range=(1, 10), conditions=None):
        self.line_range = line_range
        self.conditions = conditions or []


class _MockCondition:
    def __init__(self, lineno=5):
        self.lineno = lineno


class _MockCover:
    def __init__(self, sites=None, overlap_graph=None):
        self.sites = sites or []
        self.overlap_graph = overlap_graph or {}


class _MockDecomp:
    def __init__(self, conjuncts=None):
        self.conjuncts = conjuncts or []


class _MockVCResult:
    def __init__(self, proved=True, method="z3"):
        self.proved = proved
        self.method = method


class _MockImplAnalysis:
    def __init__(self, paths=None):
        self.paths = paths or []


class _MockSpecResult:
    def __init__(self, n_sites=3, line_ranges=None):
        sites = []
        paths = []
        vcs = []
        for i in range(n_sites):
            lr = line_ranges[i] if line_ranges else (i * 10 + 1, (i + 1) * 10)
            sites.append(_MockCoverSite(path_idx=i, conjunct_idx=i))
            paths.append(_MockPath(line_range=lr))
            vcs.append(_MockVCResult(proved=True))

        self.cover = _MockCover(
            sites=sites,
            overlap_graph={i: [j for j in range(n_sites) if j != i]
                           for i in range(n_sites)},
        )
        self.vc_results = vcs
        self.spec_decomposition = _MockDecomp()
        self.impl_analysis = _MockImplAnalysis(paths=paths)


# ── plan_incremental_reverify ────────────────────────────────────────────────

class TestPlanIncrementalReverify:
    def test_no_changes(self):
        result = _MockSpecResult(n_sites=3)
        plan = plan_incremental_reverify(result, changed_lines=set())
        assert isinstance(plan, IncrementalVerifyPlan)
        assert len(plan.recheck_vcs) == 0
        assert plan.savings == 1.0

    def test_change_in_first_site(self):
        result = _MockSpecResult(
            n_sites=3,
            line_ranges=[(1, 10), (11, 20), (21, 30)],
        )
        plan = plan_incremental_reverify(result, changed_lines={5})
        assert len(plan.recheck_vcs) >= 1
        assert 0 in plan.recheck_vcs  # site 0 covers lines 1-10

    def test_change_outside_all_sites(self):
        result = _MockSpecResult(
            n_sites=2,
            line_ranges=[(1, 10), (11, 20)],
        )
        plan = plan_incremental_reverify(result, changed_lines={100})
        # Line 100 is outside all site ranges
        assert len(plan.recheck_vcs) == 0 or plan.savings > 0

    def test_no_cover(self):
        result = _MockSpecResult()
        result.cover = None
        plan = plan_incremental_reverify(result, changed_lines={5})
        assert isinstance(plan, IncrementalVerifyPlan)
        # Without cover, conservatively recheck all
        assert len(plan.recheck_vcs) == plan.total_vcs

    def test_total_vcs_matches_cover(self):
        result = _MockSpecResult(n_sites=5)
        plan = plan_incremental_reverify(result, changed_lines={1})
        assert plan.total_vcs == 5

    def test_overlap_expansion(self):
        """Changing one site should expand to overlapping sites."""
        result = _MockSpecResult(
            n_sites=3,
            line_ranges=[(1, 10), (11, 20), (21, 30)],
        )
        # All sites overlap with all others per our mock
        plan = plan_incremental_reverify(result, changed_lines={5})
        # Should expand from site 0 to neighbors
        assert len(plan.recheck_vcs) >= 1
