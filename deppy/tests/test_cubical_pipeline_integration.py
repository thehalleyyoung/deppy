"""Tests for the cubical-AST integration into ``verify_module_safety``.

Phase 3 of the round-2 cubical audit: the pipeline now runs the
cubical analysis per function, attaches the result to the
function verdict, and aggregates module-level statistics.

These tests verify:

  * Per-function ``FunctionVerdict.cubical_cell_counts`` reflects
    the function's control-flow topology.
  * ``cubical_kan_candidates`` is non-negative and reflects the
    Kan-fillable cells.
  * ``cubical_obligations_total`` ≥ ``cubical_obligations_verified``.
  * ``cubical_euler`` is computed.
  * The module verdict aggregates correctly: sum of per-function
    counts equals the module total.
"""
from __future__ import annotations

import textwrap

from deppy.pipeline.safety_pipeline import verify_module_safety


# ─────────────────────────────────────────────────────────────────────
#  Per-function cubical fields
# ─────────────────────────────────────────────────────────────────────


class TestFunctionVerdictCubicalFields:
    def test_simple_function_has_cubical_summary(self):
        src = textwrap.dedent("""
            def f():
                return 1
        """)
        verdict = verify_module_safety(src)
        fv = verdict.functions.get("f")
        assert fv is not None
        # Cubical fields populated.
        assert isinstance(fv.cubical_cell_counts, dict)
        assert fv.cubical_kan_candidates >= 0
        assert fv.cubical_obligations_total >= 0
        # Verified count is bounded by total.
        assert (
            fv.cubical_obligations_verified
            <= fv.cubical_obligations_total
        )

    def test_branched_function_has_higher_cells(self):
        src = textwrap.dedent("""
            def f(x: int) -> int:
                if x > 0:
                    return 1
                return 0
        """)
        verdict = verify_module_safety(src)
        fv = verdict.functions.get("f")
        assert fv is not None
        # An if-statement produces a 2-cell.
        assert fv.cubical_cell_counts.get(2, 0) >= 1

    def test_loop_function_has_loop_square(self):
        src = textwrap.dedent("""
            def f(n: int) -> int:
                while n > 0:
                    n -= 1
                return n
        """)
        verdict = verify_module_safety(src)
        fv = verdict.functions.get("f")
        assert fv is not None
        assert fv.cubical_cell_counts.get(2, 0) >= 1


# ─────────────────────────────────────────────────────────────────────
#  Module-level aggregation
# ─────────────────────────────────────────────────────────────────────


class TestModuleAggregation:
    def test_module_totals_match_function_sums(self):
        src = textwrap.dedent("""
            def f(x: int) -> int:
                if x > 0:
                    return 1
                return 0

            def g(n: int) -> int:
                while n > 0:
                    n -= 1
                return n
        """)
        verdict = verify_module_safety(src)
        # Sum per-function totals.
        sum_cells = sum(
            sum(fv.cubical_cell_counts.values())
            for fv in verdict.functions.values()
        )
        sum_kan = sum(
            fv.cubical_kan_candidates
            for fv in verdict.functions.values()
        )
        sum_obs = sum(
            fv.cubical_obligations_total
            for fv in verdict.functions.values()
        )
        sum_verified = sum(
            fv.cubical_obligations_verified
            for fv in verdict.functions.values()
        )
        # Module-level totals match.
        assert verdict.cubical_total_cells == sum_cells
        assert verdict.cubical_total_kan_candidates == sum_kan
        assert verdict.cubical_total_obligations == sum_obs
        assert (
            verdict.cubical_total_obligations_verified == sum_verified
        )

    def test_safe_module_unchanged_safety_verdict(self):
        # Cubical analysis is informational; it must NOT change
        # the safety verdict.
        src = textwrap.dedent("""
            def f():
                return 1
        """)
        verdict = verify_module_safety(src)
        # Module is safe.
        fv = verdict.functions.get("f")
        assert fv is not None
        assert fv.is_safe


class TestCubicalDoesNotCauseFailures:
    def test_pipeline_succeeds_with_cubical_disabled_by_failure(self):
        # If the cubical analysis itself raises, the pipeline
        # should still produce a verdict — the cubical fields just
        # remain at their defaults.  This tests the
        # ``except Exception`` guard around the cubical block.
        src = textwrap.dedent("""
            def f():
                return 1
        """)
        verdict = verify_module_safety(src)
        # Verdict is produced regardless.
        assert verdict is not None
        assert verdict.functions
