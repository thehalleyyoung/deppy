"""Tests for deppy.render.hit_loops — HIT-based loop precision analysis."""

from __future__ import annotations

import ast
import pytest

from deppy.render.hit_loops import (
    HITLoopAnalyzer,
    HITLoopResult,
    HITQuotient,
    LoopIteration,
    PathConstructor,
)


def _analyze(code: str, entry: dict | None = None) -> HITLoopResult:
    tree = ast.parse(code)
    # Find the first loop
    for node in ast.walk(tree):
        if isinstance(node, (ast.While, ast.For)):
            analyzer = HITLoopAnalyzer()
            return analyzer.analyze_loop(node, entry)
    raise ValueError("No loop found in code")


# ── HITQuotient dataclass ────────────────────────────────────────────────────

class TestHITQuotient:
    def test_precise_with_bounds(self):
        q = HITQuotient(variable="x", lower_bound=0, upper_bound=10)
        assert q.is_precise

    def test_not_precise_without_any_info(self):
        q = HITQuotient(variable="x")
        assert not q.is_precise

    def test_precise_with_lower_only(self):
        q = HITQuotient(variable="x", lower_bound=0)
        assert q.is_precise


# ── HITLoopResult ────────────────────────────────────────────────────────────

class TestHITLoopResult:
    def test_summary(self):
        result = HITLoopResult(
            loop_line=5,
            iterations_explored=8,
            quotients={"x": HITQuotient(variable="x", lower_bound=0, upper_bound=9)},
            converged=True,
        )
        summary = result.summary()
        assert "x" in summary
        assert "0" in summary
        assert "9" in summary


# ── While-loop analysis ─────────────────────────────────────────────────────

class TestWhileLoops:
    def test_simple_increment(self):
        result = _analyze("while x < 10:\n    x += 1", {"x": 0})
        assert "x" in result.quotients
        q = result.quotients["x"]
        assert q.lower_bound == 0
        assert q.upper_bound is not None
        assert q.upper_bound <= 10
        assert q.monotonicity == "increasing"

    def test_simple_decrement(self):
        result = _analyze("while x > 0:\n    x -= 1", {"x": 10})
        assert "x" in result.quotients
        q = result.quotients["x"]
        assert q.monotonicity == "decreasing"
        assert q.upper_bound == 10

    def test_no_entry_state(self):
        result = _analyze("while x < 5:\n    x += 1")
        # Should still produce a result, possibly less precise
        assert isinstance(result, HITLoopResult)

    def test_complex_condition(self):
        code = "while x < 100 and y > 0:\n    x += 2\n    y -= 1"
        result = _analyze(code, {"x": 0, "y": 50})
        assert "x" in result.quotients or "y" in result.quotients

    def test_non_numeric_loop_still_returns(self):
        code = "while flag:\n    flag = False"
        result = _analyze(code, {"flag": True})
        assert isinstance(result, HITLoopResult)

    def test_multiple_modified_vars(self):
        code = "while i < 5:\n    i += 1\n    total += i"
        result = _analyze(code, {"i": 0, "total": 0})
        assert "i" in result.quotients


# ── For-loop analysis ────────────────────────────────────────────────────────

class TestForLoops:
    def test_simple_range(self):
        result = _analyze("for i in range(10):\n    pass")
        assert "i" in result.quotients
        q = result.quotients["i"]
        assert q.lower_bound == 0

    def test_range_with_start(self):
        result = _analyze("for i in range(5, 10):\n    pass")
        assert "i" in result.quotients
        q = result.quotients["i"]
        assert q.lower_bound == 5

    def test_range_with_step(self):
        result = _analyze("for i in range(0, 20, 3):\n    pass")
        assert "i" in result.quotients

    def test_for_with_body_modification(self):
        code = "for i in range(5):\n    total += i"
        result = _analyze(code, {"total": 0})
        assert "i" in result.quotients


# ── Path constructors ────────────────────────────────────────────────────────

class TestPathConstructors:
    def test_paths_generated(self):
        result = _analyze("while x < 5:\n    x += 1", {"x": 0})
        assert len(result.paths) > 0
        for p in result.paths:
            assert isinstance(p, PathConstructor)
            assert p.variable == "x"
            assert p.target_iter == p.source_iter + 1

    def test_monotone_detection(self):
        result = _analyze("while x < 5:\n    x += 1", {"x": 0})
        monotone_paths = [p for p in result.paths if p.monotone is not None]
        assert len(monotone_paths) > 0


# ── Edge cases ───────────────────────────────────────────────────────────────

class TestEdgeCases:
    def test_infinite_loop_bounded(self):
        """Unrolling should be bounded by MAX_UNROLL."""
        result = _analyze("while True:\n    x += 1", {"x": 0})
        assert result.iterations_explored <= HITLoopAnalyzer.MAX_UNROLL + 1
        assert isinstance(result, HITLoopResult)

    def test_immediately_false_while(self):
        """Even for a while whose condition is initially false, the analyzer
        unrolls (it doesn't evaluate conditions). We just check it's bounded."""
        result = _analyze("while x < 0:\n    x += 1", {"x": 10})
        assert result.iterations_explored <= HITLoopAnalyzer.MAX_UNROLL + 1

    def test_constant_loop_body(self):
        """Loop body that doesn't change variables."""
        result = _analyze("while x < 5:\n    y = 1", {"x": 0})
        assert isinstance(result, HITLoopResult)
