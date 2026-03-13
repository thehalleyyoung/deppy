"""Tests for deppy.equivalence.semantic_diff — behavioral change detection."""

from __future__ import annotations

import pytest

from deppy.equivalence.semantic_diff import (
    DiffKind,
    SemanticDiffResult,
    SemanticDiffSite,
    semantic_diff,
)


# ── SemanticDiffResult dataclass ─────────────────────────────────────────────

class TestSemanticDiffResult:
    def test_ratio_all_unchanged(self):
        """No textual changes → ratio is 0.0 (no semantic changes either)."""
        result = SemanticDiffResult(
            function_name="f",
            h0_unchanged=5,
            h1_changed=0,
            textual_lines_changed=0,
        )
        assert result.semantic_ratio == 0.0

    def test_ratio_all_semantic(self):
        """Every textual change is semantic → ratio = 1.0."""
        result = SemanticDiffResult(
            function_name="f",
            h0_unchanged=0,
            h1_changed=5,
            textual_lines_changed=5,
            semantic_sites_changed=5,
        )
        assert result.semantic_ratio == 1.0

    def test_ratio_empty(self):
        result = SemanticDiffResult(function_name="f")
        assert result.semantic_ratio == 0.0

    def test_summary(self):
        result = SemanticDiffResult(
            function_name="f",
            h0_unchanged=3,
            h1_changed=2,
        )
        summary = result.summary()
        assert "f" in summary


# ── DiffKind enum ────────────────────────────────────────────────────────────

class TestDiffKind:
    def test_members_exist(self):
        assert DiffKind.UNCHANGED is not None
        assert DiffKind.DIVERGENT is not None
        assert DiffKind.ADDED is not None
        assert DiffKind.REMOVED is not None


# ── semantic_diff function ───────────────────────────────────────────────────

class TestSemanticDiff:
    def test_identical_functions(self):
        code = "def f(x):\n    return x + 1"
        result = semantic_diff(code, code)
        assert result.h1_changed == 0
        assert result.h0_unchanged >= 1

    def test_body_change(self):
        old = "def f(x):\n    return x + 1"
        new = "def f(x):\n    return x + 2"
        result = semantic_diff(old, new)
        assert result.h1_changed >= 1

    def test_signature_change(self):
        old = "def f(x):\n    return x"
        new = "def f(x, y):\n    return x + y"
        result = semantic_diff(old, new)
        assert result.h1_changed >= 1

    def test_return_type_change(self):
        old = "def f(x):\n    return x"
        new = "def f(x):\n    return str(x)"
        result = semantic_diff(old, new)
        assert result.h1_changed >= 1

    def test_decorator_change(self):
        old = "def f(x):\n    return x"
        new = "@cached\ndef f(x):\n    return x"
        result = semantic_diff(old, new)
        assert result.h1_changed >= 1

    def test_added_function(self):
        old = "def f(x):\n    return x"
        new = "def f(x):\n    return x\ndef g(y):\n    return y"
        result = semantic_diff(old, new, function_name="g")
        # g is in new but not old
        assert isinstance(result, SemanticDiffResult)

    def test_removed_function(self):
        old = "def f(x):\n    return x\ndef g(y):\n    return y"
        new = "def f(x):\n    return x"
        result = semantic_diff(old, new, function_name="g")
        assert isinstance(result, SemanticDiffResult)

    def test_explicit_function_name(self):
        old = "def f(x):\n    return x\ndef g(y):\n    return y + 1"
        new = "def f(x):\n    return x\ndef g(y):\n    return y + 2"
        result = semantic_diff(old, new, function_name="g")
        assert result.h1_changed >= 1
        assert result.function_name == "g"

    def test_empty_source(self):
        result = semantic_diff("", "def f():\n    pass")
        assert isinstance(result, SemanticDiffResult)

    def test_no_functions(self):
        old = "x = 1"
        new = "x = 2"
        result = semantic_diff(old, new)
        assert isinstance(result, SemanticDiffResult)

    def test_textual_lines_changed(self):
        old = "def f(x):\n    return x + 1"
        new = "def f(x):\n    return x + 2"
        result = semantic_diff(old, new)
        assert result.textual_lines_changed >= 1

    def test_multiple_behavioral_sites(self):
        old = "def f(x, y):\n    a = x + 1\n    b = y * 2\n    return a + b"
        new = "def f(x, y):\n    a = x + 1\n    b = y * 3\n    return a + b"
        result = semantic_diff(old, new)
        # At least one site changed (the multiplication)
        assert result.h1_changed >= 1

    def test_control_flow_change(self):
        old = "def f(x):\n    if x > 0:\n        return x\n    return -x"
        new = "def f(x):\n    if x >= 0:\n        return x\n    return -x"
        result = semantic_diff(old, new)
        assert result.h1_changed >= 1


class TestSemanticDiffSite:
    def test_creation(self):
        site = SemanticDiffSite(
            kind=DiffKind.DIVERGENT,
            line_old=10,
            line_new=12,
            description="return value changed",
        )
        assert site.kind == DiffKind.DIVERGENT
        assert site.confidence == 1.0
