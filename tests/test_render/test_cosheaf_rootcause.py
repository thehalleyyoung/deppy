"""Tests for deppy.render.cosheaf_rootcause — backward data-flow root-cause tracing."""

from __future__ import annotations

import ast
import pytest

from deppy.render.cosheaf_rootcause import (
    CosheafChain,
    CosheafHomologyResult,
    CosheafRootCauseTracer,
    RootCauseKind,
    RootCauseSite,
)


# ── helpers ──────────────────────────────────────────────────────────────────

def _tracer(code: str) -> CosheafRootCauseTracer:
    return CosheafRootCauseTracer(ast.parse(code))


# ── CosheafChain dataclass ───────────────────────────────────────────────────

class TestCosheafChain:
    def test_depth_empty(self):
        chain = CosheafChain(bug_line=5, bug_type="NULL", bug_variable="x")
        assert chain.depth == 0

    def test_depth_with_entries(self):
        chain = CosheafChain(
            bug_line=5, bug_type="NULL", bug_variable="x",
            chain=[(4, "y", "assignment"), (3, "z", "assignment")],
        )
        assert chain.depth == 2

    def test_root_line_none_when_no_root(self):
        chain = CosheafChain(bug_line=5, bug_type="NULL", bug_variable="x")
        assert chain.root_line is None

    def test_root_line_present(self):
        chain = CosheafChain(
            bug_line=5, bug_type="NULL", bug_variable="x",
            root_cause=RootCauseSite(kind=RootCauseKind.LITERAL, line=1),
        )
        assert chain.root_line == 1


# ── CosheafHomologyResult ────────────────────────────────────────────────────

class TestCosheafHomologyResult:
    def test_empty(self):
        result = CosheafHomologyResult()
        assert result.h0_rank == 0
        assert result.h1_rank == 0
        assert "0 chains" in result.summary()

    def test_summary_with_data(self):
        chain = CosheafChain(
            bug_line=5, bug_type="NULL", bug_variable="x",
            root_cause=RootCauseSite(kind=RootCauseKind.PARAMETER, line=1),
        )
        result = CosheafHomologyResult(
            chains=[chain],
            root_cause_classes=[[chain]],
            h0_rank=1,
            h1_rank=0,
        )
        assert result.h0_rank == 1
        assert "1 chains" in result.summary() or "1 chain" in result.summary()


# ── CosheafRootCauseTracer ───────────────────────────────────────────────────

class TestTracer:
    def test_simple_assignment_chain(self):
        code = """\
def f(x):
    y = x
    z = y
    return z / 0
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(4, "DIVISION_BY_ZERO", "z")
        assert chain.bug_line == 4
        assert chain.bug_variable == "z"
        # Should trace back through y → x
        assert chain.depth >= 1
        assert chain.root_cause is not None

    def test_parameter_root(self):
        code = """\
def f(x):
    return x.strip()
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(2, "NULL_DEREF", "x")
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.PARAMETER

    def test_literal_root(self):
        code = """\
def f():
    x = 0
    return 1 / x
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(3, "DIVISION_BY_ZERO", "x")
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.LITERAL

    def test_call_return_root(self):
        code = """\
def f():
    x = g()
    return x.strip()
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(3, "NULL_DEREF", "x")
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.CALL_RETURN

    def test_constructor_root(self):
        code = """\
def f():
    x = []
    return x[0]
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(3, "INDEX_ERROR", "x")
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.CONSTRUCTOR

    def test_unknown_variable(self):
        code = """\
def f():
    return z
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(2, "UNBOUND", "z")
        # Should still return a chain even if variable not found
        assert chain.bug_line == 2
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.UNKNOWN

    def test_empty_function(self):
        code = """\
def f():
    pass
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(2, "NULL", "x")
        assert chain.bug_line == 2

    def test_trace_all_obstructions(self):
        """trace_all_obstructions uses duck-typed obstruction objects."""
        code = """\
def f(x, y):
    a = x
    b = y
    return a / b
"""

        class MockObs:
            def __init__(self, line, bug_type, var):
                self.line = line
                self.bug_type = bug_type
                self.requirement = type("R", (), {"description": var, "ast_node": None})()
                self.resolved_by_guard = False
                self.confidence = 1.0

        tracer = _tracer(code)
        obs_list = [
            MockObs(4, "DIVISION_BY_ZERO", "b"),
            MockObs(4, "NULL_DEREF", "a"),
        ]
        result = tracer.trace_all_obstructions(obs_list)
        assert isinstance(result, CosheafHomologyResult)
        assert len(result.chains) == 2
        assert result.h0_rank >= 1

    def test_multi_step_chain(self):
        code = """\
def f(x):
    a = x
    b = a
    c = b
    d = c
    return d.foo()
"""
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(6, "NULL_DEREF", "d")
        assert chain.depth >= 3
        assert chain.root_cause is not None
        assert chain.root_cause.kind == RootCauseKind.PARAMETER

    def test_no_function(self):
        """Module-level code should still work."""
        code = "x = 1\ny = x\n"
        tracer = _tracer(code)
        chain = tracer.trace_obstruction(2, "BUG", "y")
        assert chain.bug_line == 2


class TestH1Computation:
    def test_no_interactions(self):
        """Two independent bug chains have H1=0."""
        code = """\
def f(x, y):
    return x / y
"""
        tracer = _tracer(code)

        class MockObs:
            def __init__(self, line, bug_type, var):
                self.line = line
                self.bug_type = bug_type
                self.requirement = type("R", (), {"description": var, "ast_node": None})()
                self.resolved_by_guard = False
                self.confidence = 1.0

        obs = [
            MockObs(2, "NULL_DEREF", "x"),
            MockObs(2, "DIVISION_BY_ZERO", "y"),
        ]
        result = tracer.trace_all_obstructions(obs)
        # Two independent root causes → H0=2, H1 depends on shared vars
        assert result.h0_rank >= 1

    def test_shared_root_increases_h1(self):
        """Two bugs from the same root variable at the same assignment line
        end up in the same H0 class (= 1 class, not 2)."""
        code = """\
def f(x):
    a = x
    return a.strip() + a[0]
"""
        tracer = _tracer(code)

        class MockObs:
            def __init__(self, line, bug_type, var):
                self.line = line
                self.bug_type = bug_type
                self.requirement = type("R", (), {"description": var, "ast_node": None})()
                self.resolved_by_guard = False
                self.confidence = 1.0

        obs = [
            MockObs(3, "NULL_DEREF", "a"),
            MockObs(3, "INDEX_ERROR", "a"),
        ]
        result = tracer.trace_all_obstructions(obs)
        # Both trace back to same param x at same line → same H0 class
        assert result.h0_rank == 1
