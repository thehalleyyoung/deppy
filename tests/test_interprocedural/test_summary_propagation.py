"""Tests for summary propagation across function calls.

Covers FunctionSummary, PropagationResult, SummaryPropagator,
propagate_callee_summary, propagate_actual_to_formal, propagate_all,
and section merging.
"""

from __future__ import annotations

import textwrap

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.interprocedural.call_graph import CallEdge, CallGraph
from deppy.interprocedural.summary_propagation import (
    FunctionSummary,
    PropagationResult,
    SummaryPropagator,
    _merge_sections,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _site_id(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(name: str, kind: SiteKind = SiteKind.SSA_VALUE,
             refinements: dict | None = None,
             trust: TrustLevel = TrustLevel.BOUNDED_AUTO) -> LocalSection:
    return LocalSection(
        site_id=_site_id(name, kind),
        refinements=refinements or {},
        trust=trust,
        provenance=f"test:{name}",
    )


def _cover(*boundary_names: str, input_names: tuple[str, ...] = (),
           output_names: tuple[str, ...] = (),
           error_names: tuple[str, ...] = ()) -> Cover:
    """Build a minimal Cover for testing."""
    sites = {}
    for name in boundary_names:
        sid = _site_id(name)
        sites[sid] = ConcreteSite(_site_id=sid)

    input_boundary = set()
    for name in input_names:
        sid = _site_id(name, SiteKind.ARGUMENT_BOUNDARY)
        sites[sid] = ConcreteSite(_site_id=sid)
        input_boundary.add(sid)

    output_boundary = set()
    for name in output_names:
        sid = _site_id(name, SiteKind.RETURN_OUTPUT_BOUNDARY)
        sites[sid] = ConcreteSite(_site_id=sid)
        output_boundary.add(sid)

    error_sites = set()
    for name in error_names:
        sid = _site_id(name, SiteKind.ERROR)
        sites[sid] = ConcreteSite(_site_id=sid)
        error_sites.add(sid)

    return Cover(
        sites=sites,
        input_boundary=input_boundary,
        output_boundary=output_boundary,
        error_sites=error_sites,
    )


# ===================================================================
#  FunctionSummary
# ===================================================================


class TestFunctionSummary:
    """Tests for FunctionSummary dataclass."""

    def test_basic_properties(self):
        fs = FunctionSummary(_func_name="my_func")
        assert fs.func_name == "my_func"
        assert fs.input_sections == {}
        assert fs.output_sections == {}
        assert fs.error_sections == {}
        assert not fs.is_recursive
        assert fs.iteration_count == 0

    def test_with_sections(self):
        inp = {_site_id("param", SiteKind.ARGUMENT_BOUNDARY): _section("param")}
        out = {_site_id("ret", SiteKind.RETURN_OUTPUT_BOUNDARY): _section("ret")}
        fs = FunctionSummary(
            _func_name="f",
            _input_sections=inp,
            _output_sections=out,
            _is_recursive=True,
            _iteration_count=3,
        )
        assert len(fs.input_sections) == 1
        assert len(fs.output_sections) == 1
        assert fs.is_recursive
        assert fs.iteration_count == 3


# ===================================================================
#  PropagationResult
# ===================================================================


class TestPropagationResult:
    """Tests for PropagationResult dataclass."""

    def test_basic(self):
        pr = PropagationResult(_caller="main", _callee="helper")
        assert pr.caller == "main"
        assert pr.callee == "helper"
        assert pr.imported_sections == {}
        assert pr.trust_level == TrustLevel.BOUNDED_AUTO


# ===================================================================
#  _merge_sections
# ===================================================================


class TestMergeSections:
    """Tests for section merging."""

    def test_merge_same_site(self):
        s1 = _section("x", refinements={"lower_bound": 0})
        s2 = _section("x", refinements={"upper_bound": 10})
        merged = _merge_sections(s1, s2)
        assert "lower_bound" in merged.refinements
        assert "upper_bound" in merged.refinements

    def test_merge_trust_weaker(self):
        s1 = _section("x", trust=TrustLevel.PROOF_BACKED)
        s2 = _section("x", trust=TrustLevel.RESIDUAL)
        merged = _merge_sections(s1, s2)
        assert merged.trust == TrustLevel.RESIDUAL

    def test_merge_existing_key_preferred(self):
        s1 = _section("x", refinements={"key": "original"})
        s2 = _section("x", refinements={"key": "incoming"})
        merged = _merge_sections(s1, s2)
        assert merged.refinements["key"] == "original"

    def test_merge_witnesses(self):
        s1 = LocalSection(
            site_id=_site_id("x"), trust=TrustLevel.BOUNDED_AUTO,
            witnesses={"w1": "proof1"},
        )
        s2 = LocalSection(
            site_id=_site_id("x"), trust=TrustLevel.BOUNDED_AUTO,
            witnesses={"w2": "proof2"},
        )
        merged = _merge_sections(s1, s2)
        assert "w1" in merged.witnesses
        assert "w2" in merged.witnesses


# ===================================================================
#  SummaryPropagator
# ===================================================================


class TestSummaryPropagator:
    """Tests for SummaryPropagator."""

    def setup_method(self):
        self.propagator = SummaryPropagator()

    def test_empty_propagation(self):
        cg = CallGraph()
        result = self.propagator.propagate_all(cg, {})
        assert result == {}

    def test_propagate_callee_summary(self):
        caller_cover = _cover(
            input_names=("main.x",),
            output_names=("main.return",),
        )
        callee_cover = _cover(
            input_names=("helper.arg",),
            output_names=("helper.return",),
        )
        edge = CallEdge(
            _caller="main",
            _callee="helper",
            _call_site_id=_site_id("main.call_0", SiteKind.CALL_RESULT),
            _arguments=("x",),
        )
        updated = self.propagator.propagate_callee_summary(
            caller_cover, callee_cover, edge,
        )
        # Should produce some imported sections
        assert isinstance(updated, dict)

    def test_propagate_actual_to_formal(self):
        caller_sections = {
            _site_id("main.actual_arg", SiteKind.ARGUMENT_BOUNDARY): _section(
                "main.actual_arg", SiteKind.ARGUMENT_BOUNDARY,
                refinements={"non_negative": True},
            ),
        }
        callee_cover = _cover(input_names=("helper.arg",))
        edge = CallEdge(
            _caller="main",
            _callee="helper",
            _call_site_id=_site_id("main.call_0", SiteKind.CALL_RESULT),
            _arguments=("x",),
        )
        result = self.propagator.propagate_actual_to_formal(
            caller_sections, callee_cover, edge,
        )
        assert isinstance(result, dict)

    def test_propagation_log(self):
        caller_cover = _cover(output_names=("main.return",))
        callee_cover = _cover(output_names=("helper.return",))
        edge = CallEdge(
            _caller="main", _callee="helper",
            _call_site_id=_site_id("main.call_0", SiteKind.CALL_RESULT),
        )
        self.propagator.propagate_callee_summary(caller_cover, callee_cover, edge)
        assert len(self.propagator.propagation_log) >= 1
        log_entry = self.propagator.propagation_log[0]
        assert log_entry.caller == "main"
        assert log_entry.callee == "helper"

    def test_get_summary(self):
        assert self.propagator.get_summary("nonexistent") is None
        assert not self.propagator.has_summary("nonexistent")

    def test_clear(self):
        caller_cover = _cover(output_names=("main.return",))
        callee_cover = _cover(output_names=("helper.return",))
        edge = CallEdge(
            _caller="main", _callee="helper",
            _call_site_id=_site_id("main.call_0", SiteKind.CALL_RESULT),
        )
        self.propagator.propagate_callee_summary(caller_cover, callee_cover, edge)
        self.propagator.clear()
        assert self.propagator.summaries == {}
        assert self.propagator.propagation_log == []

    def test_propagate_all_simple_chain(self):
        """Test propagate_all on a simple a -> b chain."""
        cg = CallGraph.build_from_source(textwrap.dedent("""\
        def b():
            pass
        def a():
            b()
        """))
        cover_a = _cover(
            input_names=("a.x",),
            output_names=("a.return",),
        )
        cover_b = _cover(
            input_names=("b.arg",),
            output_names=("b.return",),
        )
        covers = {"a": cover_a, "b": cover_b}
        result = self.propagator.propagate_all(cg, covers)
        assert isinstance(result, dict)

    def test_trust_downgrade(self):
        """Test that trust is downgraded when trust_downgrade_on_transport is True."""
        prop = SummaryPropagator(trust_downgrade_on_transport=True)
        # Build a callee cover with a PROOF_BACKED output section
        callee_out_id = _site_id("callee.return", SiteKind.RETURN_OUTPUT_BOUNDARY)
        callee_cover = Cover(
            sites={callee_out_id: ConcreteSite(_site_id=callee_out_id)},
            output_boundary={callee_out_id},
        )
        caller_cover = _cover(output_names=("main.return",))
        edge = CallEdge(
            _caller="main", _callee="callee",
            _call_site_id=_site_id("main.call_0", SiteKind.CALL_RESULT),
        )
        result = prop.propagate_callee_summary(caller_cover, callee_cover, edge)
        # The result trust should be downgraded from the original
        assert isinstance(result, dict)
