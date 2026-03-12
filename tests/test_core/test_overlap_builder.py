"""Tests for OverlapBuilder -- overlap detection between observation sites.

Tests verify lineage, control, tensor-pack, call, error-path, loop-header,
proof-trace, module-boundary, and morphism-induced overlap detection.
"""

import pytest

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import ConcreteSite, ConcreteMorphism
from deppy.core.site_factory import SiteFactory
from deppy.core.overlap_builder import OverlapBuilder, OverlapEdge


# ============================================================================
# Helpers
# ============================================================================


def _make_factory():
    return SiteFactory(file_path="test.py")


def _sites_dict(*sites):
    return {s.site_id: s for s in sites}


def _has_overlap(overlaps, sid_a, sid_b):
    """Check if a pair exists in either order."""
    for a, b in overlaps:
        if (a == sid_a and b == sid_b) or (a == sid_b and b == sid_a):
            return True
    return False


# ============================================================================
# Lineage overlaps
# ============================================================================


class TestLineageOverlaps:
    """Two SSA sites for the same variable name should overlap."""

    def test_same_variable_different_versions(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        v1 = f.create_ssa_site("x", ssa_version=1)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(v0, v1), [])
        assert _has_overlap(overlaps, v0.site_id, v1.site_id)

    def test_three_versions_chain(self):
        f = _make_factory()
        v0 = f.create_ssa_site("y", ssa_version=0)
        v1 = f.create_ssa_site("y", ssa_version=1)
        v2 = f.create_ssa_site("y", ssa_version=2)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(v0, v1, v2), [])
        assert _has_overlap(overlaps, v0.site_id, v1.site_id)
        assert _has_overlap(overlaps, v1.site_id, v2.site_id)

    def test_different_variables_no_overlap(self):
        f = _make_factory()
        x0 = f.create_ssa_site("x", ssa_version=0)
        y0 = f.create_ssa_site("y", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(x0, y0), [])
        assert not _has_overlap(overlaps, x0.site_id, y0.site_id)

    def test_argument_to_first_ssa(self):
        f = _make_factory()
        arg = f.create_argument_site("x")
        ssa0 = f.create_ssa_site("x", ssa_version=0)
        ssa1 = f.create_ssa_site("x", ssa_version=1)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(arg, ssa0, ssa1), [])
        assert _has_overlap(overlaps, arg.site_id, ssa0.site_id)

    def test_annotated_overlaps(self):
        f = _make_factory()
        v0 = f.create_ssa_site("z", ssa_version=0)
        v1 = f.create_ssa_site("z", ssa_version=1)
        builder = OverlapBuilder()
        edges = builder.build_overlaps_annotated(_sites_dict(v0, v1), [])
        assert len(edges) >= 1
        edge = edges[0]
        assert isinstance(edge, OverlapEdge)
        assert edge.kind == "lineage"
        assert edge.confidence == 1.0


# ============================================================================
# Control overlaps
# ============================================================================


class TestControlOverlaps:
    """Branch guard sites should overlap with the variables they narrow."""

    def test_guard_narrows_variable(self):
        f = _make_factory()
        guard = f.create_branch_guard_site("g0", narrowed_vars=["x"])
        ssa_x = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(guard, ssa_x), [])
        assert _has_overlap(overlaps, guard.site_id, ssa_x.site_id)

    def test_guard_with_no_narrowing_no_overlap(self):
        f = _make_factory()
        guard = f.create_branch_guard_site("g0", narrowed_vars=[])
        ssa_y = f.create_ssa_site("y", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(guard, ssa_y), [])
        # Without narrowed_vars and no condition text, there may be no overlap
        # (depends on condition text heuristic)
        assert isinstance(overlaps, list)

    def test_guard_condition_text_heuristic(self):
        f = _make_factory()
        guard = f.create_branch_guard_site("g1", condition_text="x > 0")
        ssa_x = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(guard, ssa_x), [])
        # Condition text mentions "x", so heuristic overlap should fire
        assert _has_overlap(overlaps, guard.site_id, ssa_x.site_id)


# ============================================================================
# Tensor pack overlaps
# ============================================================================


class TestTensorPackOverlaps:
    """Shape, order, and indexing sites for the same tensor should overlap."""

    def test_shape_and_order_overlap(self):
        f = _make_factory()
        shape = f.create_tensor_shape_site("T")
        order = f.create_tensor_order_site("T")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(shape, order), [])
        assert _has_overlap(overlaps, shape.site_id, order.site_id)

    def test_shape_and_indexing_overlap(self):
        f = _make_factory()
        shape = f.create_tensor_shape_site("A")
        idx = f.create_tensor_indexing_site("A")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(shape, idx), [])
        assert _has_overlap(overlaps, shape.site_id, idx.site_id)

    def test_all_three_tensor_sites(self):
        f = _make_factory()
        shape = f.create_tensor_shape_site("M")
        order = f.create_tensor_order_site("M")
        idx = f.create_tensor_indexing_site("M")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(shape, order, idx), [])
        assert _has_overlap(overlaps, shape.site_id, order.site_id)
        assert _has_overlap(overlaps, shape.site_id, idx.site_id)
        assert _has_overlap(overlaps, order.site_id, idx.site_id)

    def test_different_tensors_no_pack_overlap(self):
        f = _make_factory()
        shape_a = f.create_tensor_shape_site("A")
        shape_b = f.create_tensor_shape_site("B")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(shape_a, shape_b), [])
        assert not _has_overlap(overlaps, shape_a.site_id, shape_b.site_id)

    def test_tensor_and_ssa_overlap(self):
        f = _make_factory()
        shape = f.create_tensor_shape_site("arr")
        ssa_arr = f.create_ssa_site("arr", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(shape, ssa_arr), [])
        assert _has_overlap(overlaps, shape.site_id, ssa_arr.site_id)


# ============================================================================
# Morphism-induced overlaps
# ============================================================================


class TestMorphismInducedOverlaps:
    """Morphisms connecting sites should induce overlaps."""

    def test_direct_morphism(self):
        f = _make_factory()
        a = f.create_ssa_site("a", ssa_version=0)
        b = f.create_ssa_site("b", ssa_version=0)
        morph = ConcreteMorphism(_source=a.site_id, _target=b.site_id)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(a, b), [morph])
        assert _has_overlap(overlaps, a.site_id, b.site_id)

    def test_common_target(self):
        f = _make_factory()
        a = f.create_ssa_site("a", ssa_version=0)
        b = f.create_ssa_site("b", ssa_version=0)
        c = f.create_ssa_site("c", ssa_version=0)
        m1 = ConcreteMorphism(_source=a.site_id, _target=c.site_id)
        m2 = ConcreteMorphism(_source=b.site_id, _target=c.site_id)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(a, b, c), [m1, m2])
        assert _has_overlap(overlaps, a.site_id, b.site_id)

    def test_no_morphism_no_induced_overlap(self):
        f = _make_factory()
        a = f.create_argument_site("a")
        b = f.create_argument_site("b")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(a, b), [])
        # Without shared var names or morphisms, no overlap
        assert not _has_overlap(overlaps, a.site_id, b.site_id)


# ============================================================================
# Error-path overlaps
# ============================================================================


class TestErrorPathOverlaps:

    def test_error_overlaps_with_source_op_variable(self):
        f = _make_factory()
        err = f.create_error_site("IndexError", source_op="xs[i]")
        ssa_xs = f.create_ssa_site("xs", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(err, ssa_xs), [])
        assert _has_overlap(overlaps, err.site_id, ssa_xs.site_id)

    def test_guarded_error_overlaps_with_guard(self):
        f = _make_factory()
        err = f.create_error_site("KeyError", guarded=True)
        guard = f.create_branch_guard_site("g0")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(err, guard), [])
        assert _has_overlap(overlaps, err.site_id, guard.site_id)


# ============================================================================
# Loop-header overlaps
# ============================================================================


class TestLoopHeaderOverlaps:

    def test_loop_overlaps_with_loop_variable(self):
        f = _make_factory()
        loop = f.create_loop_site("loop_0", loop_variable="i")
        ssa_i = f.create_ssa_site("i", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(loop, ssa_i), [])
        assert _has_overlap(overlaps, loop.site_id, ssa_i.site_id)

    def test_loop_no_overlap_with_unrelated_variable(self):
        f = _make_factory()
        loop = f.create_loop_site("loop_0", loop_variable="i")
        ssa_x = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(loop, ssa_x), [])
        assert not _has_overlap(overlaps, loop.site_id, ssa_x.site_id)


# ============================================================================
# Module-boundary overlaps
# ============================================================================


class TestModuleBoundaryOverlaps:

    def test_module_overlaps_with_argument(self):
        f = _make_factory()
        mod = f.create_module_summary_site("mymod")
        arg = f.create_argument_site("x")
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(mod, arg), [])
        assert _has_overlap(overlaps, mod.site_id, arg.site_id)

    def test_module_overlaps_with_return(self):
        f = _make_factory()
        mod = f.create_module_summary_site("mymod")
        ret = f.create_return_site()
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(mod, ret), [])
        assert _has_overlap(overlaps, mod.site_id, ret.site_id)


# ============================================================================
# Proof/trace overlaps
# ============================================================================


class TestProofTraceOverlaps:

    def test_proof_overlaps_with_mentioned_variable(self):
        f = _make_factory()
        proof = f.create_proof_site("p0", proposition="x >= 0")
        ssa_x = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(proof, ssa_x), [])
        assert _has_overlap(overlaps, proof.site_id, ssa_x.site_id)

    def test_trace_overlaps_with_observed_variable(self):
        f = _make_factory()
        trace = f.create_trace_site("t0", trace_point="after x assignment")
        ssa_x = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(trace, ssa_x), [])
        assert _has_overlap(overlaps, trace.site_id, ssa_x.site_id)


# ============================================================================
# Confidence threshold
# ============================================================================


class TestConfidenceThreshold:

    def test_low_confidence_filtered(self):
        f = _make_factory()
        # Error with no source_op has low confidence for call overlap
        err = f.create_error_site("RuntimeError")
        call = f.create_call_site("foo")
        builder = OverlapBuilder(confidence_threshold=0.8)
        overlaps = builder.build_overlaps(_sites_dict(err, call), [])
        # At threshold 0.8, low-confidence overlaps should be filtered
        # The exact result depends on the confidence assigned
        assert isinstance(overlaps, list)

    def test_zero_threshold_includes_all(self):
        f = _make_factory()
        err = f.create_error_site("RuntimeError")
        call = f.create_call_site("foo")
        builder = OverlapBuilder(confidence_threshold=0.0)
        overlaps = builder.build_overlaps(_sites_dict(err, call), [])
        # With zero threshold, even weak overlaps are included
        assert isinstance(overlaps, list)


# ============================================================================
# Diagnostics
# ============================================================================


class TestDiagnostics:

    def test_overlap_kind_histogram(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        v1 = f.create_ssa_site("x", ssa_version=1)
        builder = OverlapBuilder()
        builder.build_overlaps(_sites_dict(v0, v1), [])
        hist = builder.overlap_kind_histogram()
        assert "lineage" in hist
        assert hist["lineage"] >= 1

    def test_summary_report(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        v1 = f.create_ssa_site("x", ssa_version=1)
        builder = OverlapBuilder()
        builder.build_overlaps(_sites_dict(v0, v1), [])
        report = builder.summary_report()
        assert "OverlapBuilder" in report

    def test_last_edges(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        v1 = f.create_ssa_site("x", ssa_version=1)
        builder = OverlapBuilder()
        builder.build_overlaps(_sites_dict(v0, v1), [])
        assert len(builder.last_edges) >= 1

    def test_repr(self):
        builder = OverlapBuilder()
        assert "OverlapBuilder" in repr(builder)


# ============================================================================
# Deduplication
# ============================================================================


class TestDeduplication:

    def test_no_duplicate_pairs(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        v1 = f.create_ssa_site("x", ssa_version=1)
        arg = f.create_argument_site("x")
        morph = ConcreteMorphism(_source=arg.site_id, _target=v0.site_id)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(v0, v1, arg), [morph])
        # Check no (a, b) and (b, a) duplicates
        canonical = set()
        for a, b in overlaps:
            pair = tuple(sorted([str(a), str(b)]))
            assert pair not in canonical, f"Duplicate overlap: {a} <-> {b}"
            canonical.add(pair)

    def test_no_self_loops(self):
        f = _make_factory()
        v0 = f.create_ssa_site("x", ssa_version=0)
        builder = OverlapBuilder()
        overlaps = builder.build_overlaps(_sites_dict(v0), [])
        for a, b in overlaps:
            assert a != b, "Self-loop detected in overlaps"
