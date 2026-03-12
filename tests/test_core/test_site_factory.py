"""Tests for SiteFactory -- all 14 site family factory methods.

Tests verify that each factory method produces a ConcreteSite with the
correct SiteKind, SiteId naming, carrier schema, and metadata.
"""

import pytest

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import ConcreteSite
from deppy.core.site_factory import SiteFactory


# ============================================================================
# Fixture
# ============================================================================


@pytest.fixture
def factory():
    return SiteFactory(file_path="test.py", default_source_line=1)


@pytest.fixture
def bare_factory():
    return SiteFactory()


# ============================================================================
# 1. ARGUMENT_BOUNDARY
# ============================================================================


class TestArgumentSite:

    def test_create_argument_site(self, factory):
        site = factory.create_argument_site("x", param_index=0)
        assert isinstance(site, ConcreteSite)
        assert site.kind == SiteKind.ARGUMENT_BOUNDARY
        assert "x" in site.site_id.name

    def test_argument_site_metadata(self, factory):
        site = factory.create_argument_site("y", param_index=1, annotation="int")
        assert site.metadata["param_name"] == "y"
        assert site.metadata["param_index"] == 1
        assert site.metadata["annotation"] == "int"

    def test_argument_site_with_default(self, factory):
        site = factory.create_argument_site("z", has_default=True)
        assert site.metadata["has_default"] is True

    def test_argument_site_has_schema(self, factory):
        site = factory.create_argument_site("w")
        assert site.carrier_schema is not None
        assert hasattr(site.carrier_schema, "fields")

    def test_argument_site_source_location(self, factory):
        site = factory.create_argument_site("a", source_line=10, source_col=5)
        assert site.site_id.source_location is not None
        assert site.site_id.source_location[1] == 10
        assert site.site_id.source_location[2] == 5


# ============================================================================
# 2. RETURN_OUTPUT_BOUNDARY
# ============================================================================


class TestReturnSite:

    def test_create_return_site(self, factory):
        site = factory.create_return_site(return_index=0)
        assert site.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        assert "return" in site.site_id.name

    def test_yield_site(self, factory):
        site = factory.create_return_site(return_index=0, is_yield=True)
        assert "yield" in site.site_id.name
        assert site.metadata["is_yield"] is True

    def test_raise_site(self, factory):
        site = factory.create_return_site(return_index=0, is_raise=True)
        assert "raise" in site.site_id.name
        assert site.metadata["is_raise"] is True

    def test_return_site_schema(self, factory):
        site = factory.create_return_site()
        assert site.carrier_schema is not None


# ============================================================================
# 3. SSA_VALUE
# ============================================================================


class TestSSASite:

    def test_create_ssa_site(self, factory):
        site = factory.create_ssa_site("x", ssa_version=0)
        assert site.kind == SiteKind.SSA_VALUE
        assert "x" in site.site_id.name

    def test_ssa_version_in_name(self, factory):
        site = factory.create_ssa_site("x", ssa_version=3)
        assert "3" in site.site_id.name

    def test_ssa_metadata(self, factory):
        site = factory.create_ssa_site("y", ssa_version=2, defining_op="add")
        assert site.metadata["var_name"] == "y"
        assert site.metadata["ssa_version"] == 2
        assert site.metadata["defining_op"] == "add"

    def test_ssa_schema(self, factory):
        site = factory.create_ssa_site("z")
        assert site.carrier_schema is not None


# ============================================================================
# 4. BRANCH_GUARD
# ============================================================================


class TestBranchGuardSite:

    def test_create_branch_guard(self, factory):
        site = factory.create_branch_guard_site("guard_0")
        assert site.kind == SiteKind.BRANCH_GUARD
        assert "guard" in site.site_id.name

    def test_true_branch(self, factory):
        site = factory.create_branch_guard_site("g1", is_true_branch=True)
        assert "T" in site.site_id.name

    def test_false_branch(self, factory):
        site = factory.create_branch_guard_site("g1", is_true_branch=False)
        assert "F" in site.site_id.name

    def test_guard_metadata(self, factory):
        site = factory.create_branch_guard_site(
            "g2", condition_text="x > 0", narrowed_vars=["x"]
        )
        assert site.metadata["condition_text"] == "x > 0"
        assert site.metadata["narrowed_vars"] == ["x"]


# ============================================================================
# 5. CALL_RESULT
# ============================================================================


class TestCallSite:

    def test_create_call_site(self, factory):
        site = factory.create_call_site("len", call_index=0)
        assert site.kind == SiteKind.CALL_RESULT
        assert "len" in site.site_id.name

    def test_call_metadata(self, factory):
        site = factory.create_call_site("foo", call_index=1, is_method=True, arg_count=3)
        assert site.metadata["callee_name"] == "foo"
        assert site.metadata["is_method"] is True
        assert site.metadata["arg_count"] == 3

    def test_async_call(self, factory):
        site = factory.create_call_site("fetch", is_async=True)
        assert site.metadata["is_async"] is True


# ============================================================================
# 6. TENSOR_SHAPE
# ============================================================================


class TestTensorShapeSite:

    def test_create_tensor_shape(self, factory):
        site = factory.create_tensor_shape_site("A")
        assert site.kind == SiteKind.TENSOR_SHAPE
        assert "shape" in site.site_id.name

    def test_tensor_shape_metadata(self, factory):
        site = factory.create_tensor_shape_site("B", ndim=3, dtype="float32")
        assert site.metadata["ndim"] == 3
        assert site.metadata["dtype"] == "float32"

    def test_framework_default(self, factory):
        site = factory.create_tensor_shape_site("C")
        assert site.metadata["framework"] == "torch"


# ============================================================================
# 7. TENSOR_ORDER
# ============================================================================


class TestTensorOrderSite:

    def test_create_tensor_order(self, factory):
        site = factory.create_tensor_order_site("X")
        assert site.kind == SiteKind.TENSOR_ORDER

    def test_order_metadata(self, factory):
        site = factory.create_tensor_order_site("Y", layout="F", contiguous=False)
        assert site.metadata["layout"] == "F"
        assert site.metadata["contiguous"] is False


# ============================================================================
# 8. TENSOR_INDEXING
# ============================================================================


class TestTensorIndexingSite:

    def test_create_tensor_indexing(self, factory):
        site = factory.create_tensor_indexing_site("T")
        assert site.kind == SiteKind.TENSOR_INDEXING

    def test_indexing_metadata(self, factory):
        site = factory.create_tensor_indexing_site(
            "T", index_expr="i, j", bounds_checked=True
        )
        assert site.metadata["index_expr"] == "i, j"
        assert site.metadata["bounds_checked"] is True


# ============================================================================
# 9. HEAP_PROTOCOL
# ============================================================================


class TestHeapSite:

    def test_create_heap_site(self, factory):
        site = factory.create_heap_site("obj")
        assert site.kind == SiteKind.HEAP_PROTOCOL

    def test_heap_metadata(self, factory):
        site = factory.create_heap_site(
            "fd", protocol="closeable", state="open", aliases=["f"]
        )
        assert site.metadata["protocol"] == "closeable"
        assert site.metadata["state"] == "open"
        assert site.metadata["aliases"] == ["f"]


# ============================================================================
# 10. ERROR
# ============================================================================


class TestErrorSite:

    def test_create_error_site(self, factory):
        site = factory.create_error_site("IndexError")
        assert site.kind == SiteKind.ERROR
        assert "IndexError" in site.site_id.name

    def test_error_metadata(self, factory):
        site = factory.create_error_site(
            "ZeroDivisionError", viability="divisor == 0", guarded=True, source_op="div"
        )
        assert site.metadata["viability"] == "divisor == 0"
        assert site.metadata["guarded"] is True
        assert site.metadata["source_op"] == "div"


# ============================================================================
# 11. LOOP_HEADER_INVARIANT
# ============================================================================


class TestLoopSite:

    def test_create_loop_site(self, factory):
        site = factory.create_loop_site("loop_0")
        assert site.kind == SiteKind.LOOP_HEADER_INVARIANT

    def test_loop_metadata(self, factory):
        site = factory.create_loop_site(
            "loop_1", loop_variable="i", iteration_bound="n", is_while=True
        )
        assert site.metadata["loop_variable"] == "i"
        assert site.metadata["iteration_bound"] == "n"
        assert site.metadata["is_while"] is True


# ============================================================================
# 12. PROOF
# ============================================================================


class TestProofSite:

    def test_create_proof_site(self, factory):
        site = factory.create_proof_site("p1")
        assert site.kind == SiteKind.PROOF

    def test_proof_metadata(self, factory):
        site = factory.create_proof_site(
            "p2", proposition="x >= 0", status="verified"
        )
        assert site.metadata["proposition"] == "x >= 0"
        assert site.metadata["status"] == "verified"


# ============================================================================
# 13. TRACE
# ============================================================================


class TestTraceSite:

    def test_create_trace_site(self, factory):
        site = factory.create_trace_site("t1")
        assert site.kind == SiteKind.TRACE

    def test_trace_metadata(self, factory):
        site = factory.create_trace_site(
            "t2", trace_point="after_loop", sample_count=100, confidence=0.95
        )
        assert site.metadata["trace_point"] == "after_loop"
        assert site.metadata["sample_count"] == 100
        assert site.metadata["confidence"] == 0.95


# ============================================================================
# 14. MODULE_SUMMARY
# ============================================================================


class TestModuleSummarySite:

    def test_create_module_summary(self, factory):
        site = factory.create_module_summary_site("my_module")
        assert site.kind == SiteKind.MODULE_SUMMARY

    def test_module_summary_metadata(self, factory):
        site = factory.create_module_summary_site(
            "utils", exports=["helper", "Config"], import_deps=["os", "sys"]
        )
        assert site.metadata["exports"] == ["helper", "Config"]
        assert site.metadata["import_deps"] == ["os", "sys"]


# ============================================================================
# Generic create_site dispatcher
# ============================================================================


class TestGenericDispatcher:

    def test_dispatch_argument(self, factory):
        site = factory.create_site(SiteKind.ARGUMENT_BOUNDARY, "x", param_index=0)
        assert site.kind == SiteKind.ARGUMENT_BOUNDARY

    def test_dispatch_ssa(self, factory):
        site = factory.create_site(SiteKind.SSA_VALUE, "y", ssa_version=1)
        assert site.kind == SiteKind.SSA_VALUE

    def test_dispatch_error(self, factory):
        site = factory.create_site(SiteKind.ERROR, "TypeError")
        assert site.kind == SiteKind.ERROR

    def test_dispatch_all_14_kinds(self, factory):
        """Verify every SiteKind can be dispatched through create_site."""
        for kind in SiteKind:
            site = factory.create_site(kind, f"test_{kind.value}")
            assert site.kind == kind


# ============================================================================
# Counter and diagnostics
# ============================================================================


class TestCounters:

    def test_creation_counts(self, factory):
        factory.create_argument_site("a")
        factory.create_argument_site("b")
        factory.create_ssa_site("x")
        counts = factory.creation_counts
        assert counts[SiteKind.ARGUMENT_BOUNDARY] == 2
        assert counts[SiteKind.SSA_VALUE] == 1

    def test_total_created(self, factory):
        factory.create_argument_site("a")
        factory.create_return_site()
        factory.create_ssa_site("x")
        assert factory.total_created == 3

    def test_reset_counters(self, factory):
        factory.create_argument_site("a")
        factory.reset_counters()
        assert factory.total_created == 0

    def test_repr(self, factory):
        assert "SiteFactory" in repr(factory)


# ============================================================================
# SiteId properties
# ============================================================================


class TestSiteIdProperties:

    def test_site_id_frozen(self, factory):
        site = factory.create_argument_site("x")
        sid = site.site_id
        with pytest.raises(AttributeError):
            sid.name = "changed"

    def test_site_id_str(self, factory):
        site = factory.create_argument_site("x")
        s = str(site.site_id)
        assert "argument_boundary" in s

    def test_site_id_equality(self, factory):
        site1 = factory.create_argument_site("x")
        # Create another factory to get the same SiteId
        factory2 = SiteFactory(file_path="test.py", default_source_line=1)
        site2 = factory2.create_argument_site("x")
        assert site1.site_id == site2.site_id

    def test_site_id_hashable(self, factory):
        site = factory.create_argument_site("x")
        d = {site.site_id: "value"}
        assert d[site.site_id] == "value"


# ============================================================================
# No file path
# ============================================================================


class TestNoFilePath:

    def test_no_source_location_when_no_file(self, bare_factory):
        site = bare_factory.create_argument_site("x")
        assert site.site_id.source_location is None

    def test_with_file_path(self, factory):
        site = factory.create_argument_site("x", source_line=5)
        assert site.site_id.source_location is not None
        assert site.site_id.source_location[0] == "test.py"
