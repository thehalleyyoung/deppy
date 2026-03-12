"""Tests for observation site constructors — all 14 site families."""

from deppy.core._protocols import SiteKind
from deppy.static_analysis.observation_sites import (
    ArgumentBoundarySiteData,
    BranchGuardSiteData,
    CallResultSiteData,
    ErrorKind,
    ErrorSiteData,
    HeapProtocolSiteData,
    LoopInvariantSiteData,
    ModuleSummarySiteData,
    ProofSiteData,
    ReturnBoundarySiteData,
    SSAValueSiteData,
    SourceSpan,
    TensorIndexingSiteData,
    TensorOrderSiteData,
    TensorShapeSiteData,
    TraceSiteData,
    make_argument_boundary_site,
    make_branch_guard_site,
    make_call_result_site,
    make_error_site,
    make_heap_protocol_site,
    make_loop_invariant_site,
    make_module_summary_site,
    make_proof_site,
    make_return_boundary_site,
    make_ssa_value_site,
    make_tensor_indexing_site,
    make_tensor_order_site,
    make_tensor_shape_site,
    make_trace_site,
)


SPAN = SourceSpan(file="test.py", start_line=1, start_col=0)


class TestSourceSpan:
    def test_from_tuple(self):
        span = SourceSpan(file="f.py", start_line=10, start_col=4)
        assert span.as_tuple() == ("f.py", 10, 4)

    def test_defaults(self):
        span = SourceSpan(file="f.py", start_line=1, start_col=0)
        assert span.end_line == -1
        assert span.end_col == -1


class TestArgumentBoundarySite:
    def test_basic(self):
        site = make_argument_boundary_site("foo", "x", 0, SPAN)
        assert site.site_id.kind == SiteKind.ARGUMENT_BOUNDARY
        assert "foo.x" in site.site_id.name
        data = site.metadata["data"]
        assert isinstance(data, ArgumentBoundarySiteData)
        assert data.param_name == "x"
        assert data.param_index == 0

    def test_self_param(self):
        site = make_argument_boundary_site("MyClass.method", "self", 0, SPAN, is_self=True)
        data = site.metadata["data"]
        assert data.is_self is True

    def test_ghost_param(self):
        site = make_argument_boundary_site("foo", "ghost_x", 1, SPAN, is_ghost=True)
        data = site.metadata["data"]
        assert data.is_ghost is True


class TestReturnBoundarySite:
    def test_normal_return(self):
        site = make_return_boundary_site("foo", SPAN)
        assert site.site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        assert "return_0" in site.site_id.name

    def test_exceptional_return(self):
        site = make_return_boundary_site("foo", SPAN, is_exceptional=True, exception_type="ValueError")
        assert "exc_ValueError" in site.site_id.name
        data = site.metadata["data"]
        assert data.is_exceptional is True

    def test_mutation_return(self):
        site = make_return_boundary_site("foo", SPAN, is_mutation=True, mutated_name="self.data")
        assert "mutate_self.data" in site.site_id.name


class TestSSAValueSite:
    def test_basic(self):
        site = make_ssa_value_site("foo", "x", 3, SPAN)
        assert site.site_id.kind == SiteKind.SSA_VALUE
        assert "x_3" in site.site_id.name
        data = site.metadata["data"]
        assert data.variable_name == "x"
        assert data.version == 3

    def test_phi_node(self):
        site = make_ssa_value_site(
            "foo", "x", 4, SPAN,
            is_phi=True,
            predecessor_versions=[("x", 2), ("x", 3)],
        )
        data = site.metadata["data"]
        assert data.is_phi is True
        assert len(data.predecessor_versions) == 2

    def test_lineage_parent(self):
        site = make_ssa_value_site("foo", "y", 1, SPAN, lineage_parent="foo.x_0")
        data = site.metadata["data"]
        assert data.lineage_parent == "foo.x_0"


class TestBranchGuardSite:
    def test_true_branch(self):
        site = make_branch_guard_site("foo", "if_1", SPAN, polarity=True)
        assert site.site_id.kind == SiteKind.BRANCH_GUARD
        assert "_T" in site.site_id.name

    def test_false_branch(self):
        site = make_branch_guard_site("foo", "if_1", SPAN, polarity=False)
        assert "_F" in site.site_id.name

    def test_assertion(self):
        site = make_branch_guard_site("foo", "assert_1", SPAN, is_assertion=True)
        data = site.metadata["data"]
        assert data.is_assertion is True


class TestCallResultSite:
    def test_basic(self):
        site = make_call_result_site("foo", "c1", "bar", SPAN, arguments=("x", "y"))
        assert site.site_id.kind == SiteKind.CALL_RESULT
        data = site.metadata["data"]
        assert data.callee_name == "bar"
        assert data.arguments == ("x", "y")

    def test_method_call(self):
        site = make_call_result_site(
            "foo", "c2", "append", SPAN,
            is_method_call=True, receiver_variable="lst",
        )
        data = site.metadata["data"]
        assert data.is_method_call is True
        assert data.receiver_variable == "lst"


class TestTensorShapeSite:
    def test_reshape(self):
        site = make_tensor_shape_site("foo", "s1", "reshape", SPAN, target_shape=(3, 4))
        assert site.site_id.kind == SiteKind.TENSOR_SHAPE
        data = site.metadata["data"]
        assert data.operation == "reshape"
        assert data.target_shape == (3, 4)

    def test_reduction(self):
        site = make_tensor_shape_site("foo", "s2", "sum", SPAN, is_reduction=True, reduced_dim=0)
        data = site.metadata["data"]
        assert data.is_reduction is True
        assert data.reduced_dim == 0


class TestTensorOrderSite:
    def test_sort(self):
        site = make_tensor_order_site("foo", "o1", "sort", SPAN, descending=True)
        assert site.site_id.kind == SiteKind.TENSOR_ORDER
        data = site.metadata["data"]
        assert data.operation == "sort"
        assert data.descending is True


class TestTensorIndexingSite:
    def test_gather(self):
        site = make_tensor_indexing_site("foo", "i1", "gather", SPAN, dim=1)
        assert site.site_id.kind == SiteKind.TENSOR_INDEXING
        data = site.metadata["data"]
        assert data.operation == "gather"
        assert data.dim == 1


class TestHeapProtocolSite:
    def test_field_read(self):
        site = make_heap_protocol_site(
            "foo", "h1", SPAN,
            class_name="MyClass", field_name="data", is_read=True,
        )
        assert site.site_id.kind == SiteKind.HEAP_PROTOCOL
        data = site.metadata["data"]
        assert data.class_name == "MyClass"
        assert data.is_read is True

    def test_protocol_check(self):
        site = make_heap_protocol_site(
            "foo", "h2", SPAN, protocol_name="Iterable",
        )
        data = site.metadata["data"]
        assert data.protocol_name == "Iterable"


class TestProofSite:
    def test_theorem(self):
        site = make_proof_site("foo", "p1", SPAN, theorem_name="sorted_implies_monotone")
        assert site.site_id.kind == SiteKind.PROOF
        data = site.metadata["data"]
        assert data.theorem_name == "sorted_implies_monotone"

    def test_transport(self):
        site = make_proof_site(
            "foo", "p2", SPAN,
            is_transport=True,
            transport_source="x.sorted",
            transport_target="y.sorted",
        )
        data = site.metadata["data"]
        assert data.is_transport is True


class TestTraceSite:
    def test_basic(self):
        site = make_trace_site("foo", "t1", "trace-001", SPAN, observed_type="int")
        assert site.site_id.kind == SiteKind.TRACE
        data = site.metadata["data"]
        assert data.trace_id == "trace-001"
        assert data.observed_type == "int"

    def test_shape_observation(self):
        site = make_trace_site("foo", "t2", "trace-002", SPAN, observed_shape=(3, 4, 5))
        data = site.metadata["data"]
        assert data.observed_shape == (3, 4, 5)


class TestErrorSite:
    def test_index_error(self):
        site = make_error_site(
            "foo", "e1", ErrorKind.INDEX_ERROR, SPAN,
            operand_names=("lst", "i"),
            viability_description="0 <= i < len(lst)",
        )
        assert site.site_id.kind == SiteKind.ERROR
        data = site.metadata["data"]
        assert data.error_kind == ErrorKind.INDEX_ERROR
        assert data.operand_names == ("lst", "i")

    def test_all_error_kinds_exist(self):
        """All 24 error kinds from the monograph's runtime error catalogue."""
        assert len(ErrorKind) >= 24


class TestLoopInvariantSite:
    def test_for_loop(self):
        site = make_loop_invariant_site("foo", "l1", SPAN, is_for_loop=True, loop_variable="i")
        assert site.site_id.kind == SiteKind.LOOP_HEADER_INVARIANT
        data = site.metadata["data"]
        assert data.is_for_loop is True
        assert data.loop_variable == "i"

    def test_decreases(self):
        site = make_loop_invariant_site("foo", "l2", SPAN, is_while_loop=True, decreases_expression="n")
        data = site.metadata["data"]
        assert data.decreases_expression == "n"


class TestModuleSummarySite:
    def test_basic(self):
        site = make_module_summary_site(
            "my_module", SPAN,
            exported_functions=("func_a", "func_b"),
            exported_classes=("ClassA",),
        )
        assert site.site_id.kind == SiteKind.MODULE_SUMMARY
        data = site.metadata["data"]
        assert data.module_name == "my_module"
        assert "func_a" in data.exported_functions


class TestSiteFrozenness:
    """All site payloads should be frozen dataclasses."""

    def test_argument_data_is_frozen(self):
        data = ArgumentBoundarySiteData(param_name="x", param_index=0)
        try:
            data.param_name = "y"  # type: ignore
            assert False, "Should be frozen"
        except AttributeError:
            pass

    def test_error_data_is_frozen(self):
        data = ErrorSiteData(error_kind=ErrorKind.INDEX_ERROR)
        try:
            data.error_kind = ErrorKind.KEY_ERROR  # type: ignore
            assert False, "Should be frozen"
        except AttributeError:
            pass


class TestSiteIdUniqueness:
    """Different constructors produce distinct SiteIds."""

    def test_different_params_different_ids(self):
        s1 = make_argument_boundary_site("foo", "x", 0, SPAN)
        s2 = make_argument_boundary_site("foo", "y", 1, SPAN)
        assert s1.site_id != s2.site_id

    def test_different_versions_different_ids(self):
        s1 = make_ssa_value_site("foo", "x", 0, SPAN)
        s2 = make_ssa_value_site("foo", "x", 1, SPAN)
        assert s1.site_id != s2.site_id

    def test_all_14_kinds(self):
        """Every SiteKind is covered by a constructor."""
        sites = [
            make_argument_boundary_site("f", "x", 0, SPAN),
            make_return_boundary_site("f", SPAN),
            make_ssa_value_site("f", "x", 0, SPAN),
            make_branch_guard_site("f", "g1", SPAN),
            make_call_result_site("f", "c1", "bar", SPAN),
            make_tensor_shape_site("f", "s1", "reshape", SPAN),
            make_tensor_order_site("f", "o1", "sort", SPAN),
            make_tensor_indexing_site("f", "i1", "gather", SPAN),
            make_heap_protocol_site("f", "h1", SPAN),
            make_proof_site("f", "p1", SPAN),
            make_trace_site("f", "t1", "tr-001", SPAN),
            make_error_site("f", "e1", ErrorKind.INDEX_ERROR, SPAN),
            make_loop_invariant_site("f", "l1", SPAN),
            make_module_summary_site("mod", SPAN),
        ]
        kinds = {s.site_id.kind for s in sites}
        assert kinds == set(SiteKind)
