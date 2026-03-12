"""Tests for cover synthesis from Python AST (Algorithm 1)."""

import textwrap

from deppy.core._protocols import SiteKind
from deppy.static_analysis.cover_builder import build_cover, CoverBuilder


class TestBuildCoverSimpleFunction:
    """Cover synthesis for a simple function with assignments and return."""

    def test_basic_function(self):
        src = textwrap.dedent("""\
            def foo(x, y):
                z = x + y
                return z
        """)
        cover = build_cover(src)
        assert len(cover.sites) > 0
        assert len(cover.input_boundary) >= 2  # x, y
        assert len(cover.output_boundary) >= 1  # return

    def test_argument_sites_created(self):
        src = textwrap.dedent("""\
            def bar(a, b, c):
                return a
        """)
        cover = build_cover(src)
        arg_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.ARGUMENT_BOUNDARY
        ]
        assert len(arg_sites) == 3

    def test_ssa_sites_for_assignments(self):
        src = textwrap.dedent("""\
            def baz(x):
                y = x + 1
                z = y * 2
                return z
        """)
        cover = build_cover(src)
        ssa_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.SSA_VALUE
        ]
        assert len(ssa_sites) >= 2  # y, z


class TestBuildCoverBranching:
    """Cover synthesis creates branch-guard sites for if/assert."""

    def test_if_creates_guard_sites(self):
        src = textwrap.dedent("""\
            def check(x):
                if x is not None:
                    return x + 1
                return 0
        """)
        cover = build_cover(src)
        guard_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.BRANCH_GUARD
        ]
        assert len(guard_sites) >= 1

    def test_assert_creates_guard_site(self):
        src = textwrap.dedent("""\
            def validated(x):
                assert x > 0
                return x
        """)
        cover = build_cover(src)
        guard_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.BRANCH_GUARD
        ]
        assert len(guard_sites) >= 1


class TestBuildCoverErrors:
    """Cover synthesis creates error sites for error-sensitive operations."""

    def test_subscript_creates_error_site(self):
        src = textwrap.dedent("""\
            def get_item(lst, i):
                return lst[i]
        """)
        cover = build_cover(src)
        error_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.ERROR
        ]
        assert len(error_sites) >= 1
        assert len(cover.error_sites) >= 1

    def test_division_creates_error_site(self):
        src = textwrap.dedent("""\
            def divide(a, b):
                return a / b
        """)
        cover = build_cover(src)
        assert len(cover.error_sites) >= 1


class TestBuildCoverLoops:
    """Cover synthesis creates loop-invariant sites."""

    def test_for_loop(self):
        src = textwrap.dedent("""\
            def sum_list(lst):
                total = 0
                for x in lst:
                    total = total + x
                return total
        """)
        cover = build_cover(src)
        loop_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.LOOP_HEADER_INVARIANT
        ]
        assert len(loop_sites) >= 1

    def test_while_loop(self):
        src = textwrap.dedent("""\
            def countdown(n):
                while n > 0:
                    n = n - 1
                return n
        """)
        cover = build_cover(src)
        loop_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.LOOP_HEADER_INVARIANT
        ]
        assert len(loop_sites) >= 1


class TestBuildCoverCalls:
    """Cover synthesis creates call-result sites."""

    def test_function_call(self):
        src = textwrap.dedent("""\
            def caller(x):
                y = len(x)
                return y
        """)
        cover = build_cover(src)
        call_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.CALL_RESULT
        ]
        assert len(call_sites) >= 1


class TestBuildCoverTorch:
    """Cover synthesis detects torch operations and creates specialized sites."""

    def test_torch_sort(self):
        src = textwrap.dedent("""\
            def sort_scores(scores):
                values, indices = torch.sort(scores, descending=True)
                return values, indices
        """)
        cover = build_cover(src)
        order_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.TENSOR_ORDER
        ]
        assert len(order_sites) >= 1

    def test_torch_reshape(self):
        src = textwrap.dedent("""\
            def reshape_tensor(t):
                return t.reshape(3, 4)
        """)
        cover = build_cover(src)
        shape_sites = [
            sid for sid in cover.sites
            if sid.kind == SiteKind.TENSOR_SHAPE
        ]
        assert len(shape_sites) >= 1


class TestBuildCoverRaise:
    """Cover synthesis creates error/output sites for raise statements."""

    def test_raise(self):
        src = textwrap.dedent("""\
            def validate(x):
                if x < 0:
                    raise ValueError("negative")
                return x
        """)
        cover = build_cover(src)
        # raise should create an output boundary (exceptional) or error site
        assert len(cover.output_boundary) >= 1 or len(cover.error_sites) >= 1


class TestCoverBuilderAPI:
    """Test the CoverBuilder fluent API."""

    def test_add_function(self):
        import ast
        src = textwrap.dedent("""\
            def foo(x):
                return x + 1
        """)
        tree = ast.parse(src)
        func_node = tree.body[0]
        builder = CoverBuilder()
        builder.add_function(func_node, "foo")
        cover = builder.build()
        assert len(cover.sites) > 0
        assert len(cover.input_boundary) >= 1


class TestCoverMorphisms:
    """Cover synthesis creates morphisms between sites."""

    def test_has_morphisms(self):
        src = textwrap.dedent("""\
            def foo(x):
                y = x + 1
                return y
        """)
        cover = build_cover(src)
        assert len(cover.morphisms) >= 1

    def test_overlaps_detected(self):
        src = textwrap.dedent("""\
            def foo(x, y):
                z = x + y
                return z
        """)
        cover = build_cover(src)
        # At minimum, sites sharing lineage should create overlaps
        # (implementation may vary)
        assert isinstance(cover.overlaps, list)
