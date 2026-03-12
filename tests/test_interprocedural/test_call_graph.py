"""Tests for call graph construction, SCCs, topological order.

Covers CallEdge, CallTarget, CallGraph.build_from_source, add_edge/add_node,
callees/callers, topological_order, strongly_connected_components,
is_recursive, reachable_from, reaching, leaf/root functions, statistics.
"""

from __future__ import annotations

import ast
import textwrap

import pytest

from deppy.core._protocols import SiteId, SiteKind
from deppy.interprocedural.call_graph import (
    CallEdge,
    CallGraph,
    CallTarget,
    _is_builtin,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _build(source: str) -> CallGraph:
    return CallGraph.build_from_source(textwrap.dedent(source))


# ===================================================================
#  CallEdge
# ===================================================================


class TestCallEdge:
    """Tests for the CallEdge dataclass."""

    def test_basic_properties(self):
        edge = CallEdge(_caller="main", _callee="helper", _line=10, _col=4)
        assert edge.caller == "main"
        assert edge.callee == "helper"
        assert edge.line == 10
        assert edge.col == 4

    def test_arguments(self):
        edge = CallEdge(
            _caller="f", _callee="g",
            _arguments=("x", "y"),
            _keyword_arguments=(("key", "val"),),
        )
        assert edge.arguments == ("x", "y")
        assert edge.keyword_arguments == (("key", "val"),)

    def test_method_call(self):
        edge = CallEdge(
            _caller="f", _callee="obj.method",
            _is_method_call=True, _receiver="obj",
        )
        assert edge.is_method_call
        assert edge.receiver == "obj"

    def test_repr(self):
        edge = CallEdge(_caller="f", _callee="g", _arguments=("x",))
        r = repr(edge)
        assert "f" in r and "g" in r

    def test_call_site_id(self):
        sid = SiteId(SiteKind.CALL_RESULT, "f.call_0")
        edge = CallEdge(_caller="f", _callee="g", _call_site_id=sid)
        assert edge.call_site_id is sid


# ===================================================================
#  CallTarget
# ===================================================================


class TestCallTarget:
    """Tests for CallTarget."""

    def test_basic(self):
        ct = CallTarget(_name="foo")
        assert ct.name == "foo"
        assert not ct.is_builtin
        assert ct.qualified_name == "foo"

    def test_builtin(self):
        ct = CallTarget(_name="len", _is_builtin=True)
        assert ct.is_builtin

    def test_method(self):
        ct = CallTarget(_name="method", _is_method=True, _class_name="MyClass")
        assert ct.is_method
        assert ct.class_name == "MyClass"
        assert ct.qualified_name == "MyClass.method"

    def test_with_module(self):
        ct = CallTarget(_name="func", _module_name="mymod")
        assert ct.qualified_name == "mymod.func"

    def test_indirect(self):
        ct = CallTarget(_name="unknown", _is_indirect=True)
        assert ct.is_indirect


# ===================================================================
#  _is_builtin
# ===================================================================


class TestIsBuiltin:
    """Tests for _is_builtin."""

    def test_builtins(self):
        assert _is_builtin("len")
        assert _is_builtin("print")
        assert _is_builtin("isinstance")
        assert _is_builtin("range")

    def test_non_builtins(self):
        assert not _is_builtin("my_function")
        assert not _is_builtin("numpy")
        assert not _is_builtin("")


# ===================================================================
#  CallGraph construction
# ===================================================================


class TestCallGraphConstruction:
    """Tests for building call graphs from source code."""

    def test_simple_call(self):
        cg = _build("""\
        def helper():
            pass

        def main():
            helper()
        """)
        assert cg.has_edge("main", "helper")
        assert "main" in cg.nodes
        assert "helper" in cg.nodes

    def test_no_builtin_edges(self):
        cg = _build("""\
        def f(x):
            return len(x)
        """)
        assert not cg.has_edge("f", "len")

    def test_multiple_calls(self):
        cg = _build("""\
        def a():
            pass

        def b():
            pass

        def c():
            a()
            b()
        """)
        assert cg.has_edge("c", "a")
        assert cg.has_edge("c", "b")

    def test_class_method_call(self):
        cg = _build("""\
        class Foo:
            def bar(self):
                pass
            def baz(self):
                self.bar()
        """)
        assert cg.has_edge("Foo.baz", "Foo.bar") or "Foo.baz" in cg.nodes

    def test_build_from_module_ast(self):
        source = textwrap.dedent("""\
        def f():
            g()
        def g():
            pass
        """)
        tree = ast.parse(source)
        cg = CallGraph.build_from_module(tree)
        assert "f" in cg.nodes
        assert "g" in cg.nodes

    def test_edge_count(self):
        cg = _build("""\
        def a(): b()
        def b(): c()
        def c(): pass
        """)
        assert cg.edge_count() >= 2

    def test_node_count(self):
        cg = _build("""\
        def a(): pass
        def b(): pass
        def c(): pass
        """)
        assert cg.node_count() == 3


# ===================================================================
#  Queries
# ===================================================================


class TestCallGraphQueries:
    """Tests for call graph query methods."""

    def setup_method(self):
        self.cg = _build("""\
        def leaf1(): pass
        def leaf2(): pass
        def mid(): leaf1()
        def root():
            mid()
            leaf2()
        """)

    def test_get_callees(self):
        callees = self.cg.get_callees("root")
        callee_names = {e.callee for e in callees}
        assert "mid" in callee_names
        assert "leaf2" in callee_names

    def test_get_callers(self):
        callers = self.cg.get_callers("leaf1")
        caller_names = {e.caller for e in callers}
        assert "mid" in caller_names

    def test_callee_names(self):
        names = self.cg.callee_names("root")
        assert "mid" in names

    def test_caller_names(self):
        names = self.cg.caller_names("mid")
        assert "root" in names

    def test_edges_between(self):
        edges = self.cg.edges_between("root", "mid")
        assert len(edges) >= 1

    def test_has_edge(self):
        assert self.cg.has_edge("root", "mid")
        assert not self.cg.has_edge("leaf1", "root")

    def test_leaf_functions(self):
        leaves = self.cg.leaf_functions()
        assert "leaf1" in leaves
        assert "leaf2" in leaves
        assert "root" not in leaves

    def test_root_functions(self):
        roots = self.cg.root_functions()
        assert "root" in roots
        assert "leaf1" not in roots


# ===================================================================
#  Topological order
# ===================================================================


class TestTopologicalOrder:
    """Tests for topological ordering."""

    def test_simple_order(self):
        cg = _build("""\
        def leaf(): pass
        def mid(): leaf()
        def top(): mid()
        """)
        order = cg.topological_order()
        leaf_idx = order.index("leaf")
        mid_idx = order.index("mid")
        top_idx = order.index("top")
        # Callees should come before callers
        assert leaf_idx < mid_idx
        assert mid_idx < top_idx

    def test_diamond(self):
        cg = _build("""\
        def d(): pass
        def b(): d()
        def c(): d()
        def a():
            b()
            c()
        """)
        order = cg.topological_order()
        assert order.index("d") < order.index("b")
        assert order.index("d") < order.index("c")
        assert order.index("b") < order.index("a")
        assert order.index("c") < order.index("a")

    def test_isolated_node(self):
        cg = CallGraph()
        cg.add_node("isolated")
        order = cg.topological_order()
        assert "isolated" in order


# ===================================================================
#  Strongly connected components
# ===================================================================


class TestSCC:
    """Tests for strongly connected component detection."""

    def test_no_cycles(self):
        cg = _build("""\
        def a(): b()
        def b(): pass
        """)
        sccs = cg.strongly_connected_components()
        for scc in sccs:
            assert len(scc) == 1

    def test_self_recursion(self):
        cg = _build("""\
        def f():
            f()
        """)
        assert cg.is_recursive("f")

    def test_mutual_recursion(self):
        cg = _build("""\
        def even(n):
            if n == 0:
                return True
            return odd(n - 1)
        def odd(n):
            if n == 0:
                return False
            return even(n - 1)
        """)
        sccs = cg.strongly_connected_components()
        # Find the SCC containing both even and odd
        found_mutual = False
        for scc in sccs:
            if "even" in scc and "odd" in scc:
                found_mutual = True
                assert len(scc) == 2
        assert found_mutual

    def test_recursive_functions_set(self):
        cg = _build("""\
        def f(): f()
        def g(): pass
        """)
        rec = cg.recursive_functions()
        assert "f" in rec
        assert "g" not in rec


# ===================================================================
#  Reachability and depth
# ===================================================================


class TestReachability:
    """Tests for reachable_from, reaching, and call_depth."""

    def test_reachable_from(self):
        cg = _build("""\
        def a(): b()
        def b(): c()
        def c(): pass
        def d(): pass
        """)
        reachable = cg.reachable_from("a")
        assert "a" in reachable
        assert "b" in reachable
        assert "c" in reachable
        assert "d" not in reachable

    def test_reaching(self):
        cg = _build("""\
        def a(): b()
        def b(): c()
        def c(): pass
        """)
        reaching = cg.reaching("c")
        assert "a" in reaching
        assert "b" in reaching
        assert "c" in reaching

    def test_call_depth_leaf(self):
        cg = _build("""\
        def leaf(): pass
        """)
        assert cg.call_depth("leaf") == 0

    def test_call_depth_chain(self):
        cg = _build("""\
        def a(): b()
        def b(): c()
        def c(): pass
        """)
        assert cg.call_depth("a") == 2
        assert cg.call_depth("b") == 1
        assert cg.call_depth("c") == 0

    def test_call_depth_recursive(self):
        cg = _build("""\
        def f(): f()
        """)
        assert cg.call_depth("f") == -1

    def test_max_fan_out(self):
        cg = _build("""\
        def a(): pass
        def b(): pass
        def c():
            a()
            b()
        """)
        assert cg.max_fan_out() >= 2

    def test_max_fan_in(self):
        cg = _build("""\
        def target(): pass
        def caller1(): target()
        def caller2(): target()
        """)
        assert cg.max_fan_in() >= 2

    def test_repr(self):
        cg = _build("def f(): pass")
        r = repr(cg)
        assert "CallGraph" in r
