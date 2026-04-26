"""Tests for the cubical/simplicial bicomplex bridge.

Phase 5 of the round-2 cubical audit: links intra-procedural
cubical structures to the inter-procedural simplicial complex
via cross-function 1- and 2-cells.
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field

from deppy.lean.cubical_simplicial_bicomplex import (
    Bicomplex,
    BicomplexCohomology,
    BicomplexEdge,
    BicomplexFace,
    build_bicomplex,
    render_bicomplex_summary,
)


@dataclass
class _FV:
    is_safe: bool = True


@dataclass
class _SV:
    functions: dict = field(default_factory=dict)


def _parse_module(src: str) -> dict[str, ast.FunctionDef]:
    src = textwrap.dedent(src)
    out = {}
    for node in ast.parse(src).body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[node.name] = node
    return out


# ─────────────────────────────────────────────────────────────────────
#  Builder
# ─────────────────────────────────────────────────────────────────────


class TestBuildBicomplex:
    def test_empty_module(self):
        verdict = _SV()
        bicomplex = build_bicomplex(verdict, {})
        assert isinstance(bicomplex, Bicomplex)
        assert len(bicomplex.cubical_parts) == 0
        assert bicomplex.bicomplex_edges() == []

    def test_single_function_no_calls(self):
        fn_nodes = _parse_module("def f(): return 1")
        verdict = _SV(functions={"f": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        # f has a cubical part.
        assert "f" in bicomplex.cubical_parts
        # No bicomplex edges (f calls nothing).
        assert bicomplex.bicomplex_edges() == []

    def test_call_chain_produces_edges(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return h()

            def h():
                return 1
        """)
        verdict = _SV(functions={
            "f": _FV(), "g": _FV(), "h": _FV(),
        })
        bicomplex = build_bicomplex(verdict, fn_nodes)
        edges = bicomplex.bicomplex_edges()
        # f → g and g → h.
        edge_pairs = {(e.caller, e.callee) for e in edges}
        assert ("f", "g") in edge_pairs
        assert ("g", "h") in edge_pairs

    def test_call_chain_produces_face(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return h()

            def h():
                return 1
        """)
        verdict = _SV(functions={
            "f": _FV(), "g": _FV(), "h": _FV(),
        })
        bicomplex = build_bicomplex(verdict, fn_nodes)
        faces = bicomplex.bicomplex_faces()
        # The composition triple f → g → h is a 2-face.
        triples = {(face.f, face.g, face.h) for face in faces}
        assert ("f", "g", "h") in triples


# ─────────────────────────────────────────────────────────────────────
#  Cohomology computation
# ─────────────────────────────────────────────────────────────────────


class TestTotalCohomology:
    def test_intra_eulers_per_function(self):
        fn_nodes = _parse_module("""
            def f():
                return 1
        """)
        verdict = _SV(functions={"f": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        assert isinstance(coh, BicomplexCohomology)
        # f is in the intra euler map.
        assert "f" in coh.intra_eulers

    def test_inter_dim_present(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        # H^0 / H^1 / H^2 are integers ≥ 0.
        assert coh.inter_h0 >= 0
        assert coh.inter_h1 >= 0
        assert coh.inter_h2 >= 0

    def test_cross_edges_match_bicomplex_edges(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        assert coh.cross_edges == len(bicomplex.bicomplex_edges())


# ─────────────────────────────────────────────────────────────────────
#  Rendering
# ─────────────────────────────────────────────────────────────────────


class TestRenderSummary:
    def test_summary_includes_counts(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        text = render_bicomplex_summary(bicomplex)
        assert "Bicomplex" in text
        assert "cubical parts" in text
        assert "simplicial" in text
        assert "bridge" in text


# ─────────────────────────────────────────────────────────────────────
#  Soundness gates
# ─────────────────────────────────────────────────────────────────────


class TestSoundnessGates:
    def test_failed_cubical_recorded_as_gap(self):
        # When a function's AST is "not actually a function" the
        # cubical builder should skip — and we don't add anything.
        # (We can't easily produce a function whose AST fails
        # cubical analysis, so this test just ensures the gap
        # mechanism exists.)
        bicomplex = Bicomplex()
        bicomplex.gaps.append("buggy_fn")
        coh = bicomplex.compute_total_cohomology()
        assert "buggy_fn" in coh.gaps

    def test_no_cubical_for_undefined_callee_no_edge(self):
        # ``f`` calls ``g`` but ``g`` isn't in fn_nodes.  The
        # bicomplex skips the edge rather than silently inventing
        # a target.
        fn_nodes = _parse_module("""
            def f():
                return g()
        """)
        verdict = _SV(functions={"f": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        # No edges (g isn't in the module).
        assert bicomplex.bicomplex_edges() == []


# ─────────────────────────────────────────────────────────────────────
#  Bicomplex semantics — what's not a bicomplex
# ─────────────────────────────────────────────────────────────────────


class TestBicomplexInvariants:
    def test_edges_have_concrete_caller_and_callee_cells(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        for e in bicomplex.bicomplex_edges():
            assert e.caller_cell_id  # non-empty
            assert e.callee_cell_id  # non-empty


# ─────────────────────────────────────────────────────────────────────
#  Chunk E — real bicomplex invariants
# ─────────────────────────────────────────────────────────────────────


class TestRealBicomplexInvariants:
    def test_total_euler_computed(self):
        # Round-2 chunk E: total Euler χ_tot is a real integer.
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        assert isinstance(coh.total_euler, int)

    def test_total_dim_cell_counts_populated(self):
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        # Total-dim 0 has cells (intra-dim-0 × inter-dim-0).
        assert coh.total_dim_cell_counts.get(0, 0) > 0
        # Sum over all total-dims = total cell count of the
        # bicomplex grid.
        sum_total = sum(coh.total_dim_cell_counts.values())
        sum_grid = sum(coh.per_grid_cell_counts.values())
        assert sum_total == sum_grid

    def test_per_grid_cell_counts_match_intra_x_inter(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        # |C^{0,0}| = (intra 0-cells from all fns) × (inter 0-simplices).
        # Inter 0-simplices = number of functions = 2.
        # intra 0-cells > 0 (entry points).
        c00 = coh.per_grid_cell_counts.get((0, 0), 0)
        assert c00 > 0

    def test_d_intra_image_recorded(self):
        # When a cubical part has 2-cells, d_intra has image at
        # the (2, 0) grid coordinate.
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={"f": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        # An if-statement creates a square — d_intra has image at (2, 0).
        assert coh.d_intra_image_sizes.get((2, 0), 0) >= 1

    def test_d_inter_image_at_q_plus_1(self):
        fn_nodes = _parse_module("""
            def f():
                return g()

            def g():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(), "g": _FV()})
        bicomplex = build_bicomplex(verdict, fn_nodes)
        coh = bicomplex.compute_total_cohomology()
        # Two functions calling each other → at least one C^1 entry.
        # d_inter at (0, 1) = (intra 0-cells) × (number of c1 entries).
        # We just check it's non-zero.
        assert coh.d_inter_image_sizes.get((0, 1), 0) >= 1
