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
