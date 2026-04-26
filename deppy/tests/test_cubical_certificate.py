"""Tests for the Lean certificate's cubical section.

Phase 4 of the round-2 cubical audit: the certificate now carries
a cubical analysis block + Kan-fillability theorems.
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field

from deppy.lean.cubical_certificate import (
    CubicalCertificateSection,
    CubicalFunctionSummary,
    render_cubical_section,
)


# Lightweight verdict stand-ins.
@dataclass
class _FV:
    is_safe: bool = True
    cubical_obligations_verified: int = 0


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
#  Summary block
# ─────────────────────────────────────────────────────────────────────


class TestSummaryBlock:
    def test_summary_present_on_simple_function(self):
        fn_nodes = _parse_module("def f(): return 1")
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(verdict, fn_nodes)
        assert isinstance(section, CubicalCertificateSection)
        # The summary is a Lean comment block.
        assert section.summary_block.startswith("/-!")
        assert section.summary_block.rstrip().endswith("-/")
        # Includes the cell-counts line.
        assert "cells:" in section.summary_block

    def test_summary_includes_module_totals(self):
        fn_nodes = _parse_module("""
            def f():
                return 1

            def g(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={
            "f": _FV(),
            "g": _FV(),
        })
        section = render_cubical_section(verdict, fn_nodes)
        assert "Module totals" in section.summary_block

    def test_per_function_summary_populated(self):
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(verdict, fn_nodes)
        fs = section.per_function_summaries.get("f")
        assert isinstance(fs, CubicalFunctionSummary)
        # An if-statement produces at least one 2-cell.
        assert fs.cell_counts_by_dim.get(2, 0) >= 1


# ─────────────────────────────────────────────────────────────────────
#  Kan theorems
# ─────────────────────────────────────────────────────────────────────


class TestKanTheorems:
    def test_kan_theorems_emitted_when_present(self):
        # We construct a function whose AST has Kan-fillable cells.
        # If the natural builder doesn't produce any, the test
        # is trivially satisfied — but the rendering should at
        # least not crash.
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(
            verdict, fn_nodes, include_kan_theorems=True,
        )
        # Theorems list is well-formed.
        assert isinstance(section.theorems, list)
        for t in section.theorems:
            assert isinstance(t, str)

    def test_no_deppy_safe_in_theorems(self):
        # Audit invariant: no theorem in the cubical section uses
        # the silent ``Deppy.deppy_safe`` fallback.  We use
        # ``Deppy.deppy_kan`` for Kan fillers and ``Deppy.deppy_cech``
        # for higher paths — both real tactics in DeppyBase.lean.
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(
            verdict, fn_nodes,
            include_kan_theorems=True,
            include_higher_paths=True,
        )
        for t in section.theorems:
            # Strip comments, then check.
            for line in t.splitlines():
                stripped = line.lstrip()
                if stripped.startswith("--"):
                    continue
                assert "Deppy.deppy_safe" not in line, (
                    f"deppy_safe leaked into cubical theorem: {line!r}"
                )

    def test_zero_peer_face_emits_honest_sorry(self):
        # When a Kan-fillable cell has zero peer faces (theoretical
        # corner case), the theorem must emit ``sorry``, not a
        # silent fallback tactic.
        from deppy.pipeline.cubical_ast import (
            Cell, CellShape, CubicalSet, KanCandidate,
        )
        cset = CubicalSet(function_name="t")
        # Add the cell that the candidate references, so the
        # renderer doesn't take the "missing cell" early-return.
        cset.add(Cell(
            cell_id="e", dim=1, shape=CellShape.EDGE_SEQ,
            vertices=("v0", "v1"), faces=("v0", "missing"),
        ))
        candidate = KanCandidate(
            cell_id="e",
            missing_axis=0,
            missing_eps=1,
            implied_vertices=("v1",),
            implied_guards=(),
            peer_face_count=0,
        )
        from deppy.lean.cubical_certificate import _render_kan_theorem
        result = _render_kan_theorem(
            fn_name="t", idx=0, candidate=candidate, cset=cset,
        )
        # When peer_face_count == 0, the theorem is a sorry.
        assert result["is_sorry"] is True
        assert "sorry" in result["text"]
        assert "deppy_kan" not in result["text"]


# ─────────────────────────────────────────────────────────────────────
#  Higher path theorems (when enabled)
# ─────────────────────────────────────────────────────────────────────


class TestHigherPathTheorems:
    def test_higher_path_off_by_default(self):
        fn_nodes = _parse_module("""
            def f():
                return 1
        """)
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(
            verdict, fn_nodes,
        )
        # By default higher paths are OFF.
        assert section.higher_path_theorems_count == 0

    def test_higher_path_enabled_emits(self):
        fn_nodes = _parse_module("""
            def f(x):
                if x > 0:
                    return 1
                return 0
        """)
        verdict = _SV(functions={"f": _FV()})
        section = render_cubical_section(
            verdict, fn_nodes,
            include_kan_theorems=False,
            include_higher_paths=True,
        )
        assert section.higher_path_theorems_count >= 1


# ─────────────────────────────────────────────────────────────────────
#  Integration with certificate generator
# ─────────────────────────────────────────────────────────────────────


class TestCertificateIntegration:
    def test_write_certificate_includes_cubical_section(self):
        # The cubical section is emitted by ``write_certificate``,
        # which is the full-cohomology certificate path (separate
        # from ``verify_module_safety(emit_lean=True)`` which uses
        # the smaller safety_lean export).
        import tempfile
        from pathlib import Path
        from deppy.lean.certificate import write_certificate
        src = textwrap.dedent("""
            def f(x: int) -> int:
                if x > 0:
                    return 1
                return 0
        """)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "cert.lean"
            report = write_certificate(src, out, run_lean=False)
            text = out.read_text()
        # The certificate's cubical block is present.
        assert "Cubical control-flow analysis" in text
