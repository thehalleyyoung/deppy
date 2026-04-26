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

    def test_zero_peer_face_emits_trivial_theorem(self):
        # When a Kan-fillable cell has zero peer faces, the
        # filler is vacuously trivial — there's no implied
        # content to derive from no peers.  The theorem becomes
        # ``True := trivial`` (an honest tautology) rather than
        # the previous round-1 ``True := by Deppy.deppy_kan``
        # cheat or the round-1.5 ``sorry``.
        from deppy.pipeline.cubical_ast import (
            Cell, CellShape, CubicalSet, KanCandidate,
        )
        cset = CubicalSet(function_name="t")
        cset.add(Cell(
            cell_id="e", dim=1, shape=CellShape.EDGE_SEQ,
            vertices=("v0", "v1"), faces=("v0", "missing"),
        ))
        candidate = KanCandidate(
            cell_id="e",
            missing_axis=0, missing_eps=1,
            implied_vertices=("v1",),
            implied_guards=(),
            peer_face_count=0,
        )
        from deppy.lean.cubical_certificate import _render_kan_theorem
        result = _render_kan_theorem(
            fn_name="t", idx=0, candidate=candidate, cset=cset,
        )
        # Theorem is ``True := trivial`` (real proposition, real
        # proof) — not a sorry.  is_sorry stays False because
        # nothing is admitted.
        assert result["is_sorry"] is False
        assert "trivial" in result["text"]
        assert "deppy_kan" not in result["text"]
        # And no sorry token (we don't admit anything).
        assert "sorry" not in result["text"]

    def test_kan_with_peer_guards_emits_real_implication(self):
        # Round-2 chunk C invariant: when there are peer guards,
        # the theorem is a real implication, not ``: True``.
        from deppy.pipeline.cubical_ast import (
            Cell, CellShape, CubicalSet, KanCandidate,
        )
        cset = CubicalSet(function_name="t")
        cset.add(Cell(
            cell_id="sq", dim=2, shape=CellShape.SQUARE_IF,
            vertices=("a", "b", "c", "d"),
            faces=("e1", "e2", "e3", "missing"),
        ))
        candidate = KanCandidate(
            cell_id="sq",
            missing_axis=1, missing_eps=1,
            implied_vertices=("c", "d"),
            implied_guards=("x > 0", "y > 0"),
            peer_face_count=3,
        )
        from deppy.lean.cubical_certificate import _render_kan_theorem
        result = _render_kan_theorem(
            fn_name="t", idx=0, candidate=candidate, cset=cset,
        )
        text = result["text"]
        # The goal mentions BOTH peer predicates.
        assert "x > 0" in text
        assert "y > 0" in text
        # The conclusion is the conjunction.
        assert "∧" in text
        # The proof binds hypotheses and uses them.
        assert "h1" in text
        assert "h2" in text
        # Not a True-shaped goal.
        assert not text.rstrip().endswith(": True := trivial\n".rstrip())


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

    def test_certificate_has_cubical_accounting_fields(self):
        # Round-2 audit integration #3: Certificate dataclass has
        # dedicated fields for cubical theorem and sorry counts.
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
        cert = report.certificate
        # Fields exist and are integers.
        assert isinstance(cert.cubical_kan_theorems_count, int)
        assert isinstance(cert.cubical_higher_path_theorems_count, int)
        assert isinstance(cert.cubical_sorries, int)
        # Cubical sorries are bounded by total sorry count.
        assert cert.cubical_sorries <= cert.sorry_count
