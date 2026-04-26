"""Tests for the cubical + cohomological extensions (Phase C1–C4).

The deppy kernel now carries explicit higher-cubical proof terms
(``Cocycle``, ``CohomologyClass``, ``KanFill``, ``HigherPath``);
the certificate generator emits a full cochain complex with
explicit cocycles at each level and reports the cohomology
classes ``H^0``, ``H^1``, ``H^2``.  ``DeppyBase.lean`` ships the
matching meta-theory + tactic library.
"""
from __future__ import annotations

import shutil
import textwrap
from pathlib import Path

import pytest

from deppy import (
    Cocycle, CohomologyClass, KanFill, HigherPath,
    Refl, ProofKernel, Z3Proof, Structural, write_certificate,
)
from deppy.core.kernel import (
    Judgment, JudgmentKind, Context, Var,
)
from deppy.core.types import PyObjType


_HAS_LEAN = shutil.which("lean") is not None
needs_lean = pytest.mark.skipif(
    not _HAS_LEAN, reason="lean toolchain not installed",
)


def _fresh_goal():
    ctx = Context()
    return ctx, Judgment(
        kind=JudgmentKind.EQUAL, context=ctx,
        left=Var("x"), right=Var("x"), type_=PyObjType(),
    )


# ─────────────────────────────────────────────────────────────────────
# C1 — DeppyBase.lean library
# ─────────────────────────────────────────────────────────────────────

class TestDeppyBaseLibrary:
    def test_library_file_size(self):
        """Phase C1: DeppyBase grew from a stub to a comprehensive
        cubical library."""
        base = Path(__file__).parent.parent / "lean" / "DeppyBase.lean"
        text = base.read_text()
        # Sanity: at least 200 lines (was ~99).
        assert len(text.split("\n")) > 200, len(text.split("\n"))

    def test_library_declares_cubical_primitives(self):
        base = Path(__file__).parent.parent / "lean" / "DeppyBase.lean"
        text = base.read_text()
        for name in (
            "Path",
            "transportEq",
            "kanFill",
            "Equiv",
            "glueValue",
            "Trunc",
            "Interval",
        ):
            assert name in text, f"missing primitive {name!r}"

    def test_library_declares_cohomology_machinery(self):
        base = Path(__file__).parent.parent / "lean" / "DeppyBase.lean"
        text = base.read_text()
        for name in (
            "Cochain",
            "coboundary",
            "IsCocycle",
            "IsCoboundary",
            "SafetyC0",
            "CallC1",
            "ModuleC2",
            "GlueCocycle",
            "CallCocycle",
            "ModuleCertified",
        ):
            assert name in text, f"missing cohomology decl {name!r}"

    def test_library_declares_tactic_combinators(self):
        base = Path(__file__).parent.parent / "lean" / "DeppyBase.lean"
        text = base.read_text()
        for tac in (
            "deppy_safe",
            "deppy_path",
            "deppy_transport",
            "deppy_cech",
            "deppy_cocycle",
            "deppy_kan",
            "deppy_cohomology",
        ):
            assert f"\"{tac}\"" in text, f"missing tactic {tac!r}"


# ─────────────────────────────────────────────────────────────────────
# C3 — kernel proof terms
# ─────────────────────────────────────────────────────────────────────

class TestCocycleProofTerm:
    def test_empty_components_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(level=0, components=[])
        r = kernel.verify(ctx, goal, c)
        assert not r.success
        assert "empty" in r.message.lower()

    def test_negative_level_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(level=-1, components=[Refl(term=Var("x"))])
        r = kernel.verify(ctx, goal, c)
        assert not r.success

    def test_components_verified_in_order(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(
            level=1,
            components=[Refl(term=Var("x")), Refl(term=Var("x"))],
        )
        r = kernel.verify(ctx, goal, c)
        assert r.success
        assert "C^1" in r.message

    def test_boundary_zero_witness_verified(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(
            level=2,
            components=[Refl(term=Var("x"))],
            boundary_zero=Refl(term=Var("x")),
        )
        r = kernel.verify(ctx, goal, c)
        assert r.success
        assert "δ=0 witnessed" in r.message

    def test_failed_component_propagates(self):
        from deppy import Assume
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(
            level=0,
            components=[Refl(term=Var("x")), Assume(name="bad")],
        )
        r = kernel.verify(ctx, goal, c)
        assert not r.success


class TestCohomologyClassProofTerm:
    def test_basic_cohomology_class(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(level=0, components=[Refl(term=Var("x"))])
        h = CohomologyClass(level=0, cocycle=c, class_id="my_class")
        r = kernel.verify(ctx, goal, h)
        assert r.success
        assert "my_class" in r.message
        assert "H^0" in r.message

    def test_trivial_class_with_witness(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(level=1, components=[Refl(term=Var("x"))])
        h = CohomologyClass(
            level=1, cocycle=c,
            coboundary_witness=Refl(term=Var("x")),
            class_id="trivial",
        )
        r = kernel.verify(ctx, goal, h)
        assert r.success
        assert "trivial" in r.message

    def test_invalid_level_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        c = Cocycle(level=0, components=[Refl(term=Var("x"))])
        h = CohomologyClass(level=-1, cocycle=c)
        r = kernel.verify(ctx, goal, h)
        assert not r.success


class TestKanFillProofTerm:
    def test_dim_2_takes_3_faces(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        kf = KanFill(
            dimension=2,
            faces=[Refl(term=Var("x")), Refl(term=Var("x")), Refl(term=Var("x"))],
        )
        r = kernel.verify(ctx, goal, kf)
        assert r.success
        assert "dim=2" in r.message

    def test_dim_3_takes_5_faces(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        kf = KanFill(
            dimension=3,
            faces=[Refl(term=Var("x")) for _ in range(5)],
        )
        r = kernel.verify(ctx, goal, kf)
        assert r.success

    def test_wrong_face_count_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        kf = KanFill(
            dimension=2,
            faces=[Refl(term=Var("x")), Refl(term=Var("x"))],  # only 2, need 3
        )
        r = kernel.verify(ctx, goal, kf)
        assert not r.success
        assert "expected" in r.message.lower()

    def test_dim_zero_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        kf = KanFill(dimension=0, faces=[])
        r = kernel.verify(ctx, goal, kf)
        assert not r.success


class TestHigherPathProofTerm:
    def test_dim_1_two_vertices(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        hp = HigherPath(
            dimension=1,
            vertices=[Var("x"), Var("x")],
            boundary_proofs=[Refl(term=Var("x")), Refl(term=Var("x"))],
        )
        r = kernel.verify(ctx, goal, hp)
        assert r.success
        assert "dim=1" in r.message

    def test_dim_2_four_vertices(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        hp = HigherPath(
            dimension=2,
            vertices=[Var("x")] * 4,
            boundary_proofs=[Refl(term=Var("x"))] * 4,
        )
        r = kernel.verify(ctx, goal, hp)
        assert r.success

    def test_wrong_vertex_count_rejected(self):
        kernel = ProofKernel()
        ctx, goal = _fresh_goal()
        hp = HigherPath(
            dimension=2,
            vertices=[Var("x")] * 3,  # 3 vertices, dim=2 needs 4
            boundary_proofs=[Refl(term=Var("x"))],
        )
        r = kernel.verify(ctx, goal, hp)
        assert not r.success


# ─────────────────────────────────────────────────────────────────────
# C2 — cohomological certificate structure
# ─────────────────────────────────────────────────────────────────────

class TestCohomologicalCertificate:
    def test_certificate_includes_cocycle_metadata(self, tmp_path):
        src = textwrap.dedent('''
            def f(a, b):
                if b != 0:
                    return a / b
                return 0
            def g(x):
                return f(x, 2)
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out)
        cert = report.certificate
        assert cert.cocycle_count_c0 >= 2  # f and g
        assert cert.cocycle_count_c1 >= 1  # g calls f

    def test_certificate_text_has_cohomology_section(self, tmp_path):
        src = textwrap.dedent('''
            def safe_div(a, b):
                if b != 0:
                    return a / b
                return 0
            def caller(x):
                return safe_div(x, 1)
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        assert "Cohomological structure" in text
        assert "C^0" in text and "C^1" in text
        assert "deppy_c0_cocycle_safe_div" in text
        assert "deppy_c0_cocycle_caller" in text
        assert "deppy_c1_cocycle_caller_to_safe_div" in text

    def test_certificate_hk_counts_present(self, tmp_path):
        src = textwrap.dedent('''
            def f():
                return 1
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out)
        cert = report.certificate
        # H^k counts are non-negative ints.
        assert cert.cohomology_h0_size >= 0
        assert cert.cohomology_h1_size >= 0
        assert cert.cohomology_h2_size >= 0

    def test_three_step_chain_emits_c2_coherence(self, tmp_path):
        src = textwrap.dedent('''
            def h_inner():
                return 1
            def g_middle():
                return h_inner()
            def f_outer():
                return g_middle()
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out)
        # f → g → h gives one C^2 coherence theorem.
        assert report.certificate.cocycle_count_c2 >= 1
        text = out.read_text()
        assert "C^2 coherence" in text


# ─────────────────────────────────────────────────────────────────────
# Top-level exports
# ─────────────────────────────────────────────────────────────────────

class TestExports:
    def test_cubical_terms_exported(self):
        import deppy
        for name in ("Cocycle", "CohomologyClass", "KanFill", "HigherPath"):
            assert hasattr(deppy, name), f"deppy.{name} missing"


# ─────────────────────────────────────────────────────────────────────
# Mergesort certificate — cubical/cohomological end-to-end
# ─────────────────────────────────────────────────────────────────────

class TestMergesortCohomology:
    def test_mergesort_certificate_has_cocycles(self, tmp_path):
        src = textwrap.dedent('''
            from deppy import implies

            @implies("True", "len(result) == len(xs)")
            def mergesort(xs):
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = xs[:mid]
                right = xs[mid:]
                return merge(mergesort(left), mergesort(right))

            def merge(a, b):
                if len(a) == 0:
                    return b
                if len(b) == 0:
                    return a
                if a[0] <= b[0]:
                    return [a[0]] + merge(a[1:], b)
                return [b[0]] + merge(a, b[1:])
        ''').strip()
        out = tmp_path / "Mergesort.lean"
        report = write_certificate(src, out, module_name="Mergesort")
        cert = report.certificate
        # Both functions get C^0 cocycles.
        assert cert.cocycle_count_c0 == 2
        # mergesort → merge call yields a C^1 cocycle.
        # (merge → merge self-recursion is excluded).
        assert cert.cocycle_count_c1 >= 1
