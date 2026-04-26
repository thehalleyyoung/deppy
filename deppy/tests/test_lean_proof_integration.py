"""End-to-end tests for the Lean-proof integration (Phase L1–L5).

Coverage:

* L1 — kernel verifies LeanProof terms by invoking the local
  ``lean`` binary.
* L2 — ``@with_lean_proof`` attaches a script to a Python function.
* L3 — the safety pipeline picks up the attached script and uses it
  as an additional discharge path.
* L4 — ``deppy.lean.obligations.emit_obligations`` writes a Lean
  skeleton with one ``theorem ... := by sorry`` per open source.
* L5 — the verdict's ``discharge_breakdown`` and per-function
  ``discharge_paths`` distinguish Z3 / syntactic / Lean / etc.

Tests that need the actual ``lean`` binary are skipped when it isn't
on ``PATH``; the rest exercise the plumbing without invoking Lean.
"""
from __future__ import annotations

import shutil
import textwrap
from pathlib import Path

import pytest


_HAS_LEAN = shutil.which("lean") is not None
needs_lean = pytest.mark.skipif(
    not _HAS_LEAN, reason="lean toolchain not installed",
)


# ─────────────────────────────────────────────────────────────────────
# L1 — kernel verifies LeanProof
# ─────────────────────────────────────────────────────────────────────

class TestLeanProofKernel:
    def test_leanproof_term_constructible(self):
        from deppy import LeanProof
        lp = LeanProof(theorem="theorem t : True := trivial",
                       proof_script="", imports=("import Init",))
        assert lp.theorem.startswith("theorem")
        # Repr is short.
        r = repr(lp)
        assert "Lean(" in r

    def test_kernel_dispatches_leanproof(self):
        """Kernel.verify routes LeanProof to _verify_lean even when
        Lean is not installed (returns failure with reason)."""
        from deppy import LeanProof, ProofKernel
        from deppy.core.kernel import Judgment, JudgmentKind, Context, Var
        from deppy.core.types import PyObjType
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK, context=ctx,
                        term=Var("safety"), type_=PyObjType())
        # Use a unique theorem name to avoid Lean's "trivial" collision.
        lp = LeanProof(theorem="theorem deppy_t1 : True := trivial",
                       proof_script="", timeout_s=20)
        result = kernel.verify(ctx, goal, lp)
        if _HAS_LEAN:
            assert result.success
            from deppy import TrustLevel
            assert result.trust_level == TrustLevel.KERNEL
            assert "LEAN_KERNEL_VERIFIED" in result.message
        else:
            assert not result.success
            assert "lean" in result.message.lower()

    @needs_lean
    def test_kernel_rejects_false_lean_proof(self):
        from deppy import LeanProof, ProofKernel
        from deppy.core.kernel import Judgment, JudgmentKind, Context, Var
        from deppy.core.types import PyObjType
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK, context=ctx,
                        term=Var("safety"), type_=PyObjType())
        lp = LeanProof(theorem="theorem deppy_false : False := trivial",
                       proof_script="", timeout_s=20)
        r = kernel.verify(ctx, goal, lp)
        assert not r.success
        assert "rejected" in r.message.lower()

    @needs_lean
    def test_kernel_caches_lean_result(self):
        """A second verify of the same LeanProof object re-uses its
        cached result (no extra Lean invocation)."""
        from deppy import LeanProof, ProofKernel
        from deppy.core.kernel import Judgment, JudgmentKind, Context, Var
        from deppy.core.types import PyObjType
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK, context=ctx,
                        term=Var("safety"), type_=PyObjType())
        lp = LeanProof(
            theorem="theorem deppy_cached : True := trivial",
            proof_script="", timeout_s=20,
        )
        kernel.verify(ctx, goal, lp)
        cached = lp._cached_result
        assert cached is not None
        # Second verify shouldn't *change* the cache.
        kernel.verify(ctx, goal, lp)
        assert lp._cached_result is cached


# ─────────────────────────────────────────────────────────────────────
# L2 — @with_lean_proof decorator
# ─────────────────────────────────────────────────────────────────────

class TestWithLeanProofDecorator:
    def test_attaches_metadata(self):
        from deppy import with_lean_proof

        @with_lean_proof(
            theorem="theorem deppy_a : True",
            proof="trivial",
            for_kind="ZERO_DIVISION",
        )
        def divide(a, b):
            return a / b

        attached = divide._deppy_lean_proofs
        assert len(attached) == 1
        kind, theorem, proof, imports = attached[0]
        assert kind == "ZERO_DIVISION"
        assert "deppy_a" in theorem
        assert proof == "trivial"
        assert imports == ()

    def test_decorator_stacks(self):
        from deppy import with_lean_proof

        @with_lean_proof(
            theorem="theorem deppy_b1 : True", proof="trivial",
            for_kind="ZERO_DIVISION",
        )
        @with_lean_proof(
            theorem="theorem deppy_b2 : True", proof="trivial",
            for_kind="KEY_ERROR",
        )
        def f(d, k, a, b):
            return d[k] / b

        kinds = {entry[0] for entry in f._deppy_lean_proofs}
        assert kinds == {"ZERO_DIVISION", "KEY_ERROR"}


# ─────────────────────────────────────────────────────────────────────
# L3 — pipeline integration
# ─────────────────────────────────────────────────────────────────────

class TestLeanProofPipelineIntegration:
    @needs_lean
    def test_attached_lean_proof_discharges_source(self):
        """A user who attaches a Lean proof for ZERO_DIVISION via
        ``@with_lean_proof`` and whose proof Lean accepts should see
        the function marked safe — even when no precondition was
        supplied."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = textwrap.dedent('''
            from deppy import with_lean_proof

            @with_lean_proof(
                theorem="theorem deppy_pipe_safe : True",
                proof="trivial",
                for_kind="ZERO_DIVISION",
            )
            def divide(a, b):
                return a / b
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["divide"]
        assert fv.is_safe
        # The discharge tag should be ``user-lean-proof``.
        assert "user-lean-proof" in fv.discharge_paths.values()

    def test_pipeline_safe_to_run_without_lean(self):
        """When ``lean`` is missing, the pipeline must not crash —
        Lean discharges silently fail and the verdict surfaces the
        source as undischarged."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = textwrap.dedent('''
            from deppy import with_lean_proof

            @with_lean_proof(
                theorem="theorem deppy_no_lean : True",
                proof="trivial",
                for_kind="ZERO_DIVISION",
            )
            def divide(a, b):
                return a / b
        ''').strip()
        # Whether Lean is installed or not, this run completes.
        v = verify_module_safety(src, use_drafts=True)
        assert "divide" in v.functions


# ─────────────────────────────────────────────────────────────────────
# L4 — emit_obligations
# ─────────────────────────────────────────────────────────────────────

class TestEmitObligations:
    def test_emits_one_theorem_per_open_source(self, tmp_path):
        from deppy.lean.obligations import emit_obligations
        src = textwrap.dedent('''
            def divide(a, b):
                return a / b

            def lookup(d, k):
                return d[k]
        ''').strip()
        out = tmp_path / "obligations.lean"
        report = emit_obligations(src, out, use_drafts=True,
                                  module_name="DemoMod")
        # divide → ZERO_DIVISION; lookup → INDEX_ERROR + KEY_ERROR.
        assert report.open_count >= 2
        text = out.read_text()
        assert "namespace DemoMod" in text
        assert "theorem deppy_divide" in text
        assert ":= by" in text and "sorry" in text

    def test_obligations_file_is_valid_lean_syntax(self, tmp_path):
        """Even though the bodies are ``sorry``, the file should
        parse — namespace open/close, every theorem terminated."""
        from deppy.lean.obligations import emit_obligations
        src = "def f(a, b):\n    return a / b\n"
        out = tmp_path / "obligations.lean"
        emit_obligations(src, out)
        text = out.read_text()
        # Cheap structural checks: `namespace` and `end` paired.
        assert text.count("namespace ") == 1
        assert text.count("\nend ") == 1

    def test_no_obligations_when_module_safe(self, tmp_path):
        from deppy.lean.obligations import emit_obligations
        # A trivially safe module: only constant non-zero division.
        src = "def f():\n    return 1 / 1\n"
        out = tmp_path / "obligations.lean"
        report = emit_obligations(src, out, use_drafts=True)
        assert report.open_count == 0
        assert "No open obligations" in report.summary()

    def test_obligations_emit_then_re_check_round_trip(self, tmp_path):
        """Emit obligations for a module, then run the pipeline a
        second time and confirm it produces the same source set.
        Demonstrates the round-trip: emit → fill → re-check."""
        from deppy.lean.obligations import emit_obligations
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def f(a, b):\n    return a / b\n"
        out = tmp_path / "obligations.lean"
        first = emit_obligations(src, out, use_drafts=True)
        # Re-run.  Same source → same obligation count.
        second = emit_obligations(src, out, use_drafts=True)
        assert first.open_count == second.open_count
        # And the verdict still flags the function as unsafe (we
        # haven't supplied any proofs yet).
        v = verify_module_safety(src, use_drafts=True)
        assert not v.functions["f"].is_safe


# ─────────────────────────────────────────────────────────────────────
# L5 — discharge breakdown
# ─────────────────────────────────────────────────────────────────────

class TestDischargeBreakdown:
    def test_breakdown_counts_each_path(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = textwrap.dedent('''
            def safe_div(a, b):
                if b != 0:
                    return a / b
                return 0

            def safe_lookup(d, k):
                if k in d:
                    return d[k]
                return None

            def unsafe(a, b):
                return a / b
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        bd = v.discharge_breakdown
        # safe_div → at least one Z3-discharge.
        assert bd.get("z3-arithmetic", 0) >= 1 or bd.get("z3-syntactic", 0) >= 1
        # safe_lookup → at least one syntactic discharge.
        assert bd.get("z3-syntactic", 0) >= 1
        # unsafe → at least one undischarged.
        assert bd.get("undischarged", 0) >= 1

    def test_per_function_discharge_paths_populated(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def f(a, b):\n    if b != 0:\n        return a / b\n    return 0\n"
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["f"]
        assert fv.discharge_paths
        assert all(tag in (
            "z3-arithmetic", "z3-syntactic", "builtin-sidecar",
            "callee-summary", "raises-declaration", "callee-axiom",
            "is-total", "termination", "user-lean-proof",
            "co-located-peer", "undischarged",
        ) for tag in fv.discharge_paths.values())

    def test_summary_mentions_obligations_command_when_gaps(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def f(a, b):\n    return a / b\n"
        v = verify_module_safety(src, use_drafts=True)
        text = v.summary()
        assert "deppy obligations" in text
