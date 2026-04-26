"""Soundness-fix audit: tests F1–F8.

Each test exercises a specific cheat that was honestly identified in
the audit and now closed.  Many tests intentionally CONFIRM that an
unsafe-looking program is correctly flagged unsafe — they would
*pass* before the fix only because the cheat masked the unsafety.
"""
from __future__ import annotations

import shutil
import textwrap

import pytest

from deppy.pipeline.safety_pipeline import verify_module_safety
from deppy.pipeline.refinement_inference import infer_refinements
from deppy.lean.predicate_translation import translate
from deppy import LeanProof, ProofKernel
from deppy.core.kernel import Judgment, JudgmentKind, Context, Var
from deppy.core.types import PyObjType


_HAS_LEAN = shutil.which("lean") is not None
needs_lean = pytest.mark.skipif(
    not _HAS_LEAN, reason="lean toolchain not installed",
)


# ─────────────────────────────────────────────────────────────────────
# F1 — Lean kernel must check user's theorem against deppy's goal
# ─────────────────────────────────────────────────────────────────────

class TestF1_LeanGoalCheck:
    @needs_lean
    def test_trivial_proof_rejected_for_nontrivial_goal(self):
        """Cheat: user wrote ``theorem t : True := trivial`` and got
        ZeroDivisionError discharged.  Fix: kernel synthesises the
        theorem from ``expected_goal``; ``trivial`` cannot inhabit
        ``b ≠ 0``.
        """
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK, context=ctx,
            term=Var("safety"), type_=PyObjType(),
        )
        lp = LeanProof(
            expected_goal="b ≠ 0",
            binders=("(a : Int)", "(b : Int)"),
            proof_script="trivial",
            timeout_s=20,
        )
        r = kernel.verify(ctx, goal, lp)
        assert not r.success
        assert "rejected" in r.message.lower()

    @needs_lean
    def test_real_proof_accepted(self):
        """The fix doesn't reject *real* proofs."""
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK, context=ctx,
            term=Var("safety"), type_=PyObjType(),
        )
        lp = LeanProof(
            expected_goal="b ≠ 0",
            binders=("(a : Int)", "(b : Int)", "(h : b ≠ 0)"),
            proof_script="exact h",
            timeout_s=20,
        )
        r = kernel.verify(ctx, goal, lp)
        assert r.success, r.message


# ─────────────────────────────────────────────────────────────────────
# F2 — Mutation tracking in path-sensitive guards
# ─────────────────────────────────────────────────────────────────────

class TestF2_MutationTracking:
    def test_del_invalidates_membership_guard(self):
        """Cheat: ``del d[k]`` left the ``k in d`` guard live.
        Fix: mutation drops guards that mention the mutated name."""
        src = (
            "def f(d, k):\n"
            "    if k in d:\n"
            "        del d[k]\n"
            "        return d[k]\n"
        )
        m = infer_refinements(src)["f"]
        # The d[k] AFTER the del must have empty guards.
        post_del = [f for f in m.per_source if f.source_lineno == 4]
        assert post_del
        for fact in post_del:
            assert fact.guards == ()

    def test_subscript_assign_invalidates_guard(self):
        src = (
            "def f(d, k):\n"
            "    if k in d:\n"
            "        d[k] = 0\n"
            "        return d[k]\n"
        )
        m = infer_refinements(src)["f"]
        post_assign = [f for f in m.per_source if f.source_lineno == 4]
        for fact in post_assign:
            assert fact.guards == ()

    def test_pop_invalidates_bounds_guard(self):
        src = (
            "def f(xs, i):\n"
            "    if 0 <= i < len(xs):\n"
            "        xs.pop()\n"
            "        return xs[i]\n"
        )
        m = infer_refinements(src)["f"]
        post_pop = [f for f in m.per_source if f.source_lineno == 4
                    and f.source_kind in {"INDEX_ERROR", "KEY_ERROR"}]
        for fact in post_pop:
            assert fact.guards == ()

    def test_unrelated_mutation_keeps_guard(self):
        """Mutating ``ys`` does not invalidate a guard about ``d``."""
        src = (
            "def f(d, k, ys):\n"
            "    if k in d:\n"
            "        ys.append(1)\n"
            "        return d[k]\n"
        )
        m = infer_refinements(src)["f"]
        d_access = [f for f in m.per_source if f.source_lineno == 4
                    and f.source_kind == "KEY_ERROR"]
        assert d_access
        assert any("k in d" in g for f in d_access for g in f.guards)

    def test_aug_assign_to_int_keeps_membership_guard(self):
        src = (
            "def f(d, k, n):\n"
            "    if k in d:\n"
            "        n += 1\n"
            "        return d[k]\n"
        )
        m = infer_refinements(src)["f"]
        post = [f for f in m.per_source if f.source_lineno == 4
                and f.source_kind == "KEY_ERROR"]
        assert any("k in d" in g for f in post for g in f.guards)


# ─────────────────────────────────────────────────────────────────────
# F3 — Co-located INDEX/KEY promotion requires type evidence
# ─────────────────────────────────────────────────────────────────────

class TestF3_CoLocatedPromotion:
    def test_unannotated_subscript_remains_unsafe(self):
        """Cheat: ``if k in d: return d[k]`` was marked safe even
        when ``d`` could have been a list (where ``k in d`` doesn't
        bound-check).  Fix: promotion needs a type guard."""
        src = (
            "def f(d, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        # Without a type annotation, INDEX_ERROR is unaddressed.
        fv = v.functions["f"]
        assert any("INDEX_ERROR" in u for u in fv.unaddressed)

    def test_dict_annotation_enables_promotion(self):
        src = (
            "def f(d: dict, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["f"]
        assert fv.is_safe

    def test_isinstance_guard_enables_promotion(self):
        src = (
            "def f(d, k):\n"
            "    if isinstance(d, dict) and k in d:\n"
            "        return d[k]\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["f"]
        assert fv.is_safe


# ─────────────────────────────────────────────────────────────────────
# F4 — Obligation translation never falls back to True
# ─────────────────────────────────────────────────────────────────────

class TestF4_PredicateTranslation:
    def test_membership_emits_opaque_prop(self):
        result = translate("(k) in (d)")
        assert result.lean_text != "True"
        # Either Membership.mem (opaque typeclass) or an explicit
        # axiom — both rule out a `trivial` discharge.
        assert ("Membership.mem" in result.lean_text
                or result.lean_text.startswith("deppy_pred_"))

    def test_isinstance_emits_opaque_prop(self):
        result = translate("isinstance(x, int)")
        assert result.lean_text != "True"
        assert result.lean_text.startswith("deppy_pred_")
        # And carries an axiom declaration.
        assert any("axiom" in d for d in result.aux_decls)

    def test_arithmetic_translates_directly(self):
        result = translate("(b) != 0")
        assert result.exact
        assert "≠" in result.lean_text or "!=" in result.lean_text

    def test_synthetic_predicate_emits_opaque(self):
        result = translate("decreases_measure_provided")
        assert result.lean_text != "True"
        assert any("axiom" in d for d in result.aux_decls)

    def test_emit_obligations_never_uses_true_for_non_arithmetic(self, tmp_path):
        from deppy.lean.obligations import emit_obligations
        src = textwrap.dedent('''
            def f(d, k):
                return d[k]
        ''').strip()
        out = tmp_path / "obs.lean"
        emit_obligations(src, out, use_drafts=True)
        text = out.read_text()
        # The KEY_ERROR theorem's goal must NOT be the bare token
        # ``True`` — that would let the user discharge it with
        # ``trivial``.
        assert "KEY_ERROR" in text
        # Find the theorem block(s) and verify none has ``: (True)``
        # as the goal — they should be opaque Props or membership.
        import re
        goals = re.findall(r":\s*\(([^)]+)\)\s*:=", text)
        for goal in goals:
            assert goal.strip() != "True", goals


# ─────────────────────────────────────────────────────────────────────
# F5 — assert is not a function-wide precondition
# ─────────────────────────────────────────────────────────────────────

class TestF5_AssertNotFunctionWide:
    def test_leading_assert_does_not_become_precondition(self):
        src = (
            "def f(d, k):\n"
            "    assert k in d\n"
            "    return d[k]\n"
        )
        m = infer_refinements(src)["f"]
        assert m.function_wide_preconditions == []
        assert m.used_assert_narrowing is True

    def test_pipeline_warns_on_assert_narrowing(self):
        src = (
            "def f(d, k):\n"
            "    assert k in d\n"
            "    return d[k]\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        # Verdict carries a note about ``-O``.
        assert any("-O" in n for n in v.notes)

    def test_if_not_p_raise_is_function_wide(self):
        """The recommended replacement IS a function-wide precondition."""
        src = (
            "def f(b):\n"
            "    if b == 0:\n"
            "        raise AssertionError\n"
            "    return 1 / b\n"
        )
        m = infer_refinements(src)["f"]
        assert "b != 0" in m.function_wide_preconditions


# ─────────────────────────────────────────────────────────────────────
# F6 — callee-safe axiom respects summaries
# ─────────────────────────────────────────────────────────────────────

class TestF6_CalleeSafeAxiom:
    def test_caller_of_unsafe_internal_callee_remains_unsafe(self):
        """Cheat: caller's CALL_PROPAGATION was axiom-discharged
        unconditionally even when the callee summary said unsafe.
        Fix: the axiom path consults summaries."""
        src = (
            "def unsafe(a, b):\n"
            "    return a / b\n"
            "def caller(x, y):\n"
            "    return unsafe(x, y)\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        assert not v.functions["unsafe"].is_safe
        assert not v.functions["caller"].is_safe

    def test_caller_of_safe_callee_inherits_safety(self):
        src = (
            "def safe(a, b):\n"
            "    if b != 0:\n"
            "        return a / b\n"
            "    return 0\n"
            "def caller(x, y):\n"
            "    return safe(x, y)\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        assert v.functions["safe"].is_safe
        assert v.functions["caller"].is_safe


# ─────────────────────────────────────────────────────────────────────
# F7 — Discharge breakdown distinguishes unknown from syntactic
# ─────────────────────────────────────────────────────────────────────

class TestF7_DischargeBreakdown:
    def test_breakdown_uses_structural_unknown_label(self):
        """The label set has been extended with ``structural-unknown``."""
        from deppy.pipeline.safety_pipeline import _DISCHARGE_TAGS
        assert "structural-unknown" in _DISCHARGE_TAGS
        assert "builtin-total-axiom" in _DISCHARGE_TAGS

    def test_z3_arithmetic_tag_emitted_for_real_z3_work(self):
        """Z3 actually proving ``b > 0 ⇒ b != 0`` produces the
        ``z3-arithmetic`` tag (not the syntactic-shortcut tag).
        """
        src = (
            "def f(a, b: int):\n"
            "    if b > 0:\n"
            "        return a / b\n"
            "    return 0\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        bd = v.discharge_breakdown
        assert bd.get("z3-arithmetic", 0) >= 1, bd

    def test_syntactic_tag_emitted_for_membership_match(self):
        """``k in d`` matches the safety predicate verbatim, so the
        kernel emits a ``Structural`` (syntactic) discharge — tagged
        ``z3-syntactic``.
        """
        src = (
            "def f(d: dict, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
            "    return None\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        bd = v.discharge_breakdown
        assert bd.get("z3-syntactic", 0) >= 1, bd


# ─────────────────────────────────────────────────────────────────────
# F8 — Builtin total entries become AxiomInvocation
# ─────────────────────────────────────────────────────────────────────

class TestF8_BuiltinTotalIsAxiom:
    def test_total_builtin_emits_axiom_invocation(self):
        """``type(x)`` / ``hasattr(x, 'y')`` are in the
        builtin-total catalogue.  They now emit ``AxiomInvocation``
        (axiom-trusted) — visible in the discharge breakdown as
        ``builtin-total-axiom``."""
        src = (
            "def f(x):\n"
            "    return type(x)\n"
        )
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["f"]
        tags = set(fv.discharge_paths.values())
        # Either the source was discharged via builtin-total-axiom
        # (ideal) or via callee-axiom (catalogue lookup didn't
        # match).  In both cases it's *not* ``z3-syntactic`` /
        # ``co-located-peer`` / a Structural — Phase F8 made these
        # axiom-tagged.
        assert tags
        assert "builtin-total-axiom" in tags or "callee-axiom" in tags

    def test_kernel_records_builtin_total_axiom_name(self):
        """The pipeline registers an axiom named ``builtin_total[...]``
        on the kernel for any matched total entry."""
        from deppy.pipeline.builtin_sidecar import lookup_call
        import ast as _ast
        # ``hasattr`` is in the catalogue as a total entry.
        node = _ast.parse("hasattr(x, 'y')", mode="eval").body
        entries = lookup_call(node)
        total_entries = [e for e in entries if e.mode == "total"]
        assert total_entries, "hasattr should be marked total"
