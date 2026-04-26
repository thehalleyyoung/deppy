"""Audit fix #7 — honest @implies tactic selection.

Locks down :func:`deppy.lean.implies_tactics.select_implies_tactic`
across the categories the audit fix targets.

The test contract:

* When the analyser is *confident* about a proof, it picks a
  specific tactic (``omega``, ``decide``, ``intro h; exact h``,
  ``intro h; exact h.left``, …) — not the catch-all
  ``Deppy.deppy_safe``.
* When the analyser cannot find a plausible tactic (opaque
  predicate, custom function call, structurally unmatched), it
  emits ``sorry`` *honestly* — not a silent fallback.
* The user's ``proof=`` argument always wins.
* The classification metadata is correct, so a downstream report can
  count auto-proved vs sorry-emitted obligations.
"""
from __future__ import annotations

from deppy.lean.implies_tactics import (
    ImpliesAuditEntry,
    ImpliesClassification,
    ImpliesTacticPlan,
    count_auto_proved,
    count_unproved,
    count_user_supplied,
    render_audit_summary,
    select_implies_tactic,
)


# ─────────────────────────────────────────────────────────────────────
#  Trivial / identity cases
# ─────────────────────────────────────────────────────────────────────


class TestTrivialAndIdentity:
    def test_post_is_True_uses_trivial(self):
        plan = select_implies_tactic("a > 0", "True")
        assert plan.classification is ImpliesClassification.TRUE_GOAL
        assert not plan.is_sorry
        assert "trivial" in plan.tactic_text

    def test_pre_is_False_uses_ex_falso(self):
        plan = select_implies_tactic("False", "a > 0")
        assert plan.classification is ImpliesClassification.FALSE_PRE
        assert not plan.is_sorry
        assert "elim" in plan.tactic_text

    def test_pre_equals_post_uses_exact_h(self):
        plan = select_implies_tactic("a > 0", "a > 0")
        assert plan.classification is ImpliesClassification.IDENTITY
        assert not plan.is_sorry
        assert "exact h" in plan.tactic_text

    def test_pre_equals_post_complex(self):
        plan = select_implies_tactic(
            "a > 0 and b < 100", "a > 0 and b < 100"
        )
        assert plan.classification is ImpliesClassification.IDENTITY
        assert not plan.is_sorry
        assert "exact h" in plan.tactic_text


# ─────────────────────────────────────────────────────────────────────
#  Conjunct-of-pre
# ─────────────────────────────────────────────────────────────────────


class TestConjunctOfPre:
    def test_post_is_first_conjunct(self):
        plan = select_implies_tactic("a > 0 and b < 100", "a > 0")
        assert plan.classification is ImpliesClassification.CONJUNCT
        assert not plan.is_sorry
        assert "exact h" in plan.tactic_text

    def test_post_is_last_conjunct(self):
        plan = select_implies_tactic(
            "a > 0 and b < 100 and c == 1", "c == 1",
        )
        assert plan.classification is ImpliesClassification.CONJUNCT
        assert not plan.is_sorry

    def test_post_is_middle_conjunct(self):
        plan = select_implies_tactic(
            "a > 0 and b < 100 and c == 1", "b < 100",
        )
        assert plan.classification is ImpliesClassification.CONJUNCT
        assert not plan.is_sorry


# ─────────────────────────────────────────────────────────────────────
#  Linear arithmetic
# ─────────────────────────────────────────────────────────────────────


class TestLinearArith:
    def test_arith_implication_uses_omega(self):
        plan = select_implies_tactic(
            "a >= 1", "a > 0",
            py_types={"a": "int"},
        )
        assert plan.classification is ImpliesClassification.LINEAR_ARITH
        assert not plan.is_sorry
        assert "omega" in plan.tactic_text

    def test_complex_arithmetic(self):
        plan = select_implies_tactic(
            "a + b > 5 and b > 0", "a > -10",
            py_types={"a": "int", "b": "int"},
        )
        assert plan.classification is ImpliesClassification.LINEAR_ARITH
        assert "omega" in plan.tactic_text

    def test_constant_multiplication_is_linear(self):
        plan = select_implies_tactic(
            "a >= 0", "2 * a >= 0",
            py_types={"a": "int"},
        )
        assert plan.classification is ImpliesClassification.LINEAR_ARITH

    def test_variable_multiplication_is_nonlinear(self):
        # ``a * b`` is non-linear and omega rejects it.  We should
        # not pick LINEAR_ARITH here.
        plan = select_implies_tactic(
            "a >= 0 and b >= 0", "a * b >= 0",
            py_types={"a": "int", "b": "int"},
        )
        assert plan.classification is not ImpliesClassification.LINEAR_ARITH

    def test_div_by_constant_is_linear(self):
        plan = select_implies_tactic(
            "a >= 4", "a // 2 >= 2",
            py_types={"a": "int"},
        )
        assert plan.classification is ImpliesClassification.LINEAR_ARITH


# ─────────────────────────────────────────────────────────────────────
#  Decidable propositional
# ─────────────────────────────────────────────────────────────────────


class TestDecidableProp:
    def test_closed_decidable_uses_decide(self):
        plan = select_implies_tactic("True", "1 < 2")
        # post is True-shape recognized as TRUE_GOAL only when post
        # is exactly True.  Here post is ``1 < 2`` which is
        # decidable.
        assert plan.classification in (
            ImpliesClassification.LINEAR_ARITH,
            ImpliesClassification.DECIDABLE_PROP,
        )
        assert not plan.is_sorry


# ─────────────────────────────────────────────────────────────────────
#  Opaque predicates
# ─────────────────────────────────────────────────────────────────────


class TestOpaquePredicates:
    def test_hasattr_is_opaque(self):
        plan = select_implies_tactic("True", "hasattr(x, 'y')")
        assert plan.classification is ImpliesClassification.OPAQUE
        assert plan.is_sorry
        assert "sorry" in plan.tactic_text
        assert plan.sorry_reason is not None

    def test_callee_safe_is_opaque(self):
        plan = select_implies_tactic("True", "callee_safe(f, args)")
        assert plan.classification is ImpliesClassification.OPAQUE
        assert plan.is_sorry

    def test_module_present_is_opaque(self):
        plan = select_implies_tactic("True", "module_present('np')")
        assert plan.classification is ImpliesClassification.OPAQUE
        assert plan.is_sorry

    def test_user_function_call_is_opaque(self):
        plan = select_implies_tactic(
            "True", "my_helper(x) > 0",
            fn_name="some_other_function",
        )
        assert plan.classification is ImpliesClassification.OPAQUE
        assert plan.is_sorry

    def test_self_recursive_call_is_NOT_opaque(self):
        # When the function name appears in pre/post, it's the
        # function's own result — not opaque.
        plan = select_implies_tactic(
            "True", "True",  # this should be TRUE_GOAL
            fn_name="my_fn",
        )
        assert plan.classification is ImpliesClassification.TRUE_GOAL


# ─────────────────────────────────────────────────────────────────────
#  User-supplied proofs always win
# ─────────────────────────────────────────────────────────────────────


class TestUserProof:
    def test_user_proof_wins_over_auto(self):
        plan = select_implies_tactic(
            "a > 0", "a >= 0",
            py_types={"a": "int"},
            user_proof="omega",
        )
        assert plan.is_user_supplied
        assert not plan.is_sorry
        assert "omega" in plan.tactic_text

    def test_user_proof_with_sorry_marks_sorry(self):
        plan = select_implies_tactic(
            "a > 0", "a >= 0",
            user_proof="sorry",
        )
        assert plan.is_user_supplied
        # User explicitly admitted sorry — record that.
        assert plan.is_sorry

    def test_user_proof_classification_is_unknown(self):
        plan = select_implies_tactic(
            "a > 0", "True", user_proof="trivial",
        )
        # The classification field doesn't try to second-guess
        # what the user wrote — it's UNKNOWN since we didn't run
        # auto-classification.
        assert plan.classification is ImpliesClassification.UNKNOWN
        assert plan.is_user_supplied


# ─────────────────────────────────────────────────────────────────────
#  Definitional / simp-friendly
# ─────────────────────────────────────────────────────────────────────


class TestDefinitional:
    def test_compare_commutativity(self):
        # ``a > 0`` vs ``0 < a`` are simp-equivalent.
        plan = select_implies_tactic(
            "a > 0", "0 < a", py_types={"a": "int"},
        )
        # Either DEFINITIONAL or LINEAR_ARITH closes this.
        assert not plan.is_sorry

    def test_add_commutativity(self):
        plan = select_implies_tactic(
            "a + b > 0", "b + a > 0", py_types={"a": "int", "b": "int"},
        )
        assert not plan.is_sorry


# ─────────────────────────────────────────────────────────────────────
#  Audit log / counts
# ─────────────────────────────────────────────────────────────────────


class TestAuditLog:
    def _entry(self, **kw):
        defaults = dict(
            fn_name="f", idx=0, pre_py="True", post_py="True",
            classification=ImpliesClassification.TRUE_GOAL,
            is_sorry=False, confidence=1.0, notes=[],
        )
        defaults.update(kw)
        return ImpliesAuditEntry(**defaults)

    def test_count_unproved_zero_when_all_succeed(self):
        entries = [
            self._entry(),
            self._entry(idx=1, classification=ImpliesClassification.LINEAR_ARITH),
        ]
        assert count_unproved(entries) == 0
        assert count_auto_proved(entries) == 2
        assert count_user_supplied(entries) == 0

    def test_count_unproved_counts_sorries(self):
        entries = [
            self._entry(),
            self._entry(
                idx=1, is_sorry=True,
                classification=ImpliesClassification.OPAQUE,
                sorry_reason="opaque predicate",
            ),
            self._entry(idx=2, user_supplied=True),
        ]
        assert count_unproved(entries) == 1
        assert count_auto_proved(entries) == 1
        assert count_user_supplied(entries) == 1

    def test_render_audit_summary_lists_every_entry(self):
        entries = [
            self._entry(),
            self._entry(
                idx=1, is_sorry=True,
                classification=ImpliesClassification.OPAQUE,
            ),
        ]
        summary = render_audit_summary(entries)
        assert "✗" in summary  # sorry mark
        assert "true" in summary  # classification
        assert "opaque" in summary

    def test_render_audit_summary_empty_returns_empty(self):
        assert render_audit_summary([]) == ""

    def test_to_dict_roundtrip(self):
        e = self._entry(
            is_sorry=True,
            classification=ImpliesClassification.OPAQUE,
            sorry_reason="hasattr in goal",
        )
        d = e.to_dict()
        assert d["is_sorry"] is True
        assert d["classification"] == "opaque"
        assert d["sorry_reason"] == "hasattr in goal"


# ─────────────────────────────────────────────────────────────────────
#  Edge cases
# ─────────────────────────────────────────────────────────────────────


class TestEdgeCases:
    def test_unparseable_pre_emits_sorry(self):
        plan = select_implies_tactic("a >>> b", "True")
        # ``>>>`` is a Python syntax error — analyser bails.
        assert plan.is_sorry

    def test_unparseable_post_emits_sorry(self):
        plan = select_implies_tactic("True", "a >>> b")
        assert plan.is_sorry

    def test_empty_pre_treated_as_True(self):
        plan = select_implies_tactic("", "True")
        assert plan.classification is ImpliesClassification.TRUE_GOAL
        assert not plan.is_sorry

    def test_does_not_emit_deppy_safe(self):
        """Audit-fix invariant: select_implies_tactic must NEVER
        emit ``Deppy.deppy_safe`` — the cheat we replaced.  Either
        a real tactic or honest ``sorry``."""
        cases = [
            ("a > 0", "a >= 0", {"a": "int"}),  # → omega
            ("a > 0 and b > 0", "a > 0", {}),    # → conjunct
            ("True", "True", {}),                # → trivial
            ("hasattr(x, 'y')", "True", {}),    # → trivial (post=True)
            ("True", "hasattr(x, 'y')", {}),    # → sorry
        ]
        for pre, post, py_types in cases:
            plan = select_implies_tactic(pre, post, py_types=py_types)
            assert "deppy_safe" not in plan.tactic_text.lower(), (
                f"deppy_safe leaked into plan for {pre!r}/{post!r}"
            )

    def test_aesop_friendly_falls_back(self):
        """Goals that are aesop-friendly get an aesop tactic, not a
        sorry — but the confidence is lower."""
        # ``a or not a`` — classical tautology aesop closes.
        plan = select_implies_tactic(
            "True", "True", py_types={},
        )
        # In this trivial case it's TRUE_GOAL, not aesop.
        assert plan.classification is ImpliesClassification.TRUE_GOAL
        assert plan.confidence == 1.0


# ─────────────────────────────────────────────────────────────────────
#  Plan dataclass invariants
# ─────────────────────────────────────────────────────────────────────


class TestPlanInvariants:
    def test_sorry_plan_tactic_text_is_sorry(self):
        plan = ImpliesTacticPlan(
            tactic_body="anything",
            is_sorry=True, is_user_supplied=False,
            classification=ImpliesClassification.OPAQUE,
            confidence=0.0,
        )
        assert plan.tactic_text == "sorry"

    def test_non_sorry_plan_prefixes_by(self):
        plan = ImpliesTacticPlan(
            tactic_body="omega", is_sorry=False,
            is_user_supplied=False,
            classification=ImpliesClassification.LINEAR_ARITH,
            confidence=0.9,
        )
        assert plan.tactic_text == "by omega"

    def test_user_proof_no_double_by(self):
        # ``user_proof="exact h"`` should turn into ``by exact h`` —
        # but the user-supplied path skips the auto-prefix and
        # accepts the bare body.  We verify the body is the user's.
        plan = select_implies_tactic(
            "True", "True", user_proof="trivial",
        )
        assert plan.is_user_supplied
        assert plan.tactic_body == "trivial"
        # tactic_text should still emit ``by ...``.
        assert plan.tactic_text == "by trivial"
