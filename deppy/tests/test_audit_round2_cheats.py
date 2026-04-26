"""Regression tests for the round-2 cheat audit.

Each test pins down an audit-fix invariant — a behaviour that
*was* a cheat in the round-1 fix and was corrected in round 2.
A future regression that re-introduces the cheat will trip these
tests.
"""
from __future__ import annotations

import ast
import textwrap


# ─────────────────────────────────────────────────────────────────────
#  Cheat #1 — verify_chain_complex actually checks
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat1_VerifyChainComplexActuallyChecks:
    def test_matches_expected_tautology_shape(self):
        from deppy.lean.cohomology_compute import ChainComplex
        cx = ChainComplex.empty()
        for n in ("f", "g", "h"):
            cx.c0.add(n, f"P{n}")
        # Filled triangle so coboundary_1 emits a value.
        cx.calls = {"f": {"g", "h"}, "g": {"h"}}
        audit = cx.verify_chain_complex()
        # The check must actually fire (round 1 had it always True
        # without verifying anything).
        assert audit.triples_verified >= 1
        assert audit.d2_squared_zero is True
        assert not audit.mismatch_simplices

    def test_detects_corrupted_coboundary(self):
        # Construct a chain complex where δ¹(δ⁰(c0)) does NOT match
        # the expected transitivity tautology by injecting bad data
        # into c0 between the two coboundary applications.  In
        # practice we monkey-patch ``coboundary_1`` to emit the
        # wrong shape.
        from deppy.lean.cohomology_compute import ChainComplex, Cochain
        cx = ChainComplex.empty()
        for n in ("f", "g", "h"):
            cx.c0.add(n, f"P{n}")
        cx.calls = {"f": {"g", "h"}, "g": {"h"}}
        # Override coboundary_1 with a wrong (non-tautology) shape.
        original = cx.coboundary_1
        def _bad_cb1(c1):  # noqa: ANN001
            out = Cochain(level=2)
            for triple in cx._all_c2_simplices():
                f, g, h = triple
                psi_fg = c1.get((f, g))
                psi_gh = c1.get((g, h))
                psi_fh = c1.get((f, h))
                if psi_fg and psi_gh and psi_fh:
                    # Wrong: ((g,h) ∧ (f,h)) → (f,g) — the round-1
                    # cheat shape.
                    out.add(triple, f"(({psi_gh}) ∧ ({psi_fh})) → ({psi_fg})")
            return out
        cx.coboundary_1 = _bad_cb1  # type: ignore[assignment]
        audit = cx.verify_chain_complex()
        # The verifier now actually rejects the bad shape.
        assert audit.d2_squared_zero is False
        assert audit.mismatch_simplices
        cx.coboundary_1 = original  # restore (cleanup)


# ─────────────────────────────────────────────────────────────────────
#  Cheat #2 — compute_cohomology compares predicates, not simplex sets
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat2_PredicateAwareCohomology:
    def test_mismatched_c1_pred_is_obstruction(self):
        from deppy.lean.cohomology_compute import ChainComplex
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        # Mismatch: c1 says "Pfg" but δ⁰(c0) emits "(Pf) → (Pg)".
        cx.c1.add(("f", "g"), "Pfg")
        coh = cx.compute_cohomology()
        # Round 1 placed (f, g) in im δ⁰ via simplex membership.
        # Round 2 correctly classifies it as an obstruction.
        assert ("f", "g") in coh.h1_obstructions

    def test_matched_c1_pred_is_trivial(self):
        from deppy.lean.cohomology_compute import ChainComplex
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        # Match: c1's predicate equals δ⁰(c0)'s output.
        cx.c1.add(("f", "g"), "(Pf) → (Pg)")
        coh = cx.compute_cohomology()
        assert ("f", "g") not in coh.h1_obstructions


# ─────────────────────────────────────────────────────────────────────
#  Cheat #3 — kernel trust downgrade for unstructured cocycles
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat3_TrustDowngrade:
    def test_multi_component_unstructured_downgrades(self):
        from deppy.core.kernel import (
            Cocycle, Context, Judgment, JudgmentKind, ProofKernel,
            Refl, TrustLevel, Var,
        )
        from deppy.core.types import PyObjType
        kernel = ProofKernel()
        ctx = Context()
        x = Var("x")
        goal = Judgment(
            kind=JudgmentKind.EQUAL, context=ctx,
            left=x, right=x, type_=PyObjType(),
        )
        proof = Cocycle(
            level=0,
            components=[Refl(term=x), Refl(term=x)],
            # No boundary_pairs.
        )
        r = kernel.verify(ctx, goal, proof)
        assert r.success
        # Round 1 returned KERNEL trust; round 2 downgrades.
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN


# ─────────────────────────────────────────────────────────────────────
#  Cheat #4 — cocycle emitter no longer uses Deppy.deppy_safe
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat4_NoDeppyAfeInCocycles:
    def test_emitter_module_has_no_deppy_safe_strings(self):
        # Read the cohomology emitter source and verify no
        # ``Deppy.deppy_safe`` appears in code (only in comments).
        import deppy.lean.cohomology as mod
        source = open(mod.__file__).read()
        # Strip out the comment lines (anything after a ``#`` or
        # within a triple-quoted docstring).  A simple approximation:
        # check that the strings ``"Deppy.deppy_safe"`` don't appear
        # outside comments / strings.
        # We'll just ensure no body text says ``body = "...deppy_safe..."``.
        for line in source.splitlines():
            stripped = line.strip()
            if stripped.startswith("#") or stripped.startswith("--"):
                continue
            if 'body = "' in line and "deppy_safe" in line:
                raise AssertionError(
                    f"deppy_safe appears in an active body assignment: {line!r}"
                )


# ─────────────────────────────────────────────────────────────────────
#  Cheat #5 — linear-arith requires explicit type annotations
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat5_LinearArithStrict:
    def test_unannotated_name_not_linear(self):
        from deppy.lean.implies_tactics import (
            ImpliesClassification,
            select_implies_tactic,
        )
        # ``result`` has no annotation — it could be a list / dict /
        # custom class.  The classifier must NOT report linear-arith.
        plan = select_implies_tactic("True", "result > 0", py_types={})
        assert plan.classification is not ImpliesClassification.LINEAR_ARITH

    def test_annotated_int_is_linear(self):
        from deppy.lean.implies_tactics import (
            ImpliesClassification,
            select_implies_tactic,
        )
        plan = select_implies_tactic(
            "x > 0", "x >= 0",
            py_types={"x": "int"},
        )
        assert plan.classification is ImpliesClassification.LINEAR_ARITH


# ─────────────────────────────────────────────────────────────────────
#  Cheat #6 — source_id parsing fail-loud
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat6_SourceIdParsing:
    def test_parse_canonical_form(self):
        from deppy.pipeline.assert_safety import _parse_source_id
        result = _parse_source_id("divide:L4:ZERO_DIVISION")
        assert result == ("divide", 4, "ZERO_DIVISION")

    def test_parse_failure_is_None(self):
        from deppy.pipeline.assert_safety import _parse_source_id
        # Round 1 silently returned an empty tuple; round 2 returns
        # None so callers can distinguish parse failure.
        assert _parse_source_id("malformed") is None
        assert _parse_source_id("") is None
        assert _parse_source_id("fn:no_lineno:KIND") is None
        assert _parse_source_id("fn:Lnotanint:KIND") is None

    def test_source_with_no_guards_is_NOT_dependent(self):
        # Round 1 conflated "couldn't parse" with "no guards" and
        # treated both as dependent (over-conservative).  Round 2
        # treats "no guards" as definitively NOT dependent.
        from dataclasses import dataclass, field
        from deppy.pipeline.assert_safety import (
            discharge_depends_on_assert,
        )

        @dataclass
        class _Inner:
            pass

        class Z3Proof(_Inner):
            pass

        @dataclass
        class _Discharge:
            source_id: str
            inner: _Inner

        @dataclass
        class _Fact:
            source_lineno: int
            source_col: int
            source_kind: str
            guards: tuple = ()

        @dataclass
        class _RM:
            used_assert_narrowing: bool = True
            assert_derived_guards: set = field(default_factory=set)
            per_source: list = field(default_factory=list)

        rmap = _RM(
            used_assert_narrowing=True,
            assert_derived_guards={"k != 0"},
            per_source=[
                _Fact(10, 0, "INDEX_ERROR", ()),  # NO guards
            ],
        )
        d = _Discharge("f:L10:INDEX_ERROR", Z3Proof())
        assert not discharge_depends_on_assert(d, rmap)


# ─────────────────────────────────────────────────────────────────────
#  Cheat #7 — visit_Compare doesn't default to dict
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat7_NoDictDefault:
    def test_unannotated_in_does_not_force_dict(self):
        from deppy.lean.body_translation import infer_locals_types
        fn = ast.parse(textwrap.dedent("""
            def f(d, k):
                return k in d
        """)).body[0]
        types = infer_locals_types(fn)
        # d is NOT classified as dict.
        assert types.get("d", "") != "dict"


# ─────────────────────────────────────────────────────────────────────
#  Cheat #8 — substitute_result_lean is fully AST-based
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat8_NoStrReplaceInLeanForm:
    def test_lean_form_via_pure_ast(self):
        from deppy.lean.result_substitution import substitute_result_lean
        # Round 1 used a placeholder + str.replace.  Round 2 uses
        # a custom AST unparser.  Both produce ``(f x)`` for
        # ``result`` with arg ``x``.
        out = substitute_result_lean(
            "result > 0", fn_name="f", arg_names=["x"],
        )
        assert "(f x)" in out

    def test_lean_form_preserves_string_literal(self):
        from deppy.lean.result_substitution import substitute_result_lean
        out = substitute_result_lean(
            "result > 0 and 'result' in xs",
            fn_name="f", arg_names=["x"],
        )
        assert "(f x)" in out
        assert "'result'" in out

    def test_lean_form_no_substring_substitution(self):
        from deppy.lean.result_substitution import substitute_result_lean
        out = substitute_result_lean(
            "result_count == 3 and result > 0",
            fn_name="f", arg_names=["x"],
        )
        assert "result_count" in out  # untouched
        assert "(f x)" in out


# ─────────────────────────────────────────────────────────────────────
#  Cheat #9 — _constrain_list_or_dict no longer defaults to list
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat9_NoListDefault:
    def test_unannotated_len_does_not_default_to_list(self):
        from deppy.lean.body_translation import infer_locals_types
        fn = ast.parse(textwrap.dedent("""
            def f(x):
                return len(x)
        """)).body[0]
        types = infer_locals_types(fn)
        # x is NOT classified as list — could be str/dict/set/list.
        assert types.get("x", "") != "list"


# ─────────────────────────────────────────────────────────────────────
#  Cheat #10 — xs.pop() returns an element
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat10_PopSemantics:
    def test_pop_no_args_returns_element(self):
        from deppy.lean.body_translation import translate_body
        fn = ast.parse(textwrap.dedent("""
            def f(xs: list[int]) -> int:
                return xs.pop()
        """)).body[0]
        bt = translate_body(fn)
        # Round 1 emitted ``xs.dropLast`` (returns list — wrong type).
        # Round 2 emits ``xs.getLast!`` (returns element — correct).
        assert "getLast" in bt.lean_text
        assert "dropLast" not in bt.lean_text


# ─────────────────────────────────────────────────────────────────────
#  Cheat #11 — AESOP_LIKELY removed; honest sorry
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat11_NoAesopLikelyDressedAsConfidence:
    def test_aesop_classification_never_chosen(self):
        # Round 1 emitted ``intros; aesop`` for any goal under 50
        # AST nodes that lacked function calls.  Round 2 removed
        # this fall-back: the AESOP_LIKELY classification is no
        # longer reachable from ``select_implies_tactic``.
        from deppy.lean.implies_tactics import (
            ImpliesClassification,
            select_implies_tactic,
        )
        # Try a variety of goals — none should land on AESOP_LIKELY.
        for pre, post in [
            ("P", "Q"),
            ("a > 0", "b < 100"),
            ("True", "x ≠ 0"),
            ("hasattr(x, 'y')", "hasattr(x, 'z')"),
        ]:
            plan = select_implies_tactic(pre, post)
            assert plan.classification is not ImpliesClassification.AESOP_LIKELY, (
                f"AESOP_LIKELY leaked into plan for {pre!r}/{post!r}"
            )

    def test_no_aesop_in_tactic_text_at_all(self):
        # The tactic ``aesop`` should never appear in the
        # generated tactic text.
        from deppy.lean.implies_tactics import select_implies_tactic
        for pre, post in [
            ("P", "Q"),
            ("hasattr(x, 'y')", "True"),
        ]:
            plan = select_implies_tactic(pre, post)
            assert "aesop" not in plan.tactic_text


# ─────────────────────────────────────────────────────────────────────
#  Cheat #12 — alias call now reports arg aliases for unknowns
# ─────────────────────────────────────────────────────────────────────


class TestRound2Cheat12_AliasFromUnknownFunctions:
    def test_unknown_function_aliases_args(self):
        from deppy.pipeline.alias_analysis import (
            AliasTable,
            update_for_stmt,
        )
        # ``y = unknown_fn(xs)`` — round 1 returned no aliases
        # (assumed fresh).  Round 2 reports y may alias xs because
        # the unknown function might return its argument.
        stmt = ast.parse("y = unknown_fn(xs)").body[0]
        t = update_for_stmt(AliasTable.empty(), stmt)
        # The safe direction: y MAY alias xs.
        assert t.may_alias("y", "xs")

    def test_unknown_method_aliases_recv_AND_args(self):
        from deppy.pipeline.alias_analysis import (
            AliasTable,
            update_for_stmt,
        )
        # ``y = builder.frob(xs)`` — round 1 reported builder only.
        # Round 2 reports both builder and xs (the arg might be
        # passed through).
        stmt = ast.parse("y = builder.frob(xs)").body[0]
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("y", "builder")
        assert t.may_alias("y", "xs")

    def test_known_fresh_function_no_alias(self):
        from deppy.pipeline.alias_analysis import (
            AliasTable,
            update_for_stmt,
        )
        # ``y = list(xs)`` — explicitly fresh.
        stmt = ast.parse("y = list(xs)").body[0]
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert not t.may_alias("y", "xs")
