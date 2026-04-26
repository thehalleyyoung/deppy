"""Audit fix #11 — AST-based ``result`` substitution in @implies.

Locks down that the substitution:

* Replaces every free ``result`` reference with the function-call
  expression.
* Does NOT rewrite ``result`` *inside string literals*.
* Does NOT rewrite ``result_count``, ``my_result``, ``results``, or
  any identifier that merely contains the substring ``result``.
* Does NOT rewrite shadowed bindings (lambda / comprehension
  binders that re-bind ``result``).
* Returns the original text unmodified when the predicate fails to
  parse (with ``parse_failed=True`` on the structured result).
"""
from __future__ import annotations

from deppy.lean.result_substitution import (
    SubstitutionResult,
    count_result_references,
    references_result,
    substitute_result,
    substitute_result_detailed,
    substitute_result_lean,
)


# ─────────────────────────────────────────────────────────────────────
#  Basic substitutions
# ─────────────────────────────────────────────────────────────────────


class TestBasicSubstitution:
    def test_simple_result_reference(self):
        out = substitute_result(
            "result > 0", fn_name="f", arg_names=["x"],
        )
        # The substituted form is ``f(x) > 0`` (Python syntax).
        assert "f(x)" in out
        assert "result" not in out

    def test_no_args(self):
        out = substitute_result(
            "result == 42", fn_name="constant", arg_names=[],
        )
        assert "constant" in out
        assert "result" not in out

    def test_no_result_reference(self):
        out = substitute_result(
            "x > 0", fn_name="f", arg_names=["x"],
        )
        # Unchanged when there's no ``result``.
        assert "x > 0" in out

    def test_multiple_args(self):
        out = substitute_result(
            "result > 0", fn_name="add", arg_names=["a", "b"],
        )
        # ``add(a, b)`` Python form.
        assert "add(a, b)" in out


# ─────────────────────────────────────────────────────────────────────
#  String-literal safety
# ─────────────────────────────────────────────────────────────────────


class TestStringLiteralSafety:
    def test_string_literal_not_rewritten(self):
        out = substitute_result(
            "'result' in xs", fn_name="f", arg_names=["x"],
        )
        # The literal 'result' must remain.
        assert "'result'" in out

    def test_literal_with_substring(self):
        out = substitute_result(
            "msg == 'result is positive'", fn_name="f", arg_names=[],
        )
        # The string is unchanged.
        assert "'result is positive'" in out

    def test_mixed_literal_and_reference(self):
        out = substitute_result(
            "result > 0 and 'result' in xs",
            fn_name="f", arg_names=["x"],
        )
        # The first ``result`` is rewritten; the literal isn't.
        assert "f(x)" in out
        assert "'result'" in out


# ─────────────────────────────────────────────────────────────────────
#  Identifier-boundary safety
# ─────────────────────────────────────────────────────────────────────


class TestIdentifierBoundary:
    def test_result_count_not_rewritten(self):
        # The variable ``result_count`` is a different identifier.
        out = substitute_result(
            "result_count > 0",
            fn_name="f", arg_names=["x"],
        )
        # ``result_count`` is preserved as a single identifier.
        assert "result_count" in out
        # We must NOT have produced ``f(x)_count`` etc.
        assert "f(x)_count" not in out

    def test_my_result_not_rewritten(self):
        out = substitute_result(
            "my_result > 0", fn_name="f", arg_names=["x"],
        )
        assert "my_result" in out

    def test_results_not_rewritten(self):
        # Plural ``results``.
        out = substitute_result(
            "len(results) == 3", fn_name="f", arg_names=["x"],
        )
        assert "results" in out

    def test_kwarg_named_result(self):
        # Function call with ``result=`` kwarg — but in expression
        # context ``result=value`` isn't allowed (only in function
        # signatures), so we skip this case.
        pass


# ─────────────────────────────────────────────────────────────────────
#  Container / nested forms
# ─────────────────────────────────────────────────────────────────────


class TestContainerForms:
    def test_result_in_list(self):
        out = substitute_result(
            "[result, 1, 2]", fn_name="f", arg_names=["x"],
        )
        assert "f(x)" in out

    def test_result_in_call(self):
        out = substitute_result(
            "isinstance(result, int)",
            fn_name="f", arg_names=["x"],
        )
        assert "f(x)" in out

    def test_result_attribute(self):
        out = substitute_result(
            "result.length > 0", fn_name="f", arg_names=["x"],
        )
        assert "f(x).length" in out

    def test_result_subscript(self):
        out = substitute_result(
            "result[0] > 0", fn_name="f", arg_names=["x"],
        )
        assert "f(x)" in out
        assert "[0]" in out

    def test_result_in_call_arg(self):
        out = substitute_result(
            "g(result, 3)", fn_name="f", arg_names=["x"],
        )
        assert "f(x)" in out

    def test_compound_predicate(self):
        out = substitute_result(
            "result > 0 and result < 100",
            fn_name="f", arg_names=["x"],
        )
        # Both occurrences rewritten.
        assert out.count("f(x)") == 2


# ─────────────────────────────────────────────────────────────────────
#  Shadowing
# ─────────────────────────────────────────────────────────────────────


class TestShadowing:
    def test_lambda_shadowing(self):
        # Inside ``lambda result: result + 1``, the inner ``result``
        # is shadowed.  We don't rewrite there.
        out = substitute_result(
            "(lambda result: result + 1)(3) == 4",
            fn_name="f", arg_names=["x"],
        )
        # The function call ``f(x)`` should NOT appear — the
        # ``result`` is shadowed.
        assert "f(x)" not in out
        # The lambda body is preserved.
        assert "result + 1" in out

    def test_comprehension_shadowing(self):
        out = substitute_result(
            "[result for result in xs if result > 0]",
            fn_name="f", arg_names=["x"],
        )
        # ``result`` is bound by the comprehension; we leave it alone.
        assert "f(x)" not in out

    def test_unshadowed_after_lambda(self):
        # ``result`` inside the lambda is shadowed; outside is free.
        out = substitute_result(
            "(lambda y: y)(result) > 0",
            fn_name="f", arg_names=["x"],
        )
        # The outer ``result`` is rewritten.
        assert "f(x)" in out


# ─────────────────────────────────────────────────────────────────────
#  Error handling
# ─────────────────────────────────────────────────────────────────────


class TestErrorHandling:
    def test_unparseable_returns_original(self):
        # Python doesn't allow ``a >>> b`` as an expression.
        bad = "a >>> b"
        out = substitute_result_detailed(
            bad, fn_name="f", arg_names=["x"],
        )
        assert out.parse_failed
        assert out.text == bad

    def test_empty_post_returns_True(self):
        out = substitute_result_detailed(
            "", fn_name="f", arg_names=["x"],
        )
        assert out.text == "True"
        assert out.occurrences == 0


# ─────────────────────────────────────────────────────────────────────
#  Lean-form helper
# ─────────────────────────────────────────────────────────────────────


class TestLeanForm:
    def test_lean_form_uses_prefix_call(self):
        out = substitute_result_lean(
            "result > 0", fn_name="f", arg_names=["x"],
        )
        # Lean prefix-call form: ``(f x)``.
        assert "(f x)" in out

    def test_lean_form_no_args(self):
        out = substitute_result_lean(
            "result > 0", fn_name="constant", arg_names=[],
        )
        assert "constant" in out

    def test_lean_form_multiple_args(self):
        out = substitute_result_lean(
            "result == a + b", fn_name="add", arg_names=["a", "b"],
        )
        assert "(add a b)" in out

    def test_lean_form_preserves_literal(self):
        out = substitute_result_lean(
            "result > 0 and 'result' in xs",
            fn_name="f", arg_names=["x"],
        )
        assert "(f x)" in out
        assert "'result'" in out


# ─────────────────────────────────────────────────────────────────────
#  Detection helpers
# ─────────────────────────────────────────────────────────────────────


class TestDetection:
    def test_references_result(self):
        assert references_result("result > 0")
        assert references_result("len(result) > 0")
        assert not references_result("x > 0")
        # The literal isn't a reference.
        assert not references_result("'result' in xs")

    def test_count_result_references(self):
        assert count_result_references("result > 0") == 1
        assert count_result_references("result > 0 and result < 100") == 2
        assert count_result_references("x > 0") == 0
        # Lambda binder shadows.
        assert count_result_references(
            "(lambda result: result + 1)(3)",
        ) == 0

    def test_unparseable_returns_zero(self):
        assert count_result_references("a >>> b") == 0

    def test_does_not_count_substring(self):
        # ``my_result`` is a different identifier.
        assert count_result_references("my_result > 0") == 0


# ─────────────────────────────────────────────────────────────────────
#  Critical regression — the str.replace cheat is no more
# ─────────────────────────────────────────────────────────────────────


class TestStrReplaceCheatRegression:
    """Audit fix #11 — make sure the substitution is AST-based, not
    text-based.  These would have been broken by the old code."""

    def test_no_substring_replacement(self):
        """Old: ``result_count > 0`` → ``f(x)_count > 0`` (broken)."""
        out = substitute_result(
            "result_count > 0", fn_name="f", arg_names=["x"],
        )
        assert "f(x)_count" not in out
        assert "result_count" in out

    def test_no_string_literal_replacement(self):
        """Old: ``'result'`` inside a string was rewritten."""
        out = substitute_result(
            "x == 'result'", fn_name="f", arg_names=["a"],
        )
        assert "'f(a)'" not in out
        assert "'result'" in out

    def test_no_replacement_inside_double_quoted_string(self):
        out = substitute_result(
            'x == "result"', fn_name="f", arg_names=["a"],
        )
        # The literal is preserved (after AST round-trip it may use
        # different quote style, but the content stays).
        assert "result" in out
        # Ensure we didn't rewrite into ``"f(a)"``.
        assert '"f(a)"' not in out
