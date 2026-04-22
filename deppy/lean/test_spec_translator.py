"""
Tests for deppy.lean.spec_translator — Python spec → Lean 4 propositions.

Run with:
    cd /Users/halleyyoung/Documents/div/mathdivergence/deppy
    PYTHONPATH=.:src python3 -m pytest deppy/lean/test_spec_translator.py -v
"""
from __future__ import annotations

import typing
from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, List, Optional, Set, Tuple

import pytest

from deppy.lean.spec_translator import (
    LeanFunctionSig,
    LeanTheorem,
    translate_function_sig,
    translate_guarantee,
    translate_python_type,
    translate_requires,
)


# ═══════════════════════════════════════════════════════════════════
#  §1  translate_python_type
# ═══════════════════════════════════════════════════════════════════

class TestTranslatePythonType:
    """Tests for Python type → Lean 4 type translation."""

    def test_int(self):
        assert translate_python_type(int) == "Int"

    def test_float(self):
        assert translate_python_type(float) == "Float"

    def test_bool(self):
        assert translate_python_type(bool) == "Bool"

    def test_str(self):
        assert translate_python_type(str) == "String"

    def test_none(self):
        assert translate_python_type(None) == "Unit"

    def test_nonetype(self):
        assert translate_python_type(type(None)) == "Unit"

    def test_list_int(self):
        assert translate_python_type(list[int]) == "List Int"

    def test_list_str(self):
        assert translate_python_type(list[str]) == "List String"

    def test_list_nested(self):
        assert translate_python_type(list[list[int]]) == "List (List Int)"

    def test_bare_list(self):
        assert translate_python_type(list) == "List Int"

    def test_dict_int_str(self):
        assert translate_python_type(dict[int, str]) == "Int → String"

    def test_bare_dict(self):
        assert translate_python_type(dict) == "Int → Int"

    def test_tuple_int_bool(self):
        assert translate_python_type(tuple[int, bool]) == "Int × Bool"

    def test_bare_tuple(self):
        assert translate_python_type(tuple) == "Int × Int"

    def test_optional_int(self):
        result = translate_python_type(Optional[int])
        assert result == "Option Int"

    def test_set_int(self):
        assert translate_python_type(set[int]) == "Finset Int"

    def test_bare_set(self):
        assert translate_python_type(set) == "Finset Int"

    def test_callable_int_to_bool(self):
        result = translate_python_type(Callable[[int], bool])
        assert result == "Int → Bool"

    def test_callable_two_args(self):
        result = translate_python_type(Callable[[int, str], bool])
        assert result == "Int → String → Bool"

    # ── String annotation forms ──

    def test_str_annotation_int(self):
        assert translate_python_type("int") == "Int"

    def test_str_annotation_none(self):
        assert translate_python_type("None") == "Unit"

    def test_str_annotation_list_int(self):
        assert translate_python_type("list[int]") == "List Int"

    def test_str_annotation_optional(self):
        assert translate_python_type("Optional[int]") == "Option Int"

    def test_str_annotation_dict(self):
        assert translate_python_type("dict[str, int]") == "String → Int"

    def test_str_annotation_tuple(self):
        assert translate_python_type("tuple[int, bool]") == "Int × Bool"

    def test_str_annotation_set(self):
        assert translate_python_type("set[int]") == "Finset Int"


# ═══════════════════════════════════════════════════════════════════
#  §2  translate_guarantee
# ═══════════════════════════════════════════════════════════════════

class TestTranslateGuarantee:
    """Tests for guarantee string → Lean proposition translation."""

    def _g(self, spec: str, params=None, ptypes=None, rtype=None):
        return translate_guarantee(
            spec,
            func_name="f",
            param_names=params or ["x"],
            param_types=ptypes or {"x": int},
            return_type=rtype or int,
        )

    def test_result_geq_zero(self):
        thm = self._g("result >= 0")
        assert thm.conclusion == "0 ≤ (f x)"
        assert thm.proof == "by omega"

    def test_result_gt_zero(self):
        thm = self._g("result > 0")
        assert thm.conclusion == "0 < (f x)"
        assert thm.proof == "by omega"

    def test_result_leq_zero(self):
        thm = self._g("result <= 0")
        assert thm.conclusion == "(f x) ≤ 0"

    def test_result_lt_zero(self):
        thm = self._g("result < 0")
        assert thm.conclusion == "(f x) < 0"

    def test_sorted(self):
        thm = self._g("result is sorted", params=["xs"], ptypes={"xs": list[int]},
                       rtype=list[int])
        assert thm.conclusion == "List.Sorted (· ≤ ·) (f xs)"

    def test_nodup(self):
        thm = self._g("result has no duplicates", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "(f xs).Nodup"

    def test_permutation(self):
        thm = self._g("result is a permutation of xs", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "(f xs).Perm xs"

    def test_len_eq(self):
        thm = self._g("len(result) == len(xs)", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "(f xs).length = xs.length"

    def test_result_eq(self):
        thm = self._g("result == 42")
        assert thm.conclusion == "(f x) = 42"

    def test_nonempty(self):
        thm = self._g("result is non-empty", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "(f xs) ≠ []"

    def test_nonempty_hyphenated(self):
        thm = self._g("result is nonempty", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "(f xs) ≠ []"

    def test_contains(self):
        thm = self._g("result contains x", params=["x"],
                       ptypes={"x": int}, rtype=list[int])
        assert thm.conclusion == "x ∈ (f x)"

    def test_forall(self):
        thm = self._g("for all x in result, x > 0", params=["xs"],
                       ptypes={"xs": list[int]}, rtype=list[int])
        assert thm.conclusion == "∀ x ∈ (f xs), 0 < x"

    def test_subset(self):
        thm = self._g("result is a subset of s", params=["s"],
                       ptypes={"s": set[int]}, rtype=set[int])
        assert thm.conclusion == "(f s) ⊆ s"

    def test_result_geq_param(self):
        thm = self._g("result >= n", params=["n"], ptypes={"n": int}, rtype=int)
        assert thm.conclusion == "n ≤ (f n)"

    def test_result_gt_param(self):
        thm = self._g("result > n", params=["n"], ptypes={"n": int}, rtype=int)
        assert thm.conclusion == "n < (f n)"

    def test_unparseable_guarantee(self):
        thm = self._g("result is a banana split sundae")
        assert "sorry" in thm.conclusion
        assert "banana split sundae" in thm.conclusion
        assert thm.proof == "sorry"
        assert thm.comment == "result is a banana split sundae"

    def test_theorem_name(self):
        thm = self._g("result >= 0")
        assert thm.name == "f_spec"

    def test_params_in_theorem(self):
        thm = self._g("result >= 0", params=["n"], ptypes={"n": int})
        assert "(n : Int)" in thm.params

    def test_multi_param(self):
        thm = translate_guarantee(
            "result >= 0",
            func_name="add",
            param_names=["a", "b"],
            param_types={"a": int, "b": int},
            return_type=int,
        )
        assert thm.conclusion == "0 ≤ (add a b)"
        assert "(a : Int)" in thm.params
        assert "(b : Int)" in thm.params


# ═══════════════════════════════════════════════════════════════════
#  §3  translate_requires
# ═══════════════════════════════════════════════════════════════════

class TestTranslateRequires:
    """Tests for precondition → Lean hypothesis translation."""

    def _r(self, spec: str, params=None, ptypes=None):
        return translate_requires(
            spec,
            param_names=params or ["n"],
            param_types=ptypes or {"n": int},
        )

    def test_n_gt_zero(self):
        assert self._r("n > 0") == "(h : 0 < n)"

    def test_n_geq_zero(self):
        assert self._r("n >= 0") == "(h : 0 ≤ n)"

    def test_xs_nonempty(self):
        result = self._r("xs is non-empty", params=["xs"], ptypes={"xs": list[int]})
        assert result == "(h : xs ≠ [])"

    def test_xs_nonempty_no_hyphen(self):
        result = self._r("xs is nonempty", params=["xs"], ptypes={"xs": list[int]})
        assert result == "(h : xs ≠ [])"

    def test_x_in_xs(self):
        result = self._r("x in xs", params=["x", "xs"],
                          ptypes={"x": int, "xs": list[int]})
        assert result == "(h : x ∈ xs)"

    def test_n_gt_m(self):
        result = self._r("n > m", params=["n", "m"],
                          ptypes={"n": int, "m": int})
        assert result == "(h : m < n)"

    def test_n_leq_m(self):
        result = self._r("n <= m", params=["n", "m"],
                          ptypes={"n": int, "m": int})
        assert result == "(h : n ≤ m)"

    def test_len_xs_gt_zero(self):
        result = self._r("len(xs) > 0", params=["xs"],
                          ptypes={"xs": list[int]})
        assert result == "(h : 0 < xs.length)"

    def test_len_xs_eq_n(self):
        result = self._r("len(xs) == n", params=["xs", "n"],
                          ptypes={"xs": list[int], "n": int})
        assert result == "(h : xs.length = n)"

    def test_unparseable_requires(self):
        result = self._r("the moon is full")
        assert "sorry" in result
        assert "the moon is full" in result


# ═══════════════════════════════════════════════════════════════════
#  §4  LeanTheorem.render
# ═══════════════════════════════════════════════════════════════════

class TestLeanTheoremRender:
    """Tests for theorem rendering to Lean 4 text."""

    def test_basic_render(self):
        thm = LeanTheorem(
            name="f_spec",
            params=["(x : Int)"],
            preconditions=[],
            conclusion="0 ≤ (f x)",
            proof="by omega",
            comment="result >= 0",
        )
        rendered = thm.render()
        assert 'theorem f_spec' in rendered
        assert '(x : Int)' in rendered
        assert '0 ≤ (f x)' in rendered
        assert 'by omega' in rendered
        assert '-- Original: "result >= 0"' in rendered

    def test_with_preconditions(self):
        thm = LeanTheorem(
            name="f_spec",
            params=["(n : Int)"],
            preconditions=["(h : 0 < n)"],
            conclusion="0 < (f n)",
            proof="by omega",
        )
        rendered = thm.render()
        assert "(h : 0 < n)" in rendered

    def test_no_comment(self):
        thm = LeanTheorem(
            name="t",
            params=[],
            preconditions=[],
            conclusion="True",
            proof="trivial",
        )
        rendered = thm.render()
        assert "Original" not in rendered


# ═══════════════════════════════════════════════════════════════════
#  §5  translate_function_sig
# ═══════════════════════════════════════════════════════════════════

class TestTranslateFunctionSig:
    """Tests for full function → Lean signature translation."""

    def test_simple_function(self):
        def square(n: int) -> int:
            return n * n

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or ["result >= 0"]
                self.preconditions = self.preconditions or []

        sig = translate_function_sig(square, FakeSpec())
        assert sig.name == "square"
        assert "(n : Int)" in sig.params
        assert sig.return_type == "Int"
        assert len(sig.theorems) == 1
        assert sig.theorems[0].conclusion == "0 ≤ (square n)"

    def test_multiple_guarantees(self):
        def my_sort(xs: list[int]) -> list[int]:
            return sorted(xs)

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or [
                    "result is sorted",
                    "result is a permutation of xs",
                    "len(result) == len(xs)",
                ]
                self.preconditions = self.preconditions or []

        sig = translate_function_sig(my_sort, FakeSpec())
        assert len(sig.theorems) == 3
        assert sig.theorems[0].name == "my_sort_spec"
        assert sig.theorems[1].name == "my_sort_spec_1"
        assert sig.theorems[2].name == "my_sort_spec_2"
        assert "Sorted" in sig.theorems[0].conclusion
        assert "Perm" in sig.theorems[1].conclusion
        assert "length" in sig.theorems[2].conclusion

    def test_with_preconditions(self):
        def head(xs: list[int]) -> int:
            return xs[0]

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or ["result contains x"]
                self.preconditions = self.preconditions or ["xs is non-empty"]

        sig = translate_function_sig(head, FakeSpec(
            guarantees=["result >= 0"],
            preconditions=["xs is non-empty"],
        ))
        assert len(sig.preconditions) == 1
        assert "xs ≠ []" in sig.preconditions[0]

    def test_untyped_params(self):
        def mystery(x, y):
            return x + y

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or ["result >= 0"]
                self.preconditions = self.preconditions or []

        sig = translate_function_sig(mystery, FakeSpec())
        # Should use Greek letters for untyped params
        assert "(x : α)" in sig.params
        assert "(y : β)" in sig.params

    def test_render_output(self):
        def inc(n: int) -> int:
            return n + 1

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or ["result > 0"]
                self.preconditions = self.preconditions or ["n >= 0"]

        sig = translate_function_sig(inc, FakeSpec())
        rendered = sig.render()
        assert "def inc" in rendered
        assert "theorem" in rendered

    def test_no_guarantees(self):
        def noop() -> None:
            pass

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or []
                self.preconditions = self.preconditions or []

        sig = translate_function_sig(noop, FakeSpec())
        assert sig.return_type == "Unit"
        assert len(sig.theorems) == 0

    def test_deppy_spec_attribute(self):
        """When spec_metadata is None, read fn._deppy_spec."""
        def f(x: int) -> int:
            return x

        @dataclass
        class FakeSpec:
            guarantees: list = None
            preconditions: list = None
            def __post_init__(self):
                self.guarantees = self.guarantees or ["result >= 0"]
                self.preconditions = self.preconditions or []

        f._deppy_spec = FakeSpec()
        sig = translate_function_sig(f)
        assert len(sig.theorems) == 1


# ═══════════════════════════════════════════════════════════════════
#  §6  Edge cases
# ═══════════════════════════════════════════════════════════════════

class TestEdgeCases:
    """Edge cases and integration-level tests."""

    def test_guarantee_with_param_refs(self):
        """Guarantees that reference specific parameter names."""
        thm = translate_guarantee(
            "result == len(xs)",
            func_name="count",
            param_names=["xs"],
            param_types={"xs": list[int]},
            return_type=int,
        )
        assert "(count xs) = xs.length" == thm.conclusion

    def test_every_guarantee_produces_output(self):
        """NEVER silently drop a guarantee."""
        specs = [
            "result >= 0",
            "result is sorted",
            "result has no duplicates",
            "something totally weird and unparseable!!!",
            "result is a permutation of xs",
        ]
        for spec in specs:
            thm = translate_guarantee(
                spec,
                func_name="f",
                param_names=["xs"],
                param_types={"xs": list[int]},
                return_type=list[int],
            )
            assert thm is not None, f"Guarantee dropped: {spec}"
            assert thm.conclusion, f"Empty conclusion for: {spec}"

    def test_unparseable_has_sorry_and_comment(self):
        """Unknown patterns → sorry with original text."""
        thm = translate_guarantee(
            "result satisfies the Riemann hypothesis",
            func_name="f",
            param_names=["x"],
            param_types={"x": int},
            return_type=int,
        )
        assert "sorry" in thm.conclusion
        assert "Riemann hypothesis" in thm.conclusion
        assert thm.proof == "sorry"
        assert thm.comment == "result satisfies the Riemann hypothesis"

    def test_forall_with_predicate(self):
        thm = translate_guarantee(
            "for all x in result, x >= 0",
            func_name="f",
            param_names=["xs"],
            param_types={"xs": list[int]},
            return_type=list[int],
        )
        assert "∀ x ∈ (f xs), 0 ≤ x" == thm.conclusion

    def test_optional_return_type(self):
        sig_result = translate_python_type(Optional[str])
        assert sig_result == "Option String"

    def test_complex_callable(self):
        t = Callable[[int, int], bool]
        result = translate_python_type(t)
        assert result == "Int → Int → Bool"

    def test_dict_string_list(self):
        result = translate_python_type(dict[str, list[int]])
        assert result == "String → List Int"
