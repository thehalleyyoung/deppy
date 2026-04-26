"""Audit fix #6 — type-aware body translation.

Locks down the behaviour that ``len(xs)``, ``xs in d``, ``xs[i]``, and
method calls are translated through the right Lean idiom *based on
the inferred type of the receiver*.

Cases covered:

* ``len(xs)`` where ``xs : list[int]`` → ``xs.length``;
* ``len(d)`` where ``d : dict[str, int]`` → ``d.size``;
* ``len(s)`` where ``s : str`` → ``s.length``;
* ``len(s)`` where ``s : set[int]`` → ``s.toList.length``;
* ``x in d`` (dict) → ``d.contains x``;
* ``x in xs`` (list) → ``xs.contains x``;
* ``x in s`` (set) → ``x ∈ s``;
* ``xs[i]`` (list, int idx) → ``xs.get! i.toNat``;
* ``d[k]`` (dict) → ``d.find! k``;
* ``xs[:n]`` / ``xs[n:]`` / ``xs[i:j]`` (list);
* method calls: ``.append`` → ``.concat``, ``.keys`` → ``.keys``,
  ``.upper`` → ``.toUpper``, ``.add`` (set) → ``.insert``;
* equality: ``a == b`` for ints → ``==``; for lists → ``=``;
* ``infer_function_signature`` returns the inferred return type when
  no explicit ``-> T`` annotation is present.

Inference itself is also tested: parameters with no annotation are
inferred from their use; body locals are inferred through ``Assign``,
``AnnAssign``, and ``AugAssign``.
"""
from __future__ import annotations

import ast
import textwrap

from deppy.lean.body_translation import (
    BodyTranslation,
    infer_function_signature,
    infer_locals_types,
    translate_body,
)


def _parse_fn(src: str) -> ast.FunctionDef:
    """Parse one top-level function from ``src`` and return its node."""
    src = textwrap.dedent(src)
    mod = ast.parse(src)
    for node in mod.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node  # type: ignore[return-value]
    raise AssertionError(f"no function in source: {src!r}")


# ─────────────────────────────────────────────────────────────────────
#  Inference primitives
# ─────────────────────────────────────────────────────────────────────


class TestInferLocalsTypes:
    def test_explicit_param_annotation_seeds_inference(self):
        fn = _parse_fn("""
            def f(xs: list[int]) -> int:
                return len(xs)
        """)
        types = infer_locals_types(fn)
        assert types["xs"] == "list[int]"

    def test_param_types_argument_overrides_seed(self):
        fn = _parse_fn("""
            def f(xs):
                return len(xs)
        """)
        types = infer_locals_types(fn, param_types={"xs": "list[str]"})
        assert types["xs"] == "list[str]"

    def test_unannotated_param_inferred_from_method(self):
        fn = _parse_fn("""
            def f(xs):
                xs.append(3)
                return xs
        """)
        types = infer_locals_types(fn)
        assert types["xs"] == "list"

    def test_unannotated_param_inferred_from_dict_op(self):
        fn = _parse_fn("""
            def f(d):
                return d.keys()
        """)
        types = infer_locals_types(fn)
        assert types["d"] == "dict"

    def test_unannotated_param_inferred_from_in(self):
        fn = _parse_fn("""
            def f(d, k):
                return k in d
        """)
        types = infer_locals_types(fn)
        # ``k in d`` constrains d to dict (most common idiom).
        assert types["d"] == "dict"

    def test_assign_propagates_type(self):
        fn = _parse_fn("""
            def f():
                x = 3
                y = "hello"
                z = []
                return x
        """)
        types = infer_locals_types(fn)
        assert types["x"] == "int"
        assert types["y"] == "str"
        assert types["z"].startswith("list")

    def test_annassign_propagates_type(self):
        fn = _parse_fn("""
            def f():
                xs: list[int] = []
                return xs
        """)
        types = infer_locals_types(fn)
        assert types["xs"] == "list[int]"

    def test_augassign_first_use_seeds_type(self):
        fn = _parse_fn("""
            def f():
                count = 0
                count += 1
                return count
        """)
        types = infer_locals_types(fn)
        assert types["count"] == "int"

    def test_subscript_str_key_implies_dict(self):
        fn = _parse_fn("""
            def f(d):
                return d["x"]
        """)
        types = infer_locals_types(fn)
        assert types["d"] == "dict"

    def test_subscript_int_idx_implies_list(self):
        fn = _parse_fn("""
            def f(xs):
                return xs[0]
        """)
        types = infer_locals_types(fn)
        assert types["xs"] == "list"

    def test_slice_implies_list(self):
        fn = _parse_fn("""
            def f(xs):
                return xs[1:3]
        """)
        types = infer_locals_types(fn)
        assert types["xs"] == "list"


# ─────────────────────────────────────────────────────────────────────
#  Function-signature inference
# ─────────────────────────────────────────────────────────────────────


class TestInferFunctionSignature:
    def test_explicit_return_annotation_used(self):
        fn = _parse_fn("""
            def f(xs: list[int]) -> int:
                return len(xs)
        """)
        binders, ret, _ = infer_function_signature(fn, type_context=None)
        assert "xs" in binders
        assert "List" in binders or "list" in binders.lower()
        assert "Int" in ret

    def test_implicit_return_inferred_from_body(self):
        fn = _parse_fn("""
            def mergesort(xs: list[int]):
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = mergesort(xs[:mid])
                right = mergesort(xs[mid:])
                return left + right
        """)
        binders, ret, _ = infer_function_signature(fn, type_context=None)
        # The body returns ``xs`` (list[int]) and ``left + right``
        # (a list), so the inferred return type should be List, not Int.
        assert "List" in ret, f"expected List in {ret}"

    def test_no_return_falls_back_to_unit_or_any(self):
        fn = _parse_fn("""
            def f(x: int):
                pass
        """)
        binders, ret, _ = infer_function_signature(fn, type_context=None)
        # ``pass`` body produces no returns; we accept any reasonable
        # fallback (``Unit`` / ``Any`` / ``Int``) — the contract is
        # "doesn't crash."
        assert isinstance(ret, str) and ret


# ─────────────────────────────────────────────────────────────────────
#  Body translation: typed lowering
# ─────────────────────────────────────────────────────────────────────


def _translate(src: str, **kw) -> BodyTranslation:
    return translate_body(_parse_fn(src), **kw)


class TestLenLowering:
    def test_len_on_list_uses_length(self):
        bt = _translate("""
            def f(xs: list[int]) -> int:
                return len(xs)
        """)
        assert "xs.length" in bt.lean_text
        assert ".size" not in bt.lean_text

    def test_len_on_dict_uses_size(self):
        bt = _translate("""
            def f(d: dict[str, int]) -> int:
                return len(d)
        """)
        assert "d.size" in bt.lean_text

    def test_len_on_str_uses_length(self):
        bt = _translate("""
            def f(s: str) -> int:
                return len(s)
        """)
        assert "s.length" in bt.lean_text

    def test_len_on_set_uses_tolist_length(self):
        bt = _translate("""
            def f(xs: set[int]) -> int:
                return len(xs)
        """)
        assert "toList.length" in bt.lean_text

    def test_len_on_unknown_falls_back_to_length(self):
        # No annotation, no constraining ops → falls back to .length.
        bt = _translate("""
            def f(xs):
                return len(xs)
        """)
        assert "xs.length" in bt.lean_text


class TestSubscriptLowering:
    def test_list_subscript_int_idx_uses_get(self):
        bt = _translate("""
            def f(xs: list[int]) -> int:
                return xs[0]
        """)
        assert "xs.get!" in bt.lean_text or "xs.get?" in bt.lean_text
        assert ".toNat" in bt.lean_text

    def test_dict_subscript_uses_find(self):
        bt = _translate("""
            def f(d: dict[str, int]) -> int:
                return d["x"]
        """)
        assert "d.find!" in bt.lean_text

    def test_list_slice_lower_only_uses_drop(self):
        bt = _translate("""
            def f(xs: list[int]) -> list[int]:
                return xs[3:]
        """)
        assert "xs.drop" in bt.lean_text

    def test_list_slice_upper_only_uses_take(self):
        bt = _translate("""
            def f(xs: list[int]) -> list[int]:
                return xs[:3]
        """)
        assert "xs.take" in bt.lean_text

    def test_list_slice_both_chains_drop_take(self):
        bt = _translate("""
            def f(xs: list[int]) -> list[int]:
                return xs[1:5]
        """)
        assert "drop" in bt.lean_text and "take" in bt.lean_text


class TestInLowering:
    def test_in_on_dict_uses_contains(self):
        bt = _translate("""
            def f(d: dict[str, int], k: str) -> bool:
                return k in d
        """)
        assert "d.contains" in bt.lean_text

    def test_not_in_on_dict_negates_contains(self):
        bt = _translate("""
            def f(d: dict[str, int], k: str) -> bool:
                return k not in d
        """)
        assert "d.contains" in bt.lean_text and "¬" in bt.lean_text

    def test_in_on_set_uses_membership(self):
        bt = _translate("""
            def f(s: set[int], x: int) -> bool:
                return x in s
        """)
        assert "∈" in bt.lean_text

    def test_in_on_list_uses_contains(self):
        bt = _translate("""
            def f(xs: list[int], x: int) -> bool:
                return x in xs
        """)
        assert "xs.contains" in bt.lean_text


class TestMethodLowering:
    def test_list_append(self):
        bt = _translate("""
            def f(xs: list[int]) -> list[int]:
                return xs.append(3)
        """)
        # We translate ``xs.append(3)`` as ``xs.concat 3``.
        assert "xs.concat" in bt.lean_text or "xs ++" in bt.lean_text

    def test_dict_get_with_default(self):
        bt = _translate("""
            def f(d: dict[str, int]) -> int:
                return d.get("x", 0)
        """)
        assert ".findD" in bt.lean_text or ".get" in bt.lean_text

    def test_dict_keys(self):
        bt = _translate("""
            def f(d: dict[str, int]) -> list[str]:
                return d.keys()
        """)
        assert "d.keys" in bt.lean_text

    def test_str_upper(self):
        bt = _translate("""
            def f(s: str) -> str:
                return s.upper()
        """)
        assert "s.toUpper" in bt.lean_text

    def test_str_lower(self):
        bt = _translate("""
            def f(s: str) -> str:
                return s.lower()
        """)
        assert "s.toLower" in bt.lean_text

    def test_set_add(self):
        bt = _translate("""
            def f(s: set[int]) -> set[int]:
                return s.add(3)
        """)
        assert "s.insert" in bt.lean_text

    def test_list_reverse(self):
        bt = _translate("""
            def f(xs: list[int]) -> list[int]:
                return xs.reverse()
        """)
        assert "xs.reverse" in bt.lean_text


class TestComparisonLowering:
    def test_list_equality_uses_propositional_eq(self):
        bt = _translate("""
            def f(xs: list[int], ys: list[int]) -> bool:
                return xs == ys
        """)
        # Lists use Lean's ``=`` (decidable), not ``==``.
        assert " = " in bt.lean_text or "(xs = ys)" in bt.lean_text

    def test_int_equality_uses_eqop(self):
        bt = _translate("""
            def f(a: int, b: int) -> bool:
                return a == b
        """)
        assert "==" in bt.lean_text

    def test_string_equality_uses_eq(self):
        bt = _translate("""
            def f(s: str, t: str) -> bool:
                return s == t
        """)
        assert " = " in bt.lean_text


class TestAssignmentTypePropagation:
    def test_assigned_list_drives_subsequent_len(self):
        bt = _translate("""
            def f(xs: list[int]) -> int:
                ys = sorted(xs)
                return len(ys)
        """)
        # ``ys = sorted(xs)`` → ys is a list; len(ys) → ys.length.
        assert "ys.length" in bt.lean_text

    def test_annassign_drives_lowering(self):
        bt = _translate("""
            def f(d: dict[str, int]) -> int:
                k: dict[str, int] = d
                return len(k)
        """)
        assert "k.size" in bt.lean_text


# ─────────────────────────────────────────────────────────────────────
#  End-to-end mergesort regression
# ─────────────────────────────────────────────────────────────────────


class TestMergesortEnd2End:
    """The canonical example from the audit: the mergesort signature
    must read ``xs : List Int → List Int``, not ``xs : Int → Int``."""

    def test_mergesort_signature_inferred(self):
        fn = _parse_fn("""
            def mergesort(xs: list[int]):
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = mergesort(xs[:mid])
                right = mergesort(xs[mid:])
                return left + right
        """)
        binders, ret, _ = infer_function_signature(fn, type_context=None)
        assert "List" in binders, f"expected List in binders: {binders}"
        assert "List" in ret, f"expected List in return: {ret}"

    def test_mergesort_body_uses_typed_ops(self):
        bt = _translate("""
            def mergesort(xs: list[int]) -> list[int]:
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = mergesort(xs[:mid])
                right = mergesort(xs[mid:])
                return left + right
        """)
        assert "xs.length" in bt.lean_text
        assert "xs.take" in bt.lean_text
        assert "xs.drop" in bt.lean_text
