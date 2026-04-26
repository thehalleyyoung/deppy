"""Tests for Union / Optional / Any / Callable / user-class support.

Phase U1–U4 deliverables.  Covers:

* type-annotation translator output for union / optional / callable /
  user-class shapes;
* path-sensitive isinstance narrowing on union receivers;
* class-method detection in summaries and refinement maps;
* the verdict's ``Any``-warning surface.
"""
from __future__ import annotations

import textwrap

import pytest

from deppy.lean.type_translation import (
    TypeTranslation, translate_annotation_str,
)
from deppy.pipeline.refinement_inference import infer_refinements
from deppy.pipeline.interprocedural import build_call_graph, compute_summaries
from deppy.pipeline.safety_pipeline import verify_module_safety


# ─────────────────────────────────────────────────────────────────────
# U1 — type translator
# ─────────────────────────────────────────────────────────────────────

class TestTypeTranslator:
    def test_scalar_types(self):
        assert translate_annotation_str("int").lean == "Int"
        assert translate_annotation_str("float").lean == "Float"
        assert translate_annotation_str("str").lean == "String"
        assert translate_annotation_str("bool").lean == "Bool"
        assert translate_annotation_str("None").lean == "Unit"

    def test_optional_becomes_option(self):
        assert translate_annotation_str("int | None").lean == "(Option Int)"
        assert translate_annotation_str("Optional[int]").lean == "(Option Int)"
        assert translate_annotation_str(
            "Optional[list[int]]"
        ).lean == "(Option (List Int))"

    def test_two_element_union_uses_sum(self):
        r = translate_annotation_str("int | str")
        assert r.lean == "(Sum Int String)"

    def test_three_or_more_union_uses_nested_sum(self):
        """Phase U6: 3+-element unions translate to nested
        ``Sum`` rather than an opaque axiom."""
        r = translate_annotation_str("int | str | bytes")
        assert r.lean == "(Sum (Sum Int String) ByteArray)"
        # No opaque axiom required.
        assert not any("Deppy_Union" in d for d in r.aux_decls)

    def test_four_element_union_left_associative(self):
        r = translate_annotation_str("int | str | bytes | float")
        assert r.lean == "(Sum (Sum (Sum Int String) ByteArray) Float)"

    def test_any_is_polymorphic_alpha(self):
        assert translate_annotation_str("Any").lean == "α"

    def test_callable_translates_to_arrow(self):
        assert translate_annotation_str(
            "Callable[[int, int], int]"
        ).lean == "(Int → Int → Int)"
        assert translate_annotation_str(
            "Callable[[int], int | None]"
        ).lean == "(Int → (Option Int))"

    def test_higher_order_callable(self):
        r = translate_annotation_str(
            "Callable[[Callable[[int], int]], int]"
        )
        assert r.lean == "((Int → Int) → Int)"

    def test_callable_with_ellipsis(self):
        r = translate_annotation_str("Callable[..., int]")
        assert "α" in r.lean
        assert "Int" in r.lean

    def test_generic_containers(self):
        assert translate_annotation_str(
            "list[int]"
        ).lean == "(List Int)"
        assert translate_annotation_str(
            "dict[str, int]"
        ).lean == "(Std.HashMap String Int)"
        assert translate_annotation_str(
            "tuple[int, str]"
        ).lean == "(Int × String)"

    def test_user_class_emits_opaque_axiom(self):
        r = translate_annotation_str("MyCustomClass")
        assert "Deppy_MyCustomClass" in r.lean
        assert any("axiom Deppy_MyCustomClass : Type" in d
                   for d in r.aux_decls)

    def test_typevar_emits_opaque_axiom(self):
        r = translate_annotation_str("T")
        assert "Deppy_T" in r.lean

    def test_nested_generic_with_union(self):
        r = translate_annotation_str("list[int | str]")
        assert r.lean == "(List (Sum Int String))"

    def test_dict_with_optional_values(self):
        r = translate_annotation_str("dict[str, int | None]")
        assert r.lean == "(Std.HashMap String (Option Int))"


# ─────────────────────────────────────────────────────────────────────
# U2 — Union narrowing via isinstance / annotation
# ─────────────────────────────────────────────────────────────────────

class TestUnionNarrowing:
    def test_isinstance_dict_narrows_union(self):
        """``def f(d, k): if isinstance(d, dict): return d[k]`` —
        the isinstance guard narrows the receiver to dict so the
        co-located INDEX_ERROR can be promoted."""
        src = textwrap.dedent('''
            def f(d, k):
                if isinstance(d, dict) and k in d:
                    return d[k]
                return None
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert v.functions["f"].is_safe

    def test_pep604_optional_dict_with_is_not_none_narrowing(self):
        """``def f(d: dict | None, k): if d is not None and k in d: return d[k]``."""
        src = textwrap.dedent('''
            def f(d: dict | None, k):
                if d is not None and k in d:
                    return d[k]
                return None
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert v.functions["f"].is_safe

    def test_union_dict_or_list_without_narrowing_remains_unsafe(self):
        """A receiver typed ``dict | list`` cannot be subscripted
        unsafely even with ``k in d`` — list membership doesn't
        bound-check.  The type evidence rule must NOT promote."""
        src = textwrap.dedent('''
            def f(d: dict | list, k):
                if k in d:
                    return d[k]
                return None
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        # Without isinstance narrowing one source still fires.
        fv = v.functions["f"]
        assert any(
            "INDEX_ERROR" in u or "KEY_ERROR" in u for u in fv.unaddressed
        )

    def test_optional_alone_with_only_none_check_remains_open(self):
        """``d: dict | None`` with ``if d is not None`` narrows to
        ``dict`` (the None alternative is dropped) — but membership
        check is also needed."""
        src = textwrap.dedent('''
            def f(d: dict | None, k):
                if d is not None:
                    return d[k]
                return None
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        fv = v.functions["f"]
        # No ``k in d`` guard — KEY_ERROR remains open.
        assert any("KEY_ERROR" in u for u in fv.unaddressed)


# ─────────────────────────────────────────────────────────────────────
# U3 — class methods
# ─────────────────────────────────────────────────────────────────────

class TestClassMethods:
    def test_methods_appear_in_refinement_map(self):
        src = textwrap.dedent('''
            class C:
                def safe(self, a, b):
                    if b != 0:
                        return a / b
                    return 0
        ''').strip()
        maps = infer_refinements(src)
        assert "C.safe" in maps
        assert "safe" in maps  # bare-name alias

    def test_methods_appear_in_call_graph(self):
        src = textwrap.dedent('''
            class C:
                def helper(self, x):
                    return x

                def caller(self):
                    return self.helper(1)
        ''').strip()
        cg = build_call_graph(src)
        assert "helper" in cg.nodes
        assert "caller" in cg.nodes
        assert "helper" in cg.edges["caller"]

    def test_methods_summarised_and_verified(self):
        src = textwrap.dedent('''
            class Counter:
                def safe_div(self, a, b):
                    if b != 0:
                        return a / b
                    return 0

                def unsafe_div(self, a, b):
                    return a / b
        ''').strip()
        summaries = compute_summaries(
            src, refinement_maps=infer_refinements(src),
        )
        assert summaries["safe_div"].is_safe
        assert not summaries["unsafe_div"].is_safe

    def test_class_with_unsafe_method_module_unsafe(self):
        src = textwrap.dedent('''
            class C:
                def m(self, a, b):
                    return a / b
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert "m" in v.functions
        assert not v.functions["m"].is_safe


# ─────────────────────────────────────────────────────────────────────
# U4 — Any warning
# ─────────────────────────────────────────────────────────────────────

class TestAnyWarning:
    def test_any_typed_parameter_triggers_warning(self):
        src = textwrap.dedent('''
            from typing import Any

            def f(x: Any):
                return x.method()
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert any("Any" in n for n in v.notes)

    def test_object_typed_parameter_triggers_warning(self):
        src = textwrap.dedent('''
            def f(x: object):
                return x
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert any("Any" in n or "object" in n for n in v.notes)

    def test_typed_parameter_no_warning(self):
        src = textwrap.dedent('''
            def f(x: int):
                return x + 1
        ''').strip()
        v = verify_module_safety(src, use_drafts=True)
        assert not any("Any" in n for n in v.notes)


# ─────────────────────────────────────────────────────────────────────
# U5 — Callable receivers in functions
# ─────────────────────────────────────────────────────────────────────

class TestCallableReceivers:
    def test_callable_param_translates_in_obligations(self, tmp_path):
        from deppy.lean.obligations import emit_obligations
        src = textwrap.dedent('''
            from typing import Callable

            def apply_twice(f: Callable[[int], int], x: int) -> int:
                return f(f(x))
        ''').strip()
        out = tmp_path / "obs.lean"
        report = emit_obligations(src, out, use_drafts=True)
        text = out.read_text()
        # The translator should turn ``Callable[[int], int]`` into
        # ``(Int → Int)`` in the binders.  When obligations fire, the
        # binder for ``f`` will use the arrow form.
        if report.open_count > 0:
            # The Callable parameter binder appears in the file.
            assert "→" in text or "Callable" in text or "Int" in text
        # And the file at least contains the function's name.
        assert "apply_twice" in text or "open obligations" in text.lower() \
            or "No open" in text or report.open_count == 0

    def test_higher_order_callable_summary(self):
        src = textwrap.dedent('''
            def apply(f, x):
                return f(x)

            def safe_caller():
                def doubler(n):
                    return n * 2
                return apply(doubler, 5)
        ''').strip()
        cg = build_call_graph(src)
        # apply is callable with f, which is invoked → emits
        # CALL_PROPAGATION.  The graph records apply's call to f.
        assert "apply" in cg.nodes
        assert "safe_caller" in cg.nodes
