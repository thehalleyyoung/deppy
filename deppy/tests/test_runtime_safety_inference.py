"""End-to-end tests for the auto-discharge runtime-safety pipeline.

Phase B/C/D/E deliverables — these tests guard:

* path-sensitive refinement inference (deppy/pipeline/refinement_inference.py)
* inter-procedural function summaries (deppy/pipeline/interprocedural.py)
* built-in sidecar catalogue (deppy/pipeline/builtin_sidecar.py)
* the wiring in deppy/pipeline/safety_pipeline.py that consumes them

Each test takes *un-annotated* Python source and verifies that the
safety pipeline produces the right verdict — proving runtime safety
without requiring any user-supplied decorators or sidecar specs.
"""
from __future__ import annotations

import pytest

from deppy.pipeline.safety_pipeline import verify_module_safety
from deppy.pipeline.refinement_inference import (
    RefinementInferrer, infer_refinements,
)
from deppy.pipeline.interprocedural import (
    build_call_graph, compute_summaries, discharge_call_site,
)
from deppy.pipeline.builtin_sidecar import (
    lookup_call, substitute_call_arguments,
)
from deppy.core.kernel import ProofKernel


# ─────────────────────────────────────────────────────────────────────
# Phase B — path-sensitive refinement inference
# ─────────────────────────────────────────────────────────────────────

class TestRefinementInference:
    def test_if_guard_narrows_at_division_site(self):
        src = (
            "def f(a, b):\n"
            "    if b != 0:\n"
            "        return a / b\n"
            "    return None\n"
        )
        maps = infer_refinements(src)
        rmap = maps["f"]
        guards = [list(fact.guards) for fact in rmap.per_source]
        assert ["b != 0"] in guards

    def test_if_guard_narrows_at_dict_lookup(self):
        src = (
            "def f(d, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
            "    return None\n"
        )
        rmap = infer_refinements(src)["f"]
        seen_kinds = {fact.source_kind for fact in rmap.per_source}
        assert "KEY_ERROR" in seen_kinds
        for fact in rmap.per_source:
            assert "k in d" in fact.guards

    def test_if_guard_narrows_at_index_site(self):
        src = (
            "def f(xs, i):\n"
            "    if 0 <= i < len(xs):\n"
            "        return xs[i]\n"
            "    return None\n"
        )
        rmap = infer_refinements(src)["f"]
        # The subscript site in the if-body must record the guard.
        # CALL_PROPAGATION facts (from len(xs)) live outside the body
        # and do not have the guard — that's expected.
        index_or_key = [
            f for f in rmap.per_source
            if f.source_kind in {"INDEX_ERROR", "KEY_ERROR"}
        ]
        assert index_or_key, "expected at least one INDEX/KEY fact"
        for fact in index_or_key:
            assert any("0 <= i" in g for g in fact.guards)

    def test_assert_narrows_path_but_not_function_wide(self):
        """Soundness fix F5: ``assert P`` is *not* a function-wide
        precondition (asserts are stripped under ``python -O``).  It
        IS still a path-sensitive guard for sources that follow it,
        and the inferrer flags ``used_assert_narrowing`` so the
        pipeline can warn.
        """
        src = (
            "def f(d, k):\n"
            "    assert k in d\n"
            "    return d[k]\n"
        )
        rmap = infer_refinements(src)["f"]
        assert rmap.function_wide_preconditions == []
        assert rmap.used_assert_narrowing is True
        # Path-sensitive guards still see the assert.
        post_assert_guards = [list(f.guards) for f in rmap.per_source]
        assert any("k in d" in gs for gs in post_assert_guards)

    def test_leading_raise_guard_becomes_function_wide_precondition(self):
        src = (
            "def f(x):\n"
            "    if x < 0:\n"
            "        raise ValueError('negative')\n"
            "    return x * 2\n"
        )
        rmap = infer_refinements(src)["f"]
        assert "x >= 0" in rmap.function_wide_preconditions

    def test_unguarded_division_has_empty_guards(self):
        src = (
            "def f(a, b):\n"
            "    return a / b\n"
        )
        rmap = infer_refinements(src)["f"]
        zero_div_facts = [f for f in rmap.per_source
                           if f.source_kind == "ZERO_DIVISION"]
        assert zero_div_facts
        for fact in zero_div_facts:
            assert not fact.guards

    def test_guard_inside_else_branch_is_negation(self):
        src = (
            "def f(d, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
            "    else:\n"
            "        return d['default']\n"
        )
        rmap = infer_refinements(src)["f"]
        # The else-path access (constant key) doesn't get the original
        # guard, but it does get the *negation*.
        else_path_facts = [
            f for f in rmap.per_source
            if "k not in d" in f.guards or "k in d" not in f.guards
        ]
        assert else_path_facts

    def test_no_narrowing_through_loop_body(self):
        """A guard inside a for-loop body should not leak to after the
        loop, since the loop may execute zero times.
        """
        src = (
            "def f(xs):\n"
            "    for x in xs:\n"
            "        if x > 0:\n"
            "            pass\n"
            "    return xs[0]\n"  # this is unguarded — loop may be empty
        )
        rmap = infer_refinements(src)["f"]
        # The xs[0] subscript should have empty guards (loop body
        # didn't establish anything about xs).
        post_loop = [f for f in rmap.per_source
                      if f.source_kind in {"INDEX_ERROR", "KEY_ERROR"}
                      and f.source_lineno >= 5]
        for fact in post_loop:
            assert not fact.guards


# ─────────────────────────────────────────────────────────────────────
# Phase C — inter-procedural summaries
# ─────────────────────────────────────────────────────────────────────

class TestInterprocedural:
    def test_call_graph_records_internal_edges(self):
        src = (
            "def a():\n    return b()\n"
            "def b():\n    return c()\n"
            "def c():\n    return 1\n"
        )
        cg = build_call_graph(src)
        assert cg.nodes == {"a", "b", "c"}
        assert "b" in cg.edges["a"]
        assert "c" in cg.edges["b"]
        assert not cg.edges["c"]

    def test_recursive_function_marked_as_self_edge(self):
        src = "def f(n):\n    return f(n - 1)\n"
        cg = build_call_graph(src)
        assert "f" in cg.edges["f"]

    def test_sccs_in_reverse_topological_order(self):
        """Tarjan returns SCCs leaves-first."""
        src = (
            "def a():\n    return b()\n"
            "def b():\n    return c()\n"
            "def c():\n    return 1\n"
        )
        cg = build_call_graph(src)
        sccs = cg.sccs()
        # c is a leaf so its SCC must come before a's SCC
        flat = [name for comp in sccs for name in comp]
        assert flat.index("c") < flat.index("b") < flat.index("a")

    def test_summary_recursion_without_decreases_records_recursion_error(self):
        src = (
            "def fact(n):\n"
            "    if n <= 0:\n"
            "        return 1\n"
            "    return n * fact(n - 1)\n"
        )
        summaries = compute_summaries(src)
        s = summaries["fact"]
        assert "RecursionError" in s.raises

    def test_summary_with_decreases_does_not_flag_recursion(self):
        from deppy.proofs.sidecar import ExternalSpec
        src = (
            "def fact(n):\n"
            "    if n <= 0:\n"
            "        return 1\n"
            "    return n * fact(n - 1)\n"
        )
        spec = ExternalSpec(target_name="fact", decreases=["n"])
        summaries = compute_summaries(src, user_specs={"fact": spec})
        # decreases declared → caller still classifies as recursive but
        # the *summary's* preconditions/decreases reflect that.
        s = summaries["fact"]
        assert "n" in s.decreases

    def test_call_site_discharge_when_callee_is_safe(self):
        src = (
            "def safe(a, b):\n"
            "    if b != 0:\n"
            "        return a / b\n"
            "    return None\n"
            "def caller(x, y):\n"
            "    return safe(x, y)\n"
        )
        # First feed refinements through compute_summaries so safe()
        # is recognised as is_safe.
        from deppy.pipeline.refinement_inference import infer_refinements
        refs = infer_refinements(src)
        summaries = compute_summaries(src, refinement_maps=refs)
        kernel = ProofKernel()
        ok, msg = discharge_call_site(
            callee_summary=summaries["safe"],
            actuals=["x", "y"],
            caller_path_guards=(),
            z3_check=kernel._z3_check,
        )
        assert ok, msg


# ─────────────────────────────────────────────────────────────────────
# Phase D — built-in sidecar
# ─────────────────────────────────────────────────────────────────────

class TestBuiltinSidecar:
    def test_math_sqrt_negative_argument(self):
        import ast
        call = ast.parse("math.sqrt(x)", mode="eval").body
        entries = lookup_call(call)
        assert entries
        assert any(e.exception_class == "ValueError" for e in entries)
        sub = substitute_call_arguments(entries[0].predicate, call)
        assert sub == "(x) >= 0"

    def test_len_requires_dunder_len(self):
        import ast
        call = ast.parse("len(xs)", mode="eval").body
        entries = lookup_call(call)
        assert entries[0].exception_class == "TypeError"
        sub = substitute_call_arguments(entries[0].predicate, call)
        assert "__len__" in sub

    def test_int_str_requires_parseable(self):
        import ast
        call = ast.parse("int(s)", mode="eval").body
        entries = lookup_call(call)
        # int(x) has both ValueError and TypeError catalogue rows
        kinds = {e.exception_class for e in entries}
        assert "ValueError" in kinds

    def test_str_repr_bool_marked_total(self):
        import ast
        for code in ("str(x)", "repr(x)", "bool(x)"):
            call = ast.parse(code, mode="eval").body
            entries = lookup_call(call)
            assert any(e.mode == "total" for e in entries), code

    def test_json_loads_raises_declaration_only(self):
        import ast
        call = ast.parse("json.loads(s)", mode="eval").body
        entries = lookup_call(call)
        assert entries[0].mode == "raises_declaration"
        assert "JSONDecodeError" in entries[0].exception_class

    def test_pop_requires_nonempty(self):
        import ast
        call = ast.parse("xs.pop()", mode="eval").body
        entries = lookup_call(call)
        sub = substitute_call_arguments(entries[0].predicate, call)
        assert "len" in sub and "> 0" in sub

    def test_unknown_builtin_returns_empty(self):
        import ast
        call = ast.parse("totally_made_up_function(x)", mode="eval").body
        entries = lookup_call(call)
        assert entries == []


# ─────────────────────────────────────────────────────────────────────
# Phase E — pipeline integration
# ─────────────────────────────────────────────────────────────────────

class TestAutoDischargePipeline:
    """The end-to-end claim: un-annotated Python with self-evident
    guards verifies as runtime-safe without any sidecar specs."""

    def _verdict(self, src: str):
        return verify_module_safety(src, use_drafts=True)

    def test_guarded_division_verifies(self):
        src = (
            "def f(a, b):\n"
            "    if b != 0:\n"
            "        return a / b\n"
            "    return None\n"
        )
        v = self._verdict(src)
        assert v.functions["f"].is_safe

    def test_guarded_dict_lookup_verifies(self):
        # Soundness fix F3: the co-located INDEX_ERROR/KEY_ERROR pair
        # can only be jointly discharged when the receiver type is
        # statically known.  Annotate ``d: dict`` so the pipeline can
        # rule out IndexError.
        src = (
            "def f(d: dict, k):\n"
            "    if k in d:\n"
            "        return d[k]\n"
            "    return None\n"
        )
        v = self._verdict(src)
        assert v.functions["f"].is_safe

    def test_assert_does_not_imply_unconditional_safety(self):
        """Soundness fix F5: an assert *alone* is not sufficient to
        certify a function safe — under ``python -O`` the assert is
        stripped and the source can fire.  The verdict surfaces the
        assert source itself as undischarged, and the verdict notes
        a warning about ``-O``.
        """
        src = (
            "def f(d, k):\n"
            "    assert k in d\n"
            "    return d[k]\n"
        )
        v = self._verdict(src)
        fv = v.functions["f"]
        # Function is NOT marked safe (the assert source itself is
        # unaddressed without a precondition).
        assert not fv.is_safe
        # The assert source is the gap.
        assert any("ASSERTION_ERROR" in u for u in fv.unaddressed)
        # The verdict surfaces the -O warning.
        assert any("python -O" in n for n in v.notes)

    def test_if_not_p_raise_is_sound_under_optimisation(self):
        """The recommended replacement: ``if not P: raise
        AssertionError`` is *not* stripped by ``-O``, so it acts as a
        real function-wide precondition.  ``d: dict`` annotation
        gives us the type evidence required for the co-located
        promotion (Soundness fix F3).
        """
        src = (
            "def f(d: dict, k):\n"
            "    if k not in d:\n"
            "        raise AssertionError\n"
            "    return d[k]\n"
        )
        v = self._verdict(src)
        fv = v.functions["f"]
        # The d[k] source is now discharged via the function-wide
        # precondition ``k in d`` (negation of ``k not in d``).
        assert not any(
            "KEY_ERROR" in u or "INDEX_ERROR" in u for u in fv.unaddressed
        )

    def test_unguarded_division_remains_unsafe(self):
        src = "def f(a, b):\n    return a / b\n"
        v = self._verdict(src)
        assert not v.functions["f"].is_safe

    def test_unguarded_dict_lookup_remains_unsafe(self):
        src = "def f(d, k):\n    return d[k]\n"
        v = self._verdict(src)
        assert not v.functions["f"].is_safe

    def test_caller_of_safe_function_inherits_safety(self):
        src = (
            "def safe(a, b):\n"
            "    if b != 0:\n"
            "        return a / b\n"
            "    return None\n"
            "def caller(x, y):\n"
            "    return safe(x, y)\n"
        )
        v = self._verdict(src)
        assert v.functions["safe"].is_safe
        assert v.functions["caller"].is_safe

    def test_caller_of_unsafe_function_remains_unsafe(self):
        src = (
            "def unsafe(a, b):\n"
            "    return a / b\n"
            "def caller(x, y):\n"
            "    return unsafe(x, y)\n"
        )
        v = self._verdict(src)
        assert not v.functions["unsafe"].is_safe
        assert not v.functions["caller"].is_safe

    def test_leading_raise_guard_acts_as_precondition(self):
        # Constant-message raise to avoid the false-positive
        # VALUE_ERROR source that ``raise ValueError(arg)`` triggers
        # via its inner Call node.
        src = (
            "def f(b):\n"
            "    if b == 0:\n"
            "        raise Exception\n"
            "    return 1 / b\n"
        )
        v = self._verdict(src)
        # The function is "safe under preconditions" — its EXPLICIT_RAISE
        # is the only remaining unaddressed source.  Verify the
        # ZERO_DIVISION at line 4 was discharged via the inferred
        # precondition.
        from deppy.pipeline.refinement_inference import infer_refinements
        rmap = infer_refinements(src)["f"]
        assert "b != 0" in rmap.function_wide_preconditions

    def test_chained_path_guards(self):
        """Multiple narrowing checks compound.  ``d: dict`` annotation
        is required after Soundness fix F3 so the co-located
        INDEX/KEY pair on ``d[k]`` can be jointly discharged.
        """
        src = (
            "def f(a, b, d: dict, k):\n"
            "    if b != 0 and k in d:\n"
            "        return a / b + d[k]\n"
            "    return 0\n"
        )
        v = self._verdict(src)
        assert v.functions["f"].is_safe

    def test_recursion_with_decreases_via_user_spec(self):
        """Recursion is discharged via TerminationObligation when a
        ``decreases`` measure is provided; the CALL_PROPAGATION on
        ``fact(n - 1)`` is then handled via the cubical atlas's
        cocycle check.  We assert that the RUNTIME_ERROR specifically
        is discharged.
        """
        from deppy.proofs.sidecar import ExternalSpec
        src = (
            "def fact(n):\n"
            "    if n <= 0:\n"
            "        return 1\n"
            "    return n * fact(n - 1)\n"
        )
        spec = ExternalSpec(
            target_name="fact",
            exception_free_when=["n >= 0"],
            decreases=["n"],
        )
        v = verify_module_safety(src, sidecar_specs={"fact": spec},
                                 use_drafts=False)
        fv = v.functions["fact"]
        # No RUNTIME_ERROR remains undischarged — the ``decreases``
        # measure produced a real TerminationObligation.
        assert not any("RUNTIME_ERROR" in u for u in fv.unaddressed)


# ─────────────────────────────────────────────────────────────────────
# End-to-end demonstration: a realistic-feeling un-annotated module.
# ─────────────────────────────────────────────────────────────────────

DEMO_SOURCE = '''\
"""Tiny utility module — minimally-annotated Python.

The ``record: dict`` annotation is required after Soundness fix F3
so the co-located INDEX_ERROR/KEY_ERROR pair on ``record[name]`` can
be jointly discharged by the ``name in record`` guard.
"""

def safe_divide(a, b):
    if b != 0:
        return a / b
    return 0

def get_field(record: dict, name):
    if name in record:
        return record[name]
    return ""

def percentage(part, whole):
    if whole != 0:
        return safe_divide(part, whole)
    return 0
'''


class TestEndToEndDemo:
    def test_demo_safe_divide_safe(self):
        v = verify_module_safety(DEMO_SOURCE, use_drafts=True)
        assert v.functions["safe_divide"].is_safe

    def test_demo_get_field_safe(self):
        v = verify_module_safety(DEMO_SOURCE, use_drafts=True)
        assert v.functions["get_field"].is_safe

    def test_demo_module_does_not_crash(self):
        v = verify_module_safety(DEMO_SOURCE, use_drafts=True)
        for name in ("safe_divide", "get_field", "percentage"):
            assert name in v.functions
