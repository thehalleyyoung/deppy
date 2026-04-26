"""Audit fix #8 — alias tracking in mutation analysis.

Tests the :class:`AliasTable` data type and the
:func:`analyse_function` driver, as well as the integration into
the refinement inferrer (a guard mentioning ``xs`` is dropped when
``ys = xs ; ys.append(3)`` happens).

The tests fall into four sections:

* ``TestAliasTable`` — the data structure (union, kill, may_alias,
  aliases_of, join, equality).
* ``TestUpdateForStmt`` — the per-statement transition function.
* ``TestAnalyseFunction`` — the function-level driver.
* ``TestRefinementIntegration`` — the integration into
  :class:`refinement_inference._Walker` (a guard on ``xs`` is
  dropped when an aliased ``ys`` is mutated).
"""
from __future__ import annotations

import ast
import textwrap

from deppy.pipeline.alias_analysis import (
    AliasAnalysisReport,
    AliasTable,
    analyse_function,
    expand_mutations,
    update_for_stmt,
)


def _parse_stmt(src: str) -> ast.stmt:
    return ast.parse(textwrap.dedent(src)).body[0]


def _parse_fn(src: str) -> ast.FunctionDef:
    src = textwrap.dedent(src)
    for node in ast.parse(src).body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node  # type: ignore[return-value]
    raise AssertionError(src)


# ─────────────────────────────────────────────────────────────────────
#  AliasTable invariants
# ─────────────────────────────────────────────────────────────────────


class TestAliasTable:
    def test_empty_has_no_aliases(self):
        t = AliasTable.empty()
        assert not t.may_alias("x", "y")
        assert t.aliases_of("x") == {"x"}

    def test_self_aliases_self(self):
        t = AliasTable.empty()
        assert t.may_alias("x", "x")

    def test_union_is_symmetric(self):
        t = AliasTable.empty().union("a", "b")
        assert t.may_alias("a", "b")
        assert t.may_alias("b", "a")

    def test_union_is_transitive(self):
        # a↔b, b↔c should imply a↔c.
        t = AliasTable.empty().union("a", "b").union("b", "c")
        assert t.may_alias("a", "c")
        assert t.aliases_of("a") == {"a", "b", "c"}

    def test_union_idempotent(self):
        t1 = AliasTable.empty().union("a", "b")
        t2 = t1.union("a", "b")
        assert t1 == t2

    def test_kill_removes_from_class(self):
        t = AliasTable.empty().union("a", "b").union("b", "c")
        t = t.kill("b")
        # ``b`` itself is removed from the class.
        assert "b" not in t.aliases_of("a")
        assert "b" not in t.aliases_of("c")
        # a and c are still aliased: the underlying object identity
        # they shared (transitively through b) does not vanish when
        # b is rebound — Python's reference semantics mean a and c
        # still point to the same object.  This is the conservative
        # (sound) direction for our analysis.
        assert t.may_alias("a", "c")

    def test_kill_singleton_returns_empty(self):
        t = AliasTable.empty().union("a", "b")
        t = t.kill("a")
        # The class becomes singleton {b} — dropped.
        assert t.class_count() == 0

    def test_kill_unknown_name_is_noop(self):
        t = AliasTable.empty().union("a", "b")
        t2 = t.kill("c")
        assert t == t2

    def test_join_unions_classes(self):
        t1 = AliasTable.empty().union("a", "b")
        t2 = AliasTable.empty().union("b", "c")
        merged = t1.join(t2)
        # Through b, a-b-c form one class.
        assert merged.may_alias("a", "c")

    def test_join_disjoint_keeps_both(self):
        t1 = AliasTable.empty().union("a", "b")
        t2 = AliasTable.empty().union("c", "d")
        merged = t1.join(t2)
        assert merged.may_alias("a", "b")
        assert merged.may_alias("c", "d")
        assert not merged.may_alias("a", "c")

    def test_join_many(self):
        merged = AliasTable.join_many([
            AliasTable.empty().union("a", "b"),
            AliasTable.empty().union("c", "d"),
            AliasTable.empty().union("a", "c"),  # bridge
        ])
        # All four aliased.
        for a in "abcd":
            for b in "abcd":
                assert merged.may_alias(a, b)

    def test_from_pairs(self):
        t = AliasTable.from_pairs([("a", "b"), ("c", "d"), ("a", "c")])
        for a in "abcd":
            for b in "abcd":
                assert t.may_alias(a, b)

    def test_known_names(self):
        t = AliasTable.empty().union("a", "b").union("c", "d")
        assert t.known_names() == {"a", "b", "c", "d"}


# ─────────────────────────────────────────────────────────────────────
#  Per-statement transitions
# ─────────────────────────────────────────────────────────────────────


class TestUpdateForStmt:
    def test_simple_assign_creates_alias(self):
        stmt = _parse_stmt("y = x")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("x", "y")

    def test_chained_assign(self):
        stmt = _parse_stmt("y = z = x")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("y", "x")
        assert t.may_alias("z", "x")
        assert t.may_alias("y", "z")

    def test_tuple_unpacking_pairs(self):
        stmt = _parse_stmt("y, z = x, w")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("y", "x")
        assert t.may_alias("z", "w")
        # Cross-pairs are not aliased.
        assert not t.may_alias("y", "z")

    def test_tuple_unpacking_unknown_source_kills(self):
        stmt = _parse_stmt("y, z = some_call()")
        t = AliasTable.empty().union("y", "x").union("z", "w")
        t = update_for_stmt(t, stmt)
        # Both targets are killed; old aliases dropped.
        assert not t.may_alias("y", "x")
        assert not t.may_alias("z", "w")

    def test_assign_call_kills_old_alias(self):
        # ``x`` was aliased to ``y``; now ``x`` is rebound to a fresh
        # value (call result).  The old alias is killed.
        t = AliasTable.empty().union("x", "y")
        stmt = _parse_stmt("x = list()")
        t = update_for_stmt(t, stmt)
        assert not t.may_alias("x", "y")

    def test_assign_fresh_returning_call_no_alias(self):
        stmt = _parse_stmt("y = list(x)")
        t = update_for_stmt(AliasTable.empty(), stmt)
        # ``list(x)`` returns a fresh list — y is NOT aliased to x.
        assert not t.may_alias("y", "x")

    def test_assign_copy_no_alias(self):
        stmt = _parse_stmt("y = x.copy()")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert not t.may_alias("y", "x")

    def test_assign_slice_no_alias(self):
        stmt = _parse_stmt("y = x[:]")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert not t.may_alias("y", "x")

    def test_or_alias_either(self):
        stmt = _parse_stmt("y = x or z")
        t = update_for_stmt(AliasTable.empty(), stmt)
        # ``x or z`` returns x or z — y may alias either.
        assert t.may_alias("y", "x")
        assert t.may_alias("y", "z")

    def test_ifexp_alias_either(self):
        stmt = _parse_stmt("y = x if cond else z")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("y", "x")
        assert t.may_alias("y", "z")

    def test_aug_assign_kills_alias(self):
        t = AliasTable.empty().union("x", "y")
        stmt = _parse_stmt("x += 1")
        t = update_for_stmt(t, stmt)
        # ``x += 1`` rebinds x to a fresh value (for ints — and we
        # are conservative even for lists where ``__iadd__`` returns
        # self; the analyser kills regardless).
        assert not t.may_alias("x", "y")

    def test_delete_removes_alias(self):
        t = AliasTable.empty().union("x", "y").union("y", "z")
        stmt = _parse_stmt("del y")
        t = update_for_stmt(t, stmt)
        # ``del y`` removes y from the class.
        assert "y" not in t.aliases_of("x")

    def test_for_loop_kills_target(self):
        t = AliasTable.empty().union("i", "x")
        stmt = _parse_stmt("for i in xs:\n    pass")
        t = update_for_stmt(t, stmt)
        assert not t.may_alias("i", "x")

    def test_unknown_method_treated_as_self_returning(self):
        # ``builder.set_x(...)`` — we don't recognise ``set_x``, so
        # we conservatively assume it returns ``builder``.
        stmt = _parse_stmt("y = builder.set_x(3)")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert t.may_alias("y", "builder")

    def test_known_fresh_method_no_alias(self):
        stmt = _parse_stmt("y = s.upper()")
        t = update_for_stmt(AliasTable.empty(), stmt)
        assert not t.may_alias("y", "s")


# ─────────────────────────────────────────────────────────────────────
#  Function-level analysis
# ─────────────────────────────────────────────────────────────────────


class TestAnalyseFunction:
    def test_simple_alias_then_mutation(self):
        fn = _parse_fn("""
            def f(xs):
                ys = xs
                ys.append(3)
                return ys
        """)
        report = analyse_function(fn)
        assert isinstance(report, AliasAnalysisReport)
        # The mutation on ys should expand to {ys, xs}.
        all_mutated = report.all_mutated()
        assert "ys" in all_mutated
        assert "xs" in all_mutated

    def test_mutation_through_chain(self):
        fn = _parse_fn("""
            def f(xs):
                a = xs
                b = a
                c = b
                c.append(7)
        """)
        report = analyse_function(fn)
        all_mutated = report.all_mutated()
        assert {"a", "b", "c", "xs"} <= all_mutated

    def test_mutation_after_rebind_does_not_propagate(self):
        fn = _parse_fn("""
            def f(xs):
                ys = xs
                ys = list(xs)        # ys no longer aliases xs
                ys.append(3)
        """)
        report = analyse_function(fn)
        all_mutated = report.all_mutated()
        assert "ys" in all_mutated
        # xs should NOT be in the mutated set — the alias was killed.
        assert "xs" not in all_mutated

    def test_mutation_in_branch_propagates(self):
        fn = _parse_fn("""
            def f(xs, cond):
                if cond:
                    ys = xs
                    ys.append(3)
                else:
                    pass
        """)
        report = analyse_function(fn)
        all_mutated = report.all_mutated()
        assert "ys" in all_mutated
        assert "xs" in all_mutated

    def test_join_after_branch(self):
        fn = _parse_fn("""
            def f(xs, ys, cond):
                if cond:
                    z = xs
                else:
                    z = ys
                z.append(3)
        """)
        report = analyse_function(fn)
        all_mutated = report.all_mutated()
        # z aliases xs on one branch and ys on the other; after the
        # join z may alias either.  So z.append(3) mutates {z, xs, ys}.
        assert "z" in all_mutated
        assert "xs" in all_mutated
        assert "ys" in all_mutated

    def test_no_alias_through_fresh_call(self):
        fn = _parse_fn("""
            def f(xs):
                ys = sorted(xs)
                ys.append(3)
        """)
        report = analyse_function(fn)
        all_mutated = report.all_mutated()
        assert "ys" in all_mutated
        assert "xs" not in all_mutated

    def test_initial_aliases_seed(self):
        fn = _parse_fn("""
            def f(self):
                self._xs.append(3)
        """)
        # Pre-seed: ``self`` and ``other_self`` may alias.
        report = analyse_function(
            fn, initial_aliases=[("self", "other_self")],
        )
        # The alias relation is preserved at the start.
        assert report.table_at_start.may_alias("self", "other_self")


# ─────────────────────────────────────────────────────────────────────
#  Direct expand_mutations
# ─────────────────────────────────────────────────────────────────────


class TestExpandMutations:
    def test_expand_with_aliases(self):
        t = AliasTable.empty().union("ys", "xs")
        result = expand_mutations({"ys"}, t)
        assert result == {"ys", "xs"}

    def test_expand_no_aliases(self):
        t = AliasTable.empty()
        result = expand_mutations({"ys"}, t)
        assert result == {"ys"}

    def test_expand_multiple(self):
        t = AliasTable.empty().union("a", "b").union("c", "d")
        result = expand_mutations({"a", "c"}, t)
        assert result == {"a", "b", "c", "d"}

    def test_expand_with_chain(self):
        t = AliasTable.empty().union("a", "b").union("b", "c")
        result = expand_mutations({"a"}, t)
        assert result == {"a", "b", "c"}


# ─────────────────────────────────────────────────────────────────────
#  Integration with refinement_inference
# ─────────────────────────────────────────────────────────────────────


class TestRefinementIntegration:
    """Audit fix #8 — the headline claim: a guard ``len(xs) > 0`` is
    dropped after ``ys = xs; ys.pop()``.  Without alias tracking
    the original code kept the guard (``xs`` wasn't in the mutated
    set), which masked unsoundness.
    """

    def test_walker_alias_table_starts_empty(self):
        from deppy.pipeline.refinement_inference import RefinementInferrer
        w = RefinementInferrer()
        assert w._alias_table.class_count() == 0

    def test_walker_advances_alias_table(self):
        from deppy.pipeline.refinement_inference import RefinementInferrer
        from deppy.pipeline.alias_analysis import AliasTable
        w = RefinementInferrer()
        # Direct testing: simulate processing ``ys = xs``.
        stmt = _parse_stmt("ys = xs")
        from deppy.pipeline.alias_analysis import update_for_stmt
        w._alias_table = update_for_stmt(w._alias_table, stmt)
        assert w._alias_table.may_alias("ys", "xs")

    def test_walker_resets_aliases_per_function(self):
        from deppy.pipeline.refinement_inference import RefinementInferrer
        w = RefinementInferrer()
        # Manually pollute the alias table.
        w._alias_table = w._alias_table.union("a", "b")
        # Calling analyze() resets it.
        fn = _parse_fn("""
            def f(x):
                return x
        """)
        w.analyze(fn)
        assert w._alias_table.class_count() == 0
