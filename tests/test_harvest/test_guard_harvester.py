"""Tests for deppy.harvest.guard_harvester -- guard extraction from if/assert/while/try.

Exercises harvesting of guard predicates from Python AST: if/elif chains,
assert statements, while loops, try/except, ternary expressions,
comprehension filters, boolean short-circuit guards, and walrus operators.
"""

from __future__ import annotations

import ast
import pytest

from deppy.harvest.guard_harvester import (
    GuardHarvester,
    GuardKind,
    HarvestedGuard,
    deduplicate_guards,
    filter_guards_by_function,
    filter_guards_by_kind,
    filter_guards_by_variable,
    harvest_guards,
    partition_by_polarity,
)
from deppy.core._protocols import TrustLevel


# ===================================================================
# Helpers
# ===================================================================

def _harvest(source: str, file: str = "test.py") -> list:
    tree = ast.parse(source)
    return harvest_guards(tree, file=file)


# ===================================================================
# TestIfGuards
# ===================================================================

class TestIfGuards:
    """Test guard extraction from if statements."""

    def test_simple_if(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
""")
        if_guards = [g for g in guards if g.guard_kind == GuardKind.IF_TEST]
        assert len(if_guards) >= 1
        assert any(g.polarity is True for g in if_guards)

    def test_if_else_produces_both_polarities(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
    else:
        pass
""")
        if_guards = [g for g in guards if g.guard_kind == GuardKind.IF_TEST]
        true_guards = [g for g in if_guards if g.polarity is True]
        false_guards = [g for g in if_guards if g.polarity is False]
        assert len(true_guards) >= 1
        assert len(false_guards) >= 1

    def test_elif_produces_elif_guard(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
    elif x < -5:
        pass
""")
        elif_guards = [g for g in guards if g.guard_kind == GuardKind.ELIF_TEST]
        assert len(elif_guards) >= 1

    def test_nested_if_increases_depth(self):
        guards = _harvest("""
def f(x, y):
    if x > 0:
        if y > 0:
            pass
""")
        # Inner guard should have deeper nesting
        depths = sorted(set(g.nesting_depth for g in guards))
        assert len(depths) >= 2

    def test_comparison_guard(self):
        guards = _harvest("""
def f(x):
    if x == 42:
        pass
""")
        assert len(guards) >= 1

    def test_is_none_guard(self):
        guards = _harvest("""
def f(x):
    if x is None:
        pass
""")
        assert len(guards) >= 1
        assert any("x" in g.narrowed_variables for g in guards)

    def test_is_not_none_guard(self):
        guards = _harvest("""
def f(x):
    if x is not None:
        pass
""")
        assert len(guards) >= 1

    def test_chained_comparison(self):
        guards = _harvest("""
def f(x):
    if 0 < x < 100:
        pass
""")
        assert len(guards) >= 1

    def test_associated_else(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
    else:
        pass
""")
        true_guards = [g for g in guards if g.polarity is True and g.guard_kind == GuardKind.IF_TEST]
        assert any(g.associated_else for g in true_guards)

    def test_parent_function_tracked(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass

def g(y):
    if y < 0:
        pass
""")
        f_guards = [g for g in guards if g.parent_function == "f"]
        g_guards = [g for g in guards if g.parent_function == "g"]
        assert len(f_guards) >= 1
        assert len(g_guards) >= 1


# ===================================================================
# TestAssertGuards
# ===================================================================

class TestAssertGuards:
    """Test guard extraction from assert statements."""

    def test_simple_assert(self):
        guards = _harvest("""
def f(x):
    assert x > 0
""")
        assert_guards = [g for g in guards if g.guard_kind == GuardKind.ASSERT_TEST]
        assert len(assert_guards) >= 1

    def test_assert_trust_level(self):
        guards = _harvest("""
def f(x):
    assert x > 0
""")
        assert_guards = [g for g in guards if g.guard_kind == GuardKind.ASSERT_TEST]
        assert all(g.trust_level == TrustLevel.PROOF_BACKED for g in assert_guards)

    def test_assert_isinstance(self):
        guards = _harvest("""
def f(x):
    assert isinstance(x, int)
""")
        assert len(guards) >= 1

    def test_assert_with_message(self):
        guards = _harvest("""
def f(x):
    assert x > 0, "x must be positive"
""")
        assert len(guards) >= 1

    def test_assert_compound_condition(self):
        guards = _harvest("""
def f(x, y):
    assert x > 0 and y > 0
""")
        assert len(guards) >= 1


# ===================================================================
# TestWhileGuards
# ===================================================================

class TestWhileGuards:
    """Test guard extraction from while loops."""

    def test_while_guard(self):
        guards = _harvest("""
def f():
    i = 0
    while i < 10:
        i += 1
""")
        while_guards = [g for g in guards if g.guard_kind == GuardKind.WHILE_TEST]
        assert len(while_guards) >= 1

    def test_while_with_else(self):
        guards = _harvest("""
def f():
    i = 0
    while i < 10:
        i += 1
    else:
        pass
""")
        while_guards = [g for g in guards if g.guard_kind == GuardKind.WHILE_TEST]
        assert any(g.associated_else for g in while_guards)

    def test_while_truthy_test(self):
        guards = _harvest("""
def f(items):
    while items:
        items.pop()
""")
        while_guards = [g for g in guards if g.guard_kind == GuardKind.WHILE_TEST]
        assert len(while_guards) >= 1


# ===================================================================
# TestTryExceptGuards
# ===================================================================

class TestTryExceptGuards:
    """Test guard extraction from try/except blocks."""

    def test_except_handler(self):
        guards = _harvest("""
def f():
    try:
        x = int("abc")
    except ValueError as e:
        pass
""")
        try_guards = [g for g in guards if g.guard_kind == GuardKind.TRY_EXCEPT]
        assert len(try_guards) >= 1

    def test_except_multiple_handlers(self):
        guards = _harvest("""
def f():
    try:
        pass
    except ValueError:
        pass
    except TypeError:
        pass
""")
        try_guards = [g for g in guards if g.guard_kind == GuardKind.TRY_EXCEPT]
        assert len(try_guards) >= 2

    def test_bare_except_no_guard(self):
        guards = _harvest("""
def f():
    try:
        pass
    except:
        pass
""")
        # bare except has no type -> no guard
        try_guards = [g for g in guards if g.guard_kind == GuardKind.TRY_EXCEPT]
        assert len(try_guards) == 0

    def test_except_trust_level(self):
        guards = _harvest("""
def f():
    try:
        pass
    except ValueError:
        pass
""")
        try_guards = [g for g in guards if g.guard_kind == GuardKind.TRY_EXCEPT]
        assert all(g.trust_level == TrustLevel.TRUSTED_AUTO for g in try_guards)


# ===================================================================
# TestTernaryGuards
# ===================================================================

class TestTernaryGuards:
    """Test guard extraction from ternary expressions."""

    def test_ternary(self):
        guards = _harvest("""
def f(x):
    y = 1 if x > 0 else -1
""")
        ternary_guards = [g for g in guards if g.guard_kind == GuardKind.TERNARY]
        assert len(ternary_guards) >= 1

    def test_ternary_always_has_else(self):
        guards = _harvest("""
def f(x):
    y = 1 if x > 0 else -1
""")
        ternary_guards = [g for g in guards if g.guard_kind == GuardKind.TERNARY]
        assert all(g.associated_else for g in ternary_guards)


# ===================================================================
# TestComprehensionGuards
# ===================================================================

class TestComprehensionGuards:
    """Test guard extraction from comprehension if-clauses."""

    def test_list_comprehension_if(self):
        guards = _harvest("""
def f(items):
    result = [x for x in items if x > 0]
""")
        comp_guards = [g for g in guards if g.guard_kind == GuardKind.COMPREHENSION_IF]
        assert len(comp_guards) >= 1

    def test_set_comprehension_if(self):
        guards = _harvest("""
def f(items):
    result = {x for x in items if x > 0}
""")
        comp_guards = [g for g in guards if g.guard_kind == GuardKind.COMPREHENSION_IF]
        assert len(comp_guards) >= 1

    def test_dict_comprehension_if(self):
        guards = _harvest("""
def f(items):
    result = {x: x*2 for x in items if x > 0}
""")
        comp_guards = [g for g in guards if g.guard_kind == GuardKind.COMPREHENSION_IF]
        assert len(comp_guards) >= 1

    def test_generator_expression_if(self):
        guards = _harvest("""
def f(items):
    result = sum(x for x in items if x > 0)
""")
        comp_guards = [g for g in guards if g.guard_kind == GuardKind.COMPREHENSION_IF]
        assert len(comp_guards) >= 1

    def test_multiple_if_clauses(self):
        guards = _harvest("""
def f(items):
    result = [x for x in items if x > 0 if x < 100]
""")
        comp_guards = [g for g in guards if g.guard_kind == GuardKind.COMPREHENSION_IF]
        assert len(comp_guards) >= 2


# ===================================================================
# TestBooleanOpGuards
# ===================================================================

class TestBooleanOpGuards:
    """Test guard extraction from boolean short-circuit operations."""

    def test_and_short_circuit(self):
        guards = _harvest("""
def f(x, y):
    z = x and y
""")
        bool_guards = [g for g in guards if g.guard_kind == GuardKind.BOOLEAN_OP]
        assert len(bool_guards) >= 1

    def test_or_short_circuit(self):
        guards = _harvest("""
def f(x, y):
    z = x or y
""")
        bool_guards = [g for g in guards if g.guard_kind == GuardKind.BOOLEAN_OP]
        assert len(bool_guards) >= 1


# ===================================================================
# TestWalrusGuards
# ===================================================================

class TestWalrusGuards:
    """Test walrus operator guard extraction."""

    def test_walrus_in_if(self):
        guards = _harvest("""
def f(data):
    if (n := len(data)) > 0:
        pass
""")
        walrus_guards = [g for g in guards if g.walrus_target is not None]
        assert len(walrus_guards) >= 1
        assert walrus_guards[0].walrus_target == "n"

    def test_walrus_adds_narrowed_variable(self):
        guards = _harvest("""
def f(data):
    if (n := len(data)) > 0:
        pass
""")
        walrus_guards = [g for g in guards if g.walrus_target == "n"]
        assert any("n" in g.narrowed_variables for g in walrus_guards)


# ===================================================================
# TestFilteringUtilities
# ===================================================================

class TestFilteringUtilities:
    """Test deduplication and filtering functions."""

    def test_deduplicate(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
""")
        deduped = deduplicate_guards(guards + guards)
        assert len(deduped) <= len(guards)

    def test_filter_by_function(self):
        guards = _harvest("""
def f(x):
    if x > 0: pass
def g(y):
    if y < 0: pass
""")
        f_guards = filter_guards_by_function(guards, "f")
        g_guards = filter_guards_by_function(guards, "g")
        assert all(g.parent_function == "f" for g in f_guards)
        assert all(g.parent_function == "g" for g in g_guards)

    def test_filter_by_kind(self):
        guards = _harvest("""
def f(x):
    if x > 0: pass
    assert x != 0
""")
        if_guards = filter_guards_by_kind(guards, GuardKind.IF_TEST)
        assert_guards = filter_guards_by_kind(guards, GuardKind.ASSERT_TEST)
        assert all(g.guard_kind == GuardKind.IF_TEST for g in if_guards)
        assert all(g.guard_kind == GuardKind.ASSERT_TEST for g in assert_guards)

    def test_filter_by_variable(self):
        guards = _harvest("""
def f(x, y):
    if x > 0: pass
    if y < 0: pass
""")
        x_guards = filter_guards_by_variable(guards, "x")
        assert all("x" in g.narrowed_variables for g in x_guards)

    def test_partition_by_polarity(self):
        guards = _harvest("""
def f(x):
    if x > 0:
        pass
    else:
        pass
""")
        true_g, false_g = partition_by_polarity(guards)
        assert all(g.polarity is True for g in true_g)
        assert all(g.polarity is False for g in false_g)


# ===================================================================
# TestGuardKind
# ===================================================================

class TestGuardKind:
    """Test GuardKind enum completeness."""

    def test_all_kinds(self):
        expected = {
            "if_test", "elif_test", "assert_test", "walrus_if",
            "try_except", "while_test", "ternary", "boolean_op",
            "comprehension_if", "match_case",
        }
        actual = {k.value for k in GuardKind}
        assert expected == actual


# ===================================================================
# TestHarvestedGuard
# ===================================================================

class TestHarvestedGuard:
    """Test HarvestedGuard dataclass properties."""

    def test_default_polarity_true(self):
        guards = _harvest("""
def f(x):
    if x > 0: pass
""")
        true_guards = [g for g in guards if g.polarity is True]
        assert len(true_guards) >= 1

    def test_source_span_populated(self):
        guards = _harvest("""
def f(x):
    if x > 0: pass
""")
        assert all(g.source_span is not None for g in guards)
        assert all(g.source_span.file == "test.py" for g in guards)
