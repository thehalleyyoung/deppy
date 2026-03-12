"""Tests for deppy.harvest.type_guard_harvester -- isinstance/hasattr/callable narrowing.

Exercises extraction of type narrowing facts from isinstance, issubclass,
hasattr, callable, negated forms, and TypeGuard/TypeIs return annotations.
"""

from __future__ import annotations

import ast
import pytest

from deppy.harvest.type_guard_harvester import (
    NarrowingKind,
    TypeGuardHarvester,
    TypeNarrowingFact,
    collect_narrowed_types,
    filter_by_kind,
    filter_by_variable,
    harvest_type_guards,
    narrowings_for_function,
    negative_narrowings,
    positive_narrowings,
)
from deppy.core._protocols import TrustLevel


# ===================================================================
# Helpers
# ===================================================================

def _harvest(source: str, file: str = "test.py") -> list:
    tree = ast.parse(source)
    return harvest_type_guards(tree, file=file)


# ===================================================================
# TestIsinstanceNarrowing
# ===================================================================

class TestIsinstanceNarrowing:
    """Test isinstance type guard harvesting."""

    def test_simple_isinstance(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int):
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        assert len(isinstance_facts) >= 1
        assert any(f.variable == "x" and f.narrowed_type == "int" for f in isinstance_facts)

    def test_isinstance_tuple_types(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, (int, str)):
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        positive = [f for f in isinstance_facts if f.polarity]
        assert len(positive) >= 1
        assert any(f.is_union_type for f in positive)
        union_fact = [f for f in positive if f.is_union_type][0]
        assert "int" in union_fact.union_members
        assert "str" in union_fact.union_members

    def test_isinstance_negated(self):
        facts = _harvest("""
def f(x):
    if not isinstance(x, int):
        pass
""")
        negated = [f for f in facts if f.is_negated]
        assert len(negated) >= 1
        assert any(f.variable == "x" for f in negated)

    def test_isinstance_in_assert(self):
        facts = _harvest("""
def f(x):
    assert isinstance(x, str)
""")
        assert len(facts) >= 1
        assert any(f.variable == "x" and f.narrowed_type == "str" for f in facts)

    def test_isinstance_in_while(self):
        facts = _harvest("""
def f(x):
    while isinstance(x, list):
        x = x[0]
""")
        assert len(facts) >= 1

    def test_isinstance_both_polarities(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int):
        pass
""")
        positive = [f for f in facts if f.polarity and not f.is_negated]
        negative = [f for f in facts if not f.polarity or f.is_negated]
        # Should have both positive (true branch) and negative (false branch) facts
        assert len(positive) >= 1
        assert len(negative) >= 1

    def test_isinstance_dotted_type(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, collections.OrderedDict):
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        assert any("OrderedDict" in f.narrowed_type for f in isinstance_facts)


# ===================================================================
# TestIssubclassNarrowing
# ===================================================================

class TestIssubclassNarrowing:
    """Test issubclass type guard harvesting."""

    def test_simple_issubclass(self):
        facts = _harvest("""
def f(cls):
    if issubclass(cls, Exception):
        pass
""")
        issubclass_facts = filter_by_kind(facts, NarrowingKind.ISSUBCLASS)
        assert len(issubclass_facts) >= 1
        assert any(f.variable == "cls" for f in issubclass_facts)

    def test_issubclass_tuple(self):
        facts = _harvest("""
def f(cls):
    if issubclass(cls, (ValueError, TypeError)):
        pass
""")
        issubclass_facts = filter_by_kind(facts, NarrowingKind.ISSUBCLASS)
        assert len(issubclass_facts) >= 1


# ===================================================================
# TestHasattrNarrowing
# ===================================================================

class TestHasattrNarrowing:
    """Test hasattr type guard harvesting."""

    def test_simple_hasattr(self):
        facts = _harvest("""
def f(obj):
    if hasattr(obj, "name"):
        pass
""")
        hasattr_facts = filter_by_kind(facts, NarrowingKind.HASATTR)
        assert len(hasattr_facts) >= 1
        assert any(f.variable == "obj" for f in hasattr_facts)
        assert any(f.checked_attribute == "name" for f in hasattr_facts)

    def test_hasattr_negated(self):
        facts = _harvest("""
def f(obj):
    if not hasattr(obj, "method"):
        pass
""")
        hasattr_facts = filter_by_kind(facts, NarrowingKind.HASATTR)
        negated = [f for f in hasattr_facts if f.is_negated]
        assert len(negated) >= 1


# ===================================================================
# TestCallableNarrowing
# ===================================================================

class TestCallableNarrowing:
    """Test callable type guard harvesting."""

    def test_simple_callable(self):
        facts = _harvest("""
def f(x):
    if callable(x):
        pass
""")
        callable_facts = filter_by_kind(facts, NarrowingKind.CALLABLE)
        assert len(callable_facts) >= 1
        assert any(f.variable == "x" for f in callable_facts)

    def test_callable_negated(self):
        facts = _harvest("""
def f(x):
    if not callable(x):
        pass
""")
        callable_facts = filter_by_kind(facts, NarrowingKind.CALLABLE)
        negated = [f for f in callable_facts if f.is_negated]
        assert len(negated) >= 1


# ===================================================================
# TestTypeGuardReturn
# ===================================================================

class TestTypeGuardReturn:
    """Test TypeGuard/TypeIs return annotation harvesting."""

    def test_typeguard_return(self):
        facts = _harvest("""
def is_int(x) -> TypeGuard[int]:
    return isinstance(x, int)
""")
        tg_facts = filter_by_kind(facts, NarrowingKind.TYPE_GUARD_RETURN)
        assert len(tg_facts) >= 1
        assert any(f.narrowed_type == "int" for f in tg_facts)

    def test_typeis_return(self):
        facts = _harvest("""
def narrow_str(x) -> TypeIs[str]:
    return isinstance(x, str)
""")
        ti_facts = filter_by_kind(facts, NarrowingKind.TYPEIS_RETURN)
        assert len(ti_facts) >= 1


# ===================================================================
# TestBooleanCombinations
# ===================================================================

class TestBooleanCombinations:
    """Test type guards combined with boolean operators."""

    def test_and_combination(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int) and x > 0:
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        assert len(isinstance_facts) >= 1

    def test_or_combination(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int) or isinstance(x, str):
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        assert len(isinstance_facts) >= 2


# ===================================================================
# TestElifNarrowing
# ===================================================================

class TestElifNarrowing:
    """Test narrowing in elif chains."""

    def test_isinstance_in_elif(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int):
        pass
    elif isinstance(x, str):
        pass
""")
        isinstance_facts = filter_by_kind(facts, NarrowingKind.ISINSTANCE)
        assert len(isinstance_facts) >= 2
        # At least one should be in elif
        assert any(f.is_in_elif for f in isinstance_facts)


# ===================================================================
# TestFilteringUtilities
# ===================================================================

class TestFilteringUtilities:
    """Test filtering convenience functions."""

    def test_filter_by_variable(self):
        facts = _harvest("""
def f(x, y):
    if isinstance(x, int): pass
    if isinstance(y, str): pass
""")
        x_facts = filter_by_variable(facts, "x")
        assert all(f.variable == "x" for f in x_facts)

    def test_positive_narrowings(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int):
        pass
""")
        pos = positive_narrowings(facts)
        assert all(f.polarity and not f.is_negated for f in pos)

    def test_negative_narrowings(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int):
        pass
""")
        neg = negative_narrowings(facts)
        assert all(not f.polarity or f.is_negated for f in neg)

    def test_narrowings_for_function(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int): pass
def g(y):
    if isinstance(y, str): pass
""")
        f_facts = narrowings_for_function(facts, "f")
        g_facts = narrowings_for_function(facts, "g")
        assert all(f.enclosing_function == "f" for f in f_facts)
        assert all(f.enclosing_function == "g" for f in g_facts)

    def test_collect_narrowed_types(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int): pass
    if isinstance(x, str): pass
""")
        types = collect_narrowed_types(facts, "x")
        assert "int" in types
        assert "str" in types


# ===================================================================
# TestNarrowingKind
# ===================================================================

class TestNarrowingKind:
    """Test NarrowingKind enum completeness."""

    def test_all_kinds(self):
        expected = {
            "isinstance", "issubclass", "hasattr", "callable",
            "type_guard_return", "typeis_return", "class_pattern",
            "protocol_check",
        }
        actual = {k.value for k in NarrowingKind}
        assert expected == actual


# ===================================================================
# TestTypeNarrowingFact
# ===================================================================

class TestTypeNarrowingFact:
    """Test TypeNarrowingFact dataclass properties."""

    def test_default_trust_level(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int): pass
""")
        assert all(f.trust_level == TrustLevel.TRUSTED_AUTO for f in facts)

    def test_source_span_populated(self):
        facts = _harvest("""
def f(x):
    if isinstance(x, int): pass
""")
        assert all(f.source_span is not None for f in facts)
