"""Tests for deppy.equivalence.contracts — @equiv and @refines decorators."""

from __future__ import annotations

import pytest
from deppy.equivalence.contracts import (
    EquivalenceContract,
    RefinementContract,
    collect_all_contracts,
    equiv,
    refines,
)


class TestEquivDecorator:
    def test_basic_decoration(self):
        @equiv("target_func")
        def my_func(x):
            return x + 1

        assert hasattr(my_func, "__deppy_equiv__")
        assert len(my_func.__deppy_equiv__) == 1

    def test_contract_target(self):
        @equiv("other")
        def f(x): return x

        c = f.__deppy_equiv__[0]
        assert isinstance(c, EquivalenceContract)
        assert c.other == "other"

    def test_multiple_decorators(self):
        @equiv("target1")
        @equiv("target2")
        def f(x): return x

        assert len(f.__deppy_equiv__) == 2


class TestRefinesDecorator:
    def test_basic_decoration(self):
        @refines("target_func")
        def my_func(x):
            return x + 1

        assert hasattr(my_func, "__deppy_refines__")
        assert len(my_func.__deppy_refines__) == 1

    def test_contract_target(self):
        @refines("other")
        def f(x): return x

        c = f.__deppy_refines__[0]
        assert isinstance(c, RefinementContract)
        assert c.other == "other"


class TestCollectAllContracts:
    def test_empty_module(self):
        import types
        mod = types.ModuleType("empty_mod")
        result = collect_all_contracts(mod)
        assert isinstance(result, tuple)
        assert len(result) == 2
        equivs, refinements = result
        assert equivs == []
        assert refinements == []

    def test_module_with_equiv(self):
        import types
        mod = types.ModuleType("test_mod")

        @equiv("target")
        def f(x): return x

        mod.f = f
        equivs, refinements = collect_all_contracts(mod)
        assert len(equivs) >= 1
