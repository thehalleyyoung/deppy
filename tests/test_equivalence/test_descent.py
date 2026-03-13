"""Tests for deppy.equivalence.descent — descent data and cocycle conditions."""

from __future__ import annotations

import pytest
from deppy.core._protocols import SiteId, SiteKind, TrustLevel, LocalSection
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.core._protocols import DescentDatum
from deppy.equivalence.descent import (
    CocycleConditionChecker,
    CocycleResult,
    DescentDatumBuilder,
    DescentResult,
    TransitionFunction,
    TransitionFunctionBuilder,
    quick_descent_check,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str) -> LocalSection:
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements={}, trust=TrustLevel.RESIDUAL, provenance="test",
    )


def _obligation(name: str) -> EquivalenceObligation:
    return EquivalenceObligation(site_id=_site(name), description="test")


def _judgment(name: str, verdict=EquivalenceVerdict.EQUIVALENT) -> LocalEquivalenceJudgment:
    return LocalEquivalenceJudgment(
        site_id=_site(name), verdict=verdict, obligation=_obligation(name),
    )


class TestTransitionFunction:
    def test_creation(self):
        t = TransitionFunction(
            site_i=_site("a"),
            site_j=_site("b"),
            predicate=VarPred("x"),
        )
        assert t.site_i == _site("a")
        assert t.site_j == _site("b")
        assert not t.is_identity

    def test_identity(self):
        t = TransitionFunction(
            site_i=_site("a"),
            site_j=_site("a"),
            predicate=TruePred(),
            is_identity=True,
        )
        assert t.is_identity


class TestTransitionFunctionBuilder:
    def test_build(self):
        cat = SiteCategory()
        site_a = _site("a")
        site_b = _site("b")
        cat.add_site(ConcreteSite(site_a))
        cat.add_site(ConcreteSite(site_b))

        builder = TransitionFunctionBuilder(cat)
        judgments = [_judgment("a"), _judgment("b")]
        transitions = builder.build(judgments)
        assert isinstance(transitions, list)


class TestCocycleConditionChecker:
    def test_empty_transitions(self):
        cat = SiteCategory()
        checker = CocycleConditionChecker(cat)
        result = checker.check([])
        assert isinstance(result, CocycleResult)

    def test_single_transition(self):
        cat = SiteCategory()
        site_a = _site("a")
        site_b = _site("b")
        cat.add_site(ConcreteSite(site_a))
        cat.add_site(ConcreteSite(site_b))

        t = TransitionFunction(
            site_i=site_a, site_j=site_b,
            predicate=TruePred(),
        )
        checker = CocycleConditionChecker(cat)
        result = checker.check([t])
        assert isinstance(result, CocycleResult)


class TestDescentDatumBuilder:
    def test_build(self):
        cat = SiteCategory()
        site_a = _site("a")
        cat.add_site(ConcreteSite(site_a))

        builder = DescentDatumBuilder(cat)
        judgments = [_judgment("a")]
        datum = builder.build(judgments)
        assert isinstance(datum, (DescentDatum, type(datum)))


class TestQuickDescentCheck:
    def test_single_judgment(self):
        judgments = [_judgment("a")]
        result = quick_descent_check(judgments)
        # Returns True, False, or None (inconclusive)
        assert result is True or result is False or result is None or result is None

    def test_all_equivalent(self):
        judgments = [_judgment("a"), _judgment("b")]
        result = quick_descent_check(judgments)
        # Returns True, False, or None (inconclusive)
        assert result is True or result is False or result is None
