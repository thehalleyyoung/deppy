"""Tests for deppy.equivalence.cohomology — Cech cohomology with proper kernels."""

from __future__ import annotations

import pytest
from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.cohomology import (
    CechCohomologyComputer,
    CechCohomologyResult,
    CoboundaryOperator,
    CochainElement,
    CochainGroup,
    CohomologyGroup,
    SubgroupData,
    compute_cohomology,
    compute_image,
    compute_kernel,
    extract_obstructions_from_h1,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _obligation(name: str) -> EquivalenceObligation:
    return EquivalenceObligation(site_id=_site(name), description="test")


def _judgment(name: str, verdict=EquivalenceVerdict.EQUIVALENT) -> LocalEquivalenceJudgment:
    return LocalEquivalenceJudgment(
        site_id=_site(name),
        verdict=verdict,
        obligation=_obligation(name),
    )


class TestCochainElement:
    def test_creation(self):
        elem = CochainElement(
            sites=(_site("a"),),
            predicate=VarPred("x"),
        )
        assert elem.sites == (_site("a"),)
        assert isinstance(elem.predicate, VarPred)
        assert elem.is_iso is True

    def test_degree_from_sites_length(self):
        elem_0 = CochainElement(sites=(_site("a"),), predicate=TruePred())
        elem_1 = CochainElement(sites=(_site("a"), _site("b")), predicate=TruePred())
        assert len(elem_0.sites) == 1  # C^0
        assert len(elem_1.sites) == 2  # C^1


class TestCochainGroup:
    def test_creation(self):
        grp = CochainGroup(degree=0)
        assert grp.degree == 0
        assert len(grp.elements) == 0

    def test_add_element(self):
        grp = CochainGroup(degree=0)
        idx = (_site("a"),)
        elem = CochainElement(sites=idx, predicate=VarPred("x"))
        grp.elements[idx] = elem
        assert idx in grp.elements


class TestCoboundaryOperator:
    def test_d0(self):
        site_a = _site("a")
        site_b = _site("b")
        op = CoboundaryOperator(overlaps=[(site_a, site_b)])
        c0 = CochainGroup(degree=0)
        c0.elements[(_site("a"),)] = CochainElement(
            sites=(site_a,), predicate=VarPred("x"),
        )
        c0.elements[(_site("b"),)] = CochainElement(
            sites=(site_b,), predicate=VarPred("x"),
        )
        result = op.d0(c0)
        assert isinstance(result, CochainGroup)
        assert result.degree == 1

    def test_d1(self):
        site_a = _site("a")
        site_b = _site("b")
        op = CoboundaryOperator(
            overlaps=[(site_a, site_b)],
            triple_overlaps=[(site_a, site_b, site_a)],
        )
        c1 = CochainGroup(degree=1)
        c1.elements[(site_a, site_b)] = CochainElement(
            sites=(site_a, site_b), predicate=VarPred("x"),
        )
        result = op.d1(c1)
        assert isinstance(result, CochainGroup)
        assert result.degree == 2


class TestCechCohomologyComputer:
    def test_trivial_cover(self):
        site_a = _site("a")
        judgments = {site_a: _judgment("a")}
        computer = CechCohomologyComputer(judgments=judgments, overlaps=[])
        result = computer.compute()
        assert isinstance(result, CechCohomologyResult)
        assert result.h1_trivial

    def test_two_site_agreeing(self):
        site_a = _site("a")
        site_b = _site("b")
        judgments = {
            site_a: _judgment("a"),
            site_b: _judgment("b"),
        }
        computer = CechCohomologyComputer(
            judgments=judgments,
            overlaps=[(site_a, site_b)],
        )
        result = computer.compute()
        assert isinstance(result, CechCohomologyResult)

    def test_extract_obstructions_trivial(self):
        site_a = _site("a")
        judgments = {site_a: _judgment("a")}
        computer = CechCohomologyComputer(judgments=judgments, overlaps=[])
        result = computer.compute()
        obstructions = extract_obstructions_from_h1(result)
        assert isinstance(obstructions, list)
        assert len(obstructions) == 0  # trivial H^1 => no obstructions
