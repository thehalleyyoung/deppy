"""Tests for deppy.equivalence.predicates — equivalence-specific Predicate subclasses."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.types.refinement import (
    ComparisonOp,
    ComparisonPred,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.types.base import TypeBase
from deppy.equivalence.predicates import (
    BehavioralEquivalencePred,
    BiimplicationPred,
    EquivalencePred,
    FiberProductPred,
    RefinementEquivalencePred,
    SectionAgreementPred,
    TransportPred,
    build_equivalence_predicate,
    build_fiber_product_predicate,
    predicate_biimplication,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str, pred=None) -> LocalSection:
    refs = {}
    if pred is not None:
        refs["_pred"] = pred
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements=refs, trust=TrustLevel.RESIDUAL, provenance="test",
    )


class DummyType(TypeBase):
    def substitute(self, mapping): return self
    def free_variables(self): return frozenset()
    def __eq__(self, other): return isinstance(other, DummyType)
    def __hash__(self): return 42
    def __repr__(self): return "DummyType()"


class TestBiimplicationPred:
    def test_creation(self):
        p = BiimplicationPred(left=VarPred("x"), right=VarPred("y"))
        assert p.left == VarPred("x")
        assert p.right == VarPred("y")

    def test_free_vars(self):
        p = BiimplicationPred(left=VarPred("x"), right=VarPred("y"))
        assert "x" in p.free_vars()
        assert "y" in p.free_vars()

    def test_substitute_pred(self):
        p = BiimplicationPred(left=VarPred("x"), right=VarPred("y"))
        p2 = p.substitute_pred({"x": "a"})
        assert isinstance(p2, BiimplicationPred)

    def test_negate(self):
        p = BiimplicationPred(left=VarPred("x"), right=VarPred("y"))
        n = p.negate()
        assert n is not None

    def test_true_biimplication(self):
        p = BiimplicationPred(left=TruePred(), right=TruePred())
        assert p.free_vars() == frozenset()


class TestEquivalencePred:
    def test_creation(self):
        p = EquivalencePred(binder="v", expr_f="f(v)", expr_g="g(v)")
        assert p.binder == "v"

    def test_free_vars(self):
        p = EquivalencePred(
            binder="v", expr_f="f(v)", expr_g="g(v)",
            domain_predicate=VarPred("x"),
        )
        fv = p.free_vars()
        assert isinstance(fv, frozenset)

    def test_substitute_pred(self):
        p = EquivalencePred(binder="v", expr_f="f(v)", expr_g="g(v)")
        p2 = p.substitute_pred({"v": "w"})
        assert isinstance(p2, EquivalencePred)

    def test_negate(self):
        p = EquivalencePred(binder="v", expr_f="f(v)", expr_g="g(v)")
        n = p.negate()
        assert n is not None


class TestRefinementEquivalencePred:
    def test_creation(self):
        p = RefinementEquivalencePred(
            binder="v",
            predicate_f=VarPred("x"),
            predicate_g=VarPred("y"),
        )
        assert p.binder == "v"

    def test_free_vars(self):
        p = RefinementEquivalencePred(
            binder="v",
            predicate_f=VarPred("x"),
            predicate_g=VarPred("y"),
        )
        fv = p.free_vars()
        assert "x" in fv
        assert "y" in fv

    def test_substitute_pred(self):
        p = RefinementEquivalencePred(
            binder="v",
            predicate_f=VarPred("x"),
            predicate_g=VarPred("y"),
        )
        p2 = p.substitute_pred({"x": "a"})
        assert isinstance(p2, RefinementEquivalencePred)


class TestBehavioralEquivalencePred:
    def test_creation(self):
        p = BehavioralEquivalencePred(
            input_binders=("x",),
            output_predicate_f=VarPred("out_f"),
            output_predicate_g=VarPred("out_g"),
        )
        assert p.function_name_f == "f"
        assert p.function_name_g == "g"

    def test_free_vars(self):
        p = BehavioralEquivalencePred(
            output_predicate_f=VarPred("a"),
            output_predicate_g=VarPred("b"),
        )
        fv = p.free_vars()
        assert isinstance(fv, frozenset)

    def test_substitute_pred(self):
        p = BehavioralEquivalencePred(
            output_predicate_f=VarPred("a"),
            output_predicate_g=VarPred("b"),
        )
        p2 = p.substitute_pred({"a": "c"})
        assert isinstance(p2, BehavioralEquivalencePred)


class TestSectionAgreementPred:
    def test_creation(self):
        p = SectionAgreementPred(site_id=_site("a"))
        assert p.site_id.name == "a"

    def test_free_vars(self):
        pair = (VarPred("x"), VarPred("y"))
        p = SectionAgreementPred(
            site_id=_site("a"),
            predicate_pairs=(pair,),
        )
        fv = p.free_vars()
        assert "x" in fv
        assert "y" in fv


class TestTransportPred:
    def test_creation(self):
        p = TransportPred(source_predicate=VarPred("x"))
        assert isinstance(p.source_predicate, VarPred)

    def test_substitute(self):
        p = TransportPred(source_predicate=VarPred("x"))
        p2 = p.substitute_pred({"x": "y"})
        assert isinstance(p2, TransportPred)


class TestFiberProductPred:
    def test_creation(self):
        p = FiberProductPred(
            predicate_f=VarPred("x"),
            predicate_g=VarPred("y"),
        )
        assert isinstance(p, FiberProductPred)

    def test_negate(self):
        p = FiberProductPred(
            predicate_f=VarPred("x"),
            predicate_g=VarPred("y"),
        )
        n = p.negate()
        assert n is not None


class TestBuildEquivalencePredicate:
    def test_from_refinement_types(self):
        rt_f = RefinementType(
            base=DummyType(),
            binder="v",
            predicate=ComparisonPred("v", ComparisonOp.GT, 0),
        )
        rt_g = RefinementType(
            base=DummyType(),
            binder="v",
            predicate=ComparisonPred("v", ComparisonOp.GT, 0),
        )
        result = build_equivalence_predicate(rt_f, rt_g, "v")
        assert isinstance(result, RefinementEquivalencePred)

    def test_build_fiber_product_predicate(self):
        sec_f = _section("a", pred=VarPred("x"))
        sec_g = _section("a", pred=VarPred("y"))
        result = build_fiber_product_predicate(sec_f, sec_g, _site("a"))
        assert isinstance(result, FiberProductPred)
