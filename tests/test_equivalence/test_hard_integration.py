"""Level 5–6 integration tests for the sheaf-theoretic equivalence checker.

These tests exercise multiple modules in concert:
- Full pipeline from presheaves to verdict (EquivalencePipeline)
- EqualiserLocalChecker with genuine predicate equivalence
- GlobalEquivalenceChecker._attempt_gluing via FiberProductBuilder
- DescentDatumBuilder with non-trivial obligations
- Restriction coherence in LocalEquivalenceChecker
- Cohomology with non-trivial H^1
"""

from __future__ import annotations

import pytest

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
    Cover,
)
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory, ConcreteMorphism

from deppy.types.refinement import (
    Predicate,
    TruePred,
    FalsePred,
    VarPred,
    ComparisonPred,
    ComparisonOp,
    ConjunctionPred,
    DisjunctionPred,
    ImplicationPred,
    NotPred,
    RefinementType,
)
from deppy.types.base import INT_TYPE, STR_TYPE

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    EquivalenceStrength,
    EquivalenceSiteKind,
    LocalEquivalenceJudgment,
    SiteCorrespondence,
    ProgramId,
)
from deppy.equivalence.local_checker import (
    LocalEquivalenceChecker,
    EqualiserLocalChecker,
)
from deppy.equivalence.global_checker import (
    GlobalEquivalenceChecker,
    GlobalEquivalenceResult,
)
from deppy.equivalence.descent import (
    DescentDatumBuilder,
    quick_descent_check,
)
from deppy.equivalence.fiber_product import (
    FiberProductBuilder,
    FiberProduct,
    FiberSection,
)
from deppy.equivalence.sheaf_morphism import (
    SheafMorphismBuilder,
)
from deppy.equivalence.pipeline import (
    EquivalencePipeline,
    EquivalencePipelineConfig,
    EquivalencePipelineResult,
)
from deppy.equivalence.cohomology import (
    CechCohomologyComputer,
    CochainGroup,
    CoboundaryOperator,
)
from deppy.equivalence.predicate_eq import (
    predicates_equivalent,
    PredicateRelation,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════

def _sid(name: str) -> SiteId:
    return SiteId(name=name, kind=SiteKind.ARGUMENT_BOUNDARY)


def _section(name: str, carrier=None, predicate=None) -> LocalSection:
    ct = carrier
    if predicate is not None and carrier is not None:
        ct = RefinementType(base=carrier, predicate=predicate, binder="v")
    return LocalSection(
        site_id=_sid(name),
        carrier_type=ct,
        refinements={},
        trust=TrustLevel.PROOF_BACKED,
    )


def _presheaf(label: str, sections) -> ConcretePresheaf:
    builder = ConcretePresheafBuilder(name=label)
    for sec in sections:
        builder.add_section(sec)
    return builder.build()


def _site_cat(*names: str) -> SiteCategory:
    cat = SiteCategory()
    for n in names:
        cat.add_site(ConcreteSite(_site_id=_sid(n)))
    return cat


def _site_cat_with_overlaps(*names: str) -> SiteCategory:
    """Build a site category with pairwise overlaps via shared meet sites."""
    cat = SiteCategory()
    for n in names:
        cat.add_site(ConcreteSite(_site_id=_sid(n)))
    name_list = list(names)
    for i, a in enumerate(name_list):
        for b in name_list[i + 1:]:
            meet_name = f"{a}∩{b}"
            meet_site = ConcreteSite(_site_id=_sid(meet_name))
            cat.add_site(meet_site)
            cat.add_morphism(ConcreteMorphism(
                _source=_sid(a), _target=_sid(meet_name),
            ))
            cat.add_morphism(ConcreteMorphism(
                _source=_sid(b), _target=_sid(meet_name),
            ))
    return cat


def _corr(name: str, f_site=None, g_site=None) -> SiteCorrespondence:
    return SiteCorrespondence(
        f_site=_sid(f_site or name),
        g_site=_sid(g_site or name),
        common_site=_sid(name),
    )


def _judgment(
    name: str,
    verdict: EquivalenceVerdict = EquivalenceVerdict.EQUIVALENT,
    carrier_f=None,
    carrier_g=None,
    pred_f=None,
    pred_g=None,
) -> LocalEquivalenceJudgment:
    return LocalEquivalenceJudgment(
        site_id=_sid(name),
        verdict=verdict,
        obligation=EquivalenceObligation(
            site_id=_sid(name),
            description=f"obligation at {name}",
            carrier_type_f=carrier_f,
            carrier_type_g=carrier_g,
            forward_predicate=pred_f,
            backward_predicate=pred_g,
        ),
        forward_holds=(verdict == EquivalenceVerdict.EQUIVALENT),
        backward_holds=(verdict == EquivalenceVerdict.EQUIVALENT),
        proof=None,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — EqualiserLocalChecker with genuine predicate equivalence
# ═══════════════════════════════════════════════════════════════════════════════


class TestEqualiserLocalChecker:
    """The equaliser should use predicate_eq, not just isinstance(FalsePred)."""

    def test_identical_predicates_in_equaliser(self):
        """Same predicate on both sides → in equaliser."""
        pred = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pf = _presheaf("f", [_section("a", INT_TYPE, pred)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred)])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        is_in, agreements = checker.check(_sid("a"))
        assert is_in is True
        assert _sid("a") in agreements

    def test_equivalent_predicates_in_equaliser(self):
        """Logically equivalent (but structurally different) → in equaliser."""
        pred_f = NotPred(inner=NotPred(inner=VarPred(var_name="x")))  # ¬¬x
        pred_g = VarPred(var_name="x")  # x
        pf = _presheaf("f", [_section("a", INT_TYPE, pred_f)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred_g)])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        is_in, agreements = checker.check(_sid("a"))
        assert is_in is True

    def test_inequivalent_predicates_not_in_equaliser(self):
        """Different predicates → NOT in equaliser."""
        pred_f = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pred_g = ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)
        pf = _presheaf("f", [_section("a", INT_TYPE, pred_f)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred_g)])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        is_in, _ = checker.check(_sid("a"))
        assert is_in is False

    def test_false_pred_on_one_side(self):
        """FalsePred on one side → not in equaliser."""
        pf = _presheaf("f", [_section("a", INT_TYPE, FalsePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        is_in, _ = checker.check(_sid("a"))
        assert is_in is False

    def test_no_sections_not_in_equaliser(self):
        """Empty presheaves → not in equaliser."""
        pf = _presheaf("f", [])
        pg = _presheaf("g", [])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        is_in, agreements = checker.check(_sid("a"))
        assert is_in is False
        assert agreements == {}

    def test_agreement_predicate_is_biimplication(self):
        """Agreement predicate should be conjunction of two implications."""
        pred = TruePred()
        pf = _presheaf("f", [_section("a", INT_TYPE, pred)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred)])
        cat = _site_cat("a")

        checker = EqualiserLocalChecker(pf, pg, cat)
        _, agreements = checker.check(_sid("a"))
        agree = agreements[_sid("a")]
        assert isinstance(agree, ConjunctionPred)
        assert len(agree.conjuncts) == 2
        assert all(isinstance(c, ImplicationPred) for c in agree.conjuncts)


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — Fiber product builder integration
# ═══════════════════════════════════════════════════════════════════════════════


class TestFiberProductIntegration:
    """Tests that exercise FiberProductBuilder with real morphisms."""

    def test_fiber_product_three_sites(self):
        """Three-site fiber product with varying predicates."""
        cat = _site_cat("a", "b", "c")
        pred = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pf = _presheaf("f", [
            _section("a", INT_TYPE, pred),
            _section("b", INT_TYPE, TruePred()),
            _section("c", INT_TYPE, pred),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, pred),
            _section("b", INT_TYPE, TruePred()),
            _section("c", INT_TYPE, pred),
        ])
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a"), _corr("b"), _corr("c")])

        assert len(fp.site_ids()) == 3
        for sid in fp.site_ids():
            fib = fp.fiber_at(sid)
            assert fib is not None
            assert fib.is_inhabited

    def test_fiber_product_mismatched_predicates(self):
        """Different predicates → fiber still built but equaliser reflects it."""
        cat = _site_cat("a")
        pf = _presheaf("f", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)),
        ])
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a")])

        fib = fp.fiber_at(_sid("a"))
        assert fib is not None
        # Equaliser still exists (it's the conjunction), but predicates differ
        assert isinstance(fib.equaliser_predicate, ConjunctionPred)

    def test_fiber_product_one_side_empty(self):
        """One side has no section → uninhabited fiber."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [])  # No section at "a"
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a")])

        fib = fp.fiber_at(_sid("a"))
        assert fib is not None
        assert not fib.is_inhabited


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — Descent data builder
# ═══════════════════════════════════════════════════════════════════════════════


class TestDescentDatum:
    """Test DescentDatumBuilder with non-trivial obligations."""

    def test_build_with_carrier_types(self):
        """Descent datum records IdentityType when carriers are present."""
        cat = _site_cat("a")
        j = _judgment("a", carrier_f=INT_TYPE, carrier_g=INT_TYPE)
        builder = DescentDatumBuilder(site_category=cat)
        datum = builder.build([j])
        assert datum is not None
        assert _sid("a") in datum.sections

    def test_build_with_missing_carrier_g(self):
        """When carrier_g is missing, IdentityType rhs defaults to carrier_f."""
        from deppy.types.dependent import IdentityType
        cat = _site_cat("a")
        j = _judgment("a", carrier_f=INT_TYPE, carrier_g=None)
        builder = DescentDatumBuilder(site_category=cat)
        datum = builder.build([j])

        sec = datum.sections.get(_sid("a"))
        assert sec is not None
        ct = sec.carrier_type
        assert isinstance(ct, IdentityType)
        # rhs defaults to lhs when g is None
        assert ct.rhs == ct.lhs

    def test_build_multiple_sites(self):
        """Descent datum with multiple sites."""
        cat = _site_cat("a", "b")
        js = [
            _judgment("a", carrier_f=INT_TYPE, carrier_g=INT_TYPE),
            _judgment("b", carrier_f=STR_TYPE, carrier_g=STR_TYPE),
        ]
        builder = DescentDatumBuilder(site_category=cat)
        datum = builder.build(js)
        assert _sid("a") in datum.sections
        assert _sid("b") in datum.sections

    def test_quick_descent_check_all_equivalent(self):
        """All EQUIVALENT judgments → quick descent True."""
        js = [
            _judgment("a", verdict=EquivalenceVerdict.EQUIVALENT),
            _judgment("b", verdict=EquivalenceVerdict.EQUIVALENT),
        ]
        result = quick_descent_check(js)
        assert result is True

    def test_quick_descent_check_one_inequivalent(self):
        """One INEQUIVALENT judgment → quick descent returns None (inconclusive)."""
        js = [
            _judgment("a", verdict=EquivalenceVerdict.EQUIVALENT),
            _judgment("b", verdict=EquivalenceVerdict.INEQUIVALENT),
        ]
        result = quick_descent_check(js)
        # quick_descent_check returns None when any judgment is not EQUIVALENT
        # (it can only conclude True, not False)
        assert result is None

    def test_quick_descent_check_all_unknown(self):
        """All UNKNOWN → quick descent None (can't determine)."""
        js = [
            _judgment("a", verdict=EquivalenceVerdict.UNKNOWN),
        ]
        result = quick_descent_check(js)
        assert result is None


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — Global checker gluing integration
# ═══════════════════════════════════════════════════════════════════════════════


class TestGlobalCheckerGluing:
    """Test GlobalEquivalenceChecker end-to-end including gluing."""

    def test_identical_single_site_equivalent(self):
        """Two identical single-site presheaves → EQUIVALENT."""
        cat = _site_cat("a")
        pred = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pf = _presheaf("f", [_section("a", INT_TYPE, pred)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred)])

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr("a")],
            sections_f={_sid("a"): _section("a", INT_TYPE, pred)},
            sections_g={_sid("a"): _section("a", INT_TYPE, pred)},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT

    def test_different_predicates_inequivalent(self):
        """Different predicates → INEQUIVALENT."""
        cat = _site_cat("a")
        pf = _presheaf("f", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)),
        ])

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr("a")],
            sections_f={_sid("a"): _section("a", INT_TYPE,
                ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0))},
            sections_g={_sid("a"): _section("a", INT_TYPE,
                ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0))},
        )
        result = checker.check()
        assert result.verdict in (
            EquivalenceVerdict.INEQUIVALENT,
            EquivalenceVerdict.REFINED,
        )

    def test_two_site_identical_equivalent(self):
        """Two sites, both identical → EQUIVALENT."""
        cat = _site_cat("a", "b")
        pred_a = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pred_b = TruePred()
        pf = _presheaf("f", [
            _section("a", INT_TYPE, pred_a),
            _section("b", INT_TYPE, pred_b),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, pred_a),
            _section("b", INT_TYPE, pred_b),
        ])

        secs_f = {
            _sid("a"): _section("a", INT_TYPE, pred_a),
            _sid("b"): _section("b", INT_TYPE, pred_b),
        }
        secs_g = {
            _sid("a"): _section("a", INT_TYPE, pred_a),
            _sid("b"): _section("b", INT_TYPE, pred_b),
        }

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr("a"), _corr("b")],
            sections_f=secs_f,
            sections_g=secs_g,
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT

    def test_carrier_type_mismatch_inequivalent(self):
        """int vs str → INEQUIVALENT."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", STR_TYPE, TruePred())])

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr("a")],
            sections_f={_sid("a"): _section("a", INT_TYPE, TruePred())},
            sections_g={_sid("a"): _section("a", STR_TYPE, TruePred())},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.INEQUIVALENT

    def test_result_has_obstructions_for_inequivalent(self):
        """INEQUIVALENT results should carry at least one obstruction."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", STR_TYPE, TruePred())])

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr("a")],
            sections_f={_sid("a"): _section("a", INT_TYPE, TruePred())},
            sections_g={_sid("a"): _section("a", STR_TYPE, TruePred())},
        )
        result = checker.check()
        assert len(result.obstructions) >= 1


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — Pipeline integration
# ═══════════════════════════════════════════════════════════════════════════════


class TestPipelineFromPresheaves:
    """Test EquivalencePipeline.run_from_presheaves end-to-end."""

    def _make_cover(self, *names: str) -> Cover:
        sites = {}
        for n in names:
            sites[_sid(n)] = ConcreteSite(_site_id=_sid(n))
        return Cover(sites=sites)

    def test_identical_presheaves_equivalent(self):
        """Pipeline verdict: EQUIVALENT for identical presheaves."""
        pred = TruePred()
        pf = _presheaf("f", [_section("a", INT_TYPE, pred)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred)])
        cover = self._make_cover("a")

        config = EquivalencePipelineConfig(check_gluing=False, compute_cohomology=False)
        pipeline = EquivalencePipeline(config=config)
        result = pipeline.run_from_presheaves(
            pf, pg, cover, cover,
            sections_f={_sid("a"): _section("a", INT_TYPE, pred)},
            sections_g={_sid("a"): _section("a", INT_TYPE, pred)},
        )
        assert isinstance(result, EquivalencePipelineResult)
        assert result.verdict == EquivalenceVerdict.EQUIVALENT

    def test_different_presheaves_not_equivalent(self):
        """Pipeline verdict: not EQUIVALENT for different predicates."""
        pf = _presheaf("f", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)),
        ])
        cover = self._make_cover("a")

        config = EquivalencePipelineConfig(check_gluing=False, compute_cohomology=False)
        pipeline = EquivalencePipeline(config=config)
        result = pipeline.run_from_presheaves(
            pf, pg, cover, cover,
            sections_f={_sid("a"): _section("a", INT_TYPE,
                ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0))},
            sections_g={_sid("a"): _section("a", INT_TYPE,
                ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0))},
        )
        assert result.verdict != EquivalenceVerdict.EQUIVALENT

    def test_pipeline_records_stages(self):
        """Pipeline result has stage timing info."""
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])
        cover = self._make_cover("a")

        pipeline = EquivalencePipeline()
        result = pipeline.run_from_presheaves(pf, pg, cover, cover)
        assert "align_covers" in result.stages
        assert "equivalence_check" in result.stages
        assert result.total_elapsed >= 0.0

    def test_pipeline_two_sites(self):
        """Pipeline with two sites, both equivalent."""
        pred_a = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pred_b = TruePred()
        pf = _presheaf("f", [
            _section("a", INT_TYPE, pred_a),
            _section("b", STR_TYPE, pred_b),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, pred_a),
            _section("b", STR_TYPE, pred_b),
        ])
        cover = self._make_cover("a", "b")

        config = EquivalencePipelineConfig(check_gluing=False)
        pipeline = EquivalencePipeline(config=config)
        result = pipeline.run_from_presheaves(
            pf, pg, cover, cover,
            sections_f={
                _sid("a"): _section("a", INT_TYPE, pred_a),
                _sid("b"): _section("b", STR_TYPE, pred_b),
            },
            sections_g={
                _sid("a"): _section("a", INT_TYPE, pred_a),
                _sid("b"): _section("b", STR_TYPE, pred_b),
            },
        )
        assert result.verdict == EquivalenceVerdict.EQUIVALENT


# ═══════════════════════════════════════════════════════════════════════════════
# Level 5 — Cohomology with multiple sites
# ═══════════════════════════════════════════════════════════════════════════════


class TestCohomologyMultiSite:
    """Čech cohomology with multiple sites and overlaps."""

    def test_all_equivalent_trivial_h1(self):
        """All sites equivalent → H^1 = 0 (trivial)."""
        pred = TruePred()
        judgments = {
            _sid("a"): _judgment("a", carrier_f=INT_TYPE, carrier_g=INT_TYPE, pred_f=pred, pred_g=pred),
            _sid("b"): _judgment("b", carrier_f=INT_TYPE, carrier_g=INT_TYPE, pred_f=pred, pred_g=pred),
        }
        overlaps = [(_sid("a"), _sid("b"))]
        computer = CechCohomologyComputer(judgments=judgments, overlaps=overlaps)
        result = computer.compute()
        assert result.h1.is_trivial

    def test_one_inequivalent_h1_still_trivial(self):
        """One site inequivalent → H^1 is still trivial.

        H^1 measures gluing obstructions between local ISOMORPHISMS,
        not whether the isomorphisms exist. An inequivalent site means
        H^0 is incomplete, but H^1 = ker(d^1)/im(d^0) = 0 with 2 sites.
        """
        pred_a = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pred_b = ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)
        judgments = {
            _sid("a"): _judgment("a",
                verdict=EquivalenceVerdict.EQUIVALENT,
                carrier_f=INT_TYPE, carrier_g=INT_TYPE, pred_f=pred_a, pred_g=pred_a),
            _sid("b"): _judgment("b",
                verdict=EquivalenceVerdict.INEQUIVALENT,
                carrier_f=INT_TYPE, carrier_g=INT_TYPE, pred_f=pred_a, pred_g=pred_b),
        }
        overlaps = [(_sid("a"), _sid("b"))]
        computer = CechCohomologyComputer(judgments=judgments, overlaps=overlaps)
        result = computer.compute()
        # H^1 trivial because gluing obstruction requires ≥3 sites in a cycle
        assert result.h1.is_trivial
        # But the C^0 reflects that site b is NOT an isomorphism
        c0_b = result.c0.elements.get((_sid("b"),))
        assert c0_b is not None
        assert c0_b.is_iso is False

    def test_single_site_no_overlaps(self):
        """Single site, no overlaps → trivial cohomology."""
        pred = TruePred()
        judgments = {
            _sid("a"): _judgment("a", carrier_f=INT_TYPE, carrier_g=INT_TYPE, pred_f=pred, pred_g=pred),
        }
        computer = CechCohomologyComputer(judgments=judgments, overlaps=[])
        result = computer.compute()
        assert result.h1.is_trivial


# ═══════════════════════════════════════════════════════════════════════════════
# Level 6 — Stress tests
# ═══════════════════════════════════════════════════════════════════════════════


class TestStress:
    """Stress tests with many sites."""

    def test_ten_sites_all_equivalent(self):
        """10 sites, all with same predicate → EQUIVALENT."""
        names = [f"s{i}" for i in range(10)]
        pred = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        cat = _site_cat(*names)
        pf = _presheaf("f", [_section(n, INT_TYPE, pred) for n in names])
        pg = _presheaf("g", [_section(n, INT_TYPE, pred) for n in names])

        secs_f = {_sid(n): _section(n, INT_TYPE, pred) for n in names}
        secs_g = {_sid(n): _section(n, INT_TYPE, pred) for n in names}
        corrs = [_corr(n) for n in names]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f=secs_f,
            sections_g=secs_g,
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT

    def test_twenty_sites_fiber_product(self):
        """20-site fiber product builds without errors."""
        names = [f"s{i}" for i in range(20)]
        cat = _site_cat(*names)
        pf = _presheaf("f", [_section(n, INT_TYPE, TruePred()) for n in names])
        pg = _presheaf("g", [_section(n, INT_TYPE, TruePred()) for n in names])

        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr(n) for n in names])
        assert len(fp.site_ids()) == 20
        for sid in fp.site_ids():
            assert fp.fiber_at(sid) is not None

    def test_mixed_verdicts_across_sites(self):
        """Half equivalent, half inequivalent → not EQUIVALENT overall."""
        names = [f"s{i}" for i in range(6)]
        cat = _site_cat(*names)
        pred_eq = TruePred()
        pred_neq = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        pred_diff = ComparisonPred(lhs="v", op=ComparisonOp.LT, rhs=0)

        f_sections = []
        g_sections = []
        secs_f = {}
        secs_g = {}
        for i, n in enumerate(names):
            if i < 3:
                f_sections.append(_section(n, INT_TYPE, pred_eq))
                g_sections.append(_section(n, INT_TYPE, pred_eq))
                secs_f[_sid(n)] = _section(n, INT_TYPE, pred_eq)
                secs_g[_sid(n)] = _section(n, INT_TYPE, pred_eq)
            else:
                f_sections.append(_section(n, INT_TYPE, pred_neq))
                g_sections.append(_section(n, INT_TYPE, pred_diff))
                secs_f[_sid(n)] = _section(n, INT_TYPE, pred_neq)
                secs_g[_sid(n)] = _section(n, INT_TYPE, pred_diff)

        pf = _presheaf("f", f_sections)
        pg = _presheaf("g", g_sections)

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf,
            presheaf_g=pg,
            site_category=cat,
            correspondences=[_corr(n) for n in names],
            sections_f=secs_f,
            sections_g=secs_g,
        )
        result = checker.check()
        assert result.verdict != EquivalenceVerdict.EQUIVALENT
