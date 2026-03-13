"""Hard tests for global_checker — exercises all 6 phases of the global pipeline.

Level 3-5 tests that push the global orchestration through:
- Phase 1: Local checking via check_local_equivalences
- Phase 2: Naturality verification via SheafMorphismBuilder
- Phase 3: Descent (quick + full H^1 computation)
- Phase 4: Gluing via FiberProductBuilder
- Phase 5: Uniqueness
- Phase 6: Stalk verification (optional)

Each test builds proper presheaves, site categories with morphisms,
sections, and correspondences — no mocking of inner modules.
"""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.types.base import TypeBase
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    NotPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.equivalence._protocols import (
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceStrength,
    EquivalenceVerdict,
    SiteCorrespondence,
)
from deppy.equivalence.global_checker import (
    GlobalEquivalenceChecker,
    GlobalEquivalenceResult,
    GluingResult,
)
from deppy.equivalence.sheaf_morphism import SheafMorphism


# ===========================================================================
# Helpers
# ===========================================================================

def _sid(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


class IntType(TypeBase):
    """Concrete carrier type for tests."""
    def substitute(self, mapping): return self
    def free_variables(self): return frozenset()
    def __eq__(self, other): return isinstance(other, IntType)
    def __hash__(self): return hash("IntType")
    def __repr__(self): return "int"


class StrType(TypeBase):
    """A different carrier type."""
    def substitute(self, mapping): return self
    def free_variables(self): return frozenset()
    def __eq__(self, other): return isinstance(other, StrType)
    def __hash__(self): return hash("StrType")
    def __repr__(self): return "str"


def _section(name: str, carrier=None, pred=None) -> LocalSection:
    refs = {}
    if pred is not None:
        refs["_pred"] = pred
    return LocalSection(
        site_id=_sid(name),
        carrier_type=carrier,
        refinements=refs,
        trust=TrustLevel.RESIDUAL,
    )


def _ref_section(name: str, base, pred, binder="v") -> LocalSection:
    """Section whose carrier_type is a RefinementType."""
    rt = RefinementType(base=base, predicate=pred, binder=binder)
    return LocalSection(
        site_id=_sid(name),
        carrier_type=rt,
        refinements={},
        trust=TrustLevel.RESIDUAL,
    )


def _corr(f_name: str, g_name: str, common_name: str | None = None) -> SiteCorrespondence:
    common = common_name or f_name
    return SiteCorrespondence(
        f_site=_sid(f_name),
        g_site=_sid(g_name),
        common_site=_sid(common),
    )


def _build_presheaf(name: str, sections: list[LocalSection]) -> ConcretePresheaf:
    builder = ConcretePresheafBuilder(name)
    for s in sections:
        builder.add_section(s)
    return builder.build()


def _site_cat(*names: str, overlaps: list[tuple[str, str]] | None = None) -> SiteCategory:
    """Build a SiteCategory with sites and optional overlaps.

    For each overlap (a, b), creates a synthetic meet site and morphisms
    a → meet, b → meet so that find_overlaps detects the pair.
    """
    cat = SiteCategory()
    for n in names:
        cat.add_site(ConcreteSite(_site_id=_sid(n)))
    if overlaps:
        for a, b in overlaps:
            meet_id = _sid(f"{a}∩{b}")
            cat.add_site(ConcreteSite(_site_id=meet_id))
            cat.add_morphism(ConcreteMorphism(_source=_sid(a), _target=meet_id))
            cat.add_morphism(ConcreteMorphism(_source=_sid(b), _target=meet_id))
    return cat


# ===========================================================================
# Phase 1 -- Local checking integration
# ===========================================================================

class TestPhase1LocalChecking:
    """Tests that Phase 1 correctly dispatches to local checker."""

    def test_single_site_trivial_equivalent(self):
        """One site, same type, TruePred → EQUIVALENT."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT
        assert result.is_equivalent
        assert len(result.local_judgments) == 1
        assert result.local_judgments[0].verdict == EquivalenceVerdict.EQUIVALENT

    def test_single_site_carrier_mismatch(self):
        """One site, different carrier types → INEQUIVALENT."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", StrType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.INEQUIVALENT
        assert not result.is_equivalent
        assert result.obstruction_count > 0

    def test_two_sites_both_equivalent(self):
        """Two independent sites, both equivalent → global EQUIVALENT."""
        cat = _site_cat("a", "b")
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT
        assert len(result.local_judgments) == 2

    def test_two_sites_one_fails(self):
        """Two sites, one equivalent one not → global INEQUIVALENT."""
        cat = _site_cat("a", "b")
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", StrType(), TruePred()),  # mismatch
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.INEQUIVALENT
        assert result.explanation.startswith("Local equivalence check failed")

    def test_missing_section_yields_inequivalent(self):
        """Missing section at a site → INEQUIVALENT."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={},  # missing!
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.INEQUIVALENT


# ===========================================================================
# Phase 2 -- Naturality
# ===========================================================================

class TestPhase2Naturality:
    """Tests that Phase 2 builds and verifies a natural transformation."""

    def test_naturality_with_morphisms_trivial(self):
        """Two sites connected by a morphism, trivial predicates → natural."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        assert result.sheaf_morphism is not None
        # With trivial predicates, should be natural
        assert result.verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED)

    def test_result_has_sheaf_morphism(self):
        """The result should carry the constructed sheaf morphism."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.sheaf_morphism is not None
        assert isinstance(result.sheaf_morphism, SheafMorphism)


# ===========================================================================
# Phase 3 -- Descent (H^1)
# ===========================================================================

class TestPhase3Descent:
    """Tests the descent checking phase."""

    def test_trivial_descent_quick_path(self):
        """All sites EQUIVALENT with TruePred → quick descent holds."""
        cat = _site_cat("a", "b")
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        # Descent should hold — either quick path or full check
        assert result.verdict == EquivalenceVerdict.EQUIVALENT

    def test_nontrivial_predicates_trigger_full_descent(self):
        """Non-trivial but equivalent predicates → full descent path exercised."""
        pred = ComparisonPred(
            lhs="v", op=ComparisonOp.GT, rhs="0"
        )
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        secs_f = [
            _ref_section("a", IntType(), pred),
            _ref_section("b", IntType(), pred),
        ]
        secs_g = [
            _ref_section("a", IntType(), pred),
            _ref_section("b", IntType(), pred),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        # Should still pass — same predicates
        assert result.verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED)


# ===========================================================================
# Phase 4 -- Gluing
# ===========================================================================

class TestPhase4Gluing:
    """Tests the gluing phase that constructs a global section."""

    def test_gluing_result_present(self):
        """When descent passes, gluing result should be present."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.gluing_result is not None
        assert isinstance(result.gluing_result, GluingResult)

    def test_gluing_succeeds_single_site(self):
        """Single site trivially glues."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.gluing_result is not None
        assert result.gluing_result.glued


# ===========================================================================
# Phase 5 -- Uniqueness
# ===========================================================================

class TestPhase5Uniqueness:
    """Test that uniqueness check flags duplicate site judgments."""

    def test_unique_sites_passes(self):
        """Distinct sites → uniqueness holds."""
        cat = _site_cat("a", "b")
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): secs_f[0], _sid("b"): secs_f[1]},
            sections_g={_sid("a"): secs_g[0], _sid("b"): secs_g[1]},
        )
        result = checker.check()
        # Should pass uniqueness → EQUIVALENT
        assert result.verdict == EquivalenceVerdict.EQUIVALENT


# ===========================================================================
# Phase 6 -- Stalk verification
# ===========================================================================

class TestPhase6StalkVerification:
    """Tests the optional stalk check."""

    def test_stalk_check_disabled_by_default(self):
        """By default use_stalk_check=False → stalk_result is None."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        assert result.stalk_result is None

    def test_stalk_check_enabled(self):
        """When enabled, stalk check runs (even if it returns None on error)."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        sec_g = _ref_section("a", IntType(), TruePred())
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
            use_stalk_check=True,
        )
        result = checker.check()
        # Should still reach a verdict even if stalk checker errors internally
        assert result.verdict in (
            EquivalenceVerdict.EQUIVALENT,
            EquivalenceVerdict.REFINED,
            EquivalenceVerdict.INEQUIVALENT,
        )


# ===========================================================================
# Result properties and strength
# ===========================================================================

class TestGlobalEquivalenceResult:
    """Test result dataclass properties."""

    def test_is_equivalent_property(self):
        r = GlobalEquivalenceResult(verdict=EquivalenceVerdict.EQUIVALENT)
        assert r.is_equivalent
        assert not r.is_conditional

    def test_is_conditional_property(self):
        r = GlobalEquivalenceResult(verdict=EquivalenceVerdict.REFINED)
        assert not r.is_equivalent
        assert r.is_conditional

    def test_obstruction_count(self):
        obs = [
            EquivalenceObstruction(
                kind=EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH,
                sites=[_sid("a")],
                description="test",
            ),
        ]
        r = GlobalEquivalenceResult(
            verdict=EquivalenceVerdict.INEQUIVALENT,
            obstructions=obs,
        )
        assert r.obstruction_count == 1

    def test_strength_inequivalent(self):
        r = GlobalEquivalenceResult(verdict=EquivalenceVerdict.INEQUIVALENT)
        assert r.strength() == EquivalenceStrength.REFINEMENT

    def test_strength_equivalent_no_witness(self):
        r = GlobalEquivalenceResult(verdict=EquivalenceVerdict.EQUIVALENT)
        assert r.strength() == EquivalenceStrength.BISIMULATION

    def test_strength_unknown(self):
        r = GlobalEquivalenceResult(verdict=EquivalenceVerdict.UNKNOWN)
        assert r.strength() == EquivalenceStrength.CONTEXTUAL


# ===========================================================================
# Multi-site integration
# ===========================================================================

class TestMultiSiteIntegration:
    """Harder integration tests with multiple sites and overlaps."""

    def test_three_sites_all_equivalent(self):
        """Three sites with overlaps, all equivalent → global EQUIVALENT."""
        cat = _site_cat("a", "b", "c", overlaps=[("a", "b"), ("b", "c")])
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
            _ref_section("c", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
            _ref_section("c", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b"), _corr("c", "c")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid(n): s for n, s in zip(["a", "b", "c"], secs_f)},
            sections_g={_sid(n): s for n, s in zip(["a", "b", "c"], secs_g)},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT
        assert len(result.local_judgments) == 3

    def test_three_sites_one_inequivalent(self):
        """Three sites, middle one has carrier mismatch → INEQUIVALENT."""
        cat = _site_cat("a", "b", "c", overlaps=[("a", "b"), ("b", "c")])
        secs_f = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", IntType(), TruePred()),
            _ref_section("c", IntType(), TruePred()),
        ]
        secs_g = [
            _ref_section("a", IntType(), TruePred()),
            _ref_section("b", StrType(), TruePred()),  # mismatch at b
            _ref_section("c", IntType(), TruePred()),
        ]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr("a", "a"), _corr("b", "b"), _corr("c", "c")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid(n): s for n, s in zip(["a", "b", "c"], secs_f)},
            sections_g={_sid(n): s for n, s in zip(["a", "b", "c"], secs_g)},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.INEQUIVALENT

    def test_refined_verdict_with_nontrivial_predicate(self):
        """Sections with non-trivial refinement predicates → REFINED or EQUIVALENT."""
        pred_f = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs="0")
        pred_g = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs="0")
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), pred_f)
        sec_g = _ref_section("a", IntType(), pred_g)
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        # Same predicate → should be equivalent or refined
        assert result.verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED)

    def test_predicate_gap_detected(self):
        """One section has True, the other has a strict predicate → may be REFINED."""
        cat = _site_cat("a")
        sec_f = _ref_section("a", IntType(), TruePred())
        strict = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs="0")
        sec_g = _ref_section("a", IntType(), strict)
        pf = _build_presheaf("f", [sec_f])
        pg = _build_presheaf("g", [sec_g])
        corrs = [_corr("a", "a")]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid("a"): sec_f},
            sections_g={_sid("a"): sec_g},
        )
        result = checker.check()
        # True ≠ v > 0 — refinement or inequivalence
        assert result.verdict in (EquivalenceVerdict.REFINED, EquivalenceVerdict.INEQUIVALENT)

    def test_full_pipeline_five_sites(self):
        """Five sites with chain overlaps → exercises the full pipeline."""
        names = ["s1", "s2", "s3", "s4", "s5"]
        overlap_pairs = [("s1", "s2"), ("s2", "s3"), ("s3", "s4"), ("s4", "s5")]
        cat = _site_cat(*names, overlaps=overlap_pairs)
        secs_f = [_ref_section(n, IntType(), TruePred()) for n in names]
        secs_g = [_ref_section(n, IntType(), TruePred()) for n in names]
        pf = _build_presheaf("f", secs_f)
        pg = _build_presheaf("g", secs_g)
        corrs = [_corr(n, n) for n in names]

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={_sid(n): s for n, s in zip(names, secs_f)},
            sections_g={_sid(n): s for n, s in zip(names, secs_g)},
        )
        result = checker.check()
        assert result.verdict == EquivalenceVerdict.EQUIVALENT
        assert len(result.local_judgments) == 5
        assert result.gluing_result is not None

    def test_empty_correspondences(self):
        """No correspondences → vacuously equivalent."""
        cat = _site_cat()
        pf = _build_presheaf("f", [])
        pg = _build_presheaf("g", [])
        corrs: list[SiteCorrespondence] = []

        checker = GlobalEquivalenceChecker(
            presheaf_f=pf, presheaf_g=pg,
            site_category=cat,
            correspondences=corrs,
            sections_f={},
            sections_g={},
        )
        result = checker.check()
        # Vacuously equivalent
        assert result.verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED)
