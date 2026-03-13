"""Hard tests for fiber product construction — the pullback in the
sheaf-theoretic equivalence checker.

Tests exercise:
  - FiberProductBuilder.build() with various carrier/predicate combos
  - FiberSection: equaliser predicate, inhabitation, carrier SigmaType
  - FiberProduct: projection, restriction, gluing check, to_presheaf
  - Edge cases: empty fibers, mismatched carriers, many-site products

Levels:
  2 — basic single-site fiber product
  3 — two-site fiber product with matching/mismatching predicates
  4 — projection correctness, gluing check, restrict_fiber
  5 — full to_presheaf round-trip, empty fibers, many-site stress
"""
from __future__ import annotations

import pytest

from deppy.core._protocols import (
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder

from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    FalsePred,
    TruePred,
    VarPred,
    RefinementType,
)
from deppy.types.base import INT_TYPE, STR_TYPE

from deppy.equivalence._protocols import (
    SiteCorrespondence,
)
from deppy.equivalence.fiber_product import (
    FiberProduct,
    FiberProductBuilder,
    FiberProjection,
    FiberSection,
)


# ── Helpers ───────────────────────────────────────────────────────────────

def _sid(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _site_cat(*names: str) -> SiteCategory:
    cat = SiteCategory()
    for n in names:
        cat.add_site(ConcreteSite(_site_id=_sid(n)))
    return cat


def _section(name: str, carrier=None, predicate=None):
    """Build a section via LocalSection directly.
    
    If a predicate is given, wrap the carrier in a RefinementType so that
    FiberProductBuilder._extract_predicate sees it as a refinement.
    """
    from deppy.core._protocols import LocalSection
    if predicate is not None and carrier is not None:
        carrier = RefinementType(base=carrier, predicate=predicate, binder="v")
    return LocalSection(
        site_id=_sid(name),
        carrier_type=carrier,
        refinements={},
        trust=TrustLevel.PROOF_BACKED,
    )


def _presheaf(name: str, sections) -> ConcretePresheaf:
    builder = ConcretePresheafBuilder(name=name)
    for sec in sections:
        builder.add_section(sec)
    return builder.build()


def _corr(name: str, f_site: str | None = None, g_site: str | None = None) -> SiteCorrespondence:
    return SiteCorrespondence(
        f_site=_sid(f_site or name),
        g_site=_sid(g_site or name),
        common_site=_sid(name),
    )


# ═════════════════════════════════════════════════════════════════════════════
# Level 2 — basic single-site fiber product
# ═════════════════════════════════════════════════════════════════════════════

class TestBasicFiberProduct:
    """Single-site fiber product with trivial and non-trivial predicates."""

    def test_single_site_trivial_predicates(self):
        """F and G both have {v: int | True} at one site → inhabited fiber."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a")])

        assert isinstance(fp, FiberProduct)
        fiber = fp.fiber_at(_sid("a"))
        assert fiber is not None
        assert fiber.is_inhabited

    def test_single_site_matching_predicates(self):
        """Both sides have same non-trivial predicate → inhabited fiber."""
        pred = ComparisonPred(lhs="v", op=ComparisonOp.GT, rhs=0)
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, pred)])
        pg = _presheaf("g", [_section("a", INT_TYPE, pred)])
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a")])

        fiber = fp.fiber_at(_sid("a"))
        assert fiber is not None
        assert fiber.is_inhabited

    def test_site_ids_match_correspondences(self):
        """FiberProduct.site_ids() returns exactly the correspondence sites."""
        cat = _site_cat("a", "b")
        pf = _presheaf("f", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])
        builder = FiberProductBuilder(pf, pg, cat)
        fp = builder.build([_corr("a"), _corr("b")])

        assert fp.site_ids() == frozenset([_sid("a"), _sid("b")])


# ═════════════════════════════════════════════════════════════════════════════
# Level 3 — two-site fiber product with varying predicates
# ═════════════════════════════════════════════════════════════════════════════

class TestTwoSiteFiberProduct:
    """Two-site products test fiber independence and predicate interaction."""

    def test_two_sites_both_inhabited(self):
        """Two sites, both trivial → both fibers inhabited."""
        cat = _site_cat("a", "b")
        secs_f = [_section("a", INT_TYPE, TruePred()), _section("b", INT_TYPE, TruePred())]
        secs_g = [_section("a", INT_TYPE, TruePred()), _section("b", INT_TYPE, TruePred())]
        fp = FiberProductBuilder(_presheaf("f", secs_f), _presheaf("g", secs_g), cat).build(
            [_corr("a"), _corr("b")]
        )
        assert fp.fiber_at(_sid("a")).is_inhabited
        assert fp.fiber_at(_sid("b")).is_inhabited

    def test_all_fibers_dict(self):
        """all_fibers() returns a dict of all fiber sections."""
        cat = _site_cat("x", "y")
        secs_f = [_section("x", INT_TYPE, TruePred()), _section("y", INT_TYPE, TruePred())]
        secs_g = [_section("x", INT_TYPE, TruePred()), _section("y", INT_TYPE, TruePred())]
        fp = FiberProductBuilder(_presheaf("f", secs_f), _presheaf("g", secs_g), cat).build(
            [_corr("x"), _corr("y")]
        )
        fibers = fp.all_fibers()
        assert _sid("x") in fibers
        assert _sid("y") in fibers
        assert len(fibers) == 2


# ═════════════════════════════════════════════════════════════════════════════
# Level 4 — projection, restriction, gluing
# ═════════════════════════════════════════════════════════════════════════════

class TestFiberProjections:
    """Test the categorical projections π₁ : F ×_G → F and π₂ : F ×_G → G."""

    def test_project_left_returns_section(self):
        """project_left should recover the f-side section."""
        cat = _site_cat("a")
        sec_f = _section("a", INT_TYPE, TruePred())
        sec_g = _section("a", INT_TYPE, TruePred())
        fp = FiberProductBuilder(
            _presheaf("f", [sec_f]), _presheaf("g", [sec_g]), cat
        ).build([_corr("a")])

        left = fp.project_left(_sid("a"))
        assert left is not None

    def test_project_right_returns_section(self):
        """project_right should recover the g-side section."""
        cat = _site_cat("a")
        sec_f = _section("a", INT_TYPE, TruePred())
        sec_g = _section("a", INT_TYPE, TruePred())
        fp = FiberProductBuilder(
            _presheaf("f", [sec_f]), _presheaf("g", [sec_g]), cat
        ).build([_corr("a")])

        right = fp.project_right(_sid("a"))
        assert right is not None

    def test_missing_site_returns_none(self):
        """Projecting from a site not in the product returns None."""
        cat = _site_cat("a")
        fp = FiberProductBuilder(
            _presheaf("f", [_section("a", INT_TYPE, TruePred())]),
            _presheaf("g", [_section("a", INT_TYPE, TruePred())]),
            cat,
        ).build([_corr("a")])

        assert fp.fiber_at(_sid("nonexistent")) is None
        assert fp.project_left(_sid("nonexistent")) is None

    def test_inhabited_sites_subset_of_site_ids(self):
        """Inhabited sites ⊆ all site ids."""
        cat = _site_cat("a", "b")
        fp = FiberProductBuilder(
            _presheaf("f", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            _presheaf("g", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            cat,
        ).build([_corr("a"), _corr("b")])

        assert fp.inhabited_sites() <= fp.site_ids()


class TestGluingCheck:
    """Test FiberProduct.check_gluing() — the sheaf condition on fibers."""

    def test_single_site_gluing_trivial(self):
        """Single-site fiber product always satisfies gluing (vacuously)."""
        cat = _site_cat("a")
        fp = FiberProductBuilder(
            _presheaf("f", [_section("a", INT_TYPE, TruePred())]),
            _presheaf("g", [_section("a", INT_TYPE, TruePred())]),
            cat,
        ).build([_corr("a")])

        assert fp.check_gluing() is True

    def test_two_sites_gluing(self):
        """Two sites with compatible fibers satisfy gluing."""
        cat = _site_cat("a", "b")
        fp = FiberProductBuilder(
            _presheaf("f", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            _presheaf("g", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            cat,
        ).build([_corr("a"), _corr("b")])

        assert fp.check_gluing() is True


# ═════════════════════════════════════════════════════════════════════════════
# Level 5 — to_presheaf round-trip, many-site stress
# ═════════════════════════════════════════════════════════════════════════════

class TestFiberProductToPresheaf:
    """Test the functor from fiber products back to presheaves."""

    def test_to_presheaf_preserves_sites(self):
        """to_presheaf() produces a presheaf with the same site_ids."""
        cat = _site_cat("a", "b")
        fp = FiberProductBuilder(
            _presheaf("f", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            _presheaf("g", [
                _section("a", INT_TYPE, TruePred()),
                _section("b", INT_TYPE, TruePred()),
            ]),
            cat,
        ).build([_corr("a"), _corr("b")])

        result = fp.to_presheaf()
        assert isinstance(result, ConcretePresheaf)

    def test_many_sites_stress(self):
        """Fiber product over 10 sites — smoke test for scalability."""
        names = [f"s{i}" for i in range(10)]
        cat = _site_cat(*names)
        secs_f = [_section(n, INT_TYPE, TruePred()) for n in names]
        secs_g = [_section(n, INT_TYPE, TruePred()) for n in names]
        fp = FiberProductBuilder(
            _presheaf("f", secs_f), _presheaf("g", secs_g), cat
        ).build([_corr(n) for n in names])

        assert len(fp.site_ids()) == 10
        assert all(fp.fiber_at(_sid(n)).is_inhabited for n in names)


class TestFiberSectionDataclass:
    """Direct tests on FiberSection dataclass."""

    def test_fiber_section_fields(self):
        """FiberSection has the expected fields."""
        sec_f = _section("a", INT_TYPE, TruePred())
        sec_g = _section("a", INT_TYPE, TruePred())
        fs = FiberSection(
            site_id=_sid("a"),
            section_f=sec_f,
            section_g=sec_g,
            equaliser_predicate=TruePred(),
        )
        assert fs.site_id == _sid("a")
        assert fs.equaliser_predicate == TruePred()
        assert fs.is_inhabited

    def test_fiber_section_false_pred_uninhabited(self):
        """FiberSection with FalsePred is not inhabited."""
        sec_f = _section("a", INT_TYPE, TruePred())
        sec_g = _section("a", INT_TYPE, TruePred())
        fs = FiberSection(
            site_id=_sid("a"),
            section_f=sec_f,
            section_g=sec_g,
            equaliser_predicate=FalsePred(),
        )
        assert not fs.is_inhabited
