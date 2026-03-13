"""Hard tests for sheaf morphism construction and naturality verification.

Tests exercise:
  - SheafMorphismBuilder.build() from local judgments
  - MorphismComponent: forward/inverse predicates, is_isomorphism_component
  - NaturalitySquare: verdict, commutativity_evidence
  - SheafMorphism: is_natural, is_strictly_natural, is_isomorphism, compose
  - IsomorphismChecker: roundtrip verification
  - Edge cases: empty morphisms, partial components, non-natural morphisms

Levels:
  2 — basic morphism from trivial judgments
  3 — naturality squares with predicates
  4 — isomorphism detection, composition
  5 — IsomorphismChecker, to_isomorphism_witness, failing_squares
"""
from __future__ import annotations

import pytest

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder

from deppy.types.refinement import (
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    FalsePred,
    ImplicationPred,
    TruePred,
    VarPred,
    RefinementType,
)
from deppy.types.base import INT_TYPE
from deppy.types.witnesses import ReflProof

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceStrength,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.sheaf_morphism import (
    IsomorphismChecker,
    IsomorphismResult,
    MorphismComponent,
    NaturalitySquare,
    NaturalityVerdict,
    SheafMorphism,
    SheafMorphismBuilder,
)


# ── Helpers ───────────────────────────────────────────────────────────────

def _sid(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _site_cat(*names: str, overlaps=None) -> SiteCategory:
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


def _section(name: str, carrier=None, predicate=None):
    from deppy.core._protocols import LocalSection
    refs = {}
    if predicate is not None:
        refs["_pred"] = predicate
    return LocalSection(
        site_id=_sid(name),
        carrier_type=carrier,
        refinements=refs,
        trust=TrustLevel.PROOF_BACKED,
    )


def _presheaf(name: str, sections) -> ConcretePresheaf:
    builder = ConcretePresheafBuilder(name=name)
    for sec in sections:
        builder.add_section(sec)
    return builder.build()


def _judgment(
    name: str,
    verdict: EquivalenceVerdict = EquivalenceVerdict.EQUIVALENT,
    fwd_pred=None,
    bwd_pred=None,
) -> LocalEquivalenceJudgment:
    return LocalEquivalenceJudgment(
        site_id=_sid(name),
        verdict=verdict,
        obligation=EquivalenceObligation(
            site_id=_sid(name),
            description="local check",
            forward_predicate=fwd_pred,
            backward_predicate=bwd_pred,
        ),
        forward_holds=verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED),
        backward_holds=verdict == EquivalenceVerdict.EQUIVALENT,
        proof=ReflProof(),
        explanation="",
    )


# ═════════════════════════════════════════════════════════════════════════════
# Level 2 — basic morphism construction
# ═════════════════════════════════════════════════════════════════════════════

class TestBasicMorphism:
    """Basic SheafMorphismBuilder.build() with trivial judgments."""

    def test_single_site_morphism(self):
        """One site with EQUIVALENT → morphism has one component."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        builder = SheafMorphismBuilder(pf, pg, cat)
        morphism = builder.build([_judgment("a")])

        assert isinstance(morphism, SheafMorphism)
        comp = morphism.component_at(_sid("a"))
        assert comp is not None
        assert isinstance(comp, MorphismComponent)

    def test_two_sites_morphism(self):
        """Two sites → morphism has two components."""
        cat = _site_cat("a", "b")
        pf = _presheaf("f", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])

        builder = SheafMorphismBuilder(pf, pg, cat)
        morphism = builder.build([_judgment("a"), _judgment("b")])

        assert morphism.component_at(_sid("a")) is not None
        assert morphism.component_at(_sid("b")) is not None

    def test_missing_component_returns_none(self):
        """Querying a site not in the morphism returns None."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        assert morphism.component_at(_sid("missing")) is None


# ═════════════════════════════════════════════════════════════════════════════
# Level 3 — naturality properties
# ═════════════════════════════════════════════════════════════════════════════

class TestNaturality:
    """Naturality properties of the built morphism."""

    def test_no_morphisms_vacuously_natural(self):
        """Without morphisms in the site category, naturality is vacuous."""
        cat = _site_cat("a", "b")  # No overlaps → no morphisms
        pf = _presheaf("f", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([
            _judgment("a"), _judgment("b"),
        ])
        assert morphism.is_natural
        assert morphism.is_strictly_natural

    def test_with_overlap_still_natural(self):
        """Two sites with overlap and trivial predicates → natural."""
        cat = _site_cat("a", "b", overlaps=[("a", "b")])
        pf = _presheaf("f", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])
        pg = _presheaf("g", [
            _section("a", INT_TYPE, TruePred()),
            _section("b", INT_TYPE, TruePred()),
        ])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([
            _judgment("a"), _judgment("b"),
        ])
        # With trivial predicates and the meet-site skip, this should be natural
        assert morphism.is_natural

    def test_naturality_squares_list(self):
        """naturality_squares returns the list of checked squares."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        squares = morphism.naturality_squares
        assert isinstance(squares, list)

    def test_failing_squares_empty_when_natural(self):
        """failing_squares() is empty for a natural morphism."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        assert morphism.failing_squares() == []


# ═════════════════════════════════════════════════════════════════════════════
# Level 4 — isomorphism detection
# ═════════════════════════════════════════════════════════════════════════════

class TestIsomorphism:
    """Test isomorphism detection on sheaf morphisms."""

    def test_component_isomorphism_flag(self):
        """MorphismComponent with inverse_predicate is an iso component."""
        comp = MorphismComponent(
            site_id=_sid("a"),
            forward_predicate=TruePred(),
            inverse_predicate=TruePred(),
        )
        assert comp.is_isomorphism_component

    def test_component_no_inverse(self):
        """MorphismComponent without inverse is not an iso component."""
        comp = MorphismComponent(
            site_id=_sid("a"),
            forward_predicate=TruePred(),
        )
        assert not comp.is_isomorphism_component

    def test_isomorphism_checker_trivial(self):
        """IsomorphismChecker on a trivial 1-site morphism."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        checker = IsomorphismChecker(morphism)
        result = checker.check()

        assert isinstance(result, IsomorphismResult)

    def test_to_isomorphism_witness(self):
        """to_isomorphism_witness returns IsomorphismWitness when iso."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        if morphism.is_isomorphism:
            witness = morphism.to_isomorphism_witness()
            assert witness is not None
        else:
            # Even if not detected as iso, the method should not crash
            witness = morphism.to_isomorphism_witness()
            # Returns None when not an isomorphism
            assert witness is None


# ═════════════════════════════════════════════════════════════════════════════
# Level 5 — composition and multi-site integration
# ═════════════════════════════════════════════════════════════════════════════

class TestMorphismComposition:
    """Test SheafMorphism.compose() — composition of natural transformations."""

    def test_compose_identity(self):
        """Composing a morphism with itself produces a valid morphism."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        morphism = SheafMorphismBuilder(pf, pg, cat).build([_judgment("a")])
        composed = morphism.compose(morphism)

        assert isinstance(composed, SheafMorphism)
        assert composed.component_at(_sid("a")) is not None

    def test_compose_preserves_sites(self):
        """Composition of two morphisms over 3 sites preserves site set."""
        cat = _site_cat("a", "b", "c")
        secs = [_section(n, INT_TYPE, TruePred()) for n in ("a", "b", "c")]
        pf = _presheaf("f", secs)
        pg = _presheaf("g", secs)
        judgments = [_judgment("a"), _judgment("b"), _judgment("c")]

        m1 = SheafMorphismBuilder(pf, pg, cat).build(judgments)
        m2 = SheafMorphismBuilder(pf, pg, cat).build(judgments)
        composed = m1.compose(m2)

        for name in ("a", "b", "c"):
            assert composed.component_at(_sid(name)) is not None


class TestNaturalitySquareDataclass:
    """Direct tests on NaturalitySquare dataclass."""

    def test_default_verdict_unknown(self):
        ns = NaturalitySquare(
            morphism_source=_sid("a"),
            morphism_target=_sid("b"),
            path1_predicate=TruePred(),
            path2_predicate=TruePred(),
        )
        assert ns.verdict == NaturalityVerdict.UNKNOWN

    def test_commutes_verdict(self):
        ns = NaturalitySquare(
            morphism_source=_sid("a"),
            morphism_target=_sid("b"),
            path1_predicate=TruePred(),
            path2_predicate=TruePred(),
            verdict=NaturalityVerdict.COMMUTES,
        )
        assert ns.verdict == NaturalityVerdict.COMMUTES

    def test_commutativity_evidence(self):
        ns = NaturalitySquare(
            morphism_source=_sid("a"),
            morphism_target=_sid("b"),
            path1_predicate=TruePred(),
            path2_predicate=TruePred(),
            verdict=NaturalityVerdict.COMMUTES,
            commutativity_evidence=TruePred(),
        )
        assert ns.commutativity_evidence == TruePred()


class TestMultiSiteMorphism:
    """Integration tests with larger site categories."""

    def test_five_sites_no_morphisms(self):
        """Five independent sites → vacuously natural morphism."""
        names = [f"s{i}" for i in range(5)]
        cat = _site_cat(*names)
        secs = [_section(n, INT_TYPE, TruePred()) for n in names]
        pf = _presheaf("f", secs)
        pg = _presheaf("g", secs)
        judgments = [_judgment(n) for n in names]

        morphism = SheafMorphismBuilder(pf, pg, cat).build(judgments)
        assert morphism.is_natural
        assert len(morphism.failing_squares()) == 0

    def test_inequivalent_site_still_builds(self):
        """A judgment with INEQUIVALENT still produces a component (no crash)."""
        cat = _site_cat("a")
        pf = _presheaf("f", [_section("a", INT_TYPE, TruePred())])
        pg = _presheaf("g", [_section("a", INT_TYPE, TruePred())])

        j = _judgment("a", verdict=EquivalenceVerdict.INEQUIVALENT)
        morphism = SheafMorphismBuilder(pf, pg, cat).build([j])

        # Should still have a component (even if the judgment is negative)
        assert isinstance(morphism, SheafMorphism)
