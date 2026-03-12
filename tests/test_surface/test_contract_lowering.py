"""Tests for deppy.surface.contract_lowering -- requires/ensures to boundary seeds.

Exercises lowering of requires/ensures contracts into RequiresSeed/EnsuresSeed
objects, deduplication, seed-to-cover application, and the SeedOrigin enum.
"""

from __future__ import annotations

import pytest

from deppy.surface.contract_lowering import (
    ContractSeed,
    EnsuresSeed,
    RequiresSeed,
    SeedOrigin,
    apply_seeds_to_cover,
    deduplicate_ensures,
    deduplicate_requires,
    lower_ensures,
    lower_requires,
    seeds_to_collection,
)
from deppy.contracts.base import (
    Predicate as ContractPredicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
)
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ===================================================================
# Helpers
# ===================================================================

def _make_predicate(text: str, free_vars=None) -> ContractPredicate:
    """Create a simple predicate for testing."""
    terms = tuple(Term.var(v) for v in (free_vars or []))
    return ContractPredicate(
        kind=PredicateKind.ATOMIC,
        terms=terms,
        _source_text=text,
    )


def _make_trivial_predicate() -> ContractPredicate:
    """Create a trivially true predicate."""
    return ContractPredicate.true_()


def _make_source_location(file="test.py", line=10, col=0) -> SourceLocation:
    return SourceLocation(file=file, line=line, col=col)


# ===================================================================
# TestSeedOrigin
# ===================================================================

class TestSeedOrigin:
    """Test SeedOrigin enum."""

    def test_all_origins_present(self):
        expected = {
            "decorator_requires", "decorator_ensures",
            "decorator_ensures_raises", "inferred_requires",
            "inferred_ensures", "library_pack", "proof_transport",
        }
        actual = {o.value for o in SeedOrigin}
        assert expected == actual

    def test_from_value(self):
        assert SeedOrigin("decorator_requires") == SeedOrigin.DECORATOR_REQUIRES


# ===================================================================
# TestContractSeed
# ===================================================================

class TestContractSeed:
    """Test the contract_lowering ContractSeed dataclass."""

    def test_creation(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x",),
            trust=TrustLevel.ASSUMED,
        )
        assert seed.target_params == ("x",)
        assert seed.trust == TrustLevel.ASSUMED

    def test_is_trivial(self):
        trivial = _make_trivial_predicate()
        seed = ContractSeed(
            predicate=trivial,
            target_params=("x",),
        )
        assert seed.is_trivial is True

    def test_not_trivial(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x",),
        )
        assert seed.is_trivial is False

    def test_free_variables(self):
        pred = _make_predicate("x + y > 0", ["x", "y"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x", "y"),
        )
        assert "x" in seed.free_variables
        assert "y" in seed.free_variables

    def test_with_trust(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x",),
            trust=TrustLevel.ASSUMED,
        )
        upgraded = seed.with_trust(TrustLevel.PROOF_BACKED)
        assert upgraded.trust == TrustLevel.PROOF_BACKED
        assert upgraded.predicate == seed.predicate

    def test_pretty(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x",),
        )
        pretty_str = seed.pretty()
        assert "x" in pretty_str

    def test_repr(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ContractSeed(
            predicate=pred,
            target_params=("x",),
        )
        assert "ContractSeed" in repr(seed)


# ===================================================================
# TestRequiresSeed
# ===================================================================

class TestRequiresSeed:
    """Test RequiresSeed dataclass and lowering."""

    def test_creation(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(
            predicate=pred,
            parameter="x",
            trust=TrustLevel.ASSUMED,
        )
        assert seed.parameter == "x"
        assert seed.trust == TrustLevel.ASSUMED

    def test_effective_predicate_with_requirement(self):
        pred = _make_predicate("x > 0", ["x"])
        req_pred = _make_predicate("x >= 1", ["x"])
        seed = RequiresSeed(
            predicate=pred,
            parameter="x",
            requirement_predicate=req_pred,
        )
        assert seed.effective_predicate is req_pred

    def test_effective_predicate_fallback(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(
            predicate=pred,
            parameter="x",
        )
        assert seed.effective_predicate is pred

    def test_to_site_id(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(
            predicate=pred,
            parameter="x",
        )
        sid = seed.to_site_id("my_func")
        assert isinstance(sid, SiteId)
        assert sid.kind == SiteKind.ARGUMENT_BOUNDARY
        assert "my_func" in sid.name
        assert "x" in sid.name

    def test_to_local_section(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(
            predicate=pred,
            parameter="x",
            trust=TrustLevel.ASSUMED,
        )
        section = seed.to_local_section("my_func")
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.ASSUMED
        assert "predicate" in section.refinements

    def test_is_trivial(self):
        trivial = _make_trivial_predicate()
        seed = RequiresSeed(predicate=trivial, parameter="x")
        assert seed.is_trivial is True

    def test_pretty(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(predicate=pred, parameter="x")
        assert "RequiresSeed" in seed.pretty()


# ===================================================================
# TestEnsuresSeed
# ===================================================================

class TestEnsuresSeed:
    """Test EnsuresSeed dataclass and lowering."""

    def test_creation(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(
            predicate=pred,
            result_name="result",
            trust=TrustLevel.ASSUMED,
        )
        assert seed.result_name == "result"

    def test_result_component_normal(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(predicate=pred)
        assert seed.result_component == "result"

    def test_result_component_exceptional(self):
        pred = _make_predicate("True", [])
        seed = EnsuresSeed(
            predicate=pred,
            is_exceptional=True,
            exception_type="ValueError",
        )
        assert "raises" in seed.result_component
        assert "ValueError" in seed.result_component

    def test_is_relational(self):
        pred = _make_predicate("result > x", ["result", "x"])
        seed = EnsuresSeed(
            predicate=pred,
            input_params=("x",),
        )
        assert seed.is_relational() is True

    def test_not_relational(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(predicate=pred)
        assert seed.is_relational() is False

    def test_to_site_id(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(predicate=pred)
        sid = seed.to_site_id("my_func")
        assert isinstance(sid, SiteId)
        assert sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY

    def test_to_local_section(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(predicate=pred, trust=TrustLevel.ASSUMED)
        section = seed.to_local_section("my_func")
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.ASSUMED

    def test_effective_predicate_with_guarantee(self):
        pred = _make_predicate("result > 0", ["result"])
        guar = _make_predicate("result >= 1", ["result"])
        seed = EnsuresSeed(
            predicate=pred,
            guarantee_predicate=guar,
        )
        assert seed.effective_predicate is guar


# ===================================================================
# TestLowerRequires
# ===================================================================

class TestLowerRequires:
    """Test lower_requires function."""

    def test_basic_lowering(self):
        pred = _make_predicate("x > 0", ["x"])
        seeds = lower_requires(pred, ["x", "y"])
        assert len(seeds) >= 1
        assert all(isinstance(s, RequiresSeed) for s in seeds)
        assert any(s.parameter == "x" for s in seeds)

    def test_trivial_predicate_produces_empty(self):
        trivial = _make_trivial_predicate()
        seeds = lower_requires(trivial, ["x"])
        assert len(seeds) == 0

    def test_broadcast_to_all_params(self):
        # Predicate with no free vars matching params => broadcast to all
        pred = ContractPredicate(
            kind=PredicateKind.ATOMIC,
            terms=(),
            _source_text="True == True",
        )
        seeds = lower_requires(pred, ["a", "b"])
        assert len(seeds) >= 1

    def test_custom_trust(self):
        pred = _make_predicate("x > 0", ["x"])
        seeds = lower_requires(
            pred, ["x"],
            trust=TrustLevel.PROOF_BACKED,
        )
        assert all(s.trust == TrustLevel.PROOF_BACKED for s in seeds)

    def test_with_description(self):
        pred = _make_predicate("x > 0", ["x"])
        seeds = lower_requires(
            pred, ["x"],
            description="positivity constraint",
        )
        assert seeds[0].description == "positivity constraint"


# ===================================================================
# TestLowerEnsures
# ===================================================================

class TestLowerEnsures:
    """Test lower_ensures function."""

    def test_basic_lowering(self):
        pred = _make_predicate("result > 0", ["result"])
        seeds = lower_ensures(pred)
        assert len(seeds) == 1
        assert isinstance(seeds[0], EnsuresSeed)
        assert seeds[0].result_name == "result"

    def test_trivial_predicate_empty(self):
        trivial = _make_trivial_predicate()
        seeds = lower_ensures(trivial)
        assert len(seeds) == 0

    def test_exceptional_ensures(self):
        pred = _make_predicate("isinstance(exc, ValueError)", ["exc"])
        seeds = lower_ensures(
            pred,
            is_exceptional=True,
            exception_type="ValueError",
        )
        assert len(seeds) == 1
        assert seeds[0].is_exceptional is True
        assert seeds[0].exception_type == "ValueError"

    def test_with_input_params(self):
        pred = _make_predicate("result > x", ["result", "x"])
        seeds = lower_ensures(
            pred,
            input_params=["x", "y"],
        )
        assert len(seeds) == 1
        # only "x" is in free vars
        assert "x" in seeds[0].input_params

    def test_custom_return_name(self):
        pred = _make_predicate("out > 0", ["out"])
        seeds = lower_ensures(pred, return_name="out")
        assert seeds[0].result_name == "out"


# ===================================================================
# TestDeduplication
# ===================================================================

class TestDeduplication:
    """Test deduplicate_requires and deduplicate_ensures."""

    def test_deduplicate_requires_removes_duplicates(self):
        pred = _make_predicate("x > 0", ["x"])
        s1 = RequiresSeed(predicate=pred, parameter="x", trust=TrustLevel.ASSUMED)
        s2 = RequiresSeed(predicate=pred, parameter="x", trust=TrustLevel.PROOF_BACKED)
        result = deduplicate_requires([s1, s2])
        assert len(result) == 1
        assert result[0].trust == TrustLevel.PROOF_BACKED

    def test_deduplicate_ensures_removes_duplicates(self):
        pred = _make_predicate("result > 0", ["result"])
        s1 = EnsuresSeed(predicate=pred, trust=TrustLevel.ASSUMED)
        s2 = EnsuresSeed(predicate=pred, trust=TrustLevel.PROOF_BACKED)
        result = deduplicate_ensures([s1, s2])
        assert len(result) == 1
        assert result[0].trust == TrustLevel.PROOF_BACKED

    def test_different_params_kept(self):
        pred = _make_predicate("x > 0", ["x"])
        s1 = RequiresSeed(predicate=pred, parameter="x")
        s2 = RequiresSeed(predicate=pred, parameter="y")
        result = deduplicate_requires([s1, s2])
        assert len(result) == 2


# ===================================================================
# TestApplySeedsToCover
# ===================================================================

class TestApplySeedsToCover:
    """Test apply_seeds_to_cover."""

    def test_adds_input_boundary_sites(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(predicate=pred, parameter="x")
        cover = Cover()
        enriched = apply_seeds_to_cover([seed], [], cover, "my_func")
        assert len(enriched.input_boundary) >= 1

    def test_adds_output_boundary_sites(self):
        pred = _make_predicate("result > 0", ["result"])
        seed = EnsuresSeed(predicate=pred)
        cover = Cover()
        enriched = apply_seeds_to_cover([], [seed], cover, "my_func")
        assert len(enriched.output_boundary) >= 1

    def test_trivial_seed_skipped(self):
        trivial = _make_trivial_predicate()
        seed = RequiresSeed(predicate=trivial, parameter="x")
        cover = Cover()
        enriched = apply_seeds_to_cover([seed], [], cover, "my_func")
        assert len(enriched.input_boundary) == 0

    def test_preserves_existing_sites(self):
        existing_id = SiteId(kind=SiteKind.SSA_VALUE, name="existing")
        cover = Cover(sites={existing_id: existing_id})
        pred = _make_predicate("x > 0", ["x"])
        seed = RequiresSeed(predicate=pred, parameter="x")
        enriched = apply_seeds_to_cover([seed], [], cover, "my_func")
        assert existing_id in enriched.sites

    def test_empty_seeds_returns_equivalent_cover(self):
        cover = Cover()
        enriched = apply_seeds_to_cover([], [], cover, "my_func")
        assert len(enriched.sites) == 0
        assert len(enriched.input_boundary) == 0
        assert len(enriched.output_boundary) == 0
