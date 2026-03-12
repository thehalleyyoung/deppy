"""Tests for deppy.surface.theorem_lowering -- theorem/lemma to proof sites.

Exercises lowering of theorem/lemma contracts into TheoremSeed/LemmaSeed
objects, dependency graph construction, topological ordering, and
proof site creation on Covers.
"""

from __future__ import annotations

import pytest

from deppy.surface.theorem_lowering import (
    LemmaSeed,
    ProofTransportSeed,
    TheoremSeed,
    build_dependency_graph,
    create_proof_sites,
    lower_assumption,
    topological_order,
    resolve_dependencies,
)
from deppy.contracts.base import (
    Predicate as ContractPredicate,
    PredicateKind,
    SourceLocation,
    Term,
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
    var_terms = tuple(Term.var(v) for v in (free_vars or []))
    return ContractPredicate(
        kind=PredicateKind.ATOMIC,
        terms=var_terms,
        _source_text=text,
    )


def _make_trivial_predicate() -> ContractPredicate:
    return ContractPredicate(
        kind=PredicateKind.TRUE,
        description="true",
    )


def _make_source_location(file="test.py", line=10, col=0) -> SourceLocation:
    return SourceLocation(file=file, line=line, col=col)


# ===================================================================
# TestTheoremSeed
# ===================================================================

class TestTheoremSeed:
    """Test TheoremSeed dataclass."""

    def test_creation(self):
        pred = _make_predicate("forall x. f(x) > 0", ["x"])
        seed = TheoremSeed(
            name="positivity",
            statement=pred,
        )
        assert seed.name == "positivity"
        assert seed.trust == TrustLevel.PROOF_BACKED

    def test_is_trivial(self):
        trivial = _make_trivial_predicate()
        seed = TheoremSeed(name="triv", statement=trivial)
        assert seed.is_trivial is True

    def test_not_trivial(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(name="pos", statement=pred)
        assert seed.is_trivial is False

    def test_has_proof(self):
        pred = _make_predicate("x > 0", ["x"])
        seed_no_proof = TheoremSeed(name="th", statement=pred)
        assert seed_no_proof.has_proof is False
        seed_with_proof = TheoremSeed(
            name="th", statement=pred, proof_body=lambda: None
        )
        assert seed_with_proof.has_proof is True

    def test_free_variables(self):
        pred = _make_predicate("x + y > 0", ["x", "y"])
        seed = TheoremSeed(name="th", statement=pred)
        assert "x" in seed.free_variables
        assert "y" in seed.free_variables

    def test_to_site_id(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(name="my_theorem", statement=pred)
        sid = seed.to_site_id()
        assert isinstance(sid, SiteId)
        assert sid.kind == SiteKind.PROOF
        assert sid.name == "my_theorem"

    def test_to_local_section(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(name="th", statement=pred)
        section = seed.to_local_section()
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.PROOF_BACKED
        assert "statement" in section.refinements
        assert "theorem_name" in section.refinements

    def test_to_local_section_with_proof(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(
            name="th", statement=pred, proof_body=lambda: None
        )
        section = seed.to_local_section()
        assert "proof_body" in section.witnesses

    def test_dependency_graph_entry(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(
            name="th",
            statement=pred,
            dependencies=("lemma1", "lemma2"),
        )
        name, deps = seed.dependency_graph_entry()
        assert name == "th"
        assert "lemma1" in deps
        assert "lemma2" in deps

    def test_repr(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(name="th", statement=pred)
        assert "TheoremSeed" in repr(seed)
        assert "unproved" in repr(seed)

    def test_pretty(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = TheoremSeed(
            name="th",
            statement=pred,
            dependencies=("lem1",),
        )
        pretty = seed.pretty()
        assert "TheoremSeed" in pretty
        assert "lem1" in pretty


# ===================================================================
# TestLemmaSeed
# ===================================================================

class TestLemmaSeed:
    """Test LemmaSeed dataclass."""

    def test_creation(self):
        pred = _make_predicate("helper fact", ["x"])
        seed = LemmaSeed(name="helper", statement=pred)
        assert seed.name == "helper"
        assert seed.trust == TrustLevel.PROOF_BACKED

    def test_to_site_id(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = LemmaSeed(name="lem1", statement=pred)
        sid = seed.to_site_id()
        assert isinstance(sid, SiteId)
        assert sid.kind == SiteKind.PROOF
        assert "lemma" in sid.name

    def test_to_local_section(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = LemmaSeed(name="lem1", statement=pred)
        section = seed.to_local_section()
        assert isinstance(section, LocalSection)
        assert section.refinements.get("is_lemma") is True

    def test_as_theorem_seed(self):
        pred = _make_predicate("x > 0", ["x"])
        lemma = LemmaSeed(
            name="lem",
            statement=pred,
            proof_body=lambda: None,
        )
        theorem = lemma.as_theorem_seed()
        assert isinstance(theorem, TheoremSeed)
        assert theorem.name == "lem"
        assert theorem.has_proof is True

    def test_used_by(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = LemmaSeed(
            name="lem",
            statement=pred,
            used_by=("theorem1", "theorem2"),
        )
        assert seed.used_by == ("theorem1", "theorem2")

    def test_is_trivial(self):
        trivial = _make_trivial_predicate()
        seed = LemmaSeed(name="triv", statement=trivial)
        assert seed.is_trivial is True

    def test_repr_and_pretty(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = LemmaSeed(name="lem", statement=pred)
        assert "LemmaSeed" in repr(seed)
        assert "LemmaSeed" in seed.pretty()


# ===================================================================
# TestProofTransportSeed
# ===================================================================

class TestProofTransportSeed:
    """Test ProofTransportSeed dataclass."""

    def test_creation(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ProofTransportSeed(
            proof_site_name="theorem1",
            program_site_name="func.x",
            transported_proposition=pred,
        )
        assert seed.proof_site_name == "theorem1"
        assert seed.program_site_name == "func.x"

    def test_pretty(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ProofTransportSeed(
            proof_site_name="th1",
            program_site_name="f.x",
            transported_proposition=pred,
        )
        assert "th1" in seed.pretty()
        assert "f.x" in seed.pretty()

    def test_repr(self):
        pred = _make_predicate("x > 0", ["x"])
        seed = ProofTransportSeed(
            proof_site_name="th1",
            program_site_name="f.x",
            transported_proposition=pred,
        )
        assert "ProofTransportSeed" in repr(seed)


# ===================================================================
# TestDependencyGraph
# ===================================================================

class TestDependencyGraph:
    """Test dependency graph building and topological ordering."""

    def test_build_graph_empty(self):
        graph = build_dependency_graph([], [])
        assert graph == {}

    def test_build_graph_single_theorem(self):
        pred = _make_predicate("x > 0", ["x"])
        th = TheoremSeed(name="th1", statement=pred, dependencies=("lem1",))
        graph = build_dependency_graph([th], [])
        assert "th1" in graph
        assert "lem1" in graph["th1"]

    def test_build_graph_with_lemma(self):
        pred = _make_predicate("x > 0", ["x"])
        th = TheoremSeed(name="th1", statement=pred, dependencies=("lem1",))
        lem = LemmaSeed(name="lem1", statement=pred, used_by=("th1",))
        graph = build_dependency_graph([th], [lem])
        assert "th1" in graph
        assert "lem1" in graph

    def test_topological_order_linear(self):
        graph = {
            "c": ["b"],
            "b": ["a"],
            "a": [],
        }
        order = topological_order(graph)
        assert order.index("a") < order.index("b")
        assert order.index("b") < order.index("c")

    def test_topological_order_diamond(self):
        graph = {
            "d": ["b", "c"],
            "b": ["a"],
            "c": ["a"],
            "a": [],
        }
        order = topological_order(graph)
        assert order.index("a") < order.index("b")
        assert order.index("a") < order.index("c")
        assert order.index("b") < order.index("d")
        assert order.index("c") < order.index("d")

    def test_topological_order_cycle_raises(self):
        graph = {
            "a": ["b"],
            "b": ["a"],
        }
        with pytest.raises(ValueError, match="[Cc]ycle"):
            topological_order(graph)

    def test_resolve_dependencies(self):
        pred = _make_predicate("x > 0", ["x"])
        th = TheoremSeed(name="main", statement=pred, dependencies=("helper",))
        lem = LemmaSeed(name="helper", statement=pred, used_by=())
        order = resolve_dependencies([th], [lem])
        assert isinstance(order, list)
        assert "main" in order
        assert "helper" in order


# ===================================================================
# TestCreateProofSites
# ===================================================================

class TestCreateProofSites:
    """Test create_proof_sites Cover enrichment."""

    def test_adds_theorem_proof_site(self):
        pred = _make_predicate("x > 0", ["x"])
        th = TheoremSeed(name="th1", statement=pred)
        cover = Cover()
        enriched = create_proof_sites([th], [], [], [], cover)
        assert len(enriched.sites) >= 1
        # Check a proof site was added
        proof_ids = [sid for sid in enriched.sites if sid.kind == SiteKind.PROOF]
        assert len(proof_ids) >= 1

    def test_adds_lemma_proof_site(self):
        pred = _make_predicate("x > 0", ["x"])
        lem = LemmaSeed(name="lem1", statement=pred)
        cover = Cover()
        enriched = create_proof_sites([], [lem], [], [], cover)
        proof_ids = [sid for sid in enriched.sites if sid.kind == SiteKind.PROOF]
        assert len(proof_ids) >= 1

    def test_trivial_seed_skipped(self):
        trivial = _make_trivial_predicate()
        th = TheoremSeed(name="triv", statement=trivial)
        cover = Cover()
        enriched = create_proof_sites([th], [], [], [], cover)
        assert len(enriched.sites) == 0

    def test_preserves_existing_cover_sites(self):
        existing_id = SiteId(kind=SiteKind.SSA_VALUE, name="existing")
        cover = Cover(sites={existing_id: "data"})
        pred = _make_predicate("x > 0", ["x"])
        th = TheoremSeed(name="th1", statement=pred)
        enriched = create_proof_sites([th], [], [], [], cover)
        assert existing_id in enriched.sites

    def test_overlaps_between_proof_sites(self):
        pred = _make_predicate("x > 0", ["x"])
        th1 = TheoremSeed(name="th1", statement=pred)
        th2 = TheoremSeed(name="th2", statement=pred)
        cover = Cover()
        enriched = create_proof_sites([th1, th2], [], [], [], cover)
        assert len(enriched.overlaps) >= 1

    def test_empty_seeds_preserves_cover(self):
        cover = Cover()
        enriched = create_proof_sites([], [], [], [], cover)
        assert len(enriched.sites) == 0
        assert len(enriched.morphisms) == 0


# ===================================================================
# TestLowerAssumption
# ===================================================================

class TestLowerAssumption:
    """Test lower_assumption function."""

    def test_assumption_becomes_theorem_seed(self):
        from deppy.contracts.theorem import AssumptionContract
        pred = _make_predicate("x > 0", ["x"])
        contract = AssumptionContract(
            proposition=pred,
            justification="tested empirically",
        )
        seed = lower_assumption(contract)
        assert isinstance(seed, TheoremSeed)
        assert seed.trust == TrustLevel.ASSUMED
        assert seed.has_proof is False
        assert "assumption" in seed.name
