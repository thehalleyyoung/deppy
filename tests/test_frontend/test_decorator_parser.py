"""Tests for deppy.frontend.decorator_parser -- decorator seed extraction.

Exercises parsing of @deppy.requires, @deppy.ensures, @deppy.theorem,
@deppy.decreases, @deppy.invariant, @deppy.transport, @deppy.ghost,
@deppy.witness, and @deppy.axiom decorators from AST nodes.
"""

from __future__ import annotations

import ast
import pytest

from deppy.frontend.decorator_parser import (
    ContractSeed,
    DecreaseSeed,
    DecoratorParser,
    GhostSeed,
    InvariantSeed,
    ProofSeed,
    SeedKind,
    TransportSeed,
    WitnessSeed,
    extract_contracts,
    extract_invariant_seeds,
    extract_proof_seeds,
    extract_transport_seeds,
    parse_decorators,
)
from deppy.core._protocols import SiteKind, TrustLevel


# ===================================================================
# Helpers
# ===================================================================

def _get_decorator_nodes(source: str):
    """Parse source and return the decorator_list of the first function."""
    tree = ast.parse(source, mode="exec")
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node.decorator_list
    raise ValueError("No function definition found")


def _parse_single(source: str):
    """Parse a single decorator from a function definition."""
    decs = _get_decorator_nodes(source)
    parser = DecoratorParser(filename="test.py")
    results = [parser.parse(d) for d in decs]
    seeds = [r for r in results if r is not None]
    return seeds


# ===================================================================
# TestRequiresDecorator
# ===================================================================

class TestRequiresDecorator:
    """Test @deppy.requires parsing."""

    def test_basic_requires(self):
        seeds = _parse_single("""
@deppy.requires("x > 0")
def f(x): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, ContractSeed)
        assert seed.kind == SeedKind.REQUIRES
        assert seed.predicate == "x > 0"

    def test_requires_is_precondition(self):
        seeds = _parse_single("""
@deppy.requires("x > 0")
def f(x): pass
""")
        seed = seeds[0]
        assert seed.is_precondition is True
        assert seed.is_postcondition is False

    def test_requires_boundary_kind(self):
        seeds = _parse_single("""
@deppy.requires("x > 0")
def f(x): pass
""")
        assert seeds[0].boundary_kind == SiteKind.ARGUMENT_BOUNDARY

    def test_requires_with_over(self):
        seeds = _parse_single("""
@deppy.requires("x > 0", over=("x",))
def f(x, y): pass
""")
        seed = seeds[0]
        assert seed.over == ("x",)

    def test_requires_with_trust(self):
        seeds = _parse_single("""
@deppy.requires("x > 0", trust="proof_backed")
def f(x): pass
""")
        assert seeds[0].trust == TrustLevel.PROOF_BACKED

    def test_requires_default_trust(self):
        seeds = _parse_single("""
@deppy.requires("x > 0")
def f(x): pass
""")
        assert seeds[0].trust == TrustLevel.ASSUMED

    def test_requires_with_label(self):
        seeds = _parse_single("""
@deppy.requires("x > 0", label="positivity")
def f(x): pass
""")
        assert seeds[0].label == "positivity"

    def test_requires_dp_alias(self):
        seeds = _parse_single("""
@dp.requires("x > 0")
def f(x): pass
""")
        assert len(seeds) == 1
        assert seeds[0].kind == SeedKind.REQUIRES

    def test_requires_with_quantifier(self):
        seeds = _parse_single("""
@deppy.requires("x > 0", quantifier="forall")
def f(x): pass
""")
        assert seeds[0].quantifier == "forall"


# ===================================================================
# TestEnsuresDecorator
# ===================================================================

class TestEnsuresDecorator:
    """Test @deppy.ensures parsing."""

    def test_basic_ensures(self):
        seeds = _parse_single("""
@deppy.ensures("result > 0")
def f(x): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, ContractSeed)
        assert seed.kind == SeedKind.ENSURES

    def test_ensures_is_postcondition(self):
        seeds = _parse_single("""
@deppy.ensures("result > 0")
def f(x): pass
""")
        assert seeds[0].is_postcondition is True
        assert seeds[0].is_precondition is False

    def test_ensures_boundary_kind(self):
        seeds = _parse_single("""
@deppy.ensures("result > 0")
def f(x): pass
""")
        assert seeds[0].boundary_kind == SiteKind.RETURN_OUTPUT_BOUNDARY

    def test_ensures_with_over(self):
        seeds = _parse_single("""
@deppy.ensures("result > 0", over=("result",))
def f(x): pass
""")
        assert seeds[0].over == ("result",)


# ===================================================================
# TestTheoremDecorator
# ===================================================================

class TestTheoremDecorator:
    """Test @deppy.theorem parsing."""

    def test_basic_theorem(self):
        seeds = _parse_single("""
@deppy.theorem("monotonicity")
def f(x): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, ProofSeed)
        assert seed.kind == SeedKind.THEOREM
        assert seed.name == "monotonicity"

    def test_theorem_with_proof_method(self):
        seeds = _parse_single("""
@deppy.theorem("safety", proof_method="induction")
def f(x): pass
""")
        assert seeds[0].proof_method == "induction"

    def test_theorem_with_dependencies(self):
        seeds = _parse_single("""
@deppy.theorem("safety", dependencies=("lemma1", "lemma2"))
def f(x): pass
""")
        assert seeds[0].dependencies == ("lemma1", "lemma2")

    def test_theorem_is_lemma_flag(self):
        seeds = _parse_single("""
@deppy.theorem("helper", lemma=True)
def f(x): pass
""")
        assert seeds[0].is_lemma is True

    def test_theorem_boundary_kind(self):
        seeds = _parse_single("""
@deppy.theorem("th")
def f(x): pass
""")
        assert seeds[0].boundary_kind == SiteKind.PROOF

    def test_theorem_with_statement(self):
        seeds = _parse_single("""
@deppy.theorem("th", statement="forall x. x > 0 -> f(x) > 0")
def f(x): pass
""")
        assert seeds[0].statement == "forall x. x > 0 -> f(x) > 0"


# ===================================================================
# TestAxiomDecorator
# ===================================================================

class TestAxiomDecorator:
    """Test @deppy.axiom parsing."""

    def test_basic_axiom(self):
        seeds = _parse_single("""
@deppy.axiom("commutativity")
def f(x, y): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, ProofSeed)
        assert seed.kind == SeedKind.AXIOM
        assert seed.name == "commutativity"

    def test_axiom_with_statement(self):
        seeds = _parse_single("""
@deppy.axiom("comm", statement="forall x y. f(x,y) == f(y,x)")
def f(x, y): pass
""")
        assert seeds[0].statement == "forall x y. f(x,y) == f(y,x)"


# ===================================================================
# TestDecreasesDecorator
# ===================================================================

class TestDecreasesDecorator:
    """Test @deppy.decreases parsing."""

    def test_basic_decreases(self):
        seeds = _parse_single("""
@deppy.decreases("n")
def f(n): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, DecreaseSeed)
        assert seed.expression == "n"
        assert seed.kind == SeedKind.DECREASES

    def test_decreases_with_bound(self):
        seeds = _parse_single("""
@deppy.decreases("n", bound="0")
def f(n): pass
""")
        assert seeds[0].bound == "0"

    def test_decreases_boundary_kind(self):
        seeds = _parse_single("""
@deppy.decreases("n")
def f(n): pass
""")
        assert seeds[0].boundary_kind == SiteKind.LOOP_HEADER_INVARIANT

    def test_decreases_with_over(self):
        seeds = _parse_single("""
@deppy.decreases("n - m", over=("n", "m"))
def f(n, m): pass
""")
        assert seeds[0].over == ("n", "m")


# ===================================================================
# TestInvariantDecorator
# ===================================================================

class TestInvariantDecorator:
    """Test @deppy.invariant parsing."""

    def test_basic_invariant(self):
        seeds = _parse_single("""
@deppy.invariant("i >= 0")
def f(): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, InvariantSeed)
        assert seed.predicate == "i >= 0"
        assert seed.kind == SeedKind.INVARIANT

    def test_invariant_with_variables(self):
        seeds = _parse_single("""
@deppy.invariant("i >= 0 and i < n", variables=("i", "n"))
def f(): pass
""")
        assert seeds[0].variables == ("i", "n")

    def test_invariant_with_label(self):
        seeds = _parse_single("""
@deppy.invariant("i >= 0", label="loop_bound")
def f(): pass
""")
        assert seeds[0].label == "loop_bound"

    def test_invariant_boundary_kind(self):
        seeds = _parse_single("""
@deppy.invariant("i >= 0")
def f(): pass
""")
        assert seeds[0].boundary_kind == SiteKind.LOOP_HEADER_INVARIANT


# ===================================================================
# TestTransportDecorator
# ===================================================================

class TestTransportDecorator:
    """Test @deppy.transport parsing."""

    def test_basic_transport(self):
        seeds = _parse_single("""
@deppy.transport("source_site", "target_site")
def f(): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, TransportSeed)
        assert seed.source == "source_site"
        assert seed.target == "target_site"
        assert seed.kind == SeedKind.TRANSPORT

    def test_transport_with_via(self):
        seeds = _parse_single("""
@deppy.transport("src", "tgt", via="monotone_map")
def f(): pass
""")
        assert seeds[0].via == "monotone_map"

    def test_transport_with_preserves(self):
        seeds = _parse_single("""
@deppy.transport("src", "tgt", preserves=("shape", "dtype"))
def f(): pass
""")
        assert seeds[0].preserves == ("shape", "dtype")

    def test_transport_boundary_kind(self):
        seeds = _parse_single("""
@deppy.transport("src", "tgt")
def f(): pass
""")
        assert seeds[0].boundary_kind == SiteKind.PROOF


# ===================================================================
# TestGhostDecorator
# ===================================================================

class TestGhostDecorator:
    """Test @deppy.ghost parsing."""

    def test_basic_ghost(self):
        seeds = _parse_single("""
@deppy.ghost("phantom")
def f(): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, GhostSeed)
        assert seed.name == "phantom"
        assert seed.kind == SeedKind.GHOST

    def test_ghost_with_type(self):
        seeds = _parse_single("""
@deppy.ghost("counter", type="int")
def f(): pass
""")
        assert seeds[0].type_str == "int"


# ===================================================================
# TestWitnessDecorator
# ===================================================================

class TestWitnessDecorator:
    """Test @deppy.witness parsing."""

    def test_basic_witness(self):
        seeds = _parse_single("""
@deppy.witness("proof_term")
def f(): pass
""")
        assert len(seeds) == 1
        seed = seeds[0]
        assert isinstance(seed, WitnessSeed)
        assert seed.name == "proof_term"
        assert seed.kind == SeedKind.WITNESS

    def test_witness_with_type(self):
        seeds = _parse_single("""
@deppy.witness("w", type="Nat")
def f(): pass
""")
        assert seeds[0].type_str == "Nat"


# ===================================================================
# TestParseAll
# ===================================================================

class TestParseAll:
    """Test parse_all and parse_decorators."""

    def test_mixed_decorators(self):
        decs = _get_decorator_nodes("""
@deppy.requires("x > 0")
@deppy.ensures("result > 0")
@staticmethod
def f(x): pass
""")
        parser = DecoratorParser(filename="test.py")
        seeds, other = parser.parse_all(decs)
        assert len(seeds) == 2
        assert len(other) == 1
        assert any(isinstance(s, ContractSeed) and s.kind == SeedKind.REQUIRES for s in seeds)
        assert any(isinstance(s, ContractSeed) and s.kind == SeedKind.ENSURES for s in seeds)

    def test_parse_decorators_convenience(self):
        decs = _get_decorator_nodes("""
@deppy.theorem("th1")
@deppy.requires("x > 0")
def f(x): pass
""")
        seeds, other = parse_decorators(decs, filename="test.py")
        assert len(seeds) == 2
        assert len(other) == 0

    def test_non_deppy_decorators_pass_through(self):
        decs = _get_decorator_nodes("""
@property
@functools.cache
def f(): pass
""")
        parser = DecoratorParser()
        seeds, other = parser.parse_all(decs)
        assert len(seeds) == 0
        assert len(other) == 2

    def test_multiple_requires(self):
        decs = _get_decorator_nodes("""
@deppy.requires("x > 0")
@deppy.requires("x < 100")
def f(x): pass
""")
        parser = DecoratorParser()
        seeds, _ = parser.parse_all(decs)
        assert len(seeds) == 2
        predicates = {s.predicate for s in seeds}
        assert "x > 0" in predicates
        assert "x < 100" in predicates


# ===================================================================
# TestExtractConvenience
# ===================================================================

class TestExtractConvenience:
    """Test extract_contracts, extract_proof_seeds, etc."""

    def test_extract_contracts(self):
        decs = _get_decorator_nodes("""
@deppy.requires("x > 0")
@deppy.ensures("result > 0")
@deppy.theorem("th")
def f(x): pass
""")
        seeds, _ = parse_decorators(decs)
        requires, ensures = extract_contracts(seeds)
        assert len(requires) == 1
        assert len(ensures) == 1
        assert requires[0].kind == SeedKind.REQUIRES
        assert ensures[0].kind == SeedKind.ENSURES

    def test_extract_proof_seeds(self):
        decs = _get_decorator_nodes("""
@deppy.theorem("th1")
@deppy.axiom("ax1")
@deppy.requires("x > 0")
def f(x): pass
""")
        seeds, _ = parse_decorators(decs)
        proofs = extract_proof_seeds(seeds)
        assert len(proofs) == 2

    def test_extract_invariant_seeds(self):
        decs = _get_decorator_nodes("""
@deppy.invariant("i >= 0")
@deppy.requires("x > 0")
def f(x): pass
""")
        seeds, _ = parse_decorators(decs)
        invs = extract_invariant_seeds(seeds)
        assert len(invs) == 1

    def test_extract_transport_seeds(self):
        decs = _get_decorator_nodes("""
@deppy.transport("a", "b")
@deppy.requires("x > 0")
def f(x): pass
""")
        seeds, _ = parse_decorators(decs)
        transports = extract_transport_seeds(seeds)
        assert len(transports) == 1


# ===================================================================
# TestSeedKind
# ===================================================================

class TestSeedKind:
    """Test SeedKind enum values."""

    def test_all_kinds_present(self):
        expected = {
            "requires", "ensures", "theorem", "decreases",
            "invariant", "transport", "ghost", "witness", "axiom",
        }
        actual = {k.value for k in SeedKind}
        assert expected == actual

    def test_seed_kind_from_value(self):
        assert SeedKind("requires") == SeedKind.REQUIRES
        assert SeedKind("theorem") == SeedKind.THEOREM
