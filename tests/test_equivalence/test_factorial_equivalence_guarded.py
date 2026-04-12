from __future__ import annotations

from benchmarks.large_equiv_suite import EQUIV_PAIRS

from deppy.equivalence.cohomological_engine import DeepEquivalenceEngine, ProofMethod
from deppy.equivalence.pipeline import EquivalencePipeline


def _get_pair(name: str) -> tuple[str, str, bool]:
    for pair_name, source_f, source_g, expected in EQUIV_PAIRS:
        if pair_name == name:
            return source_f, source_g, expected
    raise AssertionError(f"missing benchmark pair {name}")


def test_factorial_equivalence_uses_guarded_cech_certificate() -> None:
    source_f, source_g, expected = _get_pair("factorial_iterative_vs_recursive")

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent
    assert cert.proof_method == ProofMethod.CECH_H1_ZERO
    assert cert.h1_rank == 0
    assert "Dependent domain" in cert.explanation
    assert "inferred dependent domain: n >= 0" in cert.explanation


def test_unannotated_factorial_pair_still_gets_dependent_domain() -> None:
    source_f = """
def f(n):
    result = 1
    for i in range(2, n + 1):
        result *= i
    return result
"""
    source_g = """
def g(n):
    if n <= 1:
        return 1
    return n * g(n - 1)
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None
    assert cert.equivalent
    assert cert.proof_method == ProofMethod.CECH_H1_ZERO
    assert "inferred dependent domain: n >= 0" in cert.explanation


def test_pipeline_reports_cohomology_and_domain_for_factorial_pair() -> None:
    source_f, source_g, _ = _get_pair("factorial_iterative_vs_recursive")

    result = EquivalencePipeline().run(source_f, source_g)

    assert result.is_equivalent
    assert result.global_result is not None
    assert "Ȟ¹(U, Iso) = 0" in result.global_result.explanation
    assert "Dependent domain" in result.global_result.explanation
    assert "inferred dependent domain: n >= 0" in result.global_result.explanation
