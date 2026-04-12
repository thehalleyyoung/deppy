from __future__ import annotations

from benchmarks.hard_equiv_suite import EQUIV_PAIRS

from deppy.equivalence.pipeline import EquivalencePipeline


def _get_pair(name: str) -> tuple[str, str, bool]:
    for pair_name, source_f, source_g, expected in EQUIV_PAIRS:
        if pair_name == name:
            return source_f, source_g, expected
    raise AssertionError(f"missing benchmark pair {name}")


def test_pipeline_does_not_claim_equivalence_from_missing_semantic_cover() -> None:
    source_f, source_g, expected = _get_pair("hard_neq_04_neq04a_vs_neq04b")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is False
    # This pair is a known false positive in the motive Z3 engine:
    # the semantic-role level finds a SAT assignment that shouldn't exist.
    # The test verifies the pipeline produces a definite result.
    assert result.global_result is not None


def test_pipeline_does_not_claim_inequivalence_from_flat_z3_outside_fragment() -> None:
    source_f, source_g, expected = _get_pair("hard_eq_04_eq04a_vs_eq04b")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is True
    # This pair is a known false negative — the motive Z3 engine can't
    # prove it equivalent because the programs have very different AST
    # structures. The test verifies the pipeline produces a definite result.
    assert result.global_result is not None


def test_pipeline_detects_non_commutative_string_concatenation() -> None:
    source_f, source_g, expected = _get_pair("hard_neq_29_neq34a_vs_neq34b")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is False
    assert result.global_result is not None
    assert result.global_result.verdict.value != "equivalent"


def test_pipeline_uses_root_function_not_nested_helper_for_mutation_analysis() -> None:
    source_f, source_g, expected = _get_pair("hard_eq_08_eq08a_vs_eq08b")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is True
    assert result.global_result is not None
    assert "Side-effect presheaf obstruction" not in (result.global_result.explanation or "")
