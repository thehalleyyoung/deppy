from __future__ import annotations

from deppy.equivalence.deep_equivalence import DeepEquivalenceEngine
from deppy.equivalence.pipeline import EquivalencePipeline
from benchmarks.hard_equiv_suite import EQUIV_PAIRS


def test_deep_engine_uses_product_semantics_for_tuple_returns() -> None:
    source_f = """
def f(x, y):
    return (x + 1, y + 2)
"""
    source_g = """
def g(x, y):
    return (x + 1, y + 2)
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None
    assert cert.equivalent


def test_deep_engine_detects_tuple_component_mismatch() -> None:
    source_f = """
def f(x, y):
    return (x + 1, y + 2)
"""
    source_g = """
def g(x, y):
    return (x + 1, y + 3)
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None
    assert not cert.equivalent


def test_pipeline_uses_dependent_index_guards_for_collection_access() -> None:
    source_f = """
def f(xs, i):
    return (xs[i], len(xs))
"""
    source_g = """
def g(xs, i):
    return (xs[i], len(xs))
"""

    result = EquivalencePipeline().run(source_f, source_g)

    assert result.is_equivalent


def test_deep_engine_supports_simple_loop_carried_semantics() -> None:
    source_f = """
def f(n):
    total = 0
    for i in range(n):
        total += i
    return total
"""
    source_g = """
def g(n):
    acc = 0
    for j in range(n):
        acc = acc + j
    total = acc
    return total
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None
    assert cert.equivalent


def test_pipeline_harvests_semantic_sections_from_cohomological_encoder() -> None:
    source_f = """
def f(n):
    total = 0
    for i in range(n):
        total += i
    return total
"""
    source_g = """
def g(n):
    acc = 0
    for j in range(n):
        acc = acc + j
    total = acc
    return total
"""

    result = EquivalencePipeline().run(source_f, source_g)

    assert result.global_result is not None
    assert result.global_result.explanation != "No semantic site cover available from Stage 1; deferring verdict to the Z3/cohomological engines"


def test_deep_engine_supports_local_helper_semantics() -> None:
    source_f = """
def f(x, y):
    def helper(a, b):
        return a * a + b
    return helper(x + 0, y + 0)
"""
    source_g = """
def g(x, y):
    def helper2(u, v):
        value = u * u
        return value + v
    return helper2(x + 0, y + 0)
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None
    assert cert.equivalent


def test_deep_engine_supports_basic_string_sequence_semantics() -> None:
    source_f = """
def f(s, i):
    text = s + ""
    return text[:i] + text[i:]
"""
    source_g = """
def g(s, i):
    return s + ""
"""

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert cert is not None


def test_deep_engine_proves_trailing_factorial_zero_theorem_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_48_eq48a_vs_eq48b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_binomial_theorem_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_40_eq40a_vs_eq40b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_grid_path_theorem_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_45_eq45a_vs_eq45b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_linear_recurrence_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_37_eq37a_vs_eq37b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_sorted_merge_iterator_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_11_eq11a_vs_eq11b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_safe_quantifier_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_35_eq35a_vs_eq35b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_zip_longest_protocol_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_41_eq41a_vs_eq41b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_higher_order_application_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_42_eq42a_vs_eq42b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_codec_roundtrip_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_06_eq06a_vs_eq06b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_tree_codec_roundtrip_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_12_eq12a_vs_eq12b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_recursive_object_normalization_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_20_eq20a_vs_eq20b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_expression_tree_evaluation_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_03_eq03a_vs_eq03b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent


def test_deep_engine_proves_word_frequency_normalization_pair() -> None:
    pair = next(item for item in EQUIV_PAIRS if item[0] == "hard_eq_02_eq02a_vs_eq02b")
    _, source_f, source_g, expected = pair

    cert = DeepEquivalenceEngine().check(source_f, source_g)

    assert expected is True
    assert cert is not None
    assert cert.equivalent
