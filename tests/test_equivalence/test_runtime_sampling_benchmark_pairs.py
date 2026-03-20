from __future__ import annotations

from benchmarks.large_equiv_suite import EQUIV_PAIRS

from deppy.equivalence._runtime_sampling import _build_runtime_samples, _load_primary_callable
from deppy.equivalence.pipeline import EquivalencePipeline, EquivalencePipelineConfig


def _get_pair(name: str) -> tuple[str, str, bool]:
    for pair_name, source_f, source_g, expected in EQUIV_PAIRS:
        if pair_name == name:
            return source_f, source_g, expected
    raise AssertionError(f"missing benchmark pair {name}")


def test_runtime_sampling_recovers_iterative_recursive_equivalence() -> None:
    source_f, source_g, expected = _get_pair("factorial_iterative_vs_recursive")

    result = EquivalencePipeline(
        EquivalencePipelineConfig(runtime_sample_budget=32),
    ).run(source_f, source_g)

    assert expected is True
    assert result.is_equivalent
    assert result.global_result is not None
    assert "RUNTIME_CHECKED" in result.global_result.explanation


def test_runtime_sampling_finds_negative_index_counterexample() -> None:
    source_f, source_g, expected = _get_pair("negative_index_handling")

    result = EquivalencePipeline(
        EquivalencePipelineConfig(runtime_sample_budget=32),
    ).run(source_f, source_g)

    assert expected is False
    assert not result.is_equivalent
    assert result.global_result is not None
    assert "counterexample" in result.global_result.explanation.lower()


def test_runtime_sampling_respects_range_implied_naturals() -> None:
    source_f, source_g, expected = _get_pair("power_loop_vs_builtin")

    result = EquivalencePipeline(
        EquivalencePipelineConfig(runtime_sample_budget=32),
    ).run(source_f, source_g)

    assert expected is True
    assert result.is_equivalent


def test_runtime_sampling_uses_cross_product_numeric_witnesses() -> None:
    source_f, source_g, expected = _get_pair("floor_div_vs_true_div")

    result = EquivalencePipeline(
        EquivalencePipelineConfig(runtime_sample_budget=32),
    ).run(source_f, source_g)

    assert expected is False
    assert not result.is_equivalent


def test_no_return_kernels_keep_structural_fingerprint() -> None:
    source_f, source_g, expected = _get_pair("triton_add_vs_mul_kernel")

    result = EquivalencePipeline(
        EquivalencePipelineConfig(runtime_sample_budget=16),
    ).run(source_f, source_g)

    assert expected is False
    assert not result.is_equivalent


def test_runtime_sampling_uses_generic_string_sections() -> None:
    source = """
def normalize_text(text):
    return text.lower().strip()
"""

    fn = _load_primary_callable(source)
    assert fn is not None

    samples = _build_runtime_samples(source, fn, mode="spec", max_samples=32)

    assert ("queue",) in samples
    assert ("ubuntu",) in samples


def test_runtime_sampling_uses_generic_numeric_sequence_sections() -> None:
    source = """
def keep(xs):
    return list(xs)
"""

    fn = _load_primary_callable(source)
    assert fn is not None

    samples = _build_runtime_samples(source, fn, mode="spec", max_samples=32)

    assert ([1, 0, 2],) in samples
    assert ([3, -1, 2],) in samples


def test_runtime_sampling_glues_prefix_summary_sections() -> None:
    source = """
def push(stack, maxes, item):
    new_stack = list(stack)
    new_maxes = list(maxes)
    new_stack.append(item)
    if not new_maxes:
        new_maxes.append(item)
    else:
        new_maxes.append(max(new_maxes[-1], item))
    return new_stack, new_maxes
"""

    fn = _load_primary_callable(source)
    assert fn is not None

    samples = _build_runtime_samples(source, fn, mode="spec", max_samples=32)

    assert ([1, 2], [1, 2], 3) in samples
    assert ([1, 2], [2, 1], 3) not in samples


def test_main_pipeline_dispatches_triton_add_kernel_pair() -> None:
    source_f, source_g, expected = _get_pair("triton_add_kernel_two_block_sizes")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is True
    assert result.is_equivalent
    assert result.global_result is not None
    assert "tensor sites" in result.global_result.explanation.lower()


def test_main_pipeline_dispatches_triton_softmax_kernel_pair() -> None:
    source_f, source_g, expected = _get_pair("triton_softmax_row_two_ways")

    result = EquivalencePipeline().run(source_f, source_g)

    assert expected is True
    assert result.is_equivalent
    assert result.global_result is not None
    assert "tensor sites" in result.global_result.explanation.lower()
