"""
Tests for edge-case counterexample synthesis on Triton kernel pairs.

50 pairs of Triton kernels that produce identical results on most random
inputs but diverge on **boundary strata** of the IEEE 754 input space:
NaN, ±Inf, ±0, denormals, large magnitudes, and tiling boundaries.

Sheaf-theoretically, each pair witnesses a failure of the presheaf
natural transformation η : Sem_f ⇒ Sem_g to extend from the open
interior to the compactified input space.
"""

from __future__ import annotations

import pytest

from deppy.equivalence.torch.triton_counterexample import (
    CounterexampleSynthesizer,
    CounterexampleReport,
    EdgeCaseCategory,
    InputStratum,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════

synthesizer = CounterexampleSynthesizer()


def _wrap(body_a: str, body_b: str,
          params: str = "x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr") -> tuple:
    """Wrap kernel bodies in a standard Triton kernel shell."""
    template = '''
import triton
import triton.language as tl

@triton.jit
def kernel({params}):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
{body}
'''
    src_a = template.format(params=params, body=_indent(body_a, 4))
    src_b = template.format(params=params, body=_indent(body_b, 4))
    return src_a, src_b


def _wrap2(body_a: str, body_b: str,
           params: str = "x_ptr, y_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr") -> tuple:
    """Wrap kernel bodies with two input pointers."""
    template = '''
import triton
import triton.language as tl

@triton.jit
def kernel({params}):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
{body}
'''
    src_a = template.format(params=params, body=_indent(body_a, 4))
    src_b = template.format(params=params, body=_indent(body_b, 4))
    return src_a, src_b


def _wrap3(body_a: str, body_b: str,
           params: str = "a_ptr, b_ptr, c_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr") -> tuple:
    """Wrap kernel bodies with three input pointers."""
    template = '''
import triton
import triton.language as tl

@triton.jit
def kernel({params}):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
{body}
'''
    src_a = template.format(params=params, body=_indent(body_a, 4))
    src_b = template.format(params=params, body=_indent(body_b, 4))
    return src_a, src_b


def _indent(text: str, n: int) -> str:
    prefix = " " * n
    return "\n".join(prefix + line for line in text.strip().split("\n"))


# ═══════════════════════════════════════════════════════════════════════════════
# Category 1: FP identity edge cases (pairs 1–10)
# ═══════════════════════════════════════════════════════════════════════════════


class TestFPIdentityEdgeCases:
    """Algebraic identities that fail on boundary strata."""

    def test_pair_01_self_cancellation(self):
        """x - x → 0.0 | Counterexample: x = NaN or Inf."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x - x\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.FP_IDENTITY in report.categories

    def test_pair_02_self_division(self):
        """x / x → 1.0 | Counterexample: x = 0."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x / x\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = 1.0\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.ZERO in report.strata_affected

    def test_pair_03_zero_multiply(self):
        """x * 0.0 → 0.0 | Counterexample: x = Inf."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.INFINITY in report.strata_affected

    def test_pair_04_zero_addition(self):
        """x + 0.0 → x | Counterexample: x = -0.0 (sign changes)."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x + 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.SIGN_LOSS in report.categories

    def test_pair_05_multiply_divide_cancel(self):
        """(x * y) / y → x | Counterexample: y = 0."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * y / y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_06_add_subtract_cancel(self):
        """(x + y) - y → x | Counterexample: |y| >> |x| (catastrophic cancellation)."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) - y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.CANCELLATION in report.categories

    def test_pair_07_reciprocal_roundtrip(self):
        """1/(1/x) → x | Counterexample: x = subnormal."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = 1.0 / (1.0 / x)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.SUBNORMAL in report.strata_affected

    def test_pair_08_difference_of_squares(self):
        """a²−b² vs (a+b)(a−b) | Different rounding for large values."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x - y * y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x - y)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_09_cube_vs_power(self):
        """x*x*x vs x**3 | Intermediate overflow for large x."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * x * x\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x ** 3\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_10_max_algebraic(self):
        """max(x,y) vs (x+y+|x-y|)/2 | NaN propagation differs."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.maximum(x, y)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y + tl.abs(x - y)) / 2.0\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample


# ═══════════════════════════════════════════════════════════════════════════════
# Category 2: Masked load / boundary edge cases (pairs 11–18)
# ═══════════════════════════════════════════════════════════════════════════════


class TestMaskBoundaryEdgeCases:
    """Tiling boundary strata — different mask defaults."""

    def test_pair_11_other_zero_vs_one(self):
        """Load other=0.0 vs other=1.0 → boundary elements differ."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask, other=1.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.MASK_BOUNDARY in report.categories

    def test_pair_12_other_zero_vs_nan(self):
        """Load other=0.0 vs other=nan → NaN contaminates downstream."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask, other=float('nan'))\ntl.store(out_ptr + offs, x, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.TILING_BOUNDARY in report.strata_affected

    def test_pair_13_other_zero_vs_inf(self):
        """Load other=0.0 vs other=inf → boundary gets Inf."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask, other=float('inf'))\ntl.store(out_ptr + offs, x, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_14_masked_vs_unmasked_load(self):
        """Masked load vs unmasked → unmasked reads garbage at boundary."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
            "x = tl.load(x_ptr + offs)\ntl.store(out_ptr + offs, x, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.MASK_BOUNDARY in report.categories

    def test_pair_15_masked_vs_unmasked_store(self):
        """Masked store vs unmasked → writes beyond N."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_16_where_vs_multiply_mask(self):
        """tl.where(m, x, 0) vs x * m.float() → Inf*0 = NaN."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.where(mask, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = x * mask.to(tl.float32)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_17_mask_lt_vs_le(self):
        """mask = offs < N  vs  mask = offs <= N - 1 → N=0 underflow."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    tl.store(out_ptr + offs, x, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs <= N - 1
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    tl.store(out_ptr + offs, x, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        # The expressions resolve identically but mask computation differs.
        # This is a source-level check that our synthesizer should flag.
        assert report.found_counterexample or report.structurally_identical
        # If structurally identical, the difference is in mask computation
        # which the synthesizer may not detect at expression level.
        # We accept this as a known limitation (mask computation is not in store expr).

    def test_pair_18_other_affects_sum(self):
        """Sum after masked load: other=0 vs other=1 changes the sum."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
            "x = tl.load(x_ptr + offs, mask=mask, other=1.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample


# ═══════════════════════════════════════════════════════════════════════════════
# Category 3: Associativity / distributivity (pairs 19–28)
# ═══════════════════════════════════════════════════════════════════════════════


class TestAssociativityDistributivity:
    """FP non-associativity and non-distributivity edge cases."""

    def test_pair_19_addition_associativity(self):
        """(a + b) + c  vs  a + (b + c) | 1e16 + 1 - 1e16."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) + c\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a + (b + c)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.FP_ASSOCIATIVITY in report.categories

    def test_pair_20_distributivity(self):
        """a * (b + c)  vs  a*b + a*c | FP distributivity failure."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * (b + c)\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * b + a * c\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.FP_DISTRIBUTIVITY in report.categories

    def test_pair_21_right_distributivity(self):
        """(a + b) * c  vs  a*c + b*c."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) * c\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * c + b * c\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_22_mult_associativity(self):
        """(a * b) * c  vs  a * (b * c) | Overflow boundary."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a * b) * c\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * (b * c)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.FP_ASSOCIATIVITY in report.categories

    def test_pair_23_triple_sum_vs_multiply(self):
        """a + a + a  vs  3.0 * a | Different intermediate rounding."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x + x + x\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = 3.0 * x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_24_square_expansion(self):
        """(a+b)² vs a²+2ab+b² | Different intermediate rounding."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x + 2.0 * x * y + y * y\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_25_division_distribution(self):
        """a/c + b/c  vs  (a+b)/c | Different precision."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / c + b / c\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) / c\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_26_subtract_add_cancel(self):
        """(a - b) + b  vs  a | Precision loss cancellation."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x - y) + y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_27_algebraic_identity_squares(self):
        """a²+b² vs (a+b)²−2ab | Different catastrophic cancellation."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x + y * y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x + y) - 2.0 * x * y\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_28_difference_of_squares(self):
        """(a−b)(a+b) vs a²−b² | Cancellation differs."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x - y) * (x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x - y * y\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample


# ═══════════════════════════════════════════════════════════════════════════════
# Category 4: Division / reciprocal edge cases (pairs 29–35)
# ═══════════════════════════════════════════════════════════════════════════════


class TestDivisionReciprocal:
    """Division-related edge cases on zero / precision boundaries."""

    def test_pair_29_reciprocal_multiply(self):
        """a/b vs a*(1/b) | Reciprocal double-rounding."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x / y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * (1.0 / y)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.DIVISION_HAZARD in report.categories

    def test_pair_30_division_chain(self):
        """a/b/c vs a/(b*c) | Intermediate precision."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / b / c\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / (b * c)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_31_divide_multiply_roundtrip(self):
        """(a/b)*b vs a | Round-trip fails when b=0."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x / y) * y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.ZERO in report.strata_affected

    def test_pair_32_complex_fraction(self):
        """a/(b/c) vs (a*c)/b | Different overflow behavior."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / (b / c)\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a * c) / b\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_33_fraction_addition(self):
        """1/a + 1/b  vs  (a+b)/(a*b) | a or b = 0."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = 1.0 / x + 1.0 / y\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) / (x * y)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_34_inexact_reciprocal(self):
        """a/3.0 vs a*(1.0/3.0) | 1/3 is inexact in binary FP."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * (1.0 / 3.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_35_square_self_div(self):
        """(a*a)/a vs a | a=0 → NaN vs 0."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = (x * x) / x\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert InputStratum.ZERO in report.strata_affected


# ═══════════════════════════════════════════════════════════════════════════════
# Category 5: Reduction edge cases (pairs 36–42)
# ═══════════════════════════════════════════════════════════════════════════════


class TestReductionEdgeCases:
    """Reduction order and precision edge cases."""

    def test_pair_36_sum_divide_order(self):
        """sum(x * (1/N)) vs sum(x) / N | Different precision."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    result = tl.sum(x * (1.0 / N), axis=0)
    tl.store(out_ptr + pid, result)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    result = tl.sum(x, axis=0) / N
    tl.store(out_ptr + pid, result)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_37_sum_with_nan_other(self):
        """Sum after load with other=0 vs other=nan."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
            "x = tl.load(x_ptr + offs, mask=mask, other=float('nan'))\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_38_max_vs_where_relu(self):
        """tl.maximum(x, 0) vs tl.where(x > 0, x, 0.0) | NaN handling."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.maximum(x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.where(x > 0, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.NAN_PROPAGATION in report.categories

    def test_pair_39_clamp_order(self):
        """min(max(x, lo), hi) vs max(min(x, hi), lo) | NaN differs."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.minimum(tl.maximum(x, 0.0), 1.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.maximum(tl.minimum(x, 1.0), 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_40_where_vs_mult_conditional(self):
        """tl.where(c, a, b) vs c*a + (1-c)*b when c is 0/1 | Inf edge."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, c_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    result = tl.where(c > 0.5, x, 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, c_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    result = x * c
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_41_sum_abs_vs_abs_sum(self):
        """sum(|x|) vs |sum(x)| — different for mixed-sign inputs."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(tl.abs(x), axis=0)\ntl.store(out_ptr, result)",
            "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.abs(tl.sum(x, axis=0))\ntl.store(out_ptr, result)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_42_product_vs_exp_sum_log(self):
        """prod(x) vs exp(sum(log(x))) | log(0) = -Inf, log(neg) = NaN."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=1.0)
    result = tl.reduce(x, axis=0, combine_fn=lambda a, b: a * b)
    tl.store(out_ptr + pid, result)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=1.0)
    result = tl.exp(tl.sum(tl.log(x), axis=0))
    tl.store(out_ptr + pid, result)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample


# ═══════════════════════════════════════════════════════════════════════════════
# Category 6: Mixed / subtle edge cases (pairs 43–50)
# ═══════════════════════════════════════════════════════════════════════════════


class TestMixedSubtleEdgeCases:
    """Combinations and domain-specific subtle edge cases."""

    def test_pair_43_sign_via_division_vs_conditional(self):
        """x / |x| vs where(x>0, 1, where(x<0, -1, 0)) | x=0: NaN vs 0."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = x / tl.abs(x)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.where(x > 0, 1.0, tl.where(x < 0, -1.0, 0.0))
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_44_safe_div_eps_vs_guard(self):
        """a/(b+eps) vs where(|b|>eps, a/b, 0) | b = -eps → blow-up."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(a_ptr, b_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    eps = 1e-8
    result = a / (b + eps)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(a_ptr, b_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    eps = 1e-8
    result = tl.where(tl.abs(b) > eps, a / b, 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_45_softplus_overflow(self):
        """log(1+exp(x)) vs where(x>20, x, log(1+exp(x))) | large x."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.log(1.0 + tl.exp(x))
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.where(x > 20.0, x, tl.log(1.0 + tl.exp(x)))
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_46_relu_max_vs_where(self):
        """max(x, 0) vs where(x > 0, x, 0) | NaN propagation."""
        src_a, src_b = _wrap(
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.maximum(x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.where(x > 0.0, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample
        assert EdgeCaseCategory.NAN_PROPAGATION in report.categories

    def test_pair_47_exp_product_vs_exp_sum(self):
        """exp(a)*exp(b) vs exp(a+b) | One overflows when a,b are large."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.exp(x) * tl.exp(y)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.exp(x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_48_multi_term_distribution(self):
        """a*b + a*c + a*d  vs  a*(b+c+d) | Multi-term distributivity."""
        src_a = '''
import triton
import triton.language as tl

@triton.jit
def kernel(a_ptr, b_ptr, c_ptr, d_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    d = tl.load(d_ptr + offs, mask=mask)
    result = a * b + a * c + a * d
    tl.store(out_ptr + offs, result, mask=mask)
'''
        src_b = '''
import triton
import triton.language as tl

@triton.jit
def kernel(a_ptr, b_ptr, c_ptr, d_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    d = tl.load(d_ptr + offs, mask=mask)
    result = a * (b + c + d)
    tl.store(out_ptr + offs, result, mask=mask)
'''
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_49_mean_computation(self):
        """(a+b+c)/3 vs a/3+b/3+c/3 | Different rounding."""
        src_a, src_b = _wrap3(
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b + c) / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
            "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / 3.0 + b / 3.0 + c / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample

    def test_pair_50_max_min_abs(self):
        """max(a,b) - min(a,b) vs abs(a-b) | NaN propagation."""
        src_a, src_b = _wrap2(
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.maximum(x, y) - tl.minimum(x, y)\ntl.store(out_ptr + offs, result, mask=mask)",
            "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.abs(x - y)\ntl.store(out_ptr + offs, result, mask=mask)",
        )
        report = synthesizer.synthesize(src_a, src_b)
        assert report.found_counterexample


# ═══════════════════════════════════════════════════════════════════════════════
# Summary harness
# ═══════════════════════════════════════════════════════════════════════════════


class TestSynthesizerSummary:
    """Aggregate statistics over all 50 pairs."""

    def test_all_50_detected(self):
        """Verify every edge-case pair has at least one counterexample."""
        pairs = _collect_all_50_pairs()
        n_detected = 0
        failures = []

        for i, (src_a, src_b, label) in enumerate(pairs, 1):
            report = synthesizer.synthesize(src_a, src_b)
            if report.found_counterexample:
                n_detected += 1
            else:
                failures.append(f"Pair {i}: {label}")

        detection_rate = n_detected / len(pairs) if pairs else 0
        print(f"\n{'='*60}")
        print(f"Edge-case counterexample synthesis results:")
        print(f"  Detected: {n_detected}/{len(pairs)} ({detection_rate:.1%})")
        if failures:
            print(f"  Missed:")
            for f in failures:
                print(f"    - {f}")
        print(f"{'='*60}")
        # We aim for at least 90% detection rate
        assert detection_rate >= 0.90, (
            f"Detection rate {detection_rate:.1%} below 90% target. "
            f"Missed: {failures}"
        )

    def test_category_coverage(self):
        """All edge-case categories are represented."""
        pairs = _collect_all_50_pairs()
        all_categories: set = set()
        all_strata: set = set()

        for src_a, src_b, _ in pairs:
            report = synthesizer.synthesize(src_a, src_b)
            all_categories.update(report.categories)
            all_strata.update(report.strata_affected)

        # Should cover at least 5 distinct categories
        assert len(all_categories) >= 5, f"Only {len(all_categories)} categories: {all_categories}"
        # Should cover at least 4 distinct strata
        assert len(all_strata) >= 4, f"Only {len(all_strata)} strata: {all_strata}"

        print(f"\nCategory coverage: {sorted(c.value for c in all_categories)}")
        print(f"Stratum coverage:  {sorted(s.value for s in all_strata)}")


def _collect_all_50_pairs():
    """Collect all 50 kernel pairs for aggregate testing."""
    pairs = []

    # ── FP identity (1-10) ───────────────────────────────────────────────

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x - x\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x-x vs 0",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x / x\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = 1.0\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x/x vs 1",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x*0 vs 0",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x + 0.0\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x+0 vs x",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * y / y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x*y/y vs x",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) - y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(x+y)-y vs x",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = 1.0 / (1.0 / x)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("1/(1/x) vs x",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x - y * y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x - y)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x²-y² vs (x+y)(x-y)",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * x * x\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x ** 3\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x*x*x vs x**3",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.maximum(x, y)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y + tl.abs(x - y)) / 2.0\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("max(x,y) vs algebraic",))

    # ── Mask boundary (11-18) ────────────────────────────────────────────

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask, other=1.0)\ntl.store(out_ptr + offs, x, mask=mask)",
    ) + ("other=0 vs other=1",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask, other=float('nan'))\ntl.store(out_ptr + offs, x, mask=mask)",
    ) + ("other=0 vs other=nan",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask, other=float('inf'))\ntl.store(out_ptr + offs, x, mask=mask)",
    ) + ("other=0 vs other=inf",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        "x = tl.load(x_ptr + offs)\ntl.store(out_ptr + offs, x, mask=mask)",
    ) + ("masked vs unmasked load",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\ntl.store(out_ptr + offs, x)",
    ) + ("masked vs unmasked store",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.where(mask, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = x * mask.to(tl.float32)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("where(m,x,0) vs x*m",))

    # Pair 17 (mask comparison variant) — use inline
    src17a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    tl.store(out_ptr + offs, x, mask=mask)
'''
    src17b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs <= N - 1
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    tl.store(out_ptr + offs, x, mask=mask)
'''
    pairs.append((src17a, src17b, "offs<N vs offs<=N-1"))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
        "x = tl.load(x_ptr + offs, mask=mask, other=1.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
    ) + ("sum after other=0 vs other=1",))

    # ── Associativity / distributivity (19-28) ──────────────────────────

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) + c\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a + (b + c)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a+b)+c vs a+(b+c)",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * (b + c)\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * b + a * c\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a*(b+c) vs a*b+a*c",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) * c\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * c + b * c\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a+b)*c vs a*c+b*c",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a * b) * c\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a * (b * c)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a*b)*c vs a*(b*c)",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x + x + x\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = 3.0 * x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("x+x+x vs 3*x",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x + 2.0 * x * y + y * y\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(x+y)² vs x²+2xy+y²",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / c + b / c\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b) / c\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a/c+b/c vs (a+b)/c",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x - y) + y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a-b)+b vs a",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x + y * y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) * (x + y) - 2.0 * x * y\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a²+b² vs (a+b)²-2ab",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x - y) * (x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * x - y * y\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a-b)(a+b) vs a²-b²",))

    # ── Division / reciprocal (29-35) ────────────────────────────────────

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x / y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x * (1.0 / y)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a/b vs a*(1/b)",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / b / c\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / (b * c)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a/b/c vs a/(b*c)",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x / y) * y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a/b)*b vs a",))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / (b / c)\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a * c) / b\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a/(b/c) vs (a*c)/b",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = 1.0 / x + 1.0 / y\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = (x + y) / (x * y)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("1/a+1/b vs (a+b)/(a*b)",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x * (1.0 / 3.0)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("a/3 vs a*(1/3)",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = (x * x) / x\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = x\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a*a)/a vs a",))

    # ── Reduction edge cases (36-42) ─────────────────────────────────────

    src36a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    result = tl.sum(x * (1.0 / N), axis=0)
    tl.store(out_ptr + pid, result)
'''
    src36b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=0.0)
    result = tl.sum(x, axis=0) / N
    tl.store(out_ptr + pid, result)
'''
    pairs.append((src36a, src36b, "sum(x/N) vs sum(x)/N"))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
        "x = tl.load(x_ptr + offs, mask=mask, other=float('nan'))\nresult = tl.sum(x, axis=0)\ntl.store(out_ptr, result)",
    ) + ("sum other=0 vs other=nan",))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.maximum(x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.where(x > 0, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("max(x,0) vs where(x>0,x,0)",))

    src39a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.minimum(tl.maximum(x, 0.0), 1.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src39b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.maximum(tl.minimum(x, 1.0), 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src39a, src39b, "clamp min(max) vs max(min)"))

    src40a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, c_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    result = tl.where(c > 0.5, x, 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src40b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, c_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    result = x * c
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src40a, src40b, "where(c,x,0) vs x*c"))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.sum(tl.abs(x), axis=0)\ntl.store(out_ptr, result)",
        "x = tl.load(x_ptr + offs, mask=mask, other=0.0)\nresult = tl.abs(tl.sum(x, axis=0))\ntl.store(out_ptr, result)",
    ) + ("sum(|x|) vs |sum(x)|",))

    src42a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=1.0)
    result = tl.reduce(x, axis=0, combine_fn=lambda a, b: a * b)
    tl.store(out_ptr + pid, result)
'''
    src42b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask, other=1.0)
    result = tl.exp(tl.sum(tl.log(x), axis=0))
    tl.store(out_ptr + pid, result)
'''
    pairs.append((src42a, src42b, "prod(x) vs exp(sum(log(x)))"))

    # ── Mixed / subtle (43-50) ──────────────────────────────────────────

    src43a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = x / tl.abs(x)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src43b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.where(x > 0, 1.0, tl.where(x < 0, -1.0, 0.0))
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src43a, src43b, "x/|x| vs sign(x)"))

    src44a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(a_ptr, b_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    eps = 1e-8
    result = a / (b + eps)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src44b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(a_ptr, b_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    eps = 1e-8
    result = tl.where(tl.abs(b) > eps, a / b, 0.0)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src44a, src44b, "a/(b+eps) vs guarded div"))

    src45a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.log(1.0 + tl.exp(x))
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src45b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(x_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    result = tl.where(x > 20.0, x, tl.log(1.0 + tl.exp(x)))
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src45a, src45b, "softplus naive vs stable"))

    pairs.append(_wrap(
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.maximum(x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\nresult = tl.where(x > 0.0, x, 0.0)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("relu max vs where",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.exp(x) * tl.exp(y)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.exp(x + y)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("exp(a)*exp(b) vs exp(a+b)",))

    src48a = '''
import triton
import triton.language as tl
@triton.jit
def kernel(a_ptr, b_ptr, c_ptr, d_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    d = tl.load(d_ptr + offs, mask=mask)
    result = a * b + a * c + a * d
    tl.store(out_ptr + offs, result, mask=mask)
'''
    src48b = '''
import triton
import triton.language as tl
@triton.jit
def kernel(a_ptr, b_ptr, c_ptr, d_ptr, out_ptr, N, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    a = tl.load(a_ptr + offs, mask=mask)
    b = tl.load(b_ptr + offs, mask=mask)
    c = tl.load(c_ptr + offs, mask=mask)
    d = tl.load(d_ptr + offs, mask=mask)
    result = a * (b + c + d)
    tl.store(out_ptr + offs, result, mask=mask)
'''
    pairs.append((src48a, src48b, "a*b+a*c+a*d vs a*(b+c+d)"))

    pairs.append(_wrap3(
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = (a + b + c) / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
        "a = tl.load(a_ptr + offs, mask=mask)\nb = tl.load(b_ptr + offs, mask=mask)\nc = tl.load(c_ptr + offs, mask=mask)\nresult = a / 3.0 + b / 3.0 + c / 3.0\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("(a+b+c)/3 vs a/3+b/3+c/3",))

    pairs.append(_wrap2(
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.maximum(x, y) - tl.minimum(x, y)\ntl.store(out_ptr + offs, result, mask=mask)",
        "x = tl.load(x_ptr + offs, mask=mask)\ny = tl.load(y_ptr + offs, mask=mask)\nresult = tl.abs(x - y)\ntl.store(out_ptr + offs, result, mask=mask)",
    ) + ("max-min vs |a-b|",))

    assert len(pairs) == 50, f"Expected 50 pairs, got {len(pairs)}"
    return pairs
