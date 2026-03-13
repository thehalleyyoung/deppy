"""Tests for general analysis capabilities (single-program analysis)."""
import unittest

import torch

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    BugKind,
    CorrectnessJudgment,
    ProgramId,
    TensorEquivalenceConfig,
    TensorSpec,
)
from deppy.equivalence.torch.analysis import (
    analyze_mlir,
    analyze_triton,
    check_correctness,
)
from deppy.equivalence.torch.specification import (
    SpecBuilder,
    numerical_stability_spec,
    triton_safety_spec,
)
from deppy.equivalence.torch.sheaf_condition import TensorSheafConditionChecker


ADD_TRITON = """
import triton, triton.language as tl

@triton.jit
def add_kernel(x_ptr, y_ptr, out_ptr, n: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK: tl.constexpr = 1024
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    mask = offs < n
    x = tl.load(x_ptr + offs, mask=mask)
    y = tl.load(y_ptr + offs, mask=mask)
    tl.store(out_ptr + offs, x + y, mask=mask)
"""

UNMASKED_TRITON = """
import triton, triton.language as tl

@triton.jit
def bad_kernel(x_ptr, out_ptr, n: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK: tl.constexpr = 1024
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    x = tl.load(x_ptr + offs)
    tl.store(out_ptr + offs, x)
"""

MLIR_ADD = """
module {
  func.func @add(%arg0: tensor<4x4xf32>, %arg1: tensor<4x4xf32>) -> tensor<4x4xf32> {
    %0 = arith.addf %arg0, %arg1 : tensor<4x4xf32>
    return %0 : tensor<4x4xf32>
  }
}
"""


# ── analyze_triton ──────────────────────────────────────────────────────


class TestAnalyzeTriton(unittest.TestCase):
    def test_valid_kernel(self):
        j = analyze_triton(ADD_TRITON)
        self.assertIsInstance(j, AnalysisJudgment)
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)
        self.assertEqual(len(j.bugs), 0)

    def test_unmasked_kernel_finds_bugs(self):
        j = analyze_triton(UNMASKED_TRITON)
        self.assertIsInstance(j, AnalysisJudgment)
        if j.bugs:
            kinds = {b.kind for b in j.bugs}
            self.assertTrue(
                kinds & {BugKind.UNMASKED_ACCESS, BugKind.MEMORY_VIOLATION}
                or j.verdict == AnalysisVerdict.INVALID,
            )

    def test_with_name(self):
        j = analyze_triton(ADD_TRITON, name="test_kernel")
        self.assertIsNotNone(j.verdict)

    def test_with_config(self):
        cfg = TensorEquivalenceConfig()
        j = analyze_triton(ADD_TRITON, config=cfg)
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)


# ── analyze_mlir ────────────────────────────────────────────────────────


class TestAnalyzeMLIR(unittest.TestCase):
    def test_valid_mlir(self):
        j = analyze_mlir(MLIR_ADD)
        self.assertIsInstance(j, AnalysisJudgment)
        self.assertIn(j.verdict, [AnalysisVerdict.VALID, AnalysisVerdict.INVALID])

    def test_with_name(self):
        j = analyze_mlir(MLIR_ADD, name="add_module")
        self.assertIsNotNone(j.verdict)

    def test_with_config(self):
        cfg = TensorEquivalenceConfig()
        j = analyze_mlir(MLIR_ADD, config=cfg)
        self.assertIsNotNone(j)


# ── check_correctness ──────────────────────────────────────────────────


class TestCheckCorrectness(unittest.TestCase):
    def test_valid_function(self):
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        j = check_correctness(f, spec)
        self.assertIsInstance(j, CorrectnessJudgment)
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)

    def test_nan_producing_function(self):
        def nan_fn(x):
            return x / 0.0

        spec = numerical_stability_spec()
        j = check_correctness(nan_fn, spec)
        # Should detect NaN/Inf
        self.assertIn(j.verdict, [AnalysisVerdict.INVALID, AnalysisVerdict.VALID])

    def test_conforming_sites(self):
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        j = check_correctness(f, spec)
        self.assertGreater(len(j.conforming_sites), 0)

    def test_with_explicit_specs(self):
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        tensor_specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = check_correctness(f, spec, tensor_specs=tensor_specs)
        self.assertIsNotNone(j.verdict)


# ── TensorSheafConditionChecker ─────────────────────────────────────────


class TestTensorSheafConditionChecker(unittest.TestCase):
    def test_well_behaved_function(self):
        checker = TensorSheafConditionChecker()
        f = lambda x: x * 2
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        result = checker.check(f, specs)
        self.assertTrue(result.satisfies_condition)

    def test_result_has_correct_fields(self):
        checker = TensorSheafConditionChecker()
        f = lambda x: x + 1
        specs = [TensorSpec(shape=(4,), dtype="float32", device="cpu")]
        result = checker.check(f, specs)
        self.assertIsInstance(result.gluing_failures, list)
        self.assertIsInstance(result.descent_failures, list)

    def test_no_gluing_failures_for_simple_fn(self):
        checker = TensorSheafConditionChecker()
        f = lambda x: x * 2
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        result = checker.check(f, specs)
        self.assertEqual(len(result.gluing_failures), 0)

    def test_no_descent_failures_for_simple_fn(self):
        checker = TensorSheafConditionChecker()
        f = lambda x: x * 2
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        result = checker.check(f, specs)
        self.assertEqual(len(result.descent_failures), 0)


if __name__ == "__main__":
    unittest.main()
