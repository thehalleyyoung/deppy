"""Tests for pipeline API (default_config, check_*_equivalence)."""
import unittest

import torch

from deppy.equivalence.torch._protocols import (
    AnalysisMode,
    EquivalenceStrength,
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TensorSpec,
    TensorStratum,
)
from deppy.equivalence.torch.torch_pipeline import (
    check_mlir_equivalence,
    check_torch_equivalence,
    default_config,
)


# ── default_config ──────────────────────────────────────────────────────


class TestDefaultConfig(unittest.TestCase):
    def test_returns_config(self):
        cfg = default_config()
        self.assertIsInstance(cfg, TensorEquivalenceConfig)

    def test_default_analysis_mode(self):
        cfg = default_config()
        self.assertEqual(cfg.analysis_mode, AnalysisMode.EQUIVALENCE)

    def test_default_strength(self):
        cfg = default_config()
        self.assertEqual(cfg.strength, EquivalenceStrength.DENOTATIONAL)

    def test_override_verbose(self):
        cfg = default_config(verbose=True)
        self.assertTrue(cfg.verbose)

    def test_override_check_stride(self):
        cfg = default_config(check_stride=True)
        self.assertTrue(cfg.check_stride)

    def test_override_analysis_mode(self):
        cfg = default_config(analysis_mode=AnalysisMode.BUG_FINDING)
        self.assertEqual(cfg.analysis_mode, AnalysisMode.BUG_FINDING)

    def test_override_solver_timeout(self):
        cfg = default_config(solver_timeout_ms=5000)
        self.assertEqual(cfg.solver_timeout_ms, 5000)


# ── check_torch_equivalence ────────────────────────────────────────────


class TestCheckTorchEquivalence(unittest.TestCase):
    def test_equivalent_add(self):
        f = lambda x: x + 1
        g = lambda x: x + 1
        j = check_torch_equivalence(f, g)
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)
        self.assertTrue(j.is_equivalent)

    def test_equivalent_mul(self):
        f = lambda x: x * 2
        g = lambda x: x * 2
        j = check_torch_equivalence(f, g)
        self.assertTrue(j.is_equivalent)

    def test_inequivalent(self):
        f = lambda x: x * 2
        g = lambda x: x * 3
        j = check_torch_equivalence(f, g)
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)
        self.assertFalse(j.is_equivalent)

    def test_shape_mismatch(self):
        f = lambda x: x
        g = lambda x: x.reshape(-1)
        j = check_torch_equivalence(f, g)
        self.assertFalse(j.is_equivalent)

    def test_with_explicit_specs(self):
        f = lambda x: x * 2
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = check_torch_equivalence(f, f, tensor_specs=specs)
        self.assertTrue(j.is_equivalent)

    def test_with_explicit_test_inputs(self):
        f = lambda x: x * 2
        inputs = [[torch.randn(4, 4)], [torch.randn(4, 4)]]
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = check_torch_equivalence(f, f, tensor_specs=specs, test_inputs=inputs)
        self.assertTrue(j.is_equivalent)

    def test_global_judgment_has_explanation(self):
        f = lambda x: x * 2
        j = check_torch_equivalence(f, f)
        self.assertIsNotNone(j.explanation)

    def test_global_judgment_has_stratum_results(self):
        f = lambda x: x * 2
        j = check_torch_equivalence(f, f)
        self.assertIsNotNone(j.stratum_results)

    def test_matmul_equivalence(self):
        f = lambda x: x @ x
        j = check_torch_equivalence(
            f, f,
            tensor_specs=[TensorSpec(shape=(4, 4), dtype="float32", device="cpu")],
        )
        self.assertTrue(j.is_equivalent)


# ── check_mlir_equivalence ──────────────────────────────────────────────


MLIR_ADD = """
module {
  func.func @add(%arg0: tensor<4x4xf32>, %arg1: tensor<4x4xf32>) -> tensor<4x4xf32> {
    %0 = arith.addf %arg0, %arg1 : tensor<4x4xf32>
    return %0 : tensor<4x4xf32>
  }
}
"""

MLIR_MUL = """
module {
  func.func @mul(%arg0: tensor<4x4xf32>, %arg1: tensor<4x4xf32>) -> tensor<4x4xf32> {
    %0 = arith.mulf %arg0, %arg1 : tensor<4x4xf32>
    return %0 : tensor<4x4xf32>
  }
}
"""


class TestCheckMLIREquivalence(unittest.TestCase):
    def test_same_mlir_equivalent(self):
        j = check_mlir_equivalence(MLIR_ADD, MLIR_ADD)
        self.assertTrue(j.is_equivalent)

    def test_different_mlir_inequivalent(self):
        j = check_mlir_equivalence(MLIR_ADD, MLIR_MUL)
        self.assertFalse(j.is_equivalent)

    def test_mlir_returns_global_judgment(self):
        j = check_mlir_equivalence(MLIR_ADD, MLIR_ADD)
        self.assertIsNotNone(j.verdict)
        self.assertIsNotNone(j.explanation)


if __name__ == "__main__":
    unittest.main()
