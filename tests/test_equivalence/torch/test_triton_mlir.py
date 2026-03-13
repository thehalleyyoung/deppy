"""Tests for MLIR dialect equivalence checking."""
import unittest

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    EquivalenceVerdict,
    MLIRDialect,
    MLIRModuleSpec,
    MLIROpSpec,
    TensorEquivalenceConfig,
)
from deppy.equivalence.torch.triton_mlir import (
    MLIRTextParser,
    build_mlir_module_spec,
    compute_mlir_fingerprint,
)
# Import concrete class from module to avoid Protocol shadowing
from deppy.equivalence.torch import triton_mlir as _mlir_mod


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

MLIR_TRITON = """
module {
  tt.func @add_kernel(%arg0: !tt.ptr<f32>, %arg1: !tt.ptr<f32>, %arg2: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    tt.return
  }
}
"""


def _sid(name="mlir"):
    return SiteId(kind=SiteKind.TENSOR_SHAPE, name=name)


# ── MLIRTextParser ──────────────────────────────────────────────────────


class TestMLIRTextParser(unittest.TestCase):
    def test_parse_add_module(self):
        parser = MLIRTextParser()
        mod = parser.parse(MLIR_ADD)
        self.assertIsNotNone(mod)
        self.assertIsNotNone(mod.name)

    def test_parse_detects_arith_dialect(self):
        parser = MLIRTextParser()
        mod = parser.parse(MLIR_ADD)
        # The parsed module should contain arith ops
        self.assertGreater(len(mod.functions), 0)

    def test_parse_mul_module(self):
        parser = MLIRTextParser()
        mod = parser.parse(MLIR_MUL)
        self.assertIsNotNone(mod)

    def test_parse_triton_dialect(self):
        parser = MLIRTextParser()
        mod = parser.parse(MLIR_TRITON)
        self.assertIsNotNone(mod)


# ── build_mlir_module_spec ──────────────────────────────────────────────


class TestBuildMLIRModuleSpec(unittest.TestCase):
    def test_build_add_spec(self):
        spec = build_mlir_module_spec(MLIR_ADD)
        self.assertIsInstance(spec, MLIRModuleSpec)
        self.assertIn(MLIRDialect.ARITH, spec.dialects_used)

    def test_op_count(self):
        spec = build_mlir_module_spec(MLIR_ADD)
        self.assertGreater(spec.op_count, 0)

    def test_build_mul_spec(self):
        spec = build_mlir_module_spec(MLIR_MUL)
        self.assertIn(MLIRDialect.ARITH, spec.dialects_used)

    def test_arith_ops(self):
        spec = build_mlir_module_spec(MLIR_ADD)
        ops = spec.ops_in_dialect(MLIRDialect.ARITH)
        self.assertGreater(len(ops), 0)
        self.assertEqual(ops[0].op_name, "addf")


# ── MLIRFingerprint ─────────────────────────────────────────────────────


class TestMLIRFingerprint(unittest.TestCase):
    def test_compute_fingerprint(self):
        spec = build_mlir_module_spec(MLIR_ADD)
        fp = compute_mlir_fingerprint(spec)
        self.assertIsNotNone(fp)

    def test_same_module_same_fingerprint(self):
        spec_a = build_mlir_module_spec(MLIR_ADD)
        spec_b = build_mlir_module_spec(MLIR_ADD)
        fp_a = compute_mlir_fingerprint(spec_a)
        fp_b = compute_mlir_fingerprint(spec_b)
        self.assertEqual(fp_a, fp_b)

    def test_different_modules_different_fingerprint(self):
        fp_add = compute_mlir_fingerprint(build_mlir_module_spec(MLIR_ADD))
        fp_mul = compute_mlir_fingerprint(build_mlir_module_spec(MLIR_MUL))
        self.assertNotEqual(fp_add, fp_mul)


# ── MLIREquivalenceChecker ──────────────────────────────────────────────


class TestMLIREquivalenceChecker(unittest.TestCase):
    def _make_checker(self):
        cfg = TensorEquivalenceConfig()
        return _mlir_mod.MLIREquivalenceChecker(cfg)

    def test_same_module(self):
        checker = self._make_checker()
        spec = build_mlir_module_spec(MLIR_ADD)
        j = checker.check_site(spec, spec, _sid("same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_equivalent_modules(self):
        checker = self._make_checker()
        spec_a = build_mlir_module_spec(MLIR_ADD)
        spec_b = build_mlir_module_spec(MLIR_ADD)
        j = checker.check_site(spec_a, spec_b, _sid("equiv"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_different_modules(self):
        checker = self._make_checker()
        spec_add = build_mlir_module_spec(MLIR_ADD)
        spec_mul = build_mlir_module_spec(MLIR_MUL)
        j = checker.check_site(spec_add, spec_mul, _sid("diff"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_judgment_has_site_id(self):
        checker = self._make_checker()
        spec = build_mlir_module_spec(MLIR_ADD)
        sid = _sid("siteid")
        j = checker.check_site(spec, spec, sid)
        self.assertEqual(j.site_id, sid)


if __name__ == "__main__":
    unittest.main()
