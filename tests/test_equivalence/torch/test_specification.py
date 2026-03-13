"""Tests for specification module (SpecBuilder, pre-built specs, SpecificationChecker)."""
import unittest

import torch

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    AnalysisVerdict,
    CorrectnessJudgment,
    SpecificationPresheaf,
    TensorEquivalenceConfig,
    TensorSpec,
    TensorStratum,
)
from deppy.equivalence.torch.specification import (
    SpecBuilder,
    SpecificationChecker,
    differentiability_spec,
    dtype_preservation_spec,
    mlir_validity_spec,
    numerical_stability_spec,
    shape_preservation_spec,
    triton_safety_spec,
)


# ── SpecBuilder ─────────────────────────────────────────────────────────


class TestSpecBuilder(unittest.TestCase):
    def test_build_empty(self):
        spec = SpecBuilder("empty").build()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "empty")

    def test_expect_no_nan(self):
        spec = SpecBuilder("no_nan").expect_no_nan().build()
        self.assertEqual(len(spec.sections), 1)

    def test_expect_no_inf(self):
        spec = SpecBuilder("no_inf").expect_no_inf().build()
        self.assertEqual(len(spec.sections), 1)

    def test_expect_no_nan_and_no_inf(self):
        spec = SpecBuilder("stable").expect_no_nan().expect_no_inf().build()
        self.assertEqual(len(spec.sections), 2)

    def test_expect_shape(self):
        spec = SpecBuilder("shape").expect_shape((4, 4)).build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_dtype(self):
        spec = SpecBuilder("dtype").expect_dtype("float32").build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_device(self):
        spec = SpecBuilder("device").expect_device("cpu").build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_deterministic(self):
        spec = SpecBuilder("det").expect_deterministic().build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_gradient_exists(self):
        spec = SpecBuilder("grad").expect_gradient_exists().build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_contiguous(self):
        spec = SpecBuilder("contig").expect_contiguous().build()
        self.assertGreater(len(spec.sections), 0)

    def test_expect_output_range(self):
        spec = SpecBuilder("range").expect_output_range(-1.0, 1.0).build()
        self.assertGreater(len(spec.sections), 0)

    def test_fluent_chaining(self):
        spec = (
            SpecBuilder("chained")
            .expect_no_nan()
            .expect_no_inf()
            .expect_dtype("float32")
            .build()
        )
        self.assertGreater(len(spec.sections), 2)

    def test_expect_predicate(self):
        spec = (
            SpecBuilder("pred")
            .expect_predicate(
                lambda out: out.sum() > 0,
                "output sum positive",
                TensorStratum.NUMERICAL,
            )
            .build()
        )
        self.assertGreater(len(spec.sections), 0)

    def test_strata_populated(self):
        spec = SpecBuilder("s").expect_no_nan().build()
        self.assertIn(TensorStratum.NUMERICAL, spec.strata)

    def test_with_description(self):
        spec = SpecBuilder("desc", description="A test spec").build()
        self.assertEqual(spec.name, "desc")


# ── Pre-built specifications ────────────────────────────────────────────


class TestPrebuiltSpecs(unittest.TestCase):
    def test_numerical_stability_spec(self):
        spec = numerical_stability_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "numerical_stability")
        self.assertGreater(len(spec.sections), 0)

    def test_numerical_stability_custom_name(self):
        spec = numerical_stability_spec(name="custom")
        self.assertEqual(spec.name, "custom")

    def test_differentiability_spec(self):
        spec = differentiability_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "differentiability")

    def test_shape_preservation_spec(self):
        spec = shape_preservation_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "shape_preservation")

    def test_dtype_preservation_spec(self):
        spec = dtype_preservation_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "dtype_preservation")

    def test_triton_safety_spec(self):
        spec = triton_safety_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "triton_safety")

    def test_mlir_validity_spec(self):
        spec = mlir_validity_spec()
        self.assertIsInstance(spec, SpecificationPresheaf)
        self.assertEqual(spec.name, "mlir_validity")


# ── SpecificationChecker ────────────────────────────────────────────────


class TestSpecificationChecker(unittest.TestCase):
    def test_check_valid_function(self):
        checker = SpecificationChecker()
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        tensor_specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = checker.check(f, spec, tensor_specs)
        self.assertIsInstance(j, CorrectnessJudgment)
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)

    def test_conforming_sites(self):
        checker = SpecificationChecker()
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        tensor_specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = checker.check(f, spec, tensor_specs)
        self.assertGreater(len(j.conforming_sites), 0)

    def test_no_violations_for_valid(self):
        checker = SpecificationChecker()
        f = lambda x: x + 1
        spec = numerical_stability_spec()
        tensor_specs = [TensorSpec(shape=(4,), dtype="float32", device="cpu")]
        j = checker.check(f, spec, tensor_specs)
        self.assertEqual(len(j.violating_sites), 0)

    def test_with_config(self):
        cfg = TensorEquivalenceConfig()
        checker = SpecificationChecker(config=cfg)
        f = lambda x: x * 2
        spec = numerical_stability_spec()
        tensor_specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = checker.check(f, spec, tensor_specs)
        self.assertIsNotNone(j.verdict)

    def test_custom_spec(self):
        checker = SpecificationChecker()
        f = lambda x: x * 2
        spec = SpecBuilder("custom").expect_no_nan().expect_no_inf().build()
        tensor_specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        j = checker.check(f, spec, tensor_specs)
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)


if __name__ == "__main__":
    unittest.main()
