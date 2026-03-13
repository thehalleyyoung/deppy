"""Tests for local and global checkers, descent, cohomology."""
import unittest

import torch

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
)
from deppy.equivalence.torch.torch_local_checker import TorchLocalChecker
from deppy.equivalence.torch.torch_global_checker import (
    DescentResult,
    TensorNaturalTransformation,
    TorchGlobalChecker,
    build_natural_transformation,
    compute_tensor_cohomology,
    verify_tensor_descent,
)


def _cfg(**overrides):
    return TensorEquivalenceConfig(**overrides)


def _specs():
    return [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]


# ── TorchLocalChecker ───────────────────────────────────────────────────


class TestTorchLocalChecker(unittest.TestCase):
    def test_equivalent_functions(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        for j in result.judgments:
            self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_inequivalent_functions(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        g = lambda x: x * 3
        result = lc.check_all_sites(f, g, _specs())
        verdicts = [j.verdict for j in result.judgments]
        self.assertIn(EquivalenceVerdict.INEQUIVALENT, verdicts)

    def test_shape_mismatch_short_circuits(self):
        lc = TorchLocalChecker(_cfg(short_circuit_strata=True))
        f = lambda x: x
        g = lambda x: x.reshape(-1)
        result = lc.check_all_sites(f, g, _specs())
        shape_js = [j for j in result.judgments if j.tensor_site_kind == TensorSiteKind.SHAPE]
        self.assertTrue(any(j.verdict == EquivalenceVerdict.INEQUIVALENT for j in shape_js))

    def test_returns_multiple_judgments(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        self.assertGreater(len(result.judgments), 1)

    def test_judgment_site_kinds(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        kinds = {j.tensor_site_kind for j in result.judgments}
        self.assertIn(TensorSiteKind.SHAPE, kinds)
        self.assertIn(TensorSiteKind.DTYPE, kinds)
        self.assertIn(TensorSiteKind.NUMERICAL, kinds)


# ── TorchGlobalChecker ──────────────────────────────────────────────────


class TestTorchGlobalChecker(unittest.TestCase):
    def test_equivalent_global(self):
        gc = TorchGlobalChecker(_cfg())
        f = lambda x: x * 2
        j = gc.check(f, f, _specs())
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)
        self.assertTrue(j.is_equivalent)

    def test_inequivalent_global(self):
        gc = TorchGlobalChecker(_cfg())
        f = lambda x: x * 2
        g = lambda x: x * 3
        j = gc.check(f, g, _specs())
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)
        self.assertFalse(j.is_equivalent)

    def test_global_has_stratum_results(self):
        gc = TorchGlobalChecker(_cfg())
        f = lambda x: x * 2
        j = gc.check(f, f, _specs())
        self.assertIsNotNone(j.stratum_results)
        self.assertIn(TensorStratum.STRUCTURAL, j.stratum_results)

    def test_global_has_local_judgments(self):
        gc = TorchGlobalChecker(_cfg())
        f = lambda x: x * 2
        j = gc.check(f, f, _specs())
        self.assertIsNotNone(j.local_judgments)
        self.assertGreater(len(j.local_judgments), 0)

    def test_global_explanation(self):
        gc = TorchGlobalChecker(_cfg())
        f = lambda x: x * 2
        j = gc.check(f, f, _specs())
        self.assertIsNotNone(j.explanation)
        self.assertIsInstance(j.explanation, str)
        self.assertGreater(len(j.explanation), 0)


# ── Descent Verification ────────────────────────────────────────────────


class TestDescentVerification(unittest.TestCase):
    def test_effective_descent(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        self.assertIsInstance(descent, DescentResult)
        self.assertTrue(descent.is_effective)

    def test_descent_glued_verdict(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        self.assertEqual(descent.glued_verdict, EquivalenceVerdict.EQUIVALENT)

    def test_descent_no_cocycle_violations(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        self.assertEqual(len(descent.cocycle_violations), 0)


# ── Natural Transformation ──────────────────────────────────────────────


class TestNaturalTransformation(unittest.TestCase):
    def test_isomorphism_for_equivalent(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        nt = build_natural_transformation(result, descent)
        self.assertIsInstance(nt, TensorNaturalTransformation)
        self.assertTrue(nt.is_natural)
        self.assertTrue(nt.is_isomorphism)

    def test_no_isomorphism_for_inequivalent(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        g = lambda x: x * 3
        result = lc.check_all_sites(f, g, _specs())
        descent = verify_tensor_descent(result, _cfg())
        nt = build_natural_transformation(result, descent)
        self.assertFalse(nt.is_isomorphism)

    def test_natural_transformation_components(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        nt = build_natural_transformation(result, descent)
        self.assertIsInstance(nt.components, dict)
        self.assertGreater(len(nt.components), 0)


# ── Cohomology ──────────────────────────────────────────────────────────


class TestCohomology(unittest.TestCase):
    def test_trivial_cohomology_for_equivalent(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        result = lc.check_all_sites(f, f, _specs())
        descent = verify_tensor_descent(result, _cfg())
        cohomology = compute_tensor_cohomology(result, descent)
        self.assertIsInstance(cohomology, list)
        # All classes should be trivial for equivalent functions
        for c in cohomology:
            self.assertTrue(c.is_trivial)

    def test_nontrivial_cohomology_for_inequivalent(self):
        lc = TorchLocalChecker(_cfg())
        f = lambda x: x * 2
        g = lambda x: x * 3
        result = lc.check_all_sites(f, g, _specs())
        descent = verify_tensor_descent(result, _cfg())
        cohomology = compute_tensor_cohomology(result, descent)
        # There should be nontrivial cohomology classes
        nontrivial = [c for c in cohomology if not c.is_trivial]
        self.assertGreater(len(nontrivial), 0)


if __name__ == "__main__":
    unittest.main()
