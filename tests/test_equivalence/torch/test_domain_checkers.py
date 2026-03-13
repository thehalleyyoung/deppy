"""Tests for all domain equivalence checkers."""
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
from deppy.equivalence.torch.numerical_equiv import NumericalEquivalenceChecker
from deppy.equivalence.torch.shape_equiv import ShapeEquivalenceChecker
from deppy.equivalence.torch.dtype_equiv import DtypeEquivalenceChecker
from deppy.equivalence.torch.memory_equiv import MemoryEquivalenceChecker
from deppy.equivalence.torch.autograd_equiv import AutogradEquivalenceChecker
from deppy.equivalence.torch.dispatch_equiv import DispatchEquivalenceChecker


def _cfg():
    return TensorEquivalenceConfig()


def _sid(name="test"):
    return SiteId(kind=SiteKind.TENSOR_SHAPE, name=name)


def _inputs(shape=(4, 4), n=3):
    return [[torch.randn(shape)] for _ in range(n)]


def _grad_inputs(shape=(4,), n=3):
    return [[torch.randn(shape, requires_grad=True)] for _ in range(n)]


def _specs(shape=(4, 4)):
    return [TensorSpec(shape=shape, dtype="float32", device="cpu")]


# ── NumericalEquivalenceChecker ─────────────────────────────────────────


class TestNumericalEquivalence(unittest.TestCase):
    def test_identical_functions(self):
        c = NumericalEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _inputs(), _sid())
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_close_functions(self):
        c = NumericalEquivalenceChecker(_cfg())
        f = lambda x: x * 2.0
        g = lambda x: x * 2.0 + 1e-8
        j = c.check_site(f, g, _inputs(), _sid("close"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_different_functions(self):
        c = NumericalEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        g = lambda x: x * 3
        j = c.check_site(f, g, _inputs(), _sid("diff"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_returns_local_judgment(self):
        c = NumericalEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _inputs(), _sid("type"))
        self.assertEqual(j.tensor_site_kind, TensorSiteKind.NUMERICAL)
        self.assertEqual(j.stratum, TensorStratum.NUMERICAL)

    def test_analyze_single(self):
        c = NumericalEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.analyze(f, _inputs(), _sid("analyze"))
        self.assertIsNotNone(j)


# ── ShapeEquivalenceChecker ─────────────────────────────────────────────


class TestShapeEquivalence(unittest.TestCase):
    def test_same_shape(self):
        c = ShapeEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _specs(), _sid("shape_same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_different_shape(self):
        c = ShapeEquivalenceChecker(_cfg())
        f = lambda x: x
        g = lambda x: x.reshape(-1)
        j = c.check_site(f, g, _specs(), _sid("shape_diff"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_returns_structural_stratum(self):
        c = ShapeEquivalenceChecker(_cfg())
        f = lambda x: x
        j = c.check_site(f, f, _specs(), _sid("stratum"))
        self.assertEqual(j.stratum, TensorStratum.STRUCTURAL)

    def test_analyze_single(self):
        c = ShapeEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.analyze(f, _specs(), _sid("analyze"))
        self.assertIsNotNone(j)


# ── DtypeEquivalenceChecker ─────────────────────────────────────────────


class TestDtypeEquivalence(unittest.TestCase):
    def test_same_dtype(self):
        c = DtypeEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _specs(), _sid("dtype_same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_different_dtype(self):
        c = DtypeEquivalenceChecker(_cfg())
        f = lambda x: x.float()
        g = lambda x: x.double()
        j = c.check_site(f, g, _specs(), _sid("dtype_diff"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_analyze_single(self):
        c = DtypeEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.analyze(f, _specs(), _sid("analyze"))
        self.assertIsNotNone(j)


# ── MemoryEquivalenceChecker ────────────────────────────────────────────


class TestMemoryEquivalence(unittest.TestCase):
    def test_same_layout(self):
        c = MemoryEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _inputs(), _sid("mem_same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_contiguous_vs_transpose(self):
        c = MemoryEquivalenceChecker(_cfg())
        f = lambda x: x.contiguous()
        g = lambda x: x.t().contiguous()
        j = c.check_site(f, g, _inputs(), _sid("mem_diff"))
        # Memory layout may differ
        self.assertIn(j.verdict, [EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.INEQUIVALENT])

    def test_analyze_single(self):
        c = MemoryEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.analyze(f, _inputs(), _sid("analyze"))
        self.assertIsNotNone(j)


# ── AutogradEquivalenceChecker ──────────────────────────────────────────


class TestAutogradEquivalence(unittest.TestCase):
    def test_same_gradients(self):
        c = AutogradEquivalenceChecker(_cfg())
        f = lambda x: (x ** 2).sum()
        j = c.check_site(f, f, _grad_inputs(), _sid("grad_same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_different_gradients(self):
        c = AutogradEquivalenceChecker(_cfg())
        f = lambda x: (x ** 2).sum()
        g = lambda x: (x ** 3).sum()
        j = c.check_site(f, g, _grad_inputs(), _sid("grad_diff"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_analyze_single(self):
        c = AutogradEquivalenceChecker(_cfg())
        f = lambda x: (x ** 2).sum()
        j = c.analyze(f, _grad_inputs(), _sid("analyze"))
        self.assertIsNotNone(j)


# ── DispatchEquivalenceChecker ──────────────────────────────────────────


class TestDispatchEquivalence(unittest.TestCase):
    def test_same_dispatch(self):
        c = DispatchEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.check_site(f, f, _inputs(), _sid("disp_same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_analyze_single(self):
        c = DispatchEquivalenceChecker(_cfg())
        f = lambda x: x * 2
        j = c.analyze(f, _inputs(), _sid("analyze"))
        self.assertIsNotNone(j)


if __name__ == "__main__":
    unittest.main()
