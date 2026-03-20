"""Tests for Triton kernel equivalence checking."""
import unittest

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TritonKernelSpec,
)
from deppy.equivalence.torch.triton_ir import build_kernel_spec
from deppy.equivalence.torch.triton_equiv import (
    KernelComparisonResult,
    TritonStructuralChecker,
)
# Import concrete class from module to avoid Protocol shadowing
from deppy.equivalence.torch import triton_equiv as _triton_equiv_mod


ADD_KERNEL_A = """
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

ADD_KERNEL_B = """
import triton, triton.language as tl

@triton.jit
def add_kernel(x_ptr, y_ptr, out_ptr, n: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK: tl.constexpr = 1024
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    mask = offs < n
    a = tl.load(x_ptr + offs, mask=mask)
    b = tl.load(y_ptr + offs, mask=mask)
    tl.store(out_ptr + offs, a + b, mask=mask)
"""

MUL_KERNEL = """
import triton, triton.language as tl

@triton.jit
def mul_kernel(x_ptr, y_ptr, out_ptr, n: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK: tl.constexpr = 1024
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    mask = offs < n
    x = tl.load(x_ptr + offs, mask=mask)
    y = tl.load(y_ptr + offs, mask=mask)
    tl.store(out_ptr + offs, x * y, mask=mask)
"""

SUM_KERNEL = """
import triton, triton.language as tl

@triton.jit
def sum_kernel(x_ptr, out_ptr, n: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK: tl.constexpr = 1024
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    mask = offs < n
    x = tl.load(x_ptr + offs, mask=mask)
    s = tl.sum(x, axis=0)
    tl.store(out_ptr + pid, s)
"""


def _sid(name="triton"):
    return SiteId(kind=SiteKind.TENSOR_SHAPE, name=name)


# ── TritonStructuralChecker ─────────────────────────────────────────────


class TestTritonStructuralChecker(unittest.TestCase):
    def test_same_kernel_structural_match(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, ADD_KERNEL_A)
        self.assertIsInstance(result, KernelComparisonResult)
        self.assertTrue(result.structural_match)

    def test_renamed_vars_structural_match(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, ADD_KERNEL_B)
        self.assertTrue(result.structural_match)

    def test_memory_match_same_kernel(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, ADD_KERNEL_A)
        self.assertTrue(result.memory_match)

    def test_reduction_match_same_kernel(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, ADD_KERNEL_A)
        self.assertTrue(result.reduction_match)

    def test_add_vs_mul_different(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, MUL_KERNEL)
        self.assertIsInstance(result, KernelComparisonResult)
        self.assertFalse(result.structural_match)
        self.assertFalse(result.computation_match)
        self.assertIn("store computation", result.explanation.lower())

    def test_add_vs_sum_different_structure(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, SUM_KERNEL)
        # Sum has different memory pattern (different number of loads)
        self.assertFalse(result.structural_match)

    def test_result_has_fingerprints(self):
        checker = TritonStructuralChecker()
        result = checker.compare(ADD_KERNEL_A, ADD_KERNEL_A)
        self.assertIsNotNone(result.fingerprint_f)
        self.assertIsNotNone(result.fingerprint_g)


# ── TritonEquivalenceChecker ────────────────────────────────────────────


class TestTritonEquivalenceChecker(unittest.TestCase):
    def _make_checker(self):
        cfg = TensorEquivalenceConfig()
        return _triton_equiv_mod.TritonEquivalenceChecker(cfg)

    def test_equivalent_kernels(self):
        checker = self._make_checker()
        spec_a = build_kernel_spec(ADD_KERNEL_A)
        spec_b = build_kernel_spec(ADD_KERNEL_B)
        j = checker.check_site(spec_a, spec_b, _sid("equiv"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_same_kernel_equivalent(self):
        checker = self._make_checker()
        spec = build_kernel_spec(ADD_KERNEL_A)
        j = checker.check_site(spec, spec, _sid("same"))
        self.assertEqual(j.verdict, EquivalenceVerdict.EQUIVALENT)

    def test_add_vs_mul_structural(self):
        checker = self._make_checker()
        spec_add = build_kernel_spec(ADD_KERNEL_A)
        spec_mul = build_kernel_spec(MUL_KERNEL)
        j = checker.check_site(spec_add, spec_mul, _sid("add_mul"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_add_vs_sum_inequivalent(self):
        checker = self._make_checker()
        spec_add = build_kernel_spec(ADD_KERNEL_A)
        spec_sum = build_kernel_spec(SUM_KERNEL)
        j = checker.check_site(spec_add, spec_sum, _sid("add_sum"))
        self.assertEqual(j.verdict, EquivalenceVerdict.INEQUIVALENT)

    def test_judgment_has_site_id(self):
        checker = self._make_checker()
        spec = build_kernel_spec(ADD_KERNEL_A)
        sid = _sid("siteid")
        j = checker.check_site(spec, spec, sid)
        self.assertEqual(j.site_id, sid)


# ── Memory Patterns ─────────────────────────────────────────────────────


class TestMemoryPatterns(unittest.TestCase):
    def test_add_has_three_accesses(self):
        spec = build_kernel_spec(ADD_KERNEL_A)
        self.assertEqual(len(spec.memory_accesses), 3)

    def test_add_loads_and_stores(self):
        spec = build_kernel_spec(ADD_KERNEL_A)
        loads = [m for m in spec.memory_accesses if m.kind == "load"]
        stores = [m for m in spec.memory_accesses if m.kind == "store"]
        self.assertEqual(len(loads), 2)
        self.assertEqual(len(stores), 1)

    def test_all_loads_masked(self):
        spec = build_kernel_spec(ADD_KERNEL_A)
        loads = [m for m in spec.memory_accesses if m.kind == "load"]
        for load in loads:
            self.assertIsNotNone(load.mask_expr)


if __name__ == "__main__":
    unittest.main()
