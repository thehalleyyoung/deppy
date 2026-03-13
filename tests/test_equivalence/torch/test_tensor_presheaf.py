"""Tests for tensor presheaf construction."""
import unittest

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    TensorEquivalenceConfig,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
)
from deppy.equivalence.torch.tensor_presheaf import (
    FXGraphSummary,
    PresheafMorphism,
    TensorPresheaf,
    TensorSection,
    check_presheaf_naturality,
    trace_function,
)


# ── TensorSection ───────────────────────────────────────────────────────


class TestTensorSection(unittest.TestCase):
    def test_create_section(self):
        sec = TensorSection(
            site_kind=TensorSiteKind.SHAPE,
            stratum=TensorStratum.STRUCTURAL,
            data={"shape": (4, 4)},
        )
        self.assertEqual(sec.site_kind, TensorSiteKind.SHAPE)
        self.assertEqual(sec.stratum, TensorStratum.STRUCTURAL)
        self.assertEqual(sec.data["shape"], (4, 4))

    def test_default_data(self):
        sec = TensorSection(
            site_kind=TensorSiteKind.DTYPE,
            stratum=TensorStratum.METADATA,
        )
        self.assertIsInstance(sec.data, dict)

    def test_trivial_section(self):
        sec = TensorSection(
            site_kind=TensorSiteKind.DEVICE,
            stratum=TensorStratum.METADATA,
            is_trivial=True,
        )
        self.assertTrue(sec.is_trivial)

    def test_restrict(self):
        sec = TensorSection(
            site_kind=TensorSiteKind.SHAPE,
            stratum=TensorStratum.STRUCTURAL,
            data={"shape": (4, 4)},
        )
        restricted = sec.restrict(TensorSiteKind.DTYPE)
        self.assertIsNotNone(restricted)
        self.assertEqual(restricted.site_kind, TensorSiteKind.DTYPE)


# ── FX Tracing ──────────────────────────────────────────────────────────


class TestFXTracing(unittest.TestCase):
    def test_trace_simple_function(self):
        f = lambda x: x * 2
        summary = trace_function(f, [TensorSpec(shape=(4, 4), dtype="float32")])
        self.assertIsInstance(summary, FXGraphSummary)
        self.assertGreater(summary.n_ops, 0)

    def test_trace_has_nodes(self):
        f = lambda x: x + 1
        summary = trace_function(f, [TensorSpec(shape=(4,), dtype="float32")])
        self.assertGreater(len(summary.nodes), 0)

    def test_trace_matmul(self):
        def matmul_fn(x):
            return x @ x

        summary = trace_function(matmul_fn, [TensorSpec(shape=(4, 4), dtype="float32")])
        # FX traces matmul as call_function to operator.matmul
        self.assertIn("matmul", str(summary.op_histogram))

    def test_trace_inplace(self):
        def inplace_fn(x):
            y = x.clone()
            y.add_(1)
            return y

        summary = trace_function(inplace_fn, [TensorSpec(shape=(4,), dtype="float32")])
        self.assertIsInstance(summary, FXGraphSummary)


# ── TensorPresheaf ──────────────────────────────────────────────────────


class TestTensorPresheaf(unittest.TestCase):
    def test_create_presheaf(self):
        sec = TensorSection(
            site_kind=TensorSiteKind.SHAPE,
            stratum=TensorStratum.STRUCTURAL,
            data={"shape": (4, 4)},
        )
        pf = TensorPresheaf(
            fn_name="f",
            sections={TensorSiteKind.SHAPE: sec},
        )
        self.assertEqual(pf.fn_name, "f")
        self.assertIn(TensorSiteKind.SHAPE, pf.sections)

    def test_presheaf_with_multiple_sections(self):
        secs = {
            TensorSiteKind.SHAPE: TensorSection(
                site_kind=TensorSiteKind.SHAPE,
                stratum=TensorStratum.STRUCTURAL,
                data={"shape": (4, 4)},
            ),
            TensorSiteKind.DTYPE: TensorSection(
                site_kind=TensorSiteKind.DTYPE,
                stratum=TensorStratum.METADATA,
                data={"dtype": "float32"},
            ),
        }
        pf = TensorPresheaf(fn_name="g", sections=secs)
        self.assertEqual(len(pf.sections), 2)


# ── Presheaf Naturality ────────────────────────────────────────────────


class TestPresheafNaturality(unittest.TestCase):
    def _make_presheaf(self, name, shape_data, dtype_data):
        return TensorPresheaf(
            fn_name=name,
            sections={
                TensorSiteKind.SHAPE: TensorSection(
                    site_kind=TensorSiteKind.SHAPE,
                    stratum=TensorStratum.STRUCTURAL,
                    data=shape_data,
                ),
                TensorSiteKind.DTYPE: TensorSection(
                    site_kind=TensorSiteKind.DTYPE,
                    stratum=TensorStratum.METADATA,
                    data=dtype_data,
                ),
            },
        )

    def test_natural_isomorphism_same_sections(self):
        pf = self._make_presheaf("f", {"shape": (4, 4)}, {"dtype": "float32"})
        pg = self._make_presheaf("g", {"shape": (4, 4)}, {"dtype": "float32"})
        morph = check_presheaf_naturality(pf, pg)
        self.assertTrue(morph.is_natural)
        self.assertTrue(morph.is_isomorphism)

    def test_not_isomorphism_different_sections(self):
        pf = self._make_presheaf("f", {"shape": (4, 4)}, {"dtype": "float32"})
        pg = self._make_presheaf("g", {"shape": (2, 2)}, {"dtype": "float32"})
        morph = check_presheaf_naturality(pf, pg)
        self.assertFalse(morph.is_isomorphism)

    def test_morphism_components(self):
        pf = self._make_presheaf("f", {"shape": (4, 4)}, {"dtype": "float32"})
        pg = self._make_presheaf("g", {"shape": (4, 4)}, {"dtype": "float32"})
        morph = check_presheaf_naturality(pf, pg)
        self.assertIn(TensorSiteKind.SHAPE, morph.components)
        self.assertTrue(morph.components[TensorSiteKind.SHAPE])

    def test_restricted_site_kinds(self):
        pf = self._make_presheaf("f", {"shape": (4, 4)}, {"dtype": "float32"})
        pg = self._make_presheaf("g", {"shape": (4, 4)}, {"dtype": "float32"})
        morph = check_presheaf_naturality(
            pf, pg, site_kinds=[TensorSiteKind.SHAPE],
        )
        self.assertTrue(morph.is_natural)


if __name__ == "__main__":
    unittest.main()
