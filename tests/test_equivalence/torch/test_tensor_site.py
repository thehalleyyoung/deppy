"""Tests for tensor site category construction."""
import unittest

import torch

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    TensorEquivalenceConfig,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
)
from deppy.equivalence.torch.tensor_site import (
    TensorCover,
    TensorObservationSite,
    TensorSiteCategoryBuilder,
    common_refinement,
    filtration_covers,
    generate_test_inputs,
)


# ── TensorObservationSite ───────────────────────────────────────────────


class TestTensorObservationSite(unittest.TestCase):
    def test_create_with_kind_and_spec(self):
        obs = TensorObservationSite(
            kind=TensorSiteKind.SHAPE,
            spec=TensorSpec(shape=(4, 4)),
        )
        self.assertEqual(obs.kind, TensorSiteKind.SHAPE)
        self.assertIsNotNone(obs.spec)

    def test_create_with_explicit_site_id(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="explicit")
        obs = TensorObservationSite(
            kind=TensorSiteKind.SHAPE,
            spec=TensorSpec(shape=(4, 4)),
            _site_id=sid,
        )
        self.assertEqual(obs.site_id, sid)

    def test_stratum_property(self):
        obs = TensorObservationSite(kind=TensorSiteKind.DTYPE)
        self.assertEqual(obs.stratum, TensorStratum.METADATA)

    def test_structural_stratum(self):
        obs = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        self.assertEqual(obs.stratum, TensorStratum.STRUCTURAL)

    def test_numerical_stratum(self):
        obs = TensorObservationSite(kind=TensorSiteKind.NUMERICAL)
        self.assertEqual(obs.stratum, TensorStratum.NUMERICAL)

    def test_behavioral_stratum(self):
        obs = TensorObservationSite(kind=TensorSiteKind.AUTOGRAD)
        self.assertEqual(obs.stratum, TensorStratum.BEHAVIORAL)

    def test_hashing_with_explicit_site_id(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="hash_test")
        obs = TensorObservationSite(
            kind=TensorSiteKind.SHAPE,
            spec=TensorSpec(shape=(4, 4)),
            _site_id=sid,
        )
        self.assertIsInstance(hash(obs), int)

    def test_two_sites_can_go_in_set(self):
        s1 = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        s2 = TensorObservationSite(kind=TensorSiteKind.DTYPE)
        sites = {s1, s2}
        self.assertEqual(len(sites), 2)


# ── TensorCover ─────────────────────────────────────────────────────────


class TestTensorCover(unittest.TestCase):
    def test_create_cover(self):
        obs = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        cover = TensorCover(
            sites=frozenset({obs}),
            stratum=TensorStratum.STRUCTURAL,
            name="c1",
        )
        self.assertEqual(len(cover.sites), 1)
        self.assertEqual(cover.stratum, TensorStratum.STRUCTURAL)
        self.assertEqual(cover.name, "c1")

    def test_multiple_sites(self):
        s1 = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        s2 = TensorObservationSite(kind=TensorSiteKind.DTYPE)
        s3 = TensorObservationSite(kind=TensorSiteKind.DEVICE)
        cover = TensorCover(
            sites=frozenset({s1, s2, s3}),
            stratum=TensorStratum.METADATA,
        )
        self.assertEqual(len(cover.sites), 3)


# ── common_refinement ───────────────────────────────────────────────────


class TestCommonRefinement(unittest.TestCase):
    def test_refinement_of_equal_covers(self):
        obs = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        cover = TensorCover(
            sites=frozenset({obs}),
            stratum=TensorStratum.STRUCTURAL,
        )
        ref = common_refinement(cover, cover)
        self.assertGreaterEqual(len(ref.sites), 1)

    def test_refinement_union(self):
        s1 = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        s2 = TensorObservationSite(kind=TensorSiteKind.DTYPE)
        c1 = TensorCover(sites=frozenset({s1}), stratum=TensorStratum.STRUCTURAL)
        c2 = TensorCover(sites=frozenset({s2}), stratum=TensorStratum.METADATA)
        ref = common_refinement(c1, c2)
        self.assertGreaterEqual(len(ref.sites), 2)


# ── filtration_covers ───────────────────────────────────────────────────


class TestFiltrationCovers(unittest.TestCase):
    def test_filtration_separates_strata(self):
        s_shape = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        s_dtype = TensorObservationSite(kind=TensorSiteKind.DTYPE)
        cover = TensorCover(
            sites=frozenset({s_shape, s_dtype}),
            stratum=TensorStratum.STRUCTURAL,
        )
        fc = filtration_covers(cover)
        self.assertIsInstance(fc, dict)
        self.assertTrue(len(fc) >= 1)

    def test_filtration_keys_are_strata(self):
        s = TensorObservationSite(kind=TensorSiteKind.SHAPE)
        cover = TensorCover(sites=frozenset({s}), stratum=TensorStratum.STRUCTURAL)
        fc = filtration_covers(cover)
        for key in fc:
            self.assertIsInstance(key, TensorStratum)


# ── TensorSiteCategoryBuilder ───────────────────────────────────────────


class TestSiteCategoryBuilder(unittest.TestCase):
    def test_build_from_specs(self):
        cfg = TensorEquivalenceConfig()
        builder = TensorSiteCategoryBuilder(cfg)
        inputs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        outputs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        cat, cover = builder.build_from_specs(inputs, outputs)
        self.assertGreater(len(cat.sites), 0)
        self.assertGreater(len(cover.sites), 0)

    def test_build_from_signatures(self):
        from deppy.equivalence.torch._protocols import TensorSignature

        cfg = TensorEquivalenceConfig()
        builder = TensorSiteCategoryBuilder(cfg)
        sig_f = TensorSignature(
            inputs=(TensorSpec(shape=(4, 4), dtype="float32", device="cpu"),),
            outputs=(TensorSpec(shape=(4, 4), dtype="float32", device="cpu"),),
            name="f",
        )
        sig_g = TensorSignature(
            inputs=(TensorSpec(shape=(4, 4), dtype="float32", device="cpu"),),
            outputs=(TensorSpec(shape=(4, 4), dtype="float32", device="cpu"),),
            name="g",
        )
        cat, cover_f, cover_g = builder.build_from_signatures(sig_f, sig_g)
        self.assertGreater(len(cat.sites), 0)


# ── generate_test_inputs ────────────────────────────────────────────────


class TestGenerateTestInputs(unittest.TestCase):
    def test_generate_single_spec(self):
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        inputs = generate_test_inputs(specs, seed=42, n_random=2)
        self.assertEqual(len(inputs), 2)
        self.assertIsInstance(inputs[0], list)
        self.assertEqual(inputs[0][0].shape, torch.Size([4, 4]))

    def test_generate_multiple_specs(self):
        specs = [
            TensorSpec(shape=(4, 4), dtype="float32", device="cpu"),
            TensorSpec(shape=(3, 3), dtype="float32", device="cpu"),
        ]
        inputs = generate_test_inputs(specs, seed=0, n_random=1)
        self.assertEqual(len(inputs), 1)
        self.assertEqual(len(inputs[0]), 2)
        self.assertEqual(inputs[0][0].shape, torch.Size([4, 4]))
        self.assertEqual(inputs[0][1].shape, torch.Size([3, 3]))

    def test_generate_deterministic(self):
        specs = [TensorSpec(shape=(4, 4), dtype="float32", device="cpu")]
        a = generate_test_inputs(specs, seed=42, n_random=1)
        b = generate_test_inputs(specs, seed=42, n_random=1)
        self.assertTrue(torch.equal(a[0][0], b[0][0]))

    def test_generate_with_grad(self):
        specs = [TensorSpec(shape=(4,), dtype="float32", device="cpu", requires_grad=True)]
        inputs = generate_test_inputs(specs, seed=42, n_random=1)
        self.assertTrue(inputs[0][0].requires_grad)


if __name__ == "__main__":
    unittest.main()
