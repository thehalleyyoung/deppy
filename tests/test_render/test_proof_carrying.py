"""Tests for deppy.render.proof_carrying — descent certificates."""

from __future__ import annotations

import json
import os
import tempfile
import pytest

from deppy.render.proof_carrying import (
    DescentCertificate,
    ProofStep,
    generate_certificate,
)


# ── ProofStep ────────────────────────────────────────────────────────────────

class TestProofStep:
    def test_creation(self):
        step = ProofStep(
            site_index=0, method="z3", conjunct="x > 0", status="proved",
        )
        assert step.site_index == 0
        assert step.method == "z3"

    def test_defaults(self):
        step = ProofStep(site_index=0, method="sheaf", conjunct="", status="")
        assert step.elapsed_ms == 0.0


# ── DescentCertificate ───────────────────────────────────────────────────────

class TestDescentCertificate:
    def _make_cert(self, **overrides):
        defaults = dict(
            function_name="sort",
            spec_name="is_sorted",
            verdict="verified",
            h0=1,
            h1=0,
            n_vcs_total=5,
            n_vcs_proved=5,
        )
        defaults.update(overrides)
        return DescentCertificate(**defaults)

    def test_creation(self):
        cert = self._make_cert()
        assert cert.function_name == "sort"
        assert cert.is_verified()

    def test_is_verified(self):
        assert self._make_cert(verdict="verified").is_verified()
        assert not self._make_cert(verdict="refuted").is_verified()
        assert not self._make_cert(verdict="inconclusive").is_verified()

    def test_is_sound(self):
        assert self._make_cert(h0=1, h1=0).is_sound()
        assert not self._make_cert(h0=1, h1=1).is_sound()
        assert not self._make_cert(h0=0, h1=0).is_sound()

    def test_finalize_sets_hash(self):
        cert = self._make_cert()
        assert cert.certificate_hash == ""
        cert.finalize()
        assert cert.certificate_hash != ""
        assert len(cert.certificate_hash) > 0

    def test_verify_integrity_after_finalize(self):
        cert = self._make_cert()
        cert.finalize()
        assert cert.verify_integrity()

    def test_integrity_fails_after_tamper(self):
        cert = self._make_cert()
        cert.finalize()
        cert.verdict = "refuted"  # tamper
        assert not cert.verify_integrity()

    def test_integrity_fails_after_vc_tamper(self):
        cert = self._make_cert()
        cert.finalize()
        cert.n_vcs_proved = 0  # tamper
        assert not cert.verify_integrity()

    def test_save_load_roundtrip(self):
        cert = self._make_cert(
            proof_steps=[
                ProofStep(site_index=0, method="z3", conjunct="x>0", status="proved"),
                ProofStep(site_index=1, method="sheaf", conjunct="y>0", status="proved"),
            ],
            package="mylib",
            version="1.0",
        )
        cert.finalize()

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name

        try:
            cert.save(path)
            loaded = DescentCertificate.load(path)
            assert loaded.function_name == cert.function_name
            assert loaded.spec_name == cert.spec_name
            assert loaded.verdict == cert.verdict
            assert loaded.h0 == cert.h0
            assert loaded.h1 == cert.h1
            assert loaded.n_vcs_total == cert.n_vcs_total
            assert loaded.n_vcs_proved == cert.n_vcs_proved
            assert loaded.verify_integrity()
            assert len(loaded.proof_steps) == 2
        finally:
            os.unlink(path)

    def test_save_creates_valid_json(self):
        cert = self._make_cert()
        cert.finalize()
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            cert.save(path)
            with open(path) as f:
                data = json.load(f)
            assert data["function_name"] == "sort"
            assert "certificate_hash" in data.get("integrity", data)
        finally:
            os.unlink(path)

    def test_summary(self):
        cert = self._make_cert()
        cert.finalize()
        summary = cert.summary()
        assert "sort" in summary
        assert "is_sorted" in summary

    def test_proof_steps_in_certificate(self):
        cert = self._make_cert(
            proof_steps=[
                ProofStep(site_index=0, method="z3", conjunct="x>0", status="proved"),
            ],
            proof_methods={"z3": 1},
        )
        cert.finalize()
        assert len(cert.proof_steps) == 1
        assert cert.proof_methods == {"z3": 1}

    def test_double_finalize_updates_hash(self):
        cert = self._make_cert()
        cert.finalize()
        hash1 = cert.certificate_hash
        cert.n_vcs_proved = 3
        cert.finalize()
        hash2 = cert.certificate_hash
        assert hash1 != hash2

    def test_integrity_detects_proof_step_tamper(self):
        """Hash now includes proof step contents, so tampering is detected."""
        cert = self._make_cert(
            proof_steps=[
                ProofStep(site_index=0, method="z3", conjunct="x>0", status="proved"),
            ],
            proof_methods={"z3": 1},
        )
        cert.finalize()
        assert cert.verify_integrity()
        # Tamper with a proof step
        cert.proof_steps[0] = ProofStep(
            site_index=0, method="z3", conjunct="x>0", status="failed")
        assert not cert.verify_integrity()


# ── generate_certificate integration ─────────────────────────────────────────

class _MockVCResult:
    def __init__(self, proved=True, method="z3", elapsed_ms=10.0):
        self.proved = proved
        self.method = method
        self.elapsed_ms = elapsed_ms


class _MockCoverSite:
    def __init__(self, conjunct_idx=0):
        self.conjunct_idx = conjunct_idx


class _MockConjunct:
    def __init__(self, source="x > 0"):
        self.source = source


class _MockCover:
    def __init__(self, n_sites=3):
        self.sites = [_MockCoverSite(i) for i in range(n_sites)]
        self.overlaps = []

    @property
    def overlap_graph(self):
        return {}


class _MockDecomp:
    def __init__(self, n_conjuncts=3):
        self.conjuncts = [_MockConjunct(f"pred_{i}") for i in range(n_conjuncts)]


class _MockSpecResult:
    def __init__(self, correct=True, n_vcs=3):
        self.function_name = "my_func"
        self.spec_name = "my_spec"
        self.correct = correct
        self.refuted = not correct
        self.cech_h0 = 1
        self.cech_h1 = 0
        self.n_vcs_total = n_vcs
        self.n_vcs_proved = n_vcs if correct else 0
        self.n_vcs_refuted = 0 if correct else 1
        self.elapsed_ms = 100.0
        self.vc_results = [_MockVCResult() for _ in range(n_vcs)]
        self.cover = _MockCover(n_vcs)
        self.spec_decomposition = _MockDecomp(n_vcs)


class TestGenerateCertificate:
    def test_basic_generation(self):
        result = _MockSpecResult(correct=True, n_vcs=3)
        cert = generate_certificate(result)
        assert isinstance(cert, DescentCertificate)
        assert cert.function_name == "my_func"
        assert cert.verdict == "verified"
        assert cert.verify_integrity()

    def test_refuted_result(self):
        result = _MockSpecResult(correct=False)
        cert = generate_certificate(result)
        assert cert.verdict == "refuted"
        assert not cert.is_verified()
        assert cert.verify_integrity()

    def test_with_source_hashing(self):
        result = _MockSpecResult()
        cert = generate_certificate(result, source="def f(): pass", spec_source="x > 0")
        assert cert.source_hash != ""
        assert cert.spec_hash != ""

    def test_with_package_info(self):
        result = _MockSpecResult()
        cert = generate_certificate(result, package="mylib", version="2.0")
        assert cert.package == "mylib"
        assert cert.version == "2.0"
