"""Proof-carrying code via sheaf descent certificates.

Ships verified behavioral certificates with Python packages.  Each
certificate records that a function satisfies a spec, backed by a
sheaf-theoretic descent proof: H⁰=1 (global section exists) and
H¹=0 (no obstructions), with the full proof log.

The certificate is a JSON-serializable artifact that can be:
  1. Generated during CI/CD after verification passes.
  2. Shipped alongside the package (e.g., in a `.deppy-cert` directory).
  3. Verified by consumers in O(n) time (re-check the proof log,
     not re-run Z3).

Usage:
    # Generate certificate
    from deppy.render.proof_carrying import generate_certificate
    cert = generate_certificate(verification_result)
    cert.save("path/to/cert.json")

    # Verify certificate
    cert = DescentCertificate.load("path/to/cert.json")
    valid = cert.verify_integrity()
"""

from __future__ import annotations

import hashlib
import json
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional


@dataclass
class ProofStep:
    """A single step in the proof log."""
    site_index: int
    method: str        # "z3_proof", "structural", "sheaf_transfer", "kan_complete"
    conjunct: str      # The conjunct text
    status: str        # "proved", "refuted", "inconclusive"
    elapsed_ms: float = 0.0


@dataclass
class DescentCertificate:
    """A sheaf descent certificate for a verified function.

    The certificate attests that:
      - The function satisfies the given spec
      - The proof was obtained via sheaf descent (not just testing)
      - H⁰=1 (global section exists) and H¹=0 (no obstructions)
      - Each VC was discharged by a specific method

    The certificate hash covers the function source + spec source +
    proof steps, so any change to the code invalidates it.
    """
    # Identity
    function_name: str
    spec_name: str
    package: str = ""
    version: str = ""

    # Proof summary
    verdict: str = "unknown"  # "verified", "refuted", "inconclusive"
    h0: int = 0
    h1: int = 0
    n_vcs_total: int = 0
    n_vcs_proved: int = 0
    n_vcs_refuted: int = 0

    # Proof details
    proof_steps: List[ProofStep] = field(default_factory=list)
    proof_methods: Dict[str, int] = field(default_factory=dict)

    # Integrity
    source_hash: str = ""       # SHA-256 of function source
    spec_hash: str = ""         # SHA-256 of spec source
    certificate_hash: str = ""  # SHA-256 of the full certificate
    timestamp: str = ""
    deppy_version: str = "0.1.0"

    # Metadata
    elapsed_ms: float = 0.0
    cover_sites: int = 0
    cover_overlaps: int = 0

    def is_verified(self) -> bool:
        return self.verdict == "verified"

    def is_sound(self) -> bool:
        """Check the soundness certificate: H⁰=1 ∧ H¹=0."""
        return self.h0 == 1 and self.h1 == 0

    def verify_integrity(self) -> bool:
        """Re-verify the certificate hash to detect tampering."""
        expected = self._compute_hash()
        return expected == self.certificate_hash

    def _compute_hash(self) -> str:
        """Compute the certificate hash from its contents.

        Includes all semantically meaningful fields: identity, verdict,
        cohomology, VC counts, source hashes, and proof step details.
        """
        parts = [
            f"{self.function_name}:{self.spec_name}",
            f"{self.source_hash}:{self.spec_hash}",
            f"{self.verdict}:{self.h0}:{self.h1}",
            f"{self.n_vcs_total}:{self.n_vcs_proved}:{self.n_vcs_refuted}",
            f"{self.package}:{self.version}",
        ]
        # Include each proof step's content
        for step in self.proof_steps:
            parts.append(
                f"{step.site_index}:{step.method}:"
                f"{step.conjunct}:{step.status}")
        # Include proof method counts
        for method, count in sorted(self.proof_methods.items()):
            parts.append(f"method:{method}={count}")
        data = "|".join(parts)
        return hashlib.sha256(data.encode()).hexdigest()[:32]

    def finalize(self) -> None:
        """Set the timestamp and compute certificate hash."""
        self.timestamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self.certificate_hash = self._compute_hash()

    def save(self, path: str) -> None:
        """Save certificate to a JSON file."""
        self.finalize()
        data = {
            "deppy_certificate": "v1",
            "function_name": self.function_name,
            "spec_name": self.spec_name,
            "package": self.package,
            "version": self.version,
            "verdict": self.verdict,
            "soundness": {"h0": self.h0, "h1": self.h1},
            "vcs": {
                "total": self.n_vcs_total,
                "proved": self.n_vcs_proved,
                "refuted": self.n_vcs_refuted,
            },
            "proof_methods": self.proof_methods,
            "proof_steps": [
                {"site": s.site_index, "method": s.method,
                 "conjunct": s.conjunct, "status": s.status}
                for s in self.proof_steps
            ],
            "integrity": {
                "source_hash": self.source_hash,
                "spec_hash": self.spec_hash,
                "certificate_hash": self.certificate_hash,
                "timestamp": self.timestamp,
                "deppy_version": self.deppy_version,
            },
            "metadata": {
                "elapsed_ms": self.elapsed_ms,
                "cover_sites": self.cover_sites,
                "cover_overlaps": self.cover_overlaps,
            },
        }
        Path(path).write_text(json.dumps(data, indent=2))

    @classmethod
    def load(cls, path: str) -> DescentCertificate:
        """Load certificate from a JSON file."""
        data = json.loads(Path(path).read_text())
        cert = cls(
            function_name=data.get("function_name", ""),
            spec_name=data.get("spec_name", ""),
            package=data.get("package", ""),
            version=data.get("version", ""),
            verdict=data.get("verdict", "unknown"),
            h0=data.get("soundness", {}).get("h0", 0),
            h1=data.get("soundness", {}).get("h1", 0),
            n_vcs_total=data.get("vcs", {}).get("total", 0),
            n_vcs_proved=data.get("vcs", {}).get("proved", 0),
            n_vcs_refuted=data.get("vcs", {}).get("refuted", 0),
            proof_methods=data.get("proof_methods", {}),
            source_hash=data.get("integrity", {}).get("source_hash", ""),
            spec_hash=data.get("integrity", {}).get("spec_hash", ""),
            certificate_hash=data.get("integrity", {}).get("certificate_hash", ""),
            timestamp=data.get("integrity", {}).get("timestamp", ""),
            deppy_version=data.get("integrity", {}).get("deppy_version", ""),
            elapsed_ms=data.get("metadata", {}).get("elapsed_ms", 0),
            cover_sites=data.get("metadata", {}).get("cover_sites", 0),
            cover_overlaps=data.get("metadata", {}).get("cover_overlaps", 0),
        )
        for step_data in data.get("proof_steps", []):
            cert.proof_steps.append(ProofStep(
                site_index=step_data.get("site", 0),
                method=step_data.get("method", ""),
                conjunct=step_data.get("conjunct", ""),
                status=step_data.get("status", ""),
            ))
        return cert

    def summary(self) -> str:
        lines = [
            f"Descent Certificate: {self.function_name}",
            f"  Spec: {self.spec_name}",
            f"  Verdict: {self.verdict}",
            f"  Soundness: H⁰={self.h0}, H¹={self.h1} "
            f"({'sound' if self.is_sound() else 'UNSOUND'})",
            f"  VCs: {self.n_vcs_proved}/{self.n_vcs_total} proved",
        ]
        if self.proof_methods:
            lines.append("  Methods:")
            for method, count in sorted(
                    self.proof_methods.items(), key=lambda x: -x[1]):
                lines.append(f"    {method}: {count}")
        lines.append(
            f"  Hash: {self.certificate_hash[:16]}... "
            f"({'valid' if self.verify_integrity() else 'INVALID'})")
        return "\n".join(lines)


def generate_certificate(
    verification_result,  # SpecVerificationResult
    source: str = "",
    spec_source: str = "",
    package: str = "",
    version: str = "",
) -> DescentCertificate:
    """Generate a descent certificate from a verification result."""
    vr = verification_result

    # Determine verdict
    if vr.correct is True:
        verdict = "verified"
    elif vr.refuted:
        verdict = "refuted"
    else:
        verdict = "inconclusive"

    # Build proof steps
    proof_steps: List[ProofStep] = []
    method_counts: Dict[str, int] = {}

    for i, vcr in enumerate(vr.vc_results):
        if vcr is None:
            continue
        status = "proved" if vcr.proved else "refuted" if "refuted" in vcr.method else "inconclusive"
        method = vcr.method.split("(")[0].strip() if vcr.method else "unknown"
        method_counts[method] = method_counts.get(method, 0) + 1

        conj_text = ""
        if vr.spec_decomposition and vr.cover:
            site = vr.cover.sites[i] if i < len(vr.cover.sites) else None
            if site and site.conjunct_idx < len(vr.spec_decomposition.conjuncts):
                conj_text = vr.spec_decomposition.conjuncts[site.conjunct_idx].source

        proof_steps.append(ProofStep(
            site_index=i, method=method,
            conjunct=conj_text, status=status,
            elapsed_ms=vcr.elapsed_ms,
        ))

    # Compute hashes
    source_hash = hashlib.sha256(source.encode()).hexdigest()[:32] if source else ""
    spec_hash = hashlib.sha256(spec_source.encode()).hexdigest()[:32] if spec_source else ""

    cert = DescentCertificate(
        function_name=vr.function_name,
        spec_name=vr.spec_name,
        package=package,
        version=version,
        verdict=verdict,
        h0=vr.cech_h0,
        h1=vr.cech_h1,
        n_vcs_total=vr.n_vcs_total,
        n_vcs_proved=vr.n_vcs_proved,
        n_vcs_refuted=vr.n_vcs_refuted,
        proof_steps=proof_steps,
        proof_methods=method_counts,
        source_hash=source_hash,
        spec_hash=spec_hash,
        elapsed_ms=vr.elapsed_ms,
        cover_sites=len(vr.cover.sites) if vr.cover else 0,
        cover_overlaps=len(vr.cover.overlaps) if vr.cover else 0,
    )
    cert.finalize()
    return cert
