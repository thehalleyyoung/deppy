"""Proof certificate generation from solver results.

When the solver proves an obligation UNSAT (the negated formula has no model),
a proof certificate records the reasoning chain so that the kernel can:

1. Verify the proof independently (trust escalation).
2. Cache the proof for incremental re-checking.
3. Emit the proof as a human-readable explanation.

Certificate types:

- **UNSAT_CORE**: A minimal subset of assertions that are jointly unsatisfiable.
- **INTERPOLANT**: Craig interpolants between formula partitions.
- **LEMMA_CHAIN**: A sequence of derived lemmas leading to contradiction.
- **INTERVAL_PROOF**: Proof by interval arithmetic (from ``ArithmeticSolver``).
- **TABLE_PROOF**: Proof by table lookup (from ``TableSolver``).
- **TRIVIAL**: Tautological proof (formula simplified to True/False).
"""

from __future__ import annotations

import enum
import hashlib
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import TrustLevel
from deppy.predicates.base import Predicate
from deppy.solver.solver_interface import (
    SolverObligation,
    SolverResult,
    SolverStatus,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Certificate types
# ═══════════════════════════════════════════════════════════════════════════════


class CertificateType(enum.Enum):
    """The kind of proof certificate."""

    UNSAT_CORE = "unsat_core"
    """Proof from a minimal unsatisfiable core."""

    INTERPOLANT = "interpolant"
    """Craig interpolant between formula partitions."""

    LEMMA_CHAIN = "lemma_chain"
    """Chain of derived lemmas leading to contradiction."""

    INTERVAL_PROOF = "interval_proof"
    """Proof by interval arithmetic propagation."""

    TABLE_PROOF = "table_proof"
    """Proof by table lookup."""

    TRIVIAL = "trivial"
    """Tautological: formula simplified to True/False directly."""

    Z3_PROOF = "z3_proof"
    """Raw Z3 proof object (opaque)."""

    UNKNOWN = "unknown"
    """Certificate type not determined."""


# ═══════════════════════════════════════════════════════════════════════════════
# Proof step
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProofStep:
    """A single step in a proof chain.

    Attributes:
        rule: The inference rule name (e.g., "unit_propagation", "resolution").
        premises: Indices into the proof step list for this step's premises.
        conclusion: The formula derived by this step (as a string).
        justification: Human-readable justification.
    """

    rule: str
    premises: Tuple[int, ...] = ()
    conclusion: str = ""
    justification: str = ""

    def pretty(self, index: int = 0) -> str:
        premise_str = ", ".join(str(p) for p in self.premises)
        if premise_str:
            return f"  [{index}] {self.conclusion}  ({self.rule} from [{premise_str}])"
        return f"  [{index}] {self.conclusion}  ({self.rule})"


# ═══════════════════════════════════════════════════════════════════════════════
# Proof certificate
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProofCertificate:
    """A proof certificate for an UNSAT verification result.

    Attributes:
        certificate_type: What kind of proof this is.
        formula: The formula that was proven unsatisfiable (or valid, depending
            on perspective).
        proof_steps: Ordered sequence of proof steps (for LEMMA_CHAIN).
        trust_level: The trust level of the proof.
        unsat_core: If UNSAT_CORE type, the core formulas.
        interpolant: If INTERPOLANT type, the interpolant formula.
        raw_proof: Opaque backend-specific proof object.
        generation_time_ms: Time to generate the certificate.
        certificate_hash: Content hash for caching and verification.
    """

    certificate_type: CertificateType
    formula: Optional[str] = None
    proof_steps: Tuple[ProofStep, ...] = ()
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    unsat_core: Tuple[str, ...] = ()
    interpolant: Optional[str] = None
    raw_proof: Optional[Any] = field(default=None, compare=False, hash=False)
    generation_time_ms: float = 0.0
    certificate_hash: str = ""

    @property
    def is_complete(self) -> bool:
        """Whether this certificate constitutes a complete proof."""
        return self.certificate_type in {
            CertificateType.UNSAT_CORE,
            CertificateType.LEMMA_CHAIN,
            CertificateType.TRIVIAL,
            CertificateType.Z3_PROOF,
        }

    @property
    def step_count(self) -> int:
        return len(self.proof_steps)

    def pretty(self) -> str:
        """Format the certificate for human consumption."""
        lines = [
            f"ProofCertificate ({self.certificate_type.value})",
            f"  Trust level: {self.trust_level.value}",
        ]
        if self.formula:
            formula_display = self.formula
            if len(formula_display) > 100:
                formula_display = formula_display[:100] + "..."
            lines.append(f"  Formula: {formula_display}")
        if self.unsat_core:
            lines.append(f"  UNSAT core ({len(self.unsat_core)} formulas):")
            for i, core_formula in enumerate(self.unsat_core[:5]):
                lines.append(f"    [{i}] {core_formula}")
            if len(self.unsat_core) > 5:
                lines.append(f"    ... and {len(self.unsat_core) - 5} more")
        if self.proof_steps:
            lines.append(f"  Proof steps ({len(self.proof_steps)}):")
            for i, step in enumerate(self.proof_steps[:10]):
                lines.append(step.pretty(i))
            if len(self.proof_steps) > 10:
                lines.append(f"    ... and {len(self.proof_steps) - 10} more steps")
        if self.interpolant:
            lines.append(f"  Interpolant: {self.interpolant}")
        if self.generation_time_ms > 0:
            lines.append(f"  Generated in {self.generation_time_ms:.1f}ms")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# Certificate generation
# ═══════════════════════════════════════════════════════════════════════════════


def generate_certificate(
    solver_result: SolverResult,
    obligation: SolverObligation,
) -> ProofCertificate:
    """Generate a proof certificate from a solver result and obligation.

    For UNSAT results, builds the most informative certificate possible
    from the available proof data.  For SAT results, returns a trivial
    (non-)certificate.

    Args:
        solver_result: The result from the solver.
        obligation: The original obligation.

    Returns:
        A ``ProofCertificate``.
    """
    t_start = time.perf_counter()

    if solver_result.status != SolverStatus.UNSAT:
        elapsed = (time.perf_counter() - t_start) * 1000
        return ProofCertificate(
            certificate_type=CertificateType.UNKNOWN,
            formula=_formula_str(obligation),
            trust_level=obligation.trust_level,
            generation_time_ms=elapsed,
        )

    # Determine certificate type based on available data
    if solver_result.proof_certificate is not None:
        cert = _from_z3_proof(solver_result, obligation)
    elif solver_result.unsat_core:
        cert = _from_unsat_core(solver_result, obligation)
    elif solver_result.explanation and "interval" in solver_result.explanation.lower():
        cert = _from_interval_proof(solver_result, obligation)
    elif solver_result.explanation and "table" in solver_result.explanation.lower():
        cert = _from_table_proof(solver_result, obligation)
    elif solver_result.explanation and "simpl" in solver_result.explanation.lower():
        cert = _trivial_certificate(obligation)
    else:
        cert = _minimal_certificate(solver_result, obligation)

    elapsed = (time.perf_counter() - t_start) * 1000

    # Compute certificate hash
    cert_hash = _compute_hash(cert)

    return ProofCertificate(
        certificate_type=cert.certificate_type,
        formula=cert.formula,
        proof_steps=cert.proof_steps,
        trust_level=cert.trust_level,
        unsat_core=cert.unsat_core,
        interpolant=cert.interpolant,
        raw_proof=cert.raw_proof,
        generation_time_ms=elapsed,
        certificate_hash=cert_hash,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Certificate generators for specific sources
# ═══════════════════════════════════════════════════════════════════════════════


def _from_z3_proof(
    result: SolverResult, obligation: SolverObligation
) -> ProofCertificate:
    """Build a certificate from a Z3 proof object."""
    steps: List[ProofStep] = []

    # Extract proof steps from Z3 proof tree
    raw_proof = result.proof_certificate
    if raw_proof is not None:
        try:
            proof_str = str(raw_proof)
            # Parse the Z3 proof tree into steps
            for i, line in enumerate(proof_str.split("\n")[:50]):
                line = line.strip()
                if line:
                    steps.append(ProofStep(
                        rule="z3_inference",
                        conclusion=line[:200],
                    ))
        except Exception:
            steps.append(ProofStep(
                rule="z3_proof",
                conclusion="[opaque Z3 proof]",
            ))

    return ProofCertificate(
        certificate_type=CertificateType.Z3_PROOF,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
        raw_proof=raw_proof,
    )


def _from_unsat_core(
    result: SolverResult, obligation: SolverObligation
) -> ProofCertificate:
    """Build a certificate from an UNSAT core."""
    core = result.unsat_core or []
    core_strings = tuple(str(c) for c in core)

    steps: List[ProofStep] = []
    for i, c in enumerate(core_strings):
        steps.append(ProofStep(
            rule="core_axiom",
            conclusion=c,
            justification=f"Member of UNSAT core (index {i})",
        ))
    if steps:
        steps.append(ProofStep(
            rule="contradiction",
            premises=tuple(range(len(core_strings))),
            conclusion="False",
            justification="Joint unsatisfiability of core",
        ))

    return ProofCertificate(
        certificate_type=CertificateType.UNSAT_CORE,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
        unsat_core=core_strings,
    )


def _from_interval_proof(
    result: SolverResult, obligation: SolverObligation
) -> ProofCertificate:
    """Build a certificate from interval arithmetic proof."""
    steps = [
        ProofStep(
            rule="interval_propagation",
            conclusion="Variable bounds propagated to contradiction",
            justification=result.explanation or "Interval arithmetic",
        ),
        ProofStep(
            rule="empty_interval",
            premises=(0,),
            conclusion="False",
            justification="Empty interval detected",
        ),
    ]
    return ProofCertificate(
        certificate_type=CertificateType.INTERVAL_PROOF,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
    )


def _from_table_proof(
    result: SolverResult, obligation: SolverObligation
) -> ProofCertificate:
    """Build a certificate from table lookup proof."""
    steps = [
        ProofStep(
            rule="table_lookup",
            conclusion=result.explanation or "Table lookup",
            justification="Finite-domain enumeration",
        ),
    ]
    return ProofCertificate(
        certificate_type=CertificateType.TABLE_PROOF,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
    )


def _trivial_certificate(obligation: SolverObligation) -> ProofCertificate:
    """Build a trivial certificate (formula simplifies to False)."""
    steps = [
        ProofStep(
            rule="simplification",
            conclusion="False",
            justification="Formula simplifies to contradiction",
        ),
    ]
    return ProofCertificate(
        certificate_type=CertificateType.TRIVIAL,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
    )


def _minimal_certificate(
    result: SolverResult, obligation: SolverObligation
) -> ProofCertificate:
    """Build a minimal certificate when no detailed proof data is available.

    Even without a full proof, the solver's UNSAT answer is itself a
    certificate (a LEMMA_CHAIN with a single solver-reported step).
    """
    steps = [
        ProofStep(
            rule="smt_solver",
            conclusion="False",
            justification=result.explanation or "Solver reported UNSAT",
        ),
    ]
    return ProofCertificate(
        certificate_type=CertificateType.LEMMA_CHAIN,
        formula=_formula_str(obligation),
        proof_steps=tuple(steps),
        trust_level=obligation.trust_level,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Certificate verification
# ═══════════════════════════════════════════════════════════════════════════════


def verify_certificate(certificate: ProofCertificate) -> bool:
    """Basic structural verification of a proof certificate.

    Checks that:
    - The certificate type is known.
    - For UNSAT_CORE: the core is non-empty.
    - For LEMMA_CHAIN: all premise references are valid.
    - Step indices are consistent.

    This does NOT re-check the proof semantically (that would require
    re-running the solver).
    """
    if certificate.certificate_type == CertificateType.UNKNOWN:
        return False

    if certificate.certificate_type == CertificateType.UNSAT_CORE:
        return len(certificate.unsat_core) > 0

    if certificate.certificate_type == CertificateType.LEMMA_CHAIN:
        # Verify premise indices
        for i, step in enumerate(certificate.proof_steps):
            for premise_idx in step.premises:
                if premise_idx < 0 or premise_idx >= i:
                    return False
        return len(certificate.proof_steps) > 0

    if certificate.certificate_type == CertificateType.TRIVIAL:
        return True

    if certificate.certificate_type == CertificateType.Z3_PROOF:
        return certificate.raw_proof is not None

    if certificate.certificate_type == CertificateType.INTERVAL_PROOF:
        return len(certificate.proof_steps) > 0

    if certificate.certificate_type == CertificateType.TABLE_PROOF:
        return len(certificate.proof_steps) > 0

    return False


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _formula_str(obligation: SolverObligation) -> str:
    """Extract a string representation of the obligation formula."""
    try:
        return obligation.formula.pretty()
    except Exception:
        return repr(obligation.formula)


def _compute_hash(cert: ProofCertificate) -> str:
    """Compute a content hash for a certificate."""
    h = hashlib.sha256()
    h.update(cert.certificate_type.value.encode())
    if cert.formula:
        h.update(cert.formula.encode())
    for step in cert.proof_steps:
        h.update(step.rule.encode())
        h.update(step.conclusion.encode())
    for core_item in cert.unsat_core:
        h.update(core_item.encode())
    return h.hexdigest()[:32]
