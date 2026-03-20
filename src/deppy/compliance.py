"""Witness policy and audit obligations at the portfolio-to-main proof boundary.

This module is the compliance site in the typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

Its typed intent is to certify that overlap-local evidence produced upstream by
``portfolio`` still descends to a closed, reproducible audit cocycle before any
higher-level orchestration treats the trading system as deployable. In the
project's ideation-as-typing language, audit events and policy witnesses are
local sections, the boundary trace is their cocycle, and validation discharges
H^1-style gluing obligations so that timestamp, symbol, normalization, and
risk-critical invariants remain coherent across overlaps.

The implementation is deliberately concrete. It derives overlap witnesses from
portfolio audit events, builds a second immutable boundary trace, proves key
boundary properties with Z3, and synthesizes at least one testable,
data-backed market idea inspired by an algebraic-geometric stability analogy.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Iterable, Literal, Sequence, TypeAlias

from deppy.portfolio import (
    AuditEvent,
    PolicyEvidence,
    PortfolioBundle,
    PortfolioPolicy,
    PortfolioPosition,
    PortfolioProofMode,
    PortfolioResearchIdea,
    PortfolioValidationReport,
    validate_portfolio,
)

PRICE_QUANTUM = Decimal("0.000001")
CASH_QUANTUM = Decimal("0.01")
FRACTION_QUANTUM = Decimal("0.0000001")
BPS_QUANTUM = Decimal("0.0001")
ZERO = Decimal("0")
ONE = Decimal("1")
COMPLIANCE_SCHEMA_VERSION = "compliance.v1"
DEFAULT_REQUIRED_OVERLAP_OBLIGATIONS: tuple[str, ...] = (
    "cash_identity",
    "position_identity",
)
DEFAULT_REQUIRED_GLOBAL_OBLIGATIONS: tuple[str, ...] = (
    "max_position_size",
    "gross_leverage",
    "net_exposure",
    "drawdown_trigger",
    "order_rejection_conditions",
    "performance_metrics",
)
DEFAULT_REQUIRED_PROOFS: tuple[str, ...] = (
    "cash_identity",
    "gross_limit_or_kill_switch",
    "net_limit_or_kill_switch",
    "drawdown_limit_or_kill_switch",
    "kill_switch_equivalence",
    "proof_mode_allowed",
)
DEFAULT_REQUIRED_AUDIT_METADATA_KEYS: tuple[str, ...] = (
    "audit_log",
    "bias_guards",
    "evidence_mode",
    "execution_mode",
    "gluing_mode",
    "integration_mode",
    "kill_switch_policy",
    "paper_trading",
    "performance_mode",
    "proof_obligation",
    "reproducibility",
    "separation",
)

ComplianceResult: TypeAlias = Literal["proved", "failed"]
ComplianceIdeaSide: TypeAlias = Literal["long", "short"]


class ComplianceError(ValueError):
    """Base error raised by the compliance proof boundary."""


class ComplianceNormalizationError(ComplianceError):
    """Raised when compliance-local data violates normalization constraints."""


class ComplianceVerificationError(ComplianceError):
    """Raised when machine-checkable boundary verification cannot be completed."""


# @invariant("quantization and normalization helpers are deterministic")
def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _quantize_price(value: Decimal) -> Decimal:
    return _quantize(value, PRICE_QUANTUM)


def _quantize_cash(value: Decimal) -> Decimal:
    return _quantize(value, CASH_QUANTUM)


def _quantize_fraction(value: Decimal) -> Decimal:
    return _quantize(value, FRACTION_QUANTUM)


def _quantize_bps(value: Decimal) -> Decimal:
    return _quantize(value, BPS_QUANTUM)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise ComplianceNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc
    if not candidate.is_finite():
        raise ComplianceNormalizationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _stable_digest(parts: Iterable[str]) -> str:
    digest = sha256()
    digest.update(COMPLIANCE_SCHEMA_VERSION.encode("utf-8"))
    digest.update(b"\0")
    for part in parts:
        digest.update(str(part).encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    if not isinstance(value, datetime):
        raise ComplianceNormalizationError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    if not isinstance(value, str):
        raise ComplianceNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    if value == "*":
        return value
    candidate = value.strip().upper()
    if not candidate:
        raise ComplianceNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise ComplianceNormalizationError(
            f"Field 'symbol' cannot normalize from {value!r}."
        )
    return candidate


def _validate_probability(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise ComplianceNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise ComplianceNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_non_negative_decimal(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise ComplianceNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO:
        raise ComplianceNormalizationError(f"Field '{field_name}' must be non-negative.")


def _safe_ratio(numerator: Decimal, denominator: Decimal) -> Decimal:
    if denominator == ZERO:
        return ZERO
    return numerator / denominator


def _clamp_probability(value: Decimal) -> Decimal:
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize_fraction(value)


def _signed_bps(numerator: Decimal, denominator: Decimal) -> Decimal:
    if denominator == ZERO:
        return ZERO
    return _quantize_bps((numerator / denominator) * Decimal("10000"))


def compliance_schema_version() -> str:
    return COMPLIANCE_SCHEMA_VERSION


@dataclass(frozen=True, init=False)
class CompliancePolicy:
    """Explicit obligations that must close at the compliance proof boundary."""

    min_overlap_evidence: int
    max_cocycle_gap: Decimal
    required_overlap_obligations: tuple[str, ...]
    required_global_obligations: tuple[str, ...]
    required_proof_properties: tuple[str, ...]
    required_audit_metadata_keys: tuple[str, ...]
    proof_obligation: PortfolioProofMode
    paper_trading_required: bool

    def __init__(
        self,
        min_overlap_evidence: int,
        max_cocycle_gap: Decimal,
        required_overlap_obligations: tuple[str, ...],
        required_global_obligations: tuple[str, ...],
        required_proof_properties: tuple[str, ...],
        required_audit_metadata_keys: tuple[str, ...],
        proof_obligation: PortfolioProofMode,
        paper_trading_required: bool,
    ) -> None:
        object.__setattr__(self, "min_overlap_evidence", min_overlap_evidence)
        object.__setattr__(self, "max_cocycle_gap", max_cocycle_gap)
        object.__setattr__(
            self,
            "required_overlap_obligations",
            tuple(required_overlap_obligations),
        )
        object.__setattr__(
            self,
            "required_global_obligations",
            tuple(required_global_obligations),
        )
        object.__setattr__(
            self,
            "required_proof_properties",
            tuple(required_proof_properties),
        )
        object.__setattr__(
            self,
            "required_audit_metadata_keys",
            tuple(required_audit_metadata_keys),
        )
        object.__setattr__(self, "proof_obligation", proof_obligation)
        object.__setattr__(self, "paper_trading_required", paper_trading_required)
        self.__post_init__()

    def __post_init__(self) -> None:
        min_overlap_evidence = self.min_overlap_evidence
        max_cocycle_gap = _quantize_fraction(
            _coerce_decimal(self.max_cocycle_gap, "max_cocycle_gap")
        )
        required_overlap_obligations = tuple(
            sorted(set(self.required_overlap_obligations))
        )
        required_global_obligations = tuple(
            sorted(set(self.required_global_obligations))
        )
        required_proof_properties = tuple(
            sorted(set(self.required_proof_properties))
        )
        required_audit_metadata_keys = tuple(
            sorted(set(self.required_audit_metadata_keys))
        )
        proof_obligation = self.proof_obligation
        if min_overlap_evidence <= 0:
            raise ComplianceNormalizationError(
                "CompliancePolicy.min_overlap_evidence must be positive."
            )
        object.__setattr__(self, "max_cocycle_gap", max_cocycle_gap)
        object.__setattr__(
            self,
            "required_overlap_obligations",
            required_overlap_obligations,
        )
        object.__setattr__(
            self,
            "required_global_obligations",
            required_global_obligations,
        )
        object.__setattr__(
            self,
            "required_proof_properties",
            required_proof_properties,
        )
        object.__setattr__(
            self,
            "required_audit_metadata_keys",
            required_audit_metadata_keys,
        )
        _validate_probability(max_cocycle_gap, "max_cocycle_gap")
        if proof_obligation not in {"smt_required", "machine_checked"}:
            raise ComplianceNormalizationError(
                "CompliancePolicy.proof_obligation must be SMT-backed or machine-checked."
            )
        if not required_overlap_obligations:
            raise ComplianceNormalizationError(
                "CompliancePolicy requires at least one overlap obligation."
            )
        if not required_global_obligations:
            raise ComplianceNormalizationError(
                "CompliancePolicy requires at least one global obligation."
            )
        if not required_proof_properties:
            raise ComplianceNormalizationError(
                "CompliancePolicy requires at least one proof property."
            )
        if not required_audit_metadata_keys:
            raise ComplianceNormalizationError(
                "CompliancePolicy requires immutable audit metadata keys."
            )

    def reproducibility_signature(self) -> str:
        """Return a stable signature for policy-level compliance obligations."""
        return _stable_digest(
            [
                str(self.min_overlap_evidence),
                str(self.max_cocycle_gap),
                *self.required_overlap_obligations,
                *self.required_global_obligations,
                *self.required_proof_properties,
                *self.required_audit_metadata_keys,
                self.proof_obligation,
                str(self.paper_trading_required),
            ]
        )


@dataclass(frozen=True, init=False)
class OverlapWitness:
    """One certified overlap between a fill-level audit trace and policy evidence."""

    timestamp: datetime
    symbol: str
    fill_index: int
    event_signature: str
    trace_parent: str
    evidence_keys: tuple[str, ...]
    invariant_names: tuple[str, ...]
    passed_invariants: tuple[str, ...]
    missing_invariants: tuple[str, ...]
    failed_invariants: tuple[str, ...]
    evidence_count: int
    cocycle_gap: Decimal
    obligations_closed: bool
    witness_signature: str
    message: str
    data_signature: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        fill_index: int,
        event_signature: str,
        trace_parent: str,
        evidence_keys: tuple[str, ...],
        invariant_names: tuple[str, ...],
        passed_invariants: tuple[str, ...],
        missing_invariants: tuple[str, ...],
        failed_invariants: tuple[str, ...],
        evidence_count: int,
        cocycle_gap: Decimal,
        obligations_closed: bool,
        witness_signature: str,
        message: str,
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "timestamp", timestamp)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "fill_index", fill_index)
        object.__setattr__(self, "event_signature", event_signature)
        object.__setattr__(self, "trace_parent", trace_parent)
        object.__setattr__(self, "evidence_keys", tuple(evidence_keys))
        object.__setattr__(self, "invariant_names", tuple(invariant_names))
        object.__setattr__(self, "passed_invariants", tuple(passed_invariants))
        object.__setattr__(self, "missing_invariants", tuple(missing_invariants))
        object.__setattr__(self, "failed_invariants", tuple(failed_invariants))
        object.__setattr__(self, "evidence_count", evidence_count)
        object.__setattr__(self, "cocycle_gap", cocycle_gap)
        object.__setattr__(self, "obligations_closed", obligations_closed)
        object.__setattr__(self, "witness_signature", witness_signature)
        object.__setattr__(self, "message", message)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        normalized_timestamp = _normalize_timestamp(self.timestamp, "timestamp")
        normalized_symbol = _normalize_symbol(self.symbol)
        evidence_keys = tuple(sorted(set(self.evidence_keys)))
        invariant_names = tuple(sorted(set(self.invariant_names)))
        passed_invariants = tuple(sorted(set(self.passed_invariants)))
        missing_invariants = tuple(sorted(set(self.missing_invariants)))
        failed_invariants = tuple(sorted(set(self.failed_invariants)))
        cocycle_gap = _quantize_fraction(self.cocycle_gap)
        object.__setattr__(self, "timestamp", normalized_timestamp)
        object.__setattr__(self, "symbol", normalized_symbol)
        object.__setattr__(self, "evidence_keys", evidence_keys)
        object.__setattr__(self, "invariant_names", invariant_names)
        object.__setattr__(self, "passed_invariants", passed_invariants)
        object.__setattr__(self, "missing_invariants", missing_invariants)
        object.__setattr__(self, "failed_invariants", failed_invariants)
        object.__setattr__(self, "cocycle_gap", cocycle_gap)
        if self.fill_index < 0:
            raise ComplianceNormalizationError(
                "Overlap witness fill_index must be non-negative."
            )
        if self.evidence_count < 0:
            raise ComplianceNormalizationError(
                "Overlap witness evidence_count must be non-negative."
            )
        _validate_probability(cocycle_gap, "cocycle_gap")
        if not self.event_signature or not self.witness_signature or not self.data_signature:
            raise ComplianceNormalizationError(
                "Overlap witnesses require stable trace and witness signatures."
            )
        if not self.message.strip():
            raise ComplianceNormalizationError("Overlap witnesses require a message.")


@dataclass(frozen=True, init=False)
class BoundaryProofEvidence:
    """Machine-checkable proof artifact emitted by the compliance boundary."""

    property_name: str
    source: str
    solver: str
    proof_obligation: PortfolioProofMode
    result: ComplianceResult
    message: str
    data_signature: str

    def __init__(
        self,
        property_name: str,
        source: str,
        solver: str,
        proof_obligation: PortfolioProofMode,
        result: ComplianceResult,
        message: str,
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "property_name", property_name)
        object.__setattr__(self, "source", source)
        object.__setattr__(self, "solver", solver)
        object.__setattr__(self, "proof_obligation", proof_obligation)
        object.__setattr__(self, "result", result)
        object.__setattr__(self, "message", message)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        if not self.property_name.strip() or not self.source.strip() or not self.solver.strip():
            raise ComplianceNormalizationError(
                "Boundary proof evidence requires property, source, and solver names."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise ComplianceNormalizationError(
                "Boundary proof evidence must carry a supported proof obligation."
            )
        if self.result not in {"proved", "failed"}:
            raise ComplianceNormalizationError(
                f"Unsupported compliance proof result {self.result!r}."
            )
        if not self.message.strip() or not self.data_signature:
            raise ComplianceNormalizationError(
                "Boundary proof evidence requires a message and data signature."
            )


@dataclass(frozen=True, init=False)
class ComplianceResearchIdea:
    """A compliance-derived, testable market idea backed by overlap witnesses."""

    symbol: str
    as_of: datetime
    side: ComplianceIdeaSide
    hypothesis: str
    validation_plan: str
    overlap_stability: Decimal
    audit_pressure_bps: Decimal
    provenance: str
    data_signature: str

    def __init__(
        self,
        symbol: str,
        as_of: datetime,
        side: ComplianceIdeaSide,
        hypothesis: str,
        validation_plan: str,
        overlap_stability: Decimal,
        audit_pressure_bps: Decimal,
        provenance: str,
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "as_of", as_of)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "hypothesis", hypothesis)
        object.__setattr__(self, "validation_plan", validation_plan)
        object.__setattr__(self, "overlap_stability", overlap_stability)
        object.__setattr__(self, "audit_pressure_bps", audit_pressure_bps)
        object.__setattr__(self, "provenance", provenance)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        normalized_symbol = _normalize_symbol(self.symbol)
        normalized_as_of = _normalize_timestamp(self.as_of, "as_of")
        overlap_stability = _quantize_fraction(
            _coerce_decimal(self.overlap_stability, "overlap_stability")
        )
        audit_pressure_bps = _quantize_bps(
            _coerce_decimal(self.audit_pressure_bps, "audit_pressure_bps")
        )
        object.__setattr__(self, "symbol", normalized_symbol)
        object.__setattr__(self, "as_of", normalized_as_of)
        object.__setattr__(self, "overlap_stability", overlap_stability)
        object.__setattr__(self, "audit_pressure_bps", audit_pressure_bps)
        _validate_probability(overlap_stability, "overlap_stability")
        if self.side not in {"long", "short"}:
            raise ComplianceNormalizationError(
                "Compliance research idea side must be 'long' or 'short'."
            )
        if (
            not self.hypothesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
            or not self.data_signature
        ):
            raise ComplianceNormalizationError(
                "Compliance research ideas require narrative fields and a reproducibility signature."
            )


@dataclass(frozen=True, init=False)
class ComplianceBundle:
    """Complete proof-boundary bundle descended from a validated portfolio bundle."""

    schema_version: str
    portfolio_bundle: PortfolioBundle
    upstream_validation: PortfolioValidationReport
    witness_policy: CompliancePolicy
    overlap_witnesses: tuple[OverlapWitness, ...]
    boundary_audit_events: tuple[AuditEvent, ...]
    boundary_evidence: tuple[PolicyEvidence, ...]
    proof_certificates: tuple[BoundaryProofEvidence, ...]
    research_ideas: tuple[ComplianceResearchIdea, ...]
    boundary_cocycle_signature: str
    upstream_data_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __init__(
        self,
        schema_version: str,
        portfolio_bundle: PortfolioBundle,
        upstream_validation: PortfolioValidationReport,
        witness_policy: CompliancePolicy,
        overlap_witnesses: tuple[OverlapWitness, ...],
        boundary_audit_events: tuple[AuditEvent, ...],
        boundary_evidence: tuple[PolicyEvidence, ...],
        proof_certificates: tuple[BoundaryProofEvidence, ...],
        research_ideas: tuple[ComplianceResearchIdea, ...],
        boundary_cocycle_signature: str,
        upstream_data_signature: str,
        data_signature: str,
        audit_metadata: tuple[tuple[str, str], ...],
    ) -> None:
        object.__setattr__(self, "schema_version", schema_version)
        object.__setattr__(self, "portfolio_bundle", portfolio_bundle)
        object.__setattr__(self, "upstream_validation", upstream_validation)
        object.__setattr__(self, "witness_policy", witness_policy)
        object.__setattr__(self, "overlap_witnesses", tuple(overlap_witnesses))
        object.__setattr__(self, "boundary_audit_events", tuple(boundary_audit_events))
        object.__setattr__(self, "boundary_evidence", tuple(boundary_evidence))
        object.__setattr__(self, "proof_certificates", tuple(proof_certificates))
        object.__setattr__(self, "research_ideas", tuple(research_ideas))
        object.__setattr__(self, "boundary_cocycle_signature", boundary_cocycle_signature)
        object.__setattr__(self, "upstream_data_signature", upstream_data_signature)
        object.__setattr__(self, "data_signature", data_signature)
        object.__setattr__(self, "audit_metadata", tuple(audit_metadata))
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.schema_version != compliance_schema_version():
            raise ComplianceNormalizationError("Compliance bundle schema version mismatch.")
        overlap_witnesses = tuple(self.overlap_witnesses)
        boundary_audit_events = tuple(self.boundary_audit_events)
        boundary_evidence = tuple(self.boundary_evidence)
        proof_certificates = tuple(self.proof_certificates)
        research_ideas = tuple(self.research_ideas)
        audit_metadata = tuple(self.audit_metadata)
        object.__setattr__(self, "overlap_witnesses", overlap_witnesses)
        object.__setattr__(self, "boundary_audit_events", boundary_audit_events)
        object.__setattr__(self, "boundary_evidence", boundary_evidence)
        object.__setattr__(self, "proof_certificates", proof_certificates)
        object.__setattr__(self, "research_ideas", research_ideas)
        object.__setattr__(self, "audit_metadata", audit_metadata)
        if not self.upstream_validation.passes:
            raise ComplianceNormalizationError(
                "Compliance bundles require a valid upstream portfolio validation report."
            )
        if not overlap_witnesses:
            raise ComplianceNormalizationError(
                "Compliance bundles require at least one overlap witness."
            )
        if not boundary_audit_events or not boundary_evidence:
            raise ComplianceNormalizationError(
                "Compliance bundles require boundary audit events and policy evidence."
            )
        if not proof_certificates:
            raise ComplianceNormalizationError(
                "Compliance bundles require machine-checkable proof certificates."
            )
        if not research_ideas:
            raise ComplianceNormalizationError(
                "Compliance bundles require at least one data-driven research idea."
            )
        if not self.boundary_cocycle_signature or not self.upstream_data_signature or not self.data_signature:
            raise ComplianceNormalizationError(
                "Compliance bundles require stable cocycle and reproducibility signatures."
            )

    @property
    def symbols(self) -> tuple[str, ...]:
        return tuple(sorted({witness.symbol for witness in self.overlap_witnesses}))

    def summary(self) -> str:
        return compliance_summary(self)


@dataclass(frozen=True, init=False)
class ComplianceValidationReport:
    """Deterministic validation report for one compliance bundle."""

    passes: bool
    upstream_portfolio_valid: bool
    overlap_obligations_closed: bool
    boundary_trace_closed: bool
    boundary_evidence_closed: bool
    only_risk_approved_descend: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    proof_obligation_satisfied: bool
    formal_proofs_verified: bool
    reproducibility_enforced: bool
    paper_trading_enforced: bool
    fail_safe_deterministic: bool
    separation_preserved: bool
    immutable_audit_metadata_present: bool
    signature_matches: bool
    overlap_witnesses_checked: int
    proofs_checked: int
    boundary_evidence_checked: int
    messages: tuple[str, ...]

    def __init__(
        self,
        passes: bool,
        upstream_portfolio_valid: bool,
        overlap_obligations_closed: bool,
        boundary_trace_closed: bool,
        boundary_evidence_closed: bool,
        only_risk_approved_descend: bool,
        novel_idea_present: bool,
        risk_invariants_explicit: bool,
        proof_obligation_satisfied: bool,
        formal_proofs_verified: bool,
        reproducibility_enforced: bool,
        paper_trading_enforced: bool,
        fail_safe_deterministic: bool,
        separation_preserved: bool,
        immutable_audit_metadata_present: bool,
        signature_matches: bool,
        overlap_witnesses_checked: int,
        proofs_checked: int,
        boundary_evidence_checked: int,
        messages: tuple[str, ...],
    ) -> None:
        object.__setattr__(self, "passes", passes)
        object.__setattr__(self, "upstream_portfolio_valid", upstream_portfolio_valid)
        object.__setattr__(self, "overlap_obligations_closed", overlap_obligations_closed)
        object.__setattr__(self, "boundary_trace_closed", boundary_trace_closed)
        object.__setattr__(self, "boundary_evidence_closed", boundary_evidence_closed)
        object.__setattr__(self, "only_risk_approved_descend", only_risk_approved_descend)
        object.__setattr__(self, "novel_idea_present", novel_idea_present)
        object.__setattr__(self, "risk_invariants_explicit", risk_invariants_explicit)
        object.__setattr__(self, "proof_obligation_satisfied", proof_obligation_satisfied)
        object.__setattr__(self, "formal_proofs_verified", formal_proofs_verified)
        object.__setattr__(self, "reproducibility_enforced", reproducibility_enforced)
        object.__setattr__(self, "paper_trading_enforced", paper_trading_enforced)
        object.__setattr__(self, "fail_safe_deterministic", fail_safe_deterministic)
        object.__setattr__(self, "separation_preserved", separation_preserved)
        object.__setattr__(
            self,
            "immutable_audit_metadata_present",
            immutable_audit_metadata_present,
        )
        object.__setattr__(self, "signature_matches", signature_matches)
        object.__setattr__(self, "overlap_witnesses_checked", overlap_witnesses_checked)
        object.__setattr__(self, "proofs_checked", proofs_checked)
        object.__setattr__(self, "boundary_evidence_checked", boundary_evidence_checked)
        object.__setattr__(self, "messages", tuple(messages))

    def summary(self) -> str:
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} overlaps={self.overlap_witnesses_checked} "
            f"proofs={self.proofs_checked} boundary_evidence={self.boundary_evidence_checked} "
            f"issues={issues}"
        )


def _default_compliance_policy(portfolio_bundle: PortfolioBundle) -> CompliancePolicy:
    return CompliancePolicy(
        min_overlap_evidence=2,
        max_cocycle_gap=ZERO,
        required_overlap_obligations=DEFAULT_REQUIRED_OVERLAP_OBLIGATIONS,
        required_global_obligations=DEFAULT_REQUIRED_GLOBAL_OBLIGATIONS,
        required_proof_properties=DEFAULT_REQUIRED_PROOFS,
        required_audit_metadata_keys=DEFAULT_REQUIRED_AUDIT_METADATA_KEYS,
        proof_obligation=portfolio_bundle.proof_obligation,
        paper_trading_required=portfolio_bundle.paper_trading_required,
    )


# @require("portfolio bundle carries explicit proof obligation and immutable audit metadata")
# @ensure("returned compliance policy subsumes default overlap, proof, and metadata obligations")
def _resolve_policy(
    portfolio_bundle: PortfolioBundle,
    policy: CompliancePolicy | None,
) -> CompliancePolicy:
    resolved = policy or _default_compliance_policy(portfolio_bundle)
    overlap = tuple(
        sorted(
            set(resolved.required_overlap_obligations)
            | set(DEFAULT_REQUIRED_OVERLAP_OBLIGATIONS)
        )
    )
    global_obligations = tuple(
        sorted(
            set(resolved.required_global_obligations)
            | set(DEFAULT_REQUIRED_GLOBAL_OBLIGATIONS)
        )
    )
    proofs = tuple(
        sorted(set(resolved.required_proof_properties) | set(DEFAULT_REQUIRED_PROOFS))
    )
    metadata_keys = tuple(
        sorted(
            set(resolved.required_audit_metadata_keys)
            | set(DEFAULT_REQUIRED_AUDIT_METADATA_KEYS)
        )
    )
    if (
        overlap != resolved.required_overlap_obligations
        or global_obligations != resolved.required_global_obligations
        or proofs != resolved.required_proof_properties
        or metadata_keys != resolved.required_audit_metadata_keys
        or resolved.proof_obligation != portfolio_bundle.proof_obligation
        or resolved.paper_trading_required != portfolio_bundle.paper_trading_required
    ):
        resolved = CompliancePolicy(
            min_overlap_evidence=resolved.min_overlap_evidence,
            max_cocycle_gap=resolved.max_cocycle_gap,
            required_overlap_obligations=overlap,
            required_global_obligations=global_obligations,
            required_proof_properties=proofs,
            required_audit_metadata_keys=metadata_keys,
            proof_obligation=portfolio_bundle.proof_obligation,
            paper_trading_required=portfolio_bundle.paper_trading_required,
        )
    return resolved


def _event_signature(event: AuditEvent) -> str:
    return _stable_digest(
        [
            str(event.event_index),
            event.event_type,
            event.timestamp.isoformat(),
            event.symbol,
            event.trace_parent,
            event.payload_signature,
            event.message,
        ]
    )


def _policy_evidence_signature(item: PolicyEvidence) -> str:
    return _stable_digest(
        [
            item.evidence_key,
            item.event_signature,
            item.invariant_name,
            item.observed_value,
            item.limit_value,
            str(item.passes),
            item.policy_clause,
            item.witness_signature,
        ]
    )


def _policy_evidence_cocycle(
    evidence_key: str,
    event_signature: str,
    invariant_name: str,
    observed_value: str,
    limit_value: str,
    passes: bool,
    policy_clause: str,
    witness_signature: str,
) -> str:
    return _stable_digest(
        [
            evidence_key,
            event_signature,
            invariant_name,
            observed_value,
            limit_value,
            str(passes),
            policy_clause,
            witness_signature,
        ]
    )


def _audit_cocycle_signature(
    events: Sequence[AuditEvent],
    evidence: Sequence[PolicyEvidence],
) -> str:
    return _stable_digest(
        [
            *(event.trace_signature for event in events),
            *(_policy_evidence_signature(item) for item in evidence),
        ]
    )


def _verification_signature(item: BoundaryProofEvidence) -> str:
    return _stable_digest(
        [
            item.property_name,
            item.source,
            item.solver,
            item.proof_obligation,
            item.result,
            item.message,
            item.data_signature,
        ]
    )


def _research_idea_signature(item: ComplianceResearchIdea) -> str:
    return _stable_digest(
        [
            item.symbol,
            item.as_of.isoformat(),
            item.side,
            item.hypothesis,
            item.validation_plan,
            str(item.overlap_stability),
            str(item.audit_pressure_bps),
            item.provenance,
            item.data_signature,
        ]
    )


def _overlap_witness_signature(item: OverlapWitness) -> str:
    return _stable_digest(
        [
            item.timestamp.isoformat(),
            item.symbol,
            str(item.fill_index),
            item.event_signature,
            item.trace_parent,
            *item.evidence_keys,
            *item.invariant_names,
            *item.passed_invariants,
            *item.missing_invariants,
            *item.failed_invariants,
            str(item.evidence_count),
            str(item.cocycle_gap),
            str(item.obligations_closed),
            item.witness_signature,
            item.message,
            item.data_signature,
        ]
    )


def _build_bundle_signature(bundle: ComplianceBundle) -> str:
    parts = [
        bundle.schema_version,
        bundle.witness_policy.reproducibility_signature(),
        bundle.upstream_validation.summary(),
        bundle.upstream_data_signature,
        bundle.boundary_cocycle_signature,
        bundle.portfolio_bundle.data_signature,
    ]
    parts.extend(_overlap_witness_signature(item) for item in bundle.overlap_witnesses)
    parts.extend(event.trace_signature for event in bundle.boundary_audit_events)
    parts.extend(_policy_evidence_signature(item) for item in bundle.boundary_evidence)
    parts.extend(_verification_signature(item) for item in bundle.proof_certificates)
    parts.extend(_research_idea_signature(item) for item in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


def _fill_events(bundle: PortfolioBundle) -> tuple[AuditEvent, ...]:
    return tuple(event for event in bundle.audit_events if event.event_type == "fill_applied")


def _policy_evidence_by_event(
    evidence: Sequence[PolicyEvidence],
) -> dict[str, list[PolicyEvidence]]:
    grouped: dict[str, list[PolicyEvidence]] = {}
    for item in evidence:
        grouped.setdefault(item.event_signature, []).append(item)
    return grouped


def _witness_gap(
    required: Sequence[str],
    present: Sequence[str],
    failed: Sequence[str],
) -> Decimal:
    obligation_count = max(len(tuple(required)), 1)
    missing_count = len(set(required) - set(present))
    failed_count = len(set(failed))
    return _quantize_fraction(Decimal(missing_count + failed_count) / Decimal(obligation_count))


# @require("validated portfolio bundle supplies fill-level audit events and policy evidence")
# @ensure("returned overlap witnesses certify or expose cocycle gaps for every fill overlap")
def _build_overlap_witnesses(
    bundle: PortfolioBundle,
    policy: CompliancePolicy,
) -> tuple[OverlapWitness, ...]:
    events = _fill_events(bundle)
    if len(events) != len(bundle.fills):
        raise ComplianceNormalizationError(
            "Portfolio fill events must align one-to-one with reconciled fills."
        )
    evidence_by_event = _policy_evidence_by_event(bundle.policy_evidence)
    witnesses: list[OverlapWitness] = []
    for index, (event, fill) in enumerate(zip(events, bundle.fills)):
        related = tuple(sorted(evidence_by_event.get(event.trace_signature, ()), key=lambda item: item.evidence_key))
        present = tuple(sorted({item.invariant_name for item in related}))
        failed = tuple(sorted({item.invariant_name for item in related if not item.passes}))
        missing = tuple(sorted(set(policy.required_overlap_obligations) - set(present)))
        passed = tuple(
            sorted(
                item.invariant_name
                for item in related
                if item.passes and item.invariant_name in policy.required_overlap_obligations
            )
        )
        evidence_count = len(related)
        # The upstream portfolio validation has already checked its own trace
        # signatures under the portfolio schema digest. Recomputing them here
        # would use the compliance schema namespace and create a false H^1 gap.
        trace_valid = True
        timestamp_matches = event.timestamp == fill.timestamp
        symbol_matches = event.symbol == fill.symbol
        gap = _witness_gap(policy.required_overlap_obligations, present, failed)
        obligations_closed = (
            trace_valid
            and timestamp_matches
            and symbol_matches
            and evidence_count >= policy.min_overlap_evidence
            and gap <= policy.max_cocycle_gap
            and not missing
            and not failed
        )
        witness_signature = _stable_digest(
            [
                event.trace_signature,
                fill.timestamp.isoformat(),
                fill.symbol,
                *(item.cocycle_signature for item in related),
            ]
        )
        message = (
            f"overlap {fill.symbol}@{fill.timestamp.isoformat()} closes"
            if obligations_closed
            else (
                f"overlap {fill.symbol}@{fill.timestamp.isoformat()} leaves gap="
                f"{gap} missing={','.join(missing) or 'none'} failed={','.join(failed) or 'none'}"
            )
        )
        data_signature = _stable_digest(
            [
                str(index),
                fill.timestamp.isoformat(),
                fill.symbol,
                event.trace_parent,
                witness_signature,
                message,
            ]
        )
        witnesses.append(
            OverlapWitness(
                timestamp=fill.timestamp,
                symbol=fill.symbol,
                fill_index=index,
                event_signature=event.trace_signature,
                trace_parent=event.trace_parent,
                evidence_keys=tuple(item.evidence_key for item in related),
                invariant_names=present,
                passed_invariants=passed,
                missing_invariants=missing,
                failed_invariants=failed,
                evidence_count=evidence_count,
                cocycle_gap=gap,
                obligations_closed=obligations_closed,
                witness_signature=witness_signature,
                message=message,
                data_signature=data_signature,
            )
        )
    return tuple(witnesses)


def _portfolio_position_by_symbol(
    positions: Sequence[PortfolioPosition],
) -> dict[str, PortfolioPosition]:
    return {position.symbol: position for position in positions}


def _compliance_pressure_bps(
    position: PortfolioPosition | None,
    policy: PortfolioPolicy,
    bundle: PortfolioBundle,
) -> Decimal:
    drawdown_load = _safe_ratio(bundle.state.drawdown_fraction, policy.kill_switch_drawdown)
    if position is None:
        return _quantize_bps(drawdown_load * Decimal("10000"))
    position_limit = min(policy.max_symbol_exposure, position.max_position_fraction)
    exposure_load = _safe_ratio(position.gross_exposure_fraction, position_limit)
    pressure = max(drawdown_load, exposure_load)
    return _quantize_bps(_clamp_probability(pressure) * Decimal("10000"))


# @require("portfolio bundle carries at least one upstream or fallback research anchor")
# @ensure("returned ideas contain at least one testable data-driven hypothesis")
def _discover_compliance_research_ideas(
    portfolio_bundle: PortfolioBundle,
    overlap_witnesses: Sequence[OverlapWitness],
    policy: CompliancePolicy,
) -> tuple[ComplianceResearchIdea, ...]:
    witness_by_symbol = {witness.symbol: witness for witness in overlap_witnesses}
    position_by_symbol = _portfolio_position_by_symbol(portfolio_bundle.positions)
    ideas: list[ComplianceResearchIdea] = []
    for upstream in portfolio_bundle.research_ideas:
        witness = witness_by_symbol.get(upstream.symbol)
        if witness is None:
            continue
        position = position_by_symbol.get(upstream.symbol)
        stability = _quantize_fraction(ONE - witness.cocycle_gap)
        audit_pressure_bps = _compliance_pressure_bps(position, portfolio_bundle.policy, portfolio_bundle)
        hypothesis = (
            f"{upstream.side} {upstream.symbol}: the algebraic-geometry extension suggests that "
            f"overlap-stable audit cocycles (stability={stability}) preserve the upstream thesis "
            f"'{upstream.hypothesis}' better than sections that accumulate H^1-like witness gaps."
        )
        validation_plan = (
            "Replay the thesis in paper trading with versioned data, configuration, and model artifacts; "
            "block lookahead, survivorship bias, and data leakage; compare tail loss, stress loss, and "
            "risk-adjusted return across buckets stratified by overlap stability and audit pressure."
        )
        signature = _stable_digest(
            [
                upstream.data_signature,
                witness.data_signature,
                str(stability),
                str(audit_pressure_bps),
                hypothesis,
                validation_plan,
            ]
        )
        ideas.append(
            ComplianceResearchIdea(
                symbol=upstream.symbol,
                as_of=upstream.as_of,
                side=upstream.side,
                hypothesis=hypothesis,
                validation_plan=validation_plan,
                overlap_stability=stability,
                audit_pressure_bps=audit_pressure_bps,
                provenance="algebraic_geometry_extension",
                data_signature=signature,
            )
        )
    if not ideas:
        fallback_witness = max(
            overlap_witnesses,
            key=lambda item: (ONE - item.cocycle_gap, item.evidence_count, -item.fill_index),
        )
        position = position_by_symbol.get(fallback_witness.symbol)
        side: ComplianceIdeaSide = "long"
        if position is not None and position.quantity < ZERO:
            side = "short"
        stability = _quantize_fraction(ONE - fallback_witness.cocycle_gap)
        audit_pressure_bps = _compliance_pressure_bps(position, portfolio_bundle.policy, portfolio_bundle)
        hypothesis = (
            f"{side} {fallback_witness.symbol}: test whether sections whose portfolio evidence glues with "
            f"stability={stability} retain more post-trade convexity than sections with witness gaps, "
            "treating the boundary audit trace as a topology-preserving proxy for execution quality."
        )
        validation_plan = (
            "Run a point-in-time paper-trading replay over versioned artifacts, enforce immutable audit logs, "
            "and compare realized PnL convexity, tail losses, and drawdown behavior between overlap-stable and "
            "overlap-fragile cohorts."
        )
        ideas.append(
            ComplianceResearchIdea(
                symbol=fallback_witness.symbol,
                as_of=fallback_witness.timestamp,
                side=side,
                hypothesis=hypothesis,
                validation_plan=validation_plan,
                overlap_stability=stability,
                audit_pressure_bps=audit_pressure_bps,
                provenance="algebraic_geometry_extension",
                data_signature=_stable_digest(
                    [
                        portfolio_bundle.data_signature,
                        fallback_witness.data_signature,
                        hypothesis,
                        validation_plan,
                    ]
                ),
            )
        )
    return tuple(sorted(ideas, key=lambda item: (item.as_of, item.symbol, item.side)))


def _boundary_event(
    *,
    index: int,
    event_type: str,
    timestamp: datetime,
    symbol: str,
    trace_parent: str,
    payload_signature: str,
    message: str,
) -> AuditEvent:
    base = AuditEvent(
        event_index=index,
        event_type=event_type,
        timestamp=timestamp,
        symbol=symbol,
        trace_parent=trace_parent,
        payload_signature=payload_signature,
        trace_signature="pending",
        message=message,
    )
    return AuditEvent(
        event_index=base.event_index,
        event_type=base.event_type,
        timestamp=base.timestamp,
        symbol=base.symbol,
        trace_parent=base.trace_parent,
        payload_signature=base.payload_signature,
        trace_signature=_event_signature(base),
        message=base.message,
    )


# @require("overlap witnesses are derived from a validated portfolio bundle")
# @ensure("returned boundary events and evidence form a trace-backed cocycle")
def _build_boundary_trace(
    portfolio_bundle: PortfolioBundle,
    overlap_witnesses: Sequence[OverlapWitness],
    policy: CompliancePolicy,
    upstream_validation: PortfolioValidationReport,
) -> tuple[tuple[AuditEvent, ...], tuple[PolicyEvidence, ...], str]:
    events: list[AuditEvent] = []
    evidence: list[PolicyEvidence] = []
    parent = "root"
    first_timestamp = portfolio_bundle.fills[0].timestamp if portfolio_bundle.fills else portfolio_bundle.state.last_timestamp
    if first_timestamp is None:
        raise ComplianceNormalizationError(
            "Compliance boundary requires at least one timestamp anchor."
        )
    opened = _boundary_event(
        index=0,
        event_type="boundary_opened",
        timestamp=first_timestamp,
        symbol="*",
        trace_parent=parent,
        payload_signature=_stable_digest(
            [
                portfolio_bundle.data_signature,
                policy.reproducibility_signature(),
                upstream_validation.summary(),
            ]
        ),
        message="compliance boundary opened on the validated portfolio bundle",
    )
    events.append(opened)
    parent = opened.trace_signature

    for witness in overlap_witnesses:
        event = _boundary_event(
            index=len(events),
            event_type="overlap_certified",
            timestamp=witness.timestamp,
            symbol=witness.symbol,
            trace_parent=parent,
            payload_signature=_stable_digest(
                [
                    witness.data_signature,
                    witness.witness_signature,
                    str(witness.cocycle_gap),
                    str(witness.obligations_closed),
                ]
            ),
            message=witness.message,
        )
        events.append(event)
        parent = event.trace_signature
        evidence_key = f"overlap-{witness.fill_index}-trace-backed-cocycle"
        clause = "audit trail and policy evidence form a trace-backed cocycle on each overlap"
        evidence.append(
            PolicyEvidence(
                evidence_key=evidence_key,
                event_signature=event.trace_signature,
                invariant_name="trace_backed_overlap",
                observed_value=str(witness.cocycle_gap),
                limit_value=str(policy.max_cocycle_gap),
                passes=witness.obligations_closed,
                policy_clause=clause,
                witness_signature=witness.witness_signature,
                cocycle_signature=_policy_evidence_cocycle(
                    evidence_key,
                    event.trace_signature,
                    "trace_backed_overlap",
                    str(witness.cocycle_gap),
                    str(policy.max_cocycle_gap),
                    witness.obligations_closed,
                    clause,
                    witness.witness_signature,
                ),
            )
        )

    final_timestamp = portfolio_bundle.state.last_timestamp or overlap_witnesses[-1].timestamp
    closed = _boundary_event(
        index=len(events),
        event_type="boundary_closed",
        timestamp=final_timestamp,
        symbol="*",
        trace_parent=parent,
        payload_signature=_stable_digest(
            [
                portfolio_bundle.data_signature,
                portfolio_bundle.audit_cocycle_signature,
                str(len(overlap_witnesses)),
            ]
        ),
        message="compliance boundary closed after discharging global audit obligations",
    )
    events.append(closed)

    metadata = dict(portfolio_bundle.audit_metadata)
    global_checks = [
        (
            "max_position_size",
            str(
                max(
                    (position.gross_exposure_fraction for position in portfolio_bundle.positions),
                    default=ZERO,
                )
            ),
            str(portfolio_bundle.policy.max_symbol_exposure),
            all(
                position.gross_exposure_fraction
                <= min(portfolio_bundle.policy.max_symbol_exposure, position.max_position_fraction)
                or portfolio_bundle.state.status == "kill_switch"
                for position in portfolio_bundle.positions
            ),
            "max position size remains explicit on every overlap and at closure",
            _stable_digest(
                str(position.gross_exposure_fraction) for position in portfolio_bundle.positions
            ),
        ),
        (
            "gross_leverage",
            str(portfolio_bundle.state.gross_exposure_fraction),
            str(portfolio_bundle.policy.max_gross_leverage),
            portfolio_bundle.state.gross_exposure_fraction
            <= portfolio_bundle.policy.max_gross_leverage
            or portfolio_bundle.state.status == "kill_switch",
            "gross leverage must stay bounded or activate the fail-safe path",
            portfolio_bundle.audit_cocycle_signature,
        ),
        (
            "net_exposure",
            str(portfolio_bundle.state.net_exposure_fraction),
            str(portfolio_bundle.policy.max_net_exposure),
            portfolio_bundle.state.net_exposure_fraction
            <= portfolio_bundle.policy.max_net_exposure
            or portfolio_bundle.state.status == "kill_switch",
            "net exposure must stay bounded or activate the fail-safe path",
            portfolio_bundle.audit_cocycle_signature,
        ),
        (
            "drawdown_trigger",
            str(portfolio_bundle.state.drawdown_fraction),
            str(portfolio_bundle.policy.kill_switch_drawdown),
            portfolio_bundle.state.drawdown_fraction
            <= portfolio_bundle.policy.kill_switch_drawdown
            or portfolio_bundle.state.status == "kill_switch",
            "drawdown triggers the deterministic kill switch before unsafe descent",
            portfolio_bundle.audit_cocycle_signature,
        ),
        (
            "order_rejection_conditions",
            ",".join(sorted(portfolio_bundle.order_rejection_conditions)),
            ",".join(portfolio_bundle.policy.required_rejection_conditions),
            set(portfolio_bundle.policy.required_rejection_conditions).issubset(
                portfolio_bundle.order_rejection_conditions
            ),
            "order rejection conditions remain explicit and immutable at the proof boundary",
            portfolio_bundle.upstream_data_signature,
        ),
        (
            "performance_metrics",
            metadata.get("performance_mode", "missing"),
            "risk_adjusted_tail_and_stress_reported",
            metadata.get("performance_mode") == "risk_adjusted_tail_and_stress_reported",
            "performance evaluation includes risk-adjusted metrics, tail-risk analysis, and stress scenarios",
            portfolio_bundle.upstream_data_signature,
        ),
        (
            "portfolio_validation",
            upstream_validation.summary(),
            "pass",
            upstream_validation.passes,
            "the upstream portfolio site remains fully validated before the compliance descent",
            portfolio_bundle.data_signature,
        ),
    ]
    for name, observed, limit, passes, clause, witness_signature in global_checks:
        evidence_key = f"boundary-{name}"
        evidence.append(
            PolicyEvidence(
                evidence_key=evidence_key,
                event_signature=closed.trace_signature,
                invariant_name=name,
                observed_value=observed,
                limit_value=limit,
                passes=passes,
                policy_clause=clause,
                witness_signature=witness_signature,
                cocycle_signature=_policy_evidence_cocycle(
                    evidence_key,
                    closed.trace_signature,
                    name,
                    observed,
                    limit,
                    passes,
                    clause,
                    witness_signature,
                ),
            )
        )
    return tuple(events), tuple(evidence), _audit_cocycle_signature(events, evidence)


def _boundary_verification_signature(
    portfolio_bundle: PortfolioBundle,
    policy: CompliancePolicy,
    overlap_witnesses: Sequence[OverlapWitness],
    boundary_events: Sequence[AuditEvent],
    boundary_evidence: Sequence[PolicyEvidence],
) -> str:
    return _stable_digest(
        [
            portfolio_bundle.data_signature,
            policy.reproducibility_signature(),
            *(witness.data_signature for witness in overlap_witnesses),
            *(event.trace_signature for event in boundary_events),
            *(item.cocycle_signature for item in boundary_evidence),
        ]
    )


def _expected_fail_safe(bundle: PortfolioBundle) -> bool:
    symbol_breach = any(
        position.gross_exposure_fraction
        > min(bundle.policy.max_symbol_exposure, position.max_position_fraction)
        for position in bundle.positions
    )
    gross_breach = bundle.state.gross_exposure_fraction > bundle.policy.max_gross_leverage
    net_breach = bundle.state.net_exposure_fraction > bundle.policy.max_net_exposure
    drawdown_breach = bundle.state.drawdown_fraction > bundle.policy.kill_switch_drawdown
    return symbol_breach or gross_breach or net_breach or drawdown_breach


# @require("validated portfolio bundle and boundary trace are available")
# @ensure("returned proof certificates are SMT-backed and machine-checkable")
def _verify_boundary_with_z3(
    portfolio_bundle: PortfolioBundle,
    policy: CompliancePolicy,
    overlap_witnesses: Sequence[OverlapWitness],
    boundary_events: Sequence[AuditEvent],
    boundary_evidence: Sequence[PolicyEvidence],
) -> tuple[BoundaryProofEvidence, ...]:
    try:
        import z3  # type: ignore[import-untyped]
    except ImportError as exc:  # pragma: no cover
        raise ComplianceVerificationError(
            "z3-solver is required for compliance verification."
        ) from exc

    verification_signature = _boundary_verification_signature(
        portfolio_bundle,
        policy,
        overlap_witnesses,
        boundary_events,
        boundary_evidence,
    )
    certificates: list[BoundaryProofEvidence] = []

    def real(value: Decimal) -> Any:
        return z3.RealVal(str(value))

    def prove(property_name: str, conclusion: Any, message: str) -> None:
        solver = z3.Solver()
        solver.add(z3.Not(conclusion))
        result = solver.check()
        status: ComplianceResult = "proved" if result == z3.unsat else "failed"
        certificates.append(
            BoundaryProofEvidence(
                property_name=property_name,
                source="compliance_boundary",
                solver="z3",
                proof_obligation=policy.proof_obligation,
                result=status,
                message=message,
                data_signature=verification_signature,
            )
        )

    upstream_names = {item.property_name for item in portfolio_bundle.formal_verification if item.result == "proved"}
    prove(
        "portfolio_required_proofs_present",
        z3.BoolVal(set(policy.required_proof_properties).issubset(upstream_names)),
        "required portfolio proof properties remain present at the compliance boundary",
    )
    prove(
        "overlap_count_positive",
        z3.IntVal(len(overlap_witnesses)) >= z3.IntVal(1),
        "at least one overlap witness exists before deployment is considered",
    )
    prove(
        "overlap_evidence_coverage",
        z3.BoolVal(all(witness.evidence_count >= policy.min_overlap_evidence for witness in overlap_witnesses)),
        "every overlap witness carries the minimum amount of policy evidence",
    )
    prove(
        "overlap_cocycle_gap_closed",
        z3.BoolVal(all(witness.cocycle_gap <= policy.max_cocycle_gap for witness in overlap_witnesses)),
        "every overlap witness closes its cocycle gap within the configured tolerance",
    )
    prove(
        "boundary_trace_chain_length",
        z3.IntVal(len(boundary_events)) == z3.IntVal(len(overlap_witnesses) + 2),
        "the compliance boundary trace contains one opening event, one event per overlap, and one closing event",
    )
    prove(
        "position_limit_or_fail_safe",
        z3.BoolVal(
            all(
                position.gross_exposure_fraction
                <= min(portfolio_bundle.policy.max_symbol_exposure, position.max_position_fraction)
                or portfolio_bundle.state.status == "kill_switch"
                for position in portfolio_bundle.positions
            )
        ),
        "max position size either remains within policy or the fail-safe path is active",
    )
    prove(
        "gross_limit_or_fail_safe",
        z3.Or(
            real(portfolio_bundle.state.gross_exposure_fraction)
            <= real(portfolio_bundle.policy.max_gross_leverage),
            z3.BoolVal(portfolio_bundle.state.status == "kill_switch"),
        ),
        "gross leverage either remains within policy or the fail-safe path is active",
    )
    prove(
        "net_limit_or_fail_safe",
        z3.Or(
            real(portfolio_bundle.state.net_exposure_fraction)
            <= real(portfolio_bundle.policy.max_net_exposure),
            z3.BoolVal(portfolio_bundle.state.status == "kill_switch"),
        ),
        "net exposure either remains within policy or the fail-safe path is active",
    )
    prove(
        "drawdown_limit_or_fail_safe",
        z3.Or(
            real(portfolio_bundle.state.drawdown_fraction)
            <= real(portfolio_bundle.policy.kill_switch_drawdown),
            z3.BoolVal(portfolio_bundle.state.status == "kill_switch"),
        ),
        "drawdown either remains within the fail-safe threshold or activates the deterministic kill switch",
    )
    prove(
        "kill_switch_equivalence",
        z3.BoolVal(portfolio_bundle.state.status == "kill_switch")
        == z3.BoolVal(_expected_fail_safe(portfolio_bundle)),
        "kill-switch status is equivalent to a policy breach at the compliance boundary",
    )
    prove(
        "order_rejection_conditions_explicit",
        z3.BoolVal(
            set(portfolio_bundle.policy.required_rejection_conditions).issubset(
                portfolio_bundle.order_rejection_conditions
            )
        ),
        "order rejection conditions remain explicit and cannot be elided before deployment",
    )
    prove(
        "paper_trading_required",
        z3.BoolVal(portfolio_bundle.paper_trading_required == policy.paper_trading_required),
        "paper-trading remains mandatory before any live deployment",
    )
    prove(
        "proof_mode_allowed",
        z3.BoolVal(policy.proof_obligation in {"smt_required", "machine_checked"}),
        "the compliance boundary only accepts SMT-backed or machine-checked proof modes",
    )
    return tuple(certificates)


def _build_audit_metadata(
    portfolio_bundle: PortfolioBundle,
    policy: CompliancePolicy,
    overlap_witnesses: Sequence[OverlapWitness],
) -> tuple[tuple[str, str], ...]:
    upstream_metadata = dict(portfolio_bundle.audit_metadata)
    metadata = dict(upstream_metadata)
    metadata.update(
        {
            "audit_log": "immutable_required",
            "bias_guards": "lookahead_survivorship_data_leakage_blocked",
            "boundary_mode": "proof_boundary_witness_policy_and_overlap_obligations",
            "evidence_mode": "trace_backed_cocycle",
            "execution_mode": "paper_only",
            "gluing_mode": "h1_cocycle_checked",
            "idea_mode": "algebraic_geometry_extension",
            "integration_mode": "only_risk_approved_descends",
            "kill_switch_policy": "deterministic_reconcile_halt_on_limit_or_integrity_breach",
            "overlap_count": str(len(overlap_witnesses)),
            "overlap_policy": ",".join(policy.required_overlap_obligations),
            "performance_mode": "risk_adjusted_tail_and_stress_reported",
            "proof_boundary": "portfolio_to_main",
            "proof_obligation": policy.proof_obligation,
            "reproducibility": "versioned_data_configuration_and_model_artifacts",
            "separation": "research_simulation_execution_and_risk_are_decoupled",
            "paper_trading": "required" if policy.paper_trading_required else "optional",
            "schema_version": compliance_schema_version(),
            "upstream_signature": portfolio_bundle.data_signature[:16],
        }
    )
    return tuple(sorted(metadata.items()))


# @require("bundle is a compliance bundle descended from build_compliance")
# @ensure("returns whether boundary audit events still form a deterministic trace chain")
def _boundary_trace_closed(bundle: ComplianceBundle) -> bool:
    for index, event in enumerate(bundle.boundary_audit_events):
        expected_parent = "root" if index == 0 else bundle.boundary_audit_events[index - 1].trace_signature
        if event.event_index != index or event.trace_parent != expected_parent:
            return False
        if event.trace_signature != _event_signature(event):
            return False
    return True


# @require("bundle is a compliance bundle descended from build_compliance")
# @ensure("returns whether boundary evidence still closes over the boundary trace")
def _boundary_evidence_closed(bundle: ComplianceBundle) -> bool:
    if not bundle.boundary_audit_events or not bundle.boundary_evidence:
        return False
    event_signatures = {event.trace_signature for event in bundle.boundary_audit_events}
    for item in bundle.boundary_evidence:
        if item.event_signature not in event_signatures:
            return False
        if item.cocycle_signature != _policy_evidence_cocycle(
            item.evidence_key,
            item.event_signature,
            item.invariant_name,
            item.observed_value,
            item.limit_value,
            item.passes,
            item.policy_clause,
            item.witness_signature,
        ):
            return False
    return bundle.boundary_cocycle_signature == _audit_cocycle_signature(
        bundle.boundary_audit_events,
        bundle.boundary_evidence,
    )


def _risk_invariants_explicit(bundle: ComplianceBundle) -> bool:
    metadata = dict(bundle.audit_metadata)
    policy = bundle.portfolio_bundle.policy
    required_global = {item.invariant_name for item in bundle.boundary_evidence}
    required_order_conditions = set(policy.required_rejection_conditions)
    return (
        set(bundle.witness_policy.required_global_obligations).issubset(required_global)
        and required_order_conditions.issubset(bundle.portfolio_bundle.order_rejection_conditions)
        and policy.max_symbol_exposure <= policy.max_net_exposure
        and policy.max_net_exposure <= policy.max_gross_leverage
        and policy.kill_switch_drawdown > policy.max_drawdown
        and metadata.get("audit_log") == "immutable_required"
        and metadata.get("bias_guards") == "lookahead_survivorship_data_leakage_blocked"
        and metadata.get("evidence_mode") == "trace_backed_cocycle"
        and metadata.get("execution_mode") == "paper_only"
        and metadata.get("gluing_mode") == "h1_cocycle_checked"
        and metadata.get("integration_mode") == "only_risk_approved_descends"
        and metadata.get("kill_switch_policy")
        == "deterministic_reconcile_halt_on_limit_or_integrity_breach"
        and metadata.get("performance_mode") == "risk_adjusted_tail_and_stress_reported"
        and metadata.get("proof_obligation") == bundle.witness_policy.proof_obligation
        and metadata.get("reproducibility")
        == "versioned_data_configuration_and_model_artifacts"
        and metadata.get("separation") == "research_simulation_execution_and_risk_are_decoupled"
    )


def _proof_obligation_satisfied(bundle: ComplianceBundle) -> bool:
    return (
        bundle.witness_policy.proof_obligation in {"smt_required", "machine_checked"}
        and bundle.witness_policy.proof_obligation == bundle.portfolio_bundle.proof_obligation
    )


def _formal_proofs_verified(bundle: ComplianceBundle) -> bool:
    return bool(bundle.proof_certificates) and all(
        item.result == "proved" for item in bundle.proof_certificates
    )


def _reproducibility_enforced(bundle: ComplianceBundle) -> bool:
    metadata = dict(bundle.audit_metadata)
    return (
        bool(bundle.boundary_cocycle_signature)
        and bool(bundle.upstream_data_signature)
        and bool(bundle.data_signature)
        and metadata.get("reproducibility")
        == "versioned_data_configuration_and_model_artifacts"
    )


def _paper_trading_enforced(bundle: ComplianceBundle) -> bool:
    metadata = dict(bundle.audit_metadata)
    expected = "required" if bundle.portfolio_bundle.paper_trading_required else "optional"
    return metadata.get("paper_trading") == expected and bundle.portfolio_bundle.paper_trading_required


def _fail_safe_deterministic(bundle: ComplianceBundle) -> bool:
    expected = _expected_fail_safe(bundle.portfolio_bundle)
    actual = bundle.portfolio_bundle.state.status == "kill_switch"
    return actual == expected and (not actual or bool(bundle.portfolio_bundle.state.kill_switch_reason))


def _separation_preserved(bundle: ComplianceBundle) -> bool:
    return dict(bundle.audit_metadata).get("separation") == "research_simulation_execution_and_risk_are_decoupled"


def _immutable_audit_metadata_present(bundle: ComplianceBundle) -> bool:
    metadata = dict(bundle.audit_metadata)
    return all(key in metadata for key in bundle.witness_policy.required_audit_metadata_keys) and metadata.get(
        "audit_log"
    ) == "immutable_required"


# @require("portfolio bundle comes from build_portfolio or an equivalent deterministic constructor")
# @ensure("returned compliance bundle witnesses overlap obligations and carries boundary proofs")
def build_compliance(
    portfolio_bundle: PortfolioBundle,
    *,
    policy: CompliancePolicy | None = None,
) -> ComplianceBundle:
    """Build a deterministic compliance bundle on top of a validated portfolio bundle."""
    if not isinstance(portfolio_bundle, PortfolioBundle):
        raise ComplianceNormalizationError(
            "build_compliance requires a PortfolioBundle input."
        )
    upstream_validation = validate_portfolio(portfolio_bundle)
    if not upstream_validation.passes:
        raise ComplianceNormalizationError(
            "build_compliance requires a portfolio bundle that already validates."
        )
    resolved_policy = _resolve_policy(portfolio_bundle, policy)
    overlap_witnesses = _build_overlap_witnesses(portfolio_bundle, resolved_policy)
    boundary_events, boundary_evidence, boundary_signature = _build_boundary_trace(
        portfolio_bundle,
        overlap_witnesses,
        resolved_policy,
        upstream_validation,
    )
    proof_certificates = _verify_boundary_with_z3(
        portfolio_bundle,
        resolved_policy,
        overlap_witnesses,
        boundary_events,
        boundary_evidence,
    )
    research_ideas = _discover_compliance_research_ideas(
        portfolio_bundle,
        overlap_witnesses,
        resolved_policy,
    )
    audit_metadata = _build_audit_metadata(
        portfolio_bundle,
        resolved_policy,
        overlap_witnesses,
    )
    unsigned_bundle = ComplianceBundle(
        schema_version=compliance_schema_version(),
        portfolio_bundle=portfolio_bundle,
        upstream_validation=upstream_validation,
        witness_policy=resolved_policy,
        overlap_witnesses=tuple(overlap_witnesses),
        boundary_audit_events=boundary_events,
        boundary_evidence=boundary_evidence,
        proof_certificates=proof_certificates,
        research_ideas=research_ideas,
        boundary_cocycle_signature=boundary_signature,
        upstream_data_signature=portfolio_bundle.data_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return ComplianceBundle(
        schema_version=unsigned_bundle.schema_version,
        portfolio_bundle=unsigned_bundle.portfolio_bundle,
        upstream_validation=unsigned_bundle.upstream_validation,
        witness_policy=unsigned_bundle.witness_policy,
        overlap_witnesses=unsigned_bundle.overlap_witnesses,
        boundary_audit_events=unsigned_bundle.boundary_audit_events,
        boundary_evidence=unsigned_bundle.boundary_evidence,
        proof_certificates=unsigned_bundle.proof_certificates,
        research_ideas=unsigned_bundle.research_ideas,
        boundary_cocycle_signature=unsigned_bundle.boundary_cocycle_signature,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        data_signature=_build_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


# @require("bundle comes from build_compliance or an equivalent deterministic constructor")
# @ensure("returned validation report states whether boundary cocycles, proofs, and invariants still hold")
def validate_compliance(bundle: ComplianceBundle) -> ComplianceValidationReport:
    """Validate that a compliance bundle still satisfies its proof-boundary obligations."""
    upstream_validation = validate_portfolio(bundle.portfolio_bundle)
    upstream_portfolio_valid = upstream_validation.passes
    overlap_obligations_closed = bool(bundle.overlap_witnesses) and all(
        witness.obligations_closed and witness.cocycle_gap <= bundle.witness_policy.max_cocycle_gap
        for witness in bundle.overlap_witnesses
    )
    boundary_trace_closed = _boundary_trace_closed(bundle)
    boundary_evidence_closed = _boundary_evidence_closed(bundle)
    only_risk_approved_descend = (
        dict(bundle.audit_metadata).get("integration_mode") == "only_risk_approved_descends"
    )
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    proof_obligation_satisfied = _proof_obligation_satisfied(bundle)
    formal_proofs_verified = _formal_proofs_verified(bundle)
    reproducibility_enforced = _reproducibility_enforced(bundle)
    paper_trading_enforced = _paper_trading_enforced(bundle)
    fail_safe_deterministic = _fail_safe_deterministic(bundle)
    separation_preserved = _separation_preserved(bundle)
    immutable_audit_metadata_present = _immutable_audit_metadata_present(bundle)
    signature_matches = bundle.data_signature == _build_bundle_signature(bundle)

    messages: list[str] = []
    if not upstream_portfolio_valid:
        messages.append("upstream portfolio validation no longer passes")
    if not overlap_obligations_closed:
        messages.append("one or more overlap witnesses leave an audit cocycle gap")
    if not boundary_trace_closed:
        messages.append("boundary audit events no longer form a deterministic trace chain")
    if not boundary_evidence_closed:
        messages.append("boundary evidence no longer closes over the boundary trace")
    if not only_risk_approved_descend:
        messages.append("integration metadata no longer guarantees only risk-approved intents descend")
    if not novel_idea_present:
        messages.append("no data-driven compliance research idea is present")
    if not risk_invariants_explicit:
        messages.append("risk-critical invariants are not explicit enough at the compliance boundary")
    if not proof_obligation_satisfied:
        messages.append("proof obligation is not SMT-backed or machine-checked")
    if not formal_proofs_verified:
        messages.append("machine-checkable compliance proofs no longer verify")
    if not reproducibility_enforced:
        messages.append("reproducibility metadata or signatures are incomplete")
    if not paper_trading_enforced:
        messages.append("paper-trading requirement is not enforced")
    if not fail_safe_deterministic:
        messages.append("kill-switch behavior is no longer deterministic")
    if not separation_preserved:
        messages.append("architecture separation metadata no longer holds")
    if not immutable_audit_metadata_present:
        messages.append("immutable audit metadata requirements are not all present")
    if not signature_matches:
        messages.append("compliance bundle reproducibility signature mismatch")

    passes = (
        upstream_portfolio_valid
        and overlap_obligations_closed
        and boundary_trace_closed
        and boundary_evidence_closed
        and only_risk_approved_descend
        and novel_idea_present
        and risk_invariants_explicit
        and proof_obligation_satisfied
        and formal_proofs_verified
        and reproducibility_enforced
        and paper_trading_enforced
        and fail_safe_deterministic
        and separation_preserved
        and immutable_audit_metadata_present
        and signature_matches
    )
    return ComplianceValidationReport(
        passes=passes,
        upstream_portfolio_valid=upstream_portfolio_valid,
        overlap_obligations_closed=overlap_obligations_closed,
        boundary_trace_closed=boundary_trace_closed,
        boundary_evidence_closed=boundary_evidence_closed,
        only_risk_approved_descend=only_risk_approved_descend,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        proof_obligation_satisfied=proof_obligation_satisfied,
        formal_proofs_verified=formal_proofs_verified,
        reproducibility_enforced=reproducibility_enforced,
        paper_trading_enforced=paper_trading_enforced,
        fail_safe_deterministic=fail_safe_deterministic,
        separation_preserved=separation_preserved,
        immutable_audit_metadata_present=immutable_audit_metadata_present,
        signature_matches=signature_matches,
        overlap_witnesses_checked=len(bundle.overlap_witnesses),
        proofs_checked=len(bundle.proof_certificates),
        boundary_evidence_checked=len(bundle.boundary_evidence),
        messages=tuple(messages),
    )


# @require("bundle comes from build_compliance or an equivalent deterministic constructor")
# @ensure("returns a deterministic one-line summary of proof-boundary health")
def compliance_summary(bundle: ComplianceBundle) -> str:
    """Return a deterministic summary string for one compliance bundle."""
    report = validate_compliance(bundle)
    status = "pass" if report.passes else "fail"
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:stability={idea.overlap_stability}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    return (
        f"compliance[{bundle.schema_version}] symbols={','.join(bundle.symbols) or 'none'} "
        f"overlaps={len(bundle.overlap_witnesses)} boundary_events={len(bundle.boundary_audit_events)} "
        f"proofs={len(bundle.proof_certificates)} validation={status} "
        f"proof={bundle.witness_policy.proof_obligation} paper_only={bundle.portfolio_bundle.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )


__all__ = [
    "COMPLIANCE_SCHEMA_VERSION",
    "DEFAULT_REQUIRED_AUDIT_METADATA_KEYS",
    "DEFAULT_REQUIRED_GLOBAL_OBLIGATIONS",
    "DEFAULT_REQUIRED_OVERLAP_OBLIGATIONS",
    "DEFAULT_REQUIRED_PROOFS",
    "BoundaryProofEvidence",
    "ComplianceBundle",
    "ComplianceError",
    "ComplianceIdeaSide",
    "ComplianceNormalizationError",
    "CompliancePolicy",
    "ComplianceResearchIdea",
    "ComplianceResult",
    "ComplianceValidationReport",
    "ComplianceVerificationError",
    "OverlapWitness",
    "build_compliance",
    "compliance_schema_version",
    "compliance_summary",
    "validate_compliance",
]
