"""Typed market-data schema chart for research-to-production trading descent.

This module projects normalized market-data sections into an auditable schema
chart that keeps the research hypothesis, gluing obligations, and risk-critical
descent surface explicit.  Historical and live observations are treated as local
charts in a market cover; only sections whose overlaps glue coherently are
admitted as strategy theses, and only risk-certified inhabitants may descend
toward downstream order-intent modules.

The implementation is intentionally deterministic.  Every section, invariant,
proof certificate, and certified intent carries a reproducibility signature so
that trading decisions remain replayable from versioned data, parameters, and
model artifacts.  The module therefore acts as a typed seam between hypothesis
discovery and formally constrained execution.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Iterable, Mapping, Sequence

from deppy.market_data import (
    MarketDataBundle,
    RiskInvariantSpecification,
    build_market_data,
    market_data_summary,
    validate_market_data,
)

try:
    from .market_data__domain_model_regime_atlas import design_and as _regime_atlas_design_and
except ModuleNotFoundError:
    _regime_atlas_design_and = None

SCHEMA_CHART_VERSION = "market_data__domain_model_schema_chart.v1"
FEATURE_QUANTUM = Decimal("0.0000001")
BPS_QUANTUM = Decimal("0.0001")
ZERO = Decimal("0")
ONE = Decimal("1")


class SchemaChartError(ValueError):
    """Base error raised by the schema chart layer."""


class SchemaChartDependencyError(SchemaChartError):
    """Raised when a requested dependency is unavailable."""


class SchemaChartValidationError(SchemaChartError):
    """Raised when schema preconditions or invariants fail."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _stable_digest(parts: Sequence[str]) -> str:
    return sha256("\x1f".join((SCHEMA_CHART_VERSION, *parts)).encode("utf-8")).hexdigest()


def _coerce_decimal(value: Any, field_name: str, *, quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    try:
        candidate = value if isinstance(value, Decimal) else Decimal(str(value).strip())
    except (AttributeError, InvalidOperation, ValueError) as exc:
        raise SchemaChartValidationError(f"Field '{field_name}' must be numeric, got {value!r}.") from exc
    if not candidate.is_finite():
        raise SchemaChartValidationError(f"Field '{field_name}' must be finite.")
    return _quantize(candidate, quantum)


def _clamp_probability(value: Decimal) -> Decimal:
    return _quantize(min(max(value, ZERO), ONE), FEATURE_QUANTUM)


def _bps_from_fraction(value: Decimal) -> Decimal:
    return _quantize(value * Decimal("10000"), BPS_QUANTUM)


def _normalize_symbol(value: Any) -> str:
    candidate = str(value).strip().upper().replace("/", "").replace("-", "").replace(" ", "")
    if not candidate:
        raise SchemaChartValidationError("Symbol values must normalize to non-empty text.")
    return candidate


def _normalize_regime(value: Any) -> str:
    candidate = str(value or "").strip().lower().replace("-", "_").replace(" ", "_")
    return candidate or "unspecified"


def x_at_least_min_value(x: int | Decimal, min_value: int | Decimal) -> bool:
    """Return whether ``x`` satisfies the minimum-value obligation."""
    return Decimal(str(x)) >= Decimal(str(min_value))


def precondition_holds(
    historical_entries: Sequence[Any],
    live_entries: Sequence[Any],
    *,
    min_value: int = 1,
) -> bool:
    """Return whether the raw support is sufficient for chart construction."""
    return x_at_least_min_value(len(historical_entries), min_value) and bool(live_entries)


@dataclass(frozen=True)
class TransformationStep:
    name: str
    version: str
    purpose: str
    parameters: tuple[tuple[str, str], ...] = ()

    def reproducibility_signature(self) -> str:
        return _stable_digest([self.name, self.version, self.purpose, *(f"{k}={v}" for k, v in self.parameters)])


@dataclass(frozen=True)
class CostModelAssumption:
    transaction_cost_bps: Decimal
    slippage_bps: Decimal
    latency_ms: int
    max_participation_rate: Decimal

    def __post_init__(self) -> None:
        for field_name, value in (
            ("transaction_cost_bps", self.transaction_cost_bps),
            ("slippage_bps", self.slippage_bps),
            ("max_participation_rate", self.max_participation_rate),
        ):
            if not value.is_finite() or value < ZERO:
                raise SchemaChartValidationError(f"Cost field '{field_name}' must be finite and non-negative.")
        if self.latency_ms < 0 or self.max_participation_rate > ONE:
            raise SchemaChartValidationError("Cost-model bounds are invalid.")

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            str(self.transaction_cost_bps),
            str(self.slippage_bps),
            str(self.latency_ms),
            str(self.max_participation_rate),
        ])


@dataclass(frozen=True)
class SchemaInvariant:
    name: str
    actual: Decimal
    lower_bound: Decimal | None = None
    upper_bound: Decimal | None = None
    proof_target: str = "runtime_checked"

    @property
    def satisfied(self) -> bool:
        return (self.lower_bound is None or self.actual >= self.lower_bound) and (
            self.upper_bound is None or self.actual <= self.upper_bound
        )

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            self.name,
            str(self.actual),
            str(self.lower_bound),
            str(self.upper_bound),
            self.proof_target,
            str(self.satisfied),
        ])


@dataclass(frozen=True)
class CounterexampleWitness:
    obligation: str
    details: str
    symbol: str | None = None
    timestamp: datetime | None = None
    observed: str | None = None
    expected: str | None = None

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            self.obligation,
            self.details,
            self.symbol or "",
            self.timestamp.isoformat() if self.timestamp is not None else "",
            self.observed or "",
            self.expected or "",
        ])


@dataclass(frozen=True)
class SchemaChartSection:
    symbol: str
    timestamp: datetime
    regime: str
    gluing_score: Decimal
    novelty_score: Decimal
    support_count: int
    historical_sample_size: int
    expected_edge_bps: Decimal
    effective_edge_bps: Decimal
    confidence: Decimal
    thesis: str
    cost_model: CostModelAssumption
    data_signature: str

    def __post_init__(self) -> None:
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise SchemaChartValidationError("Schema sections require canonical symbols.")
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise SchemaChartValidationError("Schema sections require timezone-aware timestamps.")
        if self.support_count < 1 or self.historical_sample_size < 1:
            raise SchemaChartValidationError("Schema sections require positive support counts.")
        for field_name, value in (
            ("gluing_score", self.gluing_score),
            ("novelty_score", self.novelty_score),
            ("confidence", self.confidence),
        ):
            if _clamp_probability(value) != value:
                raise SchemaChartValidationError(f"Section field '{field_name}' must lie in [0, 1].")
        if not self.thesis.strip() or not self.data_signature:
            raise SchemaChartValidationError("Schema sections require thesis text and a signature.")

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            self.symbol,
            self.timestamp.isoformat(),
            self.regime,
            str(self.gluing_score),
            str(self.novelty_score),
            str(self.support_count),
            str(self.historical_sample_size),
            str(self.expected_edge_bps),
            str(self.effective_edge_bps),
            str(self.confidence),
            self.thesis,
            self.cost_model.reproducibility_signature(),
            self.data_signature,
        ])


@dataclass(frozen=True)
class NoveltyPacket:
    headline: str
    ag_view: str
    typed_view: str
    proof_target: str
    cocycle_tension: Decimal
    overlap_count: int
    gluing_score: Decimal


# @invariant("proof coverage is explicit before strategy sections descend into executable intents")
@dataclass(frozen=True)
class ProofCertification:
    proof_mode: str
    obligations_checked: tuple[str, ...]
    obligations_satisfied: tuple[str, ...]
    coverage_fraction: Decimal
    paper_ready: bool
    live_ready: bool
    rationale: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.proof_mode not in {"smt_required", "machine_checked"}:
            raise SchemaChartValidationError("Proof certification requires a supported proof mode.")
        if _clamp_probability(self.coverage_fraction) != self.coverage_fraction:
            raise SchemaChartValidationError("Proof-certification coverage must lie in [0, 1].")
        if self.live_ready and not self.paper_ready:
            raise SchemaChartValidationError("Live-ready proof certification must also be paper-ready.")

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            self.proof_mode,
            *self.obligations_checked,
            "|".join(self.obligations_satisfied),
            str(self.coverage_fraction),
            str(self.paper_ready),
            str(self.live_ready),
            *self.rationale,
        ])


# @invariant("only risk-approved inhabitants descend into downstream order intents")
@dataclass(frozen=True)
class RiskCertifiedIntent:
    symbol: str
    timestamp: datetime
    regime: str
    thesis: str
    direction: str
    reference_price: Decimal
    target_edge_bps: Decimal
    stop_loss_bps: Decimal
    candidate_position_fraction: Decimal
    candidate_leverage: Decimal
    order_safety_coverage: Decimal
    proof_mode: str
    approved_for_paper: bool
    approved_for_live: bool
    audit_token: str

    def __post_init__(self) -> None:
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise SchemaChartValidationError("Certified intents require canonical symbols.")
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise SchemaChartValidationError("Certified intents require timezone-aware timestamps.")
        if self.direction not in {"long", "short"}:
            raise SchemaChartValidationError("Certified intent direction must be 'long' or 'short'.")
        if self.reference_price <= ZERO:
            raise SchemaChartValidationError("Certified intents require a positive reference price.")
        if self.target_edge_bps < ZERO or self.stop_loss_bps <= ZERO:
            raise SchemaChartValidationError("Certified intents require non-negative edge and positive stop bounds.")
        if _clamp_probability(self.candidate_position_fraction) != self.candidate_position_fraction:
            raise SchemaChartValidationError("Certified-intent position fractions must lie in [0, 1].")
        if self.candidate_leverage < ONE:
            raise SchemaChartValidationError("Certified-intent leverage must be at least one.")
        if _clamp_probability(self.order_safety_coverage) != self.order_safety_coverage:
            raise SchemaChartValidationError("Certified-intent order-safety coverage must lie in [0, 1].")
        if self.approved_for_live and not self.approved_for_paper:
            raise SchemaChartValidationError("Live-approved intents must also be paper-approved.")
        if not self.audit_token:
            raise SchemaChartValidationError("Certified intents require an audit token.")

    def reproducibility_signature(self) -> str:
        return _stable_digest([
            self.symbol,
            self.timestamp.isoformat(),
            self.regime,
            self.thesis,
            self.direction,
            str(self.reference_price),
            str(self.target_edge_bps),
            str(self.stop_loss_bps),
            str(self.candidate_position_fraction),
            str(self.candidate_leverage),
            str(self.order_safety_coverage),
            self.proof_mode,
            str(self.approved_for_paper),
            str(self.approved_for_live),
            self.audit_token,
        ])


@dataclass(frozen=True)
class PromotionGate:
    name: str
    passes: bool
    reason: str
    evidence: tuple[str, ...] = ()

    def reproducibility_signature(self) -> str:
        return _stable_digest([self.name, str(self.passes), self.reason, *self.evidence])


@dataclass(frozen=True)
class MarketDataSchemaChart:
    schema_version: str
    base_bundle: MarketDataBundle
    lineage: tuple[TransformationStep, ...]
    sections: tuple[SchemaChartSection, ...]
    invariants: tuple[SchemaInvariant, ...]
    novelty_packet: NoveltyPacket
    proof_certificate: ProofCertification
    certified_intents: tuple[RiskCertifiedIntent, ...]
    gates: tuple[PromotionGate, ...]
    dependency_state: str
    counterexamples: tuple[CounterexampleWitness, ...]
    audit_metadata: tuple[tuple[str, str], ...]
    data_signature: str

    @property
    def symbols(self) -> tuple[str, ...]:
        return tuple(sorted({section.symbol for section in self.sections}))

    def summary(self) -> str:
        return schema_chart_summary(self)


@dataclass(frozen=True)
class SchemaChartValidationReport:
    passes: bool
    preconditions_hold: bool
    minimum_bounds_hold: bool
    lineage_traceable: bool
    dependency_resolved: bool
    gates_closed_to_live: bool
    signature_matches: bool
    messages: tuple[str, ...]
    counterexamples: tuple[CounterexampleWitness, ...]

    def summary(self) -> str:
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return f"validation={'pass' if self.passes else 'fail'} issues={issues}"


def _adapt_regime_snapshot(regime_snapshot: Any | None) -> dict[str, str]:
    if regime_snapshot is None:
        return {}
    if isinstance(regime_snapshot, Mapping):
        mapping = regime_snapshot.get("symbol_regimes", regime_snapshot)
    else:
        mapping = getattr(regime_snapshot, "symbol_regimes", None)
    if not isinstance(mapping, Mapping):
        raise SchemaChartValidationError("Regime snapshots must be mappings or expose 'symbol_regimes'.")
    return {_normalize_symbol(symbol): _normalize_regime(regime) for symbol, regime in mapping.items()}


def _resolve_regimes(
    historical_entries: Sequence[Mapping[str, Any]],
    live_entries: Sequence[Mapping[str, Any]],
    local_entries: Sequence[Mapping[str, Any]],
    regime_snapshot: Any | None,
    require_regime_dependency: bool,
    min_history_points: int,
) -> tuple[dict[str, str], str]:
    explicit = _adapt_regime_snapshot(regime_snapshot)
    if explicit:
        return explicit, "provided"
    if require_regime_dependency:
        if _regime_atlas_design_and is None:
            raise SchemaChartDependencyError("market_data__domain_model_regime_atlas.design_and is required but unavailable.")
        resolved = _regime_atlas_design_and(
            historical_entries,
            live_entries,
            local_entries=local_entries,
            min_history_points=min_history_points,
        )
        return _adapt_regime_snapshot(resolved), "resolved_by_dependency"
    if _regime_atlas_design_and is None:
        return {}, "optional_missing_local_inference"
    return {}, "optional_available_not_invoked"


def _cost_model_for(section: Any, confidence: Decimal) -> CostModelAssumption:
    relative_spread = section.topology.relative_spread
    flow_pressure = abs(section.topology.flow_pressure)
    return CostModelAssumption(
        transaction_cost_bps=_bps_from_fraction((relative_spread / Decimal("2")) + Decimal("0.00005")),
        slippage_bps=_bps_from_fraction((relative_spread / Decimal("4")) + (flow_pressure / Decimal("10"))),
        latency_ms=int(_quantize((ONE - confidence) * Decimal("1500"), Decimal("1")) + Decimal("50")),
        max_participation_rate=_clamp_probability(Decimal("0.02") + flow_pressure + (confidence / Decimal("10"))),
    )


def _infer_regime(symbol: str, section: Any, hypothesis: Any | None, regimes: Mapping[str, str]) -> str:
    if symbol in regimes:
        return regimes[symbol]
    harmonic = section.topology.harmonic_advantage
    flow = section.topology.flow_pressure
    if harmonic >= ZERO and flow >= ZERO:
        return "coherent_breakout"
    if harmonic < ZERO and flow < ZERO:
        return "coherent_drawdown"
    if hypothesis is not None:
        return _normalize_regime(hypothesis.regime)
    return "range_bound"


def _derive_sections(bundle: MarketDataBundle, regimes: Mapping[str, str]) -> tuple[SchemaChartSection, ...]:
    hypotheses = {hypothesis.symbol: hypothesis for hypothesis in bundle.hypotheses}
    sections: list[SchemaChartSection] = []
    for live_section in bundle.live_sections:
        hypothesis = hypotheses.get(live_section.symbol)
        expected_edge_bps = hypothesis.expected_edge_bps if hypothesis is not None else _bps_from_fraction(abs(live_section.novelty_score))
        confidence = hypothesis.confidence if hypothesis is not None else _clamp_probability(live_section.gluing_score)
        cost_model = _cost_model_for(live_section, confidence)
        signature = _stable_digest([
            live_section.reproducibility_signature(),
            hypothesis.data_signature if hypothesis is not None else "inferred",
            cost_model.reproducibility_signature(),
        ])
        sections.append(
            SchemaChartSection(
                symbol=live_section.symbol,
                timestamp=live_section.timestamp,
                regime=_infer_regime(live_section.symbol, live_section, hypothesis, regimes),
                gluing_score=_clamp_probability(live_section.gluing_score),
                novelty_score=_clamp_probability(abs(live_section.novelty_score) * Decimal("1000")),
                support_count=live_section.support_count,
                historical_sample_size=(hypothesis.historical_sample_size if hypothesis is not None else bundle.min_history_points),
                expected_edge_bps=_quantize(expected_edge_bps, BPS_QUANTUM),
                effective_edge_bps=_quantize(expected_edge_bps - cost_model.transaction_cost_bps - cost_model.slippage_bps, BPS_QUANTUM),
                confidence=_clamp_probability(confidence),
                thesis=(hypothesis.thesis if hypothesis is not None else f"Glue-preserving {live_section.symbol} section under deterministic regime descent."),
                cost_model=cost_model,
                data_signature=signature,
            )
        )
    return tuple(sections)


def _build_invariants(
    risk_invariants: RiskInvariantSpecification,
    sections: Sequence[SchemaChartSection],
    *,
    min_support_count: int,
    min_effective_edge_bps: Decimal,
) -> tuple[SchemaInvariant, ...]:
    invariants = [
        SchemaInvariant("max_position_fraction", risk_invariants.max_position_fraction, Decimal("0.0000001"), ONE, risk_invariants.proof_obligation),
        SchemaInvariant("max_leverage", risk_invariants.max_leverage, ONE, None, risk_invariants.proof_obligation),
        SchemaInvariant("max_drawdown_fraction", risk_invariants.max_drawdown_fraction, Decimal("0.0000001"), Decimal("0.9999999"), risk_invariants.proof_obligation),
        SchemaInvariant("kill_switch_drawdown_fraction", risk_invariants.kill_switch_drawdown_fraction, risk_invariants.max_drawdown_fraction, Decimal("0.9999999"), risk_invariants.proof_obligation),
    ]
    for section in sections:
        position_fraction = _candidate_position_fraction(section, risk_invariants)
        candidate_leverage = _candidate_leverage(section, risk_invariants)
        stop_drawdown_fraction = _quantize(_stop_loss_bps(section) / Decimal("10000"), FEATURE_QUANTUM)
        latency_budget_ms = Decimal(risk_invariants.reject_on_stale_data_seconds * 1000)
        invariants.append(
            SchemaInvariant(
                f"support_count::{section.symbol}",
                Decimal(section.support_count),
                Decimal(min_support_count),
                None,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"effective_edge_bps::{section.symbol}",
                section.effective_edge_bps,
                min_effective_edge_bps,
                None,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"gluing_score::{section.symbol}",
                section.gluing_score,
                Decimal("0.5000000"),
                ONE,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"exposure_fraction::{section.symbol}",
                position_fraction,
                ZERO,
                risk_invariants.max_position_fraction,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"candidate_leverage::{section.symbol}",
                candidate_leverage,
                ONE,
                risk_invariants.max_leverage,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"stop_drawdown_fraction::{section.symbol}",
                stop_drawdown_fraction,
                ZERO,
                risk_invariants.max_drawdown_fraction,
                risk_invariants.proof_obligation,
            )
        )
        invariants.append(
            SchemaInvariant(
                f"latency_budget_ms::{section.symbol}",
                Decimal(section.cost_model.latency_ms),
                ZERO,
                latency_budget_ms,
                risk_invariants.proof_obligation,
            )
        )
    return tuple(invariants)


def _candidate_position_fraction(
    section: SchemaChartSection,
    risk_invariants: RiskInvariantSpecification,
) -> Decimal:
    signal_strength = _clamp_probability((section.confidence + section.gluing_score) / Decimal("2"))
    raw_fraction = risk_invariants.max_position_fraction * (
        Decimal("0.25") + (signal_strength / Decimal("2")) + (section.gluing_score / Decimal("4"))
    )
    return _clamp_probability(_quantize(min(raw_fraction, risk_invariants.max_position_fraction), FEATURE_QUANTUM))


def _candidate_leverage(
    section: SchemaChartSection,
    risk_invariants: RiskInvariantSpecification,
) -> Decimal:
    leverage_headroom = max(risk_invariants.max_leverage - ONE, ZERO)
    utilization = _clamp_probability((section.confidence + section.gluing_score) / Decimal("2"))
    return _quantize(min(ONE + (leverage_headroom * utilization), risk_invariants.max_leverage), FEATURE_QUANTUM)


def _stop_loss_bps(section: SchemaChartSection) -> Decimal:
    raw_stop = (
        section.cost_model.transaction_cost_bps
        + (section.cost_model.slippage_bps * Decimal("2"))
        + Decimal("5.0000")
    )
    return _quantize(max(raw_stop, Decimal("5.0000")), BPS_QUANTUM)


def _order_safety_coverage(risk_invariants: RiskInvariantSpecification) -> Decimal:
    required = risk_invariants.order_rejection_conditions
    if not required:
        return ZERO
    covered = tuple(condition for condition in required if condition.startswith("reject_"))
    return _clamp_probability(_quantize(Decimal(len(covered)) / Decimal(len(required)), FEATURE_QUANTUM))


def _invariants_match_chart(chart: MarketDataSchemaChart) -> bool:
    actuals = {invariant.name: invariant.actual for invariant in chart.invariants}
    risk = chart.base_bundle.risk_invariants
    if actuals.get("max_position_fraction") != risk.max_position_fraction:
        return False
    if actuals.get("max_leverage") != risk.max_leverage:
        return False
    if actuals.get("max_drawdown_fraction") != risk.max_drawdown_fraction:
        return False
    if actuals.get("kill_switch_drawdown_fraction") != risk.kill_switch_drawdown_fraction:
        return False
    return all(
        actuals.get(f"support_count::{section.symbol}") == Decimal(section.support_count)
        and actuals.get(f"effective_edge_bps::{section.symbol}") == section.effective_edge_bps
        and actuals.get(f"gluing_score::{section.symbol}") == section.gluing_score
        and actuals.get(f"exposure_fraction::{section.symbol}") == _candidate_position_fraction(section, risk)
        and actuals.get(f"candidate_leverage::{section.symbol}") == _candidate_leverage(section, risk)
        and actuals.get(f"stop_drawdown_fraction::{section.symbol}") == _quantize(_stop_loss_bps(section) / Decimal("10000"), FEATURE_QUANTUM)
        and actuals.get(f"latency_budget_ms::{section.symbol}") == Decimal(section.cost_model.latency_ms)
        for section in chart.sections
    )


def _build_novelty_packet(sections: Sequence[SchemaChartSection]) -> NoveltyPacket:
    gluing_score = ZERO if not sections else _clamp_probability(sum((section.gluing_score for section in sections), start=ZERO) / Decimal(len(sections)))
    return NoveltyPacket(
        headline="ext_machine_learning_16concepts",
        ag_view="View historical and live regimes as charts in a market cover; only admit signals whose local sections glue across overlaps into a coherent thesis.",
        typed_view="Encode research hypotheses as dependent strategy sections and permit only risk-certified inhabitants to descend into order intents.",
        proof_target="Prove the sizing, limits, and execution core preserves leverage, drawdown, and exposure invariants under composition.",
        cocycle_tension=_quantize(ONE - gluing_score, FEATURE_QUANTUM),
        overlap_count=sum(max(section.support_count - 1, 0) for section in sections),
        gluing_score=gluing_score,
    )


def _build_proof_certificate(
    bundle: MarketDataBundle,
    market_validation: Any,
    invariants: Sequence[SchemaInvariant],
) -> ProofCertification:
    obligations_checked = tuple(sorted(invariant.name for invariant in invariants))
    obligations_satisfied = tuple(sorted(invariant.name for invariant in invariants if invariant.satisfied))
    if not obligations_checked:
        coverage_fraction = ZERO
    else:
        coverage_fraction = _clamp_probability(
            _quantize(Decimal(len(obligations_satisfied)) / Decimal(len(obligations_checked)), FEATURE_QUANTUM)
        )
    paper_ready = bool(
        market_validation.passes
        and coverage_fraction == ONE
        and bundle.risk_invariants.order_rejection_conditions
    )
    live_ready = bool(
        paper_ready
        and bundle.risk_invariants.proof_obligation == "machine_checked"
        and not bundle.risk_invariants.paper_trading_required
    )
    rationale = (
        f"checked={len(obligations_checked)}",
        f"satisfied={len(obligations_satisfied)}",
        f"proof_mode={bundle.risk_invariants.proof_obligation}",
        f"paper_only={bundle.risk_invariants.paper_trading_required}",
    )
    return ProofCertification(
        proof_mode=bundle.risk_invariants.proof_obligation,
        obligations_checked=obligations_checked,
        obligations_satisfied=obligations_satisfied,
        coverage_fraction=coverage_fraction,
        paper_ready=paper_ready,
        live_ready=live_ready,
        rationale=rationale,
    )


def _derive_certified_intents(
    bundle: MarketDataBundle,
    sections: Sequence[SchemaChartSection],
    proof_certificate: ProofCertification,
) -> tuple[RiskCertifiedIntent, ...]:
    hypotheses = {hypothesis.symbol: hypothesis for hypothesis in bundle.hypotheses}
    live_sections = {live_section.symbol: live_section for live_section in bundle.live_sections}
    order_safety_coverage = _order_safety_coverage(bundle.risk_invariants)
    intents: list[RiskCertifiedIntent] = []
    for section in sections:
        hypothesis = hypotheses.get(section.symbol)
        live_section = live_sections.get(section.symbol)
        direction = (
            hypothesis.direction
            if hypothesis is not None
            else ("long" if live_section is None or live_section.topology.harmonic_advantage >= ZERO else "short")
        )
        reference_price = hypothesis.entry_reference_price if hypothesis is not None else (
            live_section.mid if live_section is not None else Decimal("1")
        )
        approved_for_paper = bool(
            proof_certificate.paper_ready
            and section.support_count >= 2
            and section.effective_edge_bps > ZERO
            and section.gluing_score >= Decimal("0.5000000")
        )
        approved_for_live = bool(
            approved_for_paper
            and proof_certificate.live_ready
            and section.cost_model.latency_ms <= bundle.risk_invariants.reject_on_stale_data_seconds * 1000
        )
        audit_token = _stable_digest([
            section.symbol,
            section.timestamp.isoformat(),
            direction,
            str(reference_price),
            proof_certificate.reproducibility_signature(),
        ])
        intents.append(
            RiskCertifiedIntent(
                symbol=section.symbol,
                timestamp=section.timestamp,
                regime=section.regime,
                thesis=section.thesis,
                direction=direction,
                reference_price=_quantize(reference_price, FEATURE_QUANTUM),
                target_edge_bps=section.effective_edge_bps,
                stop_loss_bps=_stop_loss_bps(section),
                candidate_position_fraction=_candidate_position_fraction(section, bundle.risk_invariants),
                candidate_leverage=_candidate_leverage(section, bundle.risk_invariants),
                order_safety_coverage=order_safety_coverage,
                proof_mode=proof_certificate.proof_mode,
                approved_for_paper=approved_for_paper,
                approved_for_live=approved_for_live,
                audit_token=audit_token,
            )
        )
    return tuple(intents)


def _build_gates(
    bundle: MarketDataBundle,
    market_validation: Any,
    invariants: Sequence[SchemaInvariant],
    sections: Sequence[SchemaChartSection],
    proof_certificate: ProofCertification,
    intents: Sequence[RiskCertifiedIntent],
) -> tuple[PromotionGate, ...]:
    verification = PromotionGate(
        "verification",
        bool(market_validation.passes and all(invariant.satisfied for invariant in invariants) and proof_certificate.coverage_fraction == ONE),
        "base bundle validates and proof-covered invariants hold",
        (
            f"proof_obligation={bundle.risk_invariants.proof_obligation}",
            f"coverage={proof_certificate.coverage_fraction}",
        ),
    )
    simulation = PromotionGate(
        "simulation",
        all(section.effective_edge_bps > ZERO and section.cost_model.latency_ms <= 2000 for section in sections),
        "cost, slippage, and latency leave positive executable edge",
        tuple(f"{section.symbol}:edge={section.effective_edge_bps}:latency={section.cost_model.latency_ms}" for section in sections),
    )
    stress = PromotionGate(
        "stress",
        all(section.support_count >= 2 and section.gluing_score >= Decimal("0.5000000") for section in sections),
        "support depth and gluing strength meet stress thresholds",
        tuple(f"{section.symbol}:support={section.support_count}:glue={section.gluing_score}" for section in sections),
    )
    prerequisites = verification.passes and simulation.passes and stress.passes
    paper = PromotionGate(
        "paper_promotion",
        prerequisites and proof_certificate.paper_ready and all(intent.approved_for_paper for intent in intents),
        "paper trading opens only after proof coverage and certified intents both pass",
    )
    live = PromotionGate(
        "live_promotion",
        paper.passes and proof_certificate.live_ready and all(intent.approved_for_live for intent in intents),
        "live trading requires machine-checked proof mode, certified intents, and non-paper-only policy",
    )
    return (verification, simulation, stress, paper, live)


def _counterexamples(bundle: MarketDataBundle, validation: Any, invariants: Sequence[SchemaInvariant], gates: Sequence[PromotionGate]) -> tuple[CounterexampleWitness, ...]:
    examples = [CounterexampleWitness("base_market_validation", message, observed=market_data_summary(bundle), expected="validated bundle") for message in validation.messages]
    examples.extend(
        CounterexampleWitness(invariant.name, "machine-checkable invariant failed", observed=str(invariant.actual), expected=f">= {invariant.lower_bound}")
        for invariant in invariants
        if not invariant.satisfied
    )
    examples.extend(
        CounterexampleWitness(gate.name, gate.reason, observed=" | ".join(gate.evidence), expected="gate passes")
        for gate in gates
        if not gate.passes
    )
    return tuple(examples)


def _lineage(bundle: MarketDataBundle, dependency_state: str, versions: Mapping[str, str]) -> tuple[TransformationStep, ...]:
    return (
        TransformationStep("normalize_market_data", versions.get("normalize_market_data", bundle.schema_version), "Canonicalize timestamps, symbols, and feeds."),
        TransformationStep("glue_market_sections", versions.get("glue_market_sections", "market_data.glue.v1"), "Discharge overlap obligations.", (("h1_tolerance", str(bundle.h1_tolerance)),)),
        TransformationStep("discover_novel_hypotheses", versions.get("discover_novel_hypotheses", "market_data.hypothesis.v1"), "Generate at least one deterministic market idea.", (("min_history_points", str(bundle.min_history_points)),)),
        TransformationStep("schema_chart_projection", versions.get("schema_chart_projection", SCHEMA_CHART_VERSION), "Project data into auditable sections and gates.", (("dependency_state", dependency_state),)),
    )


def _schema_chart_signature(chart: MarketDataSchemaChart) -> str:
    parts = [chart.schema_version, chart.base_bundle.data_signature, chart.dependency_state]
    parts.extend(step.reproducibility_signature() for step in chart.lineage)
    parts.extend(section.reproducibility_signature() for section in chart.sections)
    parts.extend(invariant.reproducibility_signature() for invariant in chart.invariants)
    parts.append(_stable_digest([
        chart.novelty_packet.headline,
        chart.novelty_packet.ag_view,
        chart.novelty_packet.typed_view,
        chart.novelty_packet.proof_target,
        str(chart.novelty_packet.cocycle_tension),
        str(chart.novelty_packet.overlap_count),
        str(chart.novelty_packet.gluing_score),
    ]))
    parts.append(chart.proof_certificate.reproducibility_signature())
    parts.extend(intent.reproducibility_signature() for intent in chart.certified_intents)
    parts.extend(gate.reproducibility_signature() for gate in chart.gates)
    parts.extend(counterexample.reproducibility_signature() for counterexample in chart.counterexamples)
    parts.extend(f"{k}={v}" for k, v in chart.audit_metadata)
    return _stable_digest(parts)


# @require("chart descends from build_market_data and retains explicit proof and risk surfaces")
# @ensure("report states whether preconditions, proof coverage, invariants, and intent descent remain valid")
def validate_schema_chart(chart: MarketDataSchemaChart) -> SchemaChartValidationReport:
    """Validate that a schema chart remains traceable, bounded, and closed to live risk."""
    market_validation = validate_market_data(chart.base_bundle)
    preconditions = precondition_holds(chart.base_bundle.historical_observations, chart.base_bundle.live_observations, min_value=chart.base_bundle.min_history_points)
    minimum_bounds_hold = all(invariant.satisfied for invariant in chart.invariants) and _invariants_match_chart(chart)
    expected_proof_certificate = _build_proof_certificate(chart.base_bundle, market_validation, chart.invariants)
    proof_surface_matches = chart.proof_certificate == expected_proof_certificate
    intent_surface_matches = chart.certified_intents == _derive_certified_intents(chart.base_bundle, chart.sections, expected_proof_certificate)
    signature_matches = chart.data_signature == _schema_chart_signature(chart)
    lineage_traceable = bool(chart.lineage) and all(step.version and step.reproducibility_signature() for step in chart.lineage)
    dependency_resolved = chart.dependency_state != "required_missing"
    gate_map = {gate.name: gate for gate in chart.gates}
    prerequisites = all(gate_map[name].passes for name in ("verification", "simulation", "stress"))
    expected_paper = prerequisites and expected_proof_certificate.paper_ready and all(intent.approved_for_paper for intent in chart.certified_intents)
    expected_live = expected_paper and expected_proof_certificate.live_ready and all(intent.approved_for_live for intent in chart.certified_intents)
    gates_closed_to_live = (
        gate_map["paper_promotion"].passes == expected_paper
        and gate_map["live_promotion"].passes == expected_live
    )
    messages = list(market_validation.messages)
    if not preconditions:
        messages.append("raw-entry preconditions do not hold")
    if not minimum_bounds_hold:
        messages.append("one or more minimum-bound invariants failed")
    if not proof_surface_matches:
        messages.append("proof certification surface no longer matches chart invariants")
    if not intent_surface_matches:
        messages.append("risk-certified intent surface no longer matches chart sections")
    if not lineage_traceable:
        messages.append("transformation lineage is incomplete")
    if not dependency_resolved:
        messages.append("required regime atlas dependency is unavailable")
    if not gates_closed_to_live:
        messages.append("promotion gates permit downstream descent too early")
    if not signature_matches:
        messages.append("schema chart signature mismatch")
    if chart.dependency_state.startswith("optional_missing"):
        messages.append("regime atlas dependency unavailable; deterministic local regime inference used")
    counterexamples = list(_counterexamples(chart.base_bundle, market_validation, chart.invariants, chart.gates))
    if not preconditions:
        counterexamples.append(CounterexampleWitness("precondition_holds", "raw-entry preconditions do not hold", observed=f"historical={len(chart.base_bundle.historical_observations)} live={len(chart.base_bundle.live_observations)}", expected=f"historical>={chart.base_bundle.min_history_points} and live>0"))
    if not proof_surface_matches:
        counterexamples.append(
            CounterexampleWitness(
                "proof_certificate",
                "proof certification surface no longer matches chart invariants",
                observed=chart.proof_certificate.reproducibility_signature(),
                expected=expected_proof_certificate.reproducibility_signature(),
            )
        )
    if not intent_surface_matches:
        expected_intents = _derive_certified_intents(chart.base_bundle, chart.sections, expected_proof_certificate)
        counterexamples.append(
            CounterexampleWitness(
                "risk_certified_intents",
                "risk-certified intent surface no longer matches chart sections",
                observed=_stable_digest([intent.reproducibility_signature() for intent in chart.certified_intents]),
                expected=_stable_digest([intent.reproducibility_signature() for intent in expected_intents]),
            )
        )
    if not signature_matches:
        counterexamples.append(CounterexampleWitness("schema_chart_signature", "schema chart signature mismatch", observed=chart.data_signature, expected=_schema_chart_signature(chart)))
    return SchemaChartValidationReport(
        passes=all((
            market_validation.passes,
            preconditions,
            minimum_bounds_hold,
            proof_surface_matches,
            intent_surface_matches,
            lineage_traceable,
            dependency_resolved,
            gates_closed_to_live,
            signature_matches,
        )),
        preconditions_hold=preconditions,
        minimum_bounds_hold=minimum_bounds_hold,
        lineage_traceable=lineage_traceable,
        dependency_resolved=dependency_resolved,
        gates_closed_to_live=gates_closed_to_live,
        signature_matches=signature_matches,
        messages=tuple(messages),
        counterexamples=tuple(counterexamples),
    )


# @require("chart is a deterministic schema chart built from versioned market data")
# @ensure("summary text remains reproducible and references proof and signature state")
def schema_chart_summary(chart: MarketDataSchemaChart) -> str:
    report = validate_schema_chart(chart)
    section_text = ",".join(f"{section.symbol}:{section.regime}:{section.effective_edge_bps}" for section in chart.sections[:3]) or "none"
    proof_text = (
        f"{chart.proof_certificate.proof_mode}:{chart.proof_certificate.coverage_fraction}"
    )
    return (
        f"market_schema_chart[{chart.schema_version}] symbols={','.join(chart.symbols)} "
        f"sections={len(chart.sections)} invariants={len(chart.invariants)} "
        f"intents={len(chart.certified_intents)} gates={len(chart.gates)} "
        f"validation={'pass' if report.passes else 'fail'} "
        f"proof={proof_text} "
        f"dependency={chart.dependency_state} signature={chart.data_signature[:12]} sections_view={section_text}"
    )


# @require("historical support predates live support and gluing obligations can be evaluated deterministically")
# @ensure("returned chart is auditable, proof-covered, and only exposes risk-certified intent descent")
def design_and(
    historical_entries: Iterable[Mapping[str, Any]],
    live_entries: Iterable[Mapping[str, Any]],
    *,
    local_entries: Iterable[Mapping[str, Any]] = (),
    regime_snapshot: Any | None = None,
    require_regime_dependency: bool = False,
    transformation_versions: Mapping[str, str] | None = None,
    min_history_points: int = 12,
    min_support_count: int = 2,
    min_effective_edge_bps: Decimal | str = Decimal("1.0000"),
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
    risk_invariants: RiskInvariantSpecification | None = None,
) -> MarketDataSchemaChart:
    """Build a deterministic schema chart on top of the normalized market-data bundle."""
    historical_materialized = tuple(dict(entry) for entry in historical_entries)
    live_materialized = tuple(dict(entry) for entry in live_entries)
    local_materialized = tuple(dict(entry) for entry in local_entries)
    if not precondition_holds(historical_materialized, live_materialized, min_value=min_history_points):
        raise SchemaChartValidationError("precondition_holds failed: historical support or live support is insufficient.")
    if not x_at_least_min_value(min_support_count, 1):
        raise SchemaChartValidationError("min_support_count must be at least one.")
    effective_edge_floor = _coerce_decimal(min_effective_edge_bps, "min_effective_edge_bps", quantum=BPS_QUANTUM)
    regimes, dependency_state = _resolve_regimes(
        historical_materialized,
        live_materialized,
        local_materialized,
        regime_snapshot,
        require_regime_dependency,
        min_history_points,
    )
    bundle = build_market_data(
        historical_materialized,
        live_materialized,
        local_entries=local_materialized,
        min_history_points=min_history_points,
        price_tolerance=price_tolerance,
        spread_tolerance=spread_tolerance,
        h1_tolerance=h1_tolerance,
        risk_invariants=risk_invariants,
    )
    validation = validate_market_data(bundle)
    sections = _derive_sections(bundle, regimes)
    invariants = _build_invariants(bundle.risk_invariants, sections, min_support_count=min_support_count, min_effective_edge_bps=effective_edge_floor)
    novelty_packet = _build_novelty_packet(sections)
    proof_certificate = _build_proof_certificate(bundle, validation, invariants)
    certified_intents = _derive_certified_intents(bundle, sections, proof_certificate)
    gates = _build_gates(bundle, validation, invariants, sections, proof_certificate, certified_intents)
    lineage = _lineage(bundle, dependency_state, transformation_versions or {})
    audit_metadata = tuple(sorted((
        ("base_summary", market_data_summary(bundle)),
        ("dependency_state", dependency_state),
        ("novelty_headline", novelty_packet.headline),
        ("proof_coverage", str(proof_certificate.coverage_fraction)),
        ("proof_mode", proof_certificate.proof_mode),
        ("proof_obligation", bundle.risk_invariants.proof_obligation),
        ("schema_version", SCHEMA_CHART_VERSION),
        ("intent_count", str(len(certified_intents))),
        ("transformation_count", str(len(lineage))),
    )))
    provisional = MarketDataSchemaChart(
        schema_version=SCHEMA_CHART_VERSION,
        base_bundle=bundle,
        lineage=lineage,
        sections=sections,
        invariants=invariants,
        novelty_packet=novelty_packet,
        proof_certificate=proof_certificate,
        certified_intents=certified_intents,
        gates=gates,
        dependency_state=dependency_state,
        counterexamples=_counterexamples(bundle, validation, invariants, gates),
        audit_metadata=audit_metadata,
        data_signature="pending",
    )
    return MarketDataSchemaChart(
        schema_version=provisional.schema_version,
        base_bundle=provisional.base_bundle,
        lineage=provisional.lineage,
        sections=provisional.sections,
        invariants=provisional.invariants,
        novelty_packet=provisional.novelty_packet,
        proof_certificate=provisional.proof_certificate,
        certified_intents=provisional.certified_intents,
        gates=provisional.gates,
        dependency_state=provisional.dependency_state,
        counterexamples=provisional.counterexamples,
        audit_metadata=provisional.audit_metadata,
        data_signature=_schema_chart_signature(provisional),
    )


# @require("same preconditions as design_and")
# @ensure("result matches design_and for the same versioned market inputs")
def research_to_production_trading(
    historical_entries: Iterable[Mapping[str, Any]],
    live_entries: Iterable[Mapping[str, Any]],
    *,
    local_entries: Iterable[Mapping[str, Any]] = (),
    regime_snapshot: Any | None = None,
    require_regime_dependency: bool = False,
    transformation_versions: Mapping[str, str] | None = None,
    min_history_points: int = 12,
    min_support_count: int = 2,
    min_effective_edge_bps: Decimal | str = Decimal("1.0000"),
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
    risk_invariants: RiskInvariantSpecification | None = None,
) -> MarketDataSchemaChart:
    return design_and(
        historical_entries,
        live_entries,
        local_entries=local_entries,
        regime_snapshot=regime_snapshot,
        require_regime_dependency=require_regime_dependency,
        transformation_versions=transformation_versions,
        min_history_points=min_history_points,
        min_support_count=min_support_count,
        min_effective_edge_bps=min_effective_edge_bps,
        price_tolerance=price_tolerance,
        spread_tolerance=spread_tolerance,
        h1_tolerance=h1_tolerance,
        risk_invariants=risk_invariants,
    )


__all__ = [
    "CostModelAssumption",
    "CounterexampleWitness",
    "MarketDataSchemaChart",
    "NoveltyPacket",
    "ProofCertification",
    "PromotionGate",
    "RiskCertifiedIntent",
    "SchemaChartDependencyError",
    "SchemaChartError",
    "SchemaChartSection",
    "SchemaChartValidationError",
    "SchemaChartValidationReport",
    "SchemaInvariant",
    "TransformationStep",
    "design_and",
    "precondition_holds",
    "research_to_production_trading",
    "schema_chart_summary",
    "validate_schema_chart",
    "x_at_least_min_value",
]
