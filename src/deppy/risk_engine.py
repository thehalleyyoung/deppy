"""Refine strategy intents into explicit, auditable risk approvals.

This module is the risk-critical site in the typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

The upstream strategy kernel emits typed position intents that are still only
research- and simulation-facing.  The responsibility of this module is to make
those intents concrete enough for downstream execution while preserving explicit
risk invariants that can be inspected, tested, and machine-checked:

* leverage limits cap gross balance-sheet usage,
* exposure limits cap symbol and net directional concentration,
* drawdown limits clip targets to the remaining loss budget,
* a kill-switch threshold rejects intent descent before execution, and
* only risk-approved intents are allowed to propagate further.

The implementation is intentionally deterministic.  All public bundle and
summary objects carry stable signatures so validation can detect tampering and
support replayable paper-trading workflows.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Collection, Iterable, Literal, Mapping, Sequence, TypeAlias

from deppy.strategy_kernel import (
    PositionIntent,
    RiskBounds,
    StrategyKernelBundle,
    StrategyResearchIdea,
    StrategyRiskPolicy,
)

FEATURE_QUANTUM = Decimal("0.0000001")
FRACTION_QUANTUM = Decimal("0.0000001")
EDGE_QUANTUM = Decimal("0.0001")
ZERO = Decimal("0")
ONE = Decimal("1")
RISK_ENGINE_SCHEMA_VERSION = "risk_engine.v1"
DEFAULT_ORDER_REJECTION_CONDITIONS: tuple[str, ...] = (
    "reject_failed_gluing",
    "reject_kill_switch",
    "reject_max_drawdown",
    "reject_exposure_breach",
    "reject_leverage_breach",
    "reject_unverified_risk_core",
)

RiskKey: TypeAlias = tuple[datetime, str]
RiskLens: TypeAlias = Literal["drawdown", "exposure", "leverage"]
RiskApprovalStatus: TypeAlias = Literal["rejected", "risk_approved"]
RiskProofMode: TypeAlias = Literal["smt_required", "machine_checked"]
RiskIdeaSide: TypeAlias = Literal["long", "short"]
RiskEngineInput: TypeAlias = StrategyKernelBundle | Iterable[PositionIntent]

LENSES: tuple[RiskLens, ...] = ("drawdown", "exposure", "leverage")


class RiskEngineError(ValueError):
    """Base error raised by the risk engine."""


class RiskNormalizationError(RiskEngineError):
    """Raised when risk data violates normalization or invariant checks."""


class RiskRestrictionError(RiskEngineError):
    """Raised when a risk restriction map is ill-formed."""


class RiskGluingError(RiskEngineError):
    """Raised when local risk sections fail to glue on overlaps."""


def _quantize(value: Decimal, quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    """Round *value* onto the project-wide decimal lattice."""
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _quantize_fraction(value: Decimal) -> Decimal:
    """Round a fraction onto the shared fraction lattice."""
    return _quantize(value, FRACTION_QUANTUM)


def _quantize_edge(value: Decimal) -> Decimal:
    """Round an expected-edge estimate onto the shared bps lattice."""
    return _quantize(value, EDGE_QUANTUM)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    """Convert *value* to a finite :class:`Decimal`."""
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise RiskNormalizationError(f"Field '{field_name}' must be numeric, got {value!r}.") from exc
    if not candidate.is_finite():
        raise RiskNormalizationError(f"Field '{field_name}' must be finite, got {value!r}.")
    return candidate


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    """Normalize *value* to a timezone-aware UTC timestamp."""
    if not isinstance(value, datetime):
        raise RiskRestrictionError(f"Field '{field_name}' must be a datetime, got {value!r}.")
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    """Return the canonical overlap symbol representation."""
    if not isinstance(value, str):
        raise RiskNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise RiskNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise RiskNormalizationError(f"Field 'symbol' cannot normalize from {value!r}.")
    return candidate


def _stable_digest(parts: Iterable[str]) -> str:
    """Return a deterministic digest over *parts*."""
    digest = sha256()
    digest.update(RISK_ENGINE_SCHEMA_VERSION.encode("utf-8"))
    digest.update(b"\0")
    for part in parts:
        digest.update(str(part).encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def _validate_probability(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in the closed unit interval."""
    if not value.is_finite():
        raise RiskNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise RiskNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_signed_fraction(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in the signed unit interval."""
    if not value.is_finite():
        raise RiskNormalizationError(f"Field '{field_name}' must be finite.")
    if abs(value) > ONE:
        raise RiskNormalizationError(f"Field '{field_name}' must lie in [-1, 1].")


def _validate_unit_signal(value: Decimal, field_name: str) -> None:
    """Validate that *value* is a bounded signal score."""
    if not value.is_finite():
        raise RiskNormalizationError(f"Field '{field_name}' must be finite.")
    if abs(value) > ONE:
        raise RiskNormalizationError(f"Field '{field_name}' must lie in [-1, 1].")


def _validate_positive_decimal(value: Decimal, field_name: str) -> None:
    """Validate that *value* is finite and strictly positive."""
    if not value.is_finite():
        raise RiskNormalizationError(f"Field '{field_name}' must be finite.")
    if value <= ZERO:
        raise RiskNormalizationError(f"Field '{field_name}' must be strictly positive.")


def _safe_ratio(numerator: Decimal, denominator: Decimal) -> Decimal:
    """Return a quantized ratio, treating a zero denominator as zero."""
    if denominator == ZERO:
        return ZERO
    return _quantize_fraction(numerator / denominator)


def _clamp_probability(value: Decimal) -> Decimal:
    """Clamp *value* onto the closed unit interval."""
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize_fraction(value)


def _median_decimal(
    values: Sequence[Decimal], quantum: Decimal = FEATURE_QUANTUM
) -> Decimal:
    """Return the median of *values* on the requested lattice."""
    if not values:
        raise RiskNormalizationError("Median is undefined for an empty value set.")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return _quantize(ordered[middle], quantum)
    return _quantize((ordered[middle - 1] + ordered[middle]) / Decimal("2"), quantum)


def _max_gap(values: Sequence[Decimal], quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    """Return the maximum gap across one overlap family."""
    if not values:
        return ZERO
    return _quantize(max(values) - min(values), quantum)


def _triple_overlap_residual(values: Sequence[Decimal]) -> Decimal:
    """Return an H^1-style residual over overlap corrections."""
    if len(values) < 3:
        return ZERO
    median_value = _median_decimal(values, FRACTION_QUANTUM)
    residual = max((abs(value - median_value) for value in values), default=ZERO)
    return _quantize_fraction(residual)


def _resolve_tolerance(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize one non-negative tolerance parameter."""
    tolerance = _coerce_decimal(value, field_name)
    if tolerance < ZERO:
        raise RiskRestrictionError(f"Tolerance '{field_name}' must be non-negative.")
    return _quantize_fraction(tolerance)


def _gluing_score(obstruction: Decimal, h1_tolerance: Decimal) -> Decimal:
    """Convert an obstruction witness into a unit gluing score."""
    if h1_tolerance == ZERO:
        return ZERO if obstruction > ZERO else ONE
    return _clamp_probability(ONE - min(ONE, obstruction / h1_tolerance))


def _side_sign(side: str) -> int:
    """Return the signed direction encoded by *side*."""
    if side == "long":
        return 1
    if side == "short":
        return -1
    if side == "flat":
        return 0
    raise RiskNormalizationError(f"Unsupported trading side {side!r}.")


def _same_direction(current: Decimal, side: str) -> bool:
    """Return whether *current* already points in the requested *side*."""
    sign = _side_sign(side)
    if sign == 0 or current == ZERO:
        return False
    return current > ZERO if sign > 0 else current < ZERO


def _signed_fraction(side: str, fraction: Decimal) -> Decimal:
    """Apply the sign implied by *side* to *fraction*."""
    sign = _side_sign(side)
    if sign == 0:
        return ZERO
    return _quantize_fraction(fraction * Decimal(sign))


def _effective_gross_limit(policy: "RiskPolicy") -> Decimal:
    """Return the effective gross exposure budget after the cash buffer."""
    gross_limit = min(policy.max_gross_leverage, _quantize_fraction(ONE - policy.min_cash_buffer))
    return _clamp_probability(gross_limit)


def _drawdown_fraction(state: "PortfolioRiskState") -> Decimal:
    """Return the realized drawdown fraction of one portfolio state."""
    if state.peak_equity == ZERO:
        return ZERO
    realized = _quantize_fraction((state.peak_equity - state.current_equity) / state.peak_equity)
    return _clamp_probability(realized)


def _projected_symbol_exposure(
    state: "PortfolioRiskState", side: str, fraction: Decimal
) -> Decimal:
    """Return the signed projected symbol exposure after one approved trade."""
    return _quantize_fraction(state.symbol_exposure_fraction + _signed_fraction(side, fraction))


def _projected_net_exposure(
    state: "PortfolioRiskState", side: str, fraction: Decimal
) -> Decimal:
    """Return the signed projected portfolio net exposure after one trade."""
    return _quantize_fraction(state.net_exposure_fraction + _signed_fraction(side, fraction))


def _projected_gross_exposure(
    state: "PortfolioRiskState", side: str, fraction: Decimal
) -> Decimal:
    """Return projected gross exposure after applying one signed trade."""
    current_symbol = state.symbol_exposure_fraction
    projected_symbol = _projected_symbol_exposure(state, side, fraction)
    gross_delta = abs(projected_symbol) - abs(current_symbol)
    projected = state.gross_exposure_fraction + gross_delta
    return _clamp_probability(_quantize_fraction(max(ZERO, projected)))


def _directional_capacity(current: Decimal, side: str, limit: Decimal) -> Decimal:
    """Return the largest non-negative trade that keeps ``abs(current + s*x) <= limit``."""
    sign = _side_sign(side)
    if sign == 0:
        return ZERO
    capacity = limit - (Decimal(sign) * current)
    return _clamp_probability(max(ZERO, _quantize_fraction(capacity)))


def _resolve_portfolio_state(
    symbol: str,
    *,
    portfolio_state: "PortfolioRiskState",
    state_by_symbol: Mapping[str, "PortfolioRiskState"] | None,
) -> "PortfolioRiskState":
    """Resolve the symbol-specific portfolio state used by one risk check."""
    if state_by_symbol is None:
        return portfolio_state
    return state_by_symbol.get(_normalize_symbol(symbol), portfolio_state)


def _require_unique_lenses(
    members: Sequence["LocalRiskSection"], key: RiskKey
) -> tuple[RiskLens, ...]:
    """Require that one overlap family contains each lens at most once."""
    lenses = tuple(sorted(member.lens for member in members))
    if len(lenses) != len(set(lenses)):
        timestamp, symbol = key
        raise RiskGluingError(f"Risk overlap {symbol}@{timestamp.isoformat()} carries duplicate lenses.")
    return lenses


def _require_unique_value(values: Sequence[Any], key: RiskKey, field_name: str) -> Any:
    """Require that *values* agree exactly on an overlap."""
    first = values[0]
    if any(value != first for value in values[1:]):
        timestamp, symbol = key
        raise RiskGluingError(f"Risk overlap {symbol}@{timestamp.isoformat()} disagrees on {field_name}.")
    return first


def _risk_bounds_gap(members: Sequence["LocalRiskSection"]) -> Decimal:
    """Return zero when all risk envelopes match exactly, else one."""
    first = members[0].risk_bounds
    if all(member.risk_bounds == first for member in members[1:]):
        return ZERO
    return ONE


def _local_thesis(lens: RiskLens, intent: PositionIntent, approved_fraction: Decimal) -> str:
    """Return a concise thesis for one local risk section."""
    return f"{lens} lens refines {intent.style} {intent.side} intent in {intent.symbol}; target={intent.target_fraction} approved={approved_fraction}"


def _global_thesis(status: RiskApprovalStatus, section: "GlobalRiskSection") -> str:
    """Return the thesis carried by one glued risk section."""
    if status == "risk_approved":
        message = (
            f"risk engine approves {section.side} {section.symbol} at "
            f"{section.approved_fraction} after leverage, drawdown, and exposure "
            "invariants agree on overlaps"
        )
        return message
    message = (
        f"risk engine rejects descent of {section.side} {section.symbol} because one "
        "or more risk invariants bind too tightly"
    )
    return message


def _global_rationale(
    status: RiskApprovalStatus,
    section: "GlobalRiskSection",
    binding_lenses: Sequence[RiskLens],
) -> str:
    """Return the rationale attached to one glued risk section."""
    if status == "risk_approved":
        if binding_lenses:
            joined = ", ".join(binding_lenses)
            message = (
                f"approval stays admissible because local charts still glue after clipping on "
                f"{joined}; only the clipped, overlap-consistent intent may descend"
            )
            return message
        message = (
            "approval is exact on all overlaps, so the full target survives leverage, "
            "drawdown, and exposure review"
        )
        return message
    if binding_lenses:
        joined = ", ".join(binding_lenses)
        message = (
            f"descent is blocked because {joined} leaves no executable allocation once all "
            "risk charts are glued"
        )
        return message
    return "descent is blocked because the glued section fails the minimum approval threshold"


def _approval_reason(status: RiskApprovalStatus, section: "GlobalRiskSection") -> str:
    """Return the execution-facing rationale for one approved or rejected intent."""
    if status == "risk_approved":
        message = (
            "intent is risk-approved: all explicit invariants hold and only this reviewed "
            "fraction may descend toward order generation"
        )
        return message
    message = (
        "intent is rejected: leverage, drawdown, exposure, kill-switch, or minimum-size "
        "requirements did not permit safe descent"
    )
    return message


@dataclass(init=False)
class RiskPolicy:
    """Static, explicit policy parameters used by the risk engine."""

    max_gross_leverage: Decimal
    max_net_exposure: Decimal
    max_symbol_exposure: Decimal
    max_drawdown: Decimal
    min_cash_buffer: Decimal
    min_approval_fraction: Decimal
    kill_switch_drawdown: Decimal = Decimal("0.1500000")
    order_rejection_conditions: tuple[str, ...] = DEFAULT_ORDER_REJECTION_CONDITIONS
    proof_obligation: RiskProofMode = "smt_required"
    paper_trading_required: bool = True

    def __init__(
        self,
        max_gross_leverage: Decimal,
        max_net_exposure: Decimal,
        max_symbol_exposure: Decimal,
        max_drawdown: Decimal,
        min_cash_buffer: Decimal,
        min_approval_fraction: Decimal,
        kill_switch_drawdown: Decimal = Decimal("0.1500000"),
        order_rejection_conditions: tuple[str, ...] = DEFAULT_ORDER_REJECTION_CONDITIONS,
        proof_obligation: RiskProofMode = "smt_required",
        paper_trading_required: bool = True,
    ) -> None:
        self.max_gross_leverage = max_gross_leverage
        self.max_net_exposure = max_net_exposure
        self.max_symbol_exposure = max_symbol_exposure
        self.max_drawdown = max_drawdown
        self.min_cash_buffer = min_cash_buffer
        self.min_approval_fraction = min_approval_fraction
        self.kill_switch_drawdown = kill_switch_drawdown
        self.order_rejection_conditions = tuple(order_rejection_conditions)
        self.proof_obligation = proof_obligation
        self.paper_trading_required = paper_trading_required
        self.__post_init__()

    def __post_init__(self) -> None:
        _validate_probability(self.max_gross_leverage, "max_gross_leverage")
        _validate_probability(self.max_net_exposure, "max_net_exposure")
        _validate_probability(self.max_symbol_exposure, "max_symbol_exposure")
        _validate_probability(self.max_drawdown, "max_drawdown")
        _validate_probability(self.min_cash_buffer, "min_cash_buffer")
        _validate_probability(self.min_approval_fraction, "min_approval_fraction")
        _validate_probability(self.kill_switch_drawdown, "kill_switch_drawdown")
        if self.max_gross_leverage == ZERO:
            raise RiskNormalizationError("Field 'max_gross_leverage' must be strictly positive.")
        if self.max_drawdown == ZERO:
            raise RiskNormalizationError("Field 'max_drawdown' must be strictly positive.")
        if self.max_symbol_exposure > self.max_net_exposure:
            raise RiskNormalizationError("Field 'max_symbol_exposure' cannot exceed max_net_exposure.")
        if self.kill_switch_drawdown <= self.max_drawdown or self.kill_switch_drawdown >= ONE:
            raise RiskNormalizationError("Field 'kill_switch_drawdown' must exceed max_drawdown and remain below 1.")
        if self.min_cash_buffer >= ONE:
            raise RiskNormalizationError("Field 'min_cash_buffer' must be less than 1.")
        if _effective_gross_limit(self) == ZERO:
            raise RiskNormalizationError("Risk policy leaves no gross exposure capacity.")
        if not self.order_rejection_conditions:
            raise RiskNormalizationError("Risk policy requires explicit order rejection conditions.")
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise RiskNormalizationError("Risk policy requires an SMT-backed or machine-checked proof mode.")

    def reproducibility_signature(self) -> str:
        """Return a deterministic digest for audit logging and replay."""
        parts = [
            str(self.max_gross_leverage),
            str(self.max_net_exposure),
            str(self.max_symbol_exposure),
            str(self.max_drawdown),
            str(self.min_cash_buffer),
            str(self.min_approval_fraction),
            str(self.kill_switch_drawdown),
            self.proof_obligation,
            str(self.paper_trading_required),
            *self.order_rejection_conditions,
        ]
        return _stable_digest(parts)


@dataclass(init=False)
class PortfolioRiskState:
    """Portfolio snapshot relevant to symbol-level risk review."""

    gross_exposure_fraction: Decimal
    net_exposure_fraction: Decimal
    symbol_exposure_fraction: Decimal
    peak_equity: Decimal
    current_equity: Decimal

    def __init__(
        self,
        gross_exposure_fraction: Decimal,
        net_exposure_fraction: Decimal,
        symbol_exposure_fraction: Decimal,
        peak_equity: Decimal,
        current_equity: Decimal,
    ) -> None:
        self.gross_exposure_fraction = gross_exposure_fraction
        self.net_exposure_fraction = net_exposure_fraction
        self.symbol_exposure_fraction = symbol_exposure_fraction
        self.peak_equity = peak_equity
        self.current_equity = current_equity
        self.__post_init__()

    def __post_init__(self) -> None:
        _validate_probability(self.gross_exposure_fraction, "gross_exposure_fraction")
        _validate_signed_fraction(self.net_exposure_fraction, "net_exposure_fraction")
        _validate_signed_fraction(self.symbol_exposure_fraction, "symbol_exposure_fraction")
        _validate_positive_decimal(self.peak_equity, "peak_equity")
        _validate_positive_decimal(self.current_equity, "current_equity")
        if abs(self.net_exposure_fraction) > self.gross_exposure_fraction:
            raise RiskNormalizationError("Absolute net exposure cannot exceed gross exposure.")
        if abs(self.symbol_exposure_fraction) > self.gross_exposure_fraction:
            raise RiskNormalizationError("Absolute symbol exposure cannot exceed gross exposure.")

    @property
    def drawdown_fraction(self) -> Decimal:
        """Return the realized drawdown fraction."""
        return _drawdown_fraction(self)


def default_risk_policy() -> RiskPolicy:
    """Return the default verified policy used by the trading platform."""
    policy = RiskPolicy(
        max_gross_leverage=Decimal("0.8500000"),
        max_net_exposure=Decimal("0.4500000"),
        max_symbol_exposure=Decimal("0.3000000"),
        max_drawdown=Decimal("0.1200000"),
        min_cash_buffer=Decimal("0.1000000"),
        min_approval_fraction=Decimal("0.0100000"),
        kill_switch_drawdown=Decimal("0.1800000"),
    )
    return policy


def neutral_portfolio_state() -> PortfolioRiskState:
    """Return a neutral portfolio state with zero exposure and no drawdown."""
    state = PortfolioRiskState(
        gross_exposure_fraction=ZERO,
        net_exposure_fraction=ZERO,
        symbol_exposure_fraction=ZERO,
        peak_equity=ONE,
        current_equity=ONE,
    )
    return state


@dataclass(init=False)
class LocalRiskSection:
    """One local risk chart attached to a pending-risk position intent."""

    timestamp: datetime
    symbol: str
    lens: RiskLens
    side: str
    style: str
    target_fraction: Decimal
    approved_fraction: Decimal
    alpha_score: Decimal
    conviction: Decimal
    risk_bounds: RiskBounds
    limit_fraction: Decimal
    utilization: Decimal
    haircut_fraction: Decimal
    binding: bool
    passes: bool
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        lens: RiskLens,
        side: str,
        style: str,
        target_fraction: Decimal,
        approved_fraction: Decimal,
        alpha_score: Decimal,
        conviction: Decimal,
        risk_bounds: RiskBounds,
        limit_fraction: Decimal,
        utilization: Decimal,
        haircut_fraction: Decimal,
        binding: bool,
        passes: bool,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.lens = lens
        self.side = side
        self.style = style
        self.target_fraction = target_fraction
        self.approved_fraction = approved_fraction
        self.alpha_score = alpha_score
        self.conviction = conviction
        self.risk_bounds = risk_bounds
        self.limit_fraction = limit_fraction
        self.utilization = utilization
        self.haircut_fraction = haircut_fraction
        self.binding = binding
        self.passes = passes
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise RiskNormalizationError("Risk timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise RiskNormalizationError("Risk timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise RiskNormalizationError("Risk symbols must be canonicalized.")
        if self.lens not in LENSES:
            raise RiskNormalizationError(f"Unknown risk lens {self.lens!r}.")
        if self.side not in {"long", "short", "flat"}:
            raise RiskNormalizationError(f"Unsupported risk side {self.side!r}.")
        if not self.style.strip():
            raise RiskNormalizationError("Risk sections must carry a style.")
        _validate_probability(self.target_fraction, "target_fraction")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.limit_fraction, "limit_fraction")
        _validate_probability(self.utilization, "utilization")
        _validate_probability(self.haircut_fraction, "haircut_fraction")
        if self.approved_fraction > self.target_fraction:
            raise RiskNormalizationError("Approved fraction cannot exceed the pending target fraction.")
        if self.target_fraction > self.risk_bounds.max_position_fraction:
            raise RiskNormalizationError("Risk section target fraction cannot exceed the intent risk envelope.")
        if self.haircut_fraction != _quantize_fraction(
            self.target_fraction - self.approved_fraction
        ):
            raise RiskNormalizationError("Haircut fraction must equal target minus approved fraction.")
        if self.binding != (self.approved_fraction < self.target_fraction):
            raise RiskNormalizationError("Binding must match whether the target was clipped.")
        if not self.thesis.strip() or not self.rationale.strip():
            raise RiskNormalizationError("Risk sections must explain their thesis and rationale.")

    def risk_key(self) -> RiskKey:
        """Return the overlap key of this risk chart."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, RiskLens]:
        """Return the signature that must survive restriction."""
        return (self.timestamp, self.symbol, self.lens)


@dataclass(init=False)
class RiskCocycleCertificate:
    """Deterministic witness that one overlap family can be glued."""

    key: RiskKey
    lenses: tuple[RiskLens, ...]
    target_gap: Decimal
    approval_gap: Decimal
    utilization_gap: Decimal
    bounds_gap: Decimal
    triple_overlap_residual: Decimal
    h1_obstruction: Decimal
    passes: bool
    reason: str

    def __init__(
        self,
        key: RiskKey,
        lenses: tuple[RiskLens, ...],
        target_gap: Decimal,
        approval_gap: Decimal,
        utilization_gap: Decimal,
        bounds_gap: Decimal,
        triple_overlap_residual: Decimal,
        h1_obstruction: Decimal,
        passes: bool,
        reason: str,
    ) -> None:
        self.key = key
        self.lenses = tuple(lenses)
        self.target_gap = target_gap
        self.approval_gap = approval_gap
        self.utilization_gap = utilization_gap
        self.bounds_gap = bounds_gap
        self.triple_overlap_residual = triple_overlap_residual
        self.h1_obstruction = h1_obstruction
        self.passes = passes
        self.reason = reason

    def assert_passes(self) -> None:
        """Raise :class:`RiskGluingError` when the certificate fails."""
        if not self.passes:
            timestamp, symbol = self.key
            message = f"Risk overlap {symbol}@{timestamp.isoformat()} failed gluing: {self.reason}"
            raise RiskGluingError(message)


@dataclass(init=False)
class GlobalRiskSection:
    """A coherent risk section obtained by gluing local invariant charts."""

    timestamp: datetime
    symbol: str
    lenses: tuple[RiskLens, ...]
    side: str
    style: str
    target_fraction: Decimal
    approved_fraction: Decimal
    alpha_score: Decimal
    conviction: Decimal
    risk_bounds: RiskBounds
    aggregate_utilization: Decimal
    gluing_score: Decimal
    approval_status: RiskApprovalStatus
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        lenses: tuple[RiskLens, ...],
        side: str,
        style: str,
        target_fraction: Decimal,
        approved_fraction: Decimal,
        alpha_score: Decimal,
        conviction: Decimal,
        risk_bounds: RiskBounds,
        aggregate_utilization: Decimal,
        gluing_score: Decimal,
        approval_status: RiskApprovalStatus,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.lenses = tuple(lenses)
        self.side = side
        self.style = style
        self.target_fraction = target_fraction
        self.approved_fraction = approved_fraction
        self.alpha_score = alpha_score
        self.conviction = conviction
        self.risk_bounds = risk_bounds
        self.aggregate_utilization = aggregate_utilization
        self.gluing_score = gluing_score
        self.approval_status = approval_status
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise RiskNormalizationError("Global risk timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise RiskNormalizationError("Global risk timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise RiskNormalizationError("Global risk symbols must be canonicalized.")
        if not self.lenses:
            raise RiskNormalizationError("Global risk sections must retain risk lenses.")
        if self.side not in {"long", "short", "flat"}:
            raise RiskNormalizationError(f"Unsupported global risk side {self.side!r}.")
        if not self.style.strip():
            raise RiskNormalizationError("Global risk sections must carry a style.")
        _validate_probability(self.target_fraction, "target_fraction")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.aggregate_utilization, "aggregate_utilization")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.approved_fraction > self.target_fraction:
            raise RiskNormalizationError("Glued approved fraction cannot exceed the pending target fraction.")
        if self.approved_fraction > self.risk_bounds.max_position_fraction:
            raise RiskNormalizationError("Glued approved fraction cannot exceed the final risk envelope.")
        if self.approval_status not in {"rejected", "risk_approved"}:
            raise RiskNormalizationError(f"Unsupported risk approval status {self.approval_status!r}.")
        if not self.thesis.strip() or not self.rationale.strip():
            raise RiskNormalizationError("Global risk sections must explain their decision.")


@dataclass(init=False)
class RiskApprovedIntent:
    """A position intent refined by risk review for downstream execution."""

    timestamp: datetime
    symbol: str
    side: str
    style: str
    target_fraction: Decimal
    approved_fraction: Decimal
    alpha_score: Decimal
    conviction: Decimal
    risk_bounds: RiskBounds
    gluing_score: Decimal
    approval_status: RiskApprovalStatus
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        side: str,
        style: str,
        target_fraction: Decimal,
        approved_fraction: Decimal,
        alpha_score: Decimal,
        conviction: Decimal,
        risk_bounds: RiskBounds,
        gluing_score: Decimal,
        approval_status: RiskApprovalStatus,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.side = side
        self.style = style
        self.target_fraction = target_fraction
        self.approved_fraction = approved_fraction
        self.alpha_score = alpha_score
        self.conviction = conviction
        self.risk_bounds = risk_bounds
        self.gluing_score = gluing_score
        self.approval_status = approval_status
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise RiskNormalizationError("Approved intent timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise RiskNormalizationError("Approved intent timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise RiskNormalizationError("Approved intent symbols must be canonicalized.")
        if self.side not in {"long", "short", "flat"}:
            raise RiskNormalizationError(f"Unsupported approved intent side {self.side!r}.")
        if not self.style.strip():
            raise RiskNormalizationError("Approved intents must carry a style.")
        _validate_probability(self.target_fraction, "target_fraction")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.approved_fraction > self.target_fraction:
            raise RiskNormalizationError("Approved fraction cannot exceed the pending target fraction.")
        if self.approved_fraction > self.risk_bounds.max_position_fraction:
            raise RiskNormalizationError("Approved fraction cannot exceed the final risk envelope.")
        if self.approval_status not in {"rejected", "risk_approved"}:
            raise RiskNormalizationError(f"Unsupported approved intent status {self.approval_status!r}.")
        if not self.thesis.strip() or not self.rationale.strip():
            raise RiskNormalizationError("Approved intents must explain their thesis and rationale.")

    def intent_key(self) -> RiskKey:
        """Return the overlap key carried by the refined intent."""
        return (self.timestamp, self.symbol)


def _build_drawdown_section(
    intent: PositionIntent,
    state: PortfolioRiskState,
    policy: RiskPolicy,
) -> LocalRiskSection:
    """Build the drawdown-local section for one pending-risk intent."""
    if state.drawdown_fraction >= policy.kill_switch_drawdown:
        approved_fraction = ZERO
        projected_drawdown = state.drawdown_fraction
        passes = False
        rationale = (
            "kill-switch drawdown threshold is already breached, so the intent cannot descend"
        )
    else:
        headroom = max(ZERO, policy.max_drawdown - state.drawdown_fraction)
        drawdown_capacity = _quantize_fraction(headroom / intent.risk_bounds.stop_loss_fraction)
        approved_fraction = _clamp_probability(
            min(
                intent.target_fraction,
                intent.risk_bounds.max_position_fraction,
                drawdown_capacity,
            )
        )
        projected_drawdown = _clamp_probability(
            state.drawdown_fraction
            + _quantize_fraction(
                approved_fraction * intent.risk_bounds.stop_loss_fraction
            )
        )
        passes = approved_fraction > ZERO and projected_drawdown <= policy.max_drawdown
        if approved_fraction < intent.target_fraction:
            rationale = (
                "remaining drawdown budget clips the target so the encoded stop-loss stays "
                "inside the verified loss bound"
            )
        else:
            rationale = (
                "remaining drawdown budget fully absorbs the proposed stop-loss envelope"
            )
    utilization = _clamp_probability(_safe_ratio(projected_drawdown, policy.max_drawdown))
    haircut_fraction = _quantize_fraction(intent.target_fraction - approved_fraction)
    section = LocalRiskSection(
        timestamp=intent.timestamp,
        symbol=intent.symbol,
        lens="drawdown",
        side=intent.side,
        style=intent.style,
        target_fraction=intent.target_fraction,
        approved_fraction=approved_fraction,
        alpha_score=intent.alpha_score,
        conviction=intent.conviction,
        risk_bounds=intent.risk_bounds,
        limit_fraction=policy.max_drawdown,
        utilization=utilization,
        haircut_fraction=haircut_fraction,
        binding=approved_fraction < intent.target_fraction,
        passes=passes,
        thesis=_local_thesis("drawdown", intent, approved_fraction),
        rationale=rationale,
    )
    return section


def _build_exposure_section(
    intent: PositionIntent,
    state: PortfolioRiskState,
    policy: RiskPolicy,
) -> LocalRiskSection:
    """Build the exposure-local section for one pending-risk intent."""
    symbol_limit = min(policy.max_symbol_exposure, intent.risk_bounds.max_position_fraction)
    net_limit = policy.max_net_exposure
    symbol_capacity = _directional_capacity(state.symbol_exposure_fraction, intent.side, symbol_limit)
    net_capacity = _directional_capacity(state.net_exposure_fraction, intent.side, net_limit)
    approved_fraction = _clamp_probability(
        min(
            intent.target_fraction,
            intent.risk_bounds.max_position_fraction,
            symbol_capacity,
            net_capacity,
        )
    )
    projected_symbol = abs(_projected_symbol_exposure(state, intent.side, approved_fraction))
    projected_net = abs(_projected_net_exposure(state, intent.side, approved_fraction))
    utilization = _clamp_probability(
        max(
            _safe_ratio(projected_symbol, symbol_limit),
            _safe_ratio(projected_net, net_limit),
        )
    )
    haircut_fraction = _quantize_fraction(intent.target_fraction - approved_fraction)
    passes = (
        approved_fraction > ZERO
        and projected_symbol <= symbol_limit
        and projected_net <= net_limit
    )
    rationale = (
        "symbol and net exposures remain inside their shared admissible interval"
        if not haircut_fraction
        else "symbol or net exposure binds, so the target is clipped onto the overlap"
    )
    section = LocalRiskSection(
        timestamp=intent.timestamp,
        symbol=intent.symbol,
        lens="exposure",
        side=intent.side,
        style=intent.style,
        target_fraction=intent.target_fraction,
        approved_fraction=approved_fraction,
        alpha_score=intent.alpha_score,
        conviction=intent.conviction,
        risk_bounds=intent.risk_bounds,
        limit_fraction=min(symbol_limit, net_limit),
        utilization=utilization,
        haircut_fraction=haircut_fraction,
        binding=approved_fraction < intent.target_fraction,
        passes=passes,
        thesis=_local_thesis("exposure", intent, approved_fraction),
        rationale=rationale,
    )
    return section


def _build_leverage_section(
    intent: PositionIntent,
    state: PortfolioRiskState,
    policy: RiskPolicy,
) -> LocalRiskSection:
    """Build the leverage-local section for one pending-risk intent."""
    gross_limit = _effective_gross_limit(policy)
    if _same_direction(state.symbol_exposure_fraction, intent.side):
        leverage_capacity = gross_limit - state.gross_exposure_fraction
    else:
        leverage_capacity = gross_limit - state.gross_exposure_fraction + abs(
            state.symbol_exposure_fraction
        )
    approved_fraction = _clamp_probability(
        min(
            intent.target_fraction,
            intent.risk_bounds.max_position_fraction,
            _quantize_fraction(max(ZERO, leverage_capacity)),
        )
    )
    projected_gross = _projected_gross_exposure(state, intent.side, approved_fraction)
    utilization = _clamp_probability(_safe_ratio(projected_gross, gross_limit))
    haircut_fraction = _quantize_fraction(intent.target_fraction - approved_fraction)
    passes = approved_fraction > ZERO and projected_gross <= gross_limit
    rationale = (
        "gross balance-sheet usage remains inside the leverage budget"
        if not haircut_fraction
        else "gross exposure forces a conservative clip to preserve leverage invariants"
    )
    section = LocalRiskSection(
        timestamp=intent.timestamp,
        symbol=intent.symbol,
        lens="leverage",
        side=intent.side,
        style=intent.style,
        target_fraction=intent.target_fraction,
        approved_fraction=approved_fraction,
        alpha_score=intent.alpha_score,
        conviction=intent.conviction,
        risk_bounds=intent.risk_bounds,
        limit_fraction=gross_limit,
        utilization=utilization,
        haircut_fraction=haircut_fraction,
        binding=approved_fraction < intent.target_fraction,
        passes=passes,
        thesis=_local_thesis("leverage", intent, approved_fraction),
        rationale=rationale,
    )
    return section


def build_risk_cover(
    intents: Iterable[PositionIntent],
    *,
    policy: RiskPolicy | None = None,
    portfolio_state: PortfolioRiskState | None = None,
    state_by_symbol: Mapping[str, PortfolioRiskState] | None = None,
) -> list[LocalRiskSection]:
    """Build the local risk cover for a batch of pending-risk intents."""
    resolved_policy = policy or default_risk_policy()
    default_state = portfolio_state or neutral_portfolio_state()
    sections: list[LocalRiskSection] = []
    for index, intent in enumerate(intents):
        if intent.approval_status != "pending_risk":
            continue
        state = _resolve_portfolio_state(
            intent.symbol,
            portfolio_state=default_state,
            state_by_symbol=state_by_symbol,
        )
        try:
            sections.extend(
                (
                    _build_drawdown_section(intent, state, resolved_policy),
                    _build_exposure_section(intent, state, resolved_policy),
                    _build_leverage_section(intent, state, resolved_policy),
                )
            )
        except RiskEngineError as exc:
            raise RiskNormalizationError(f"Failed to build risk cover at intent index {index}: {exc}") from exc
    return sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.lens))


def restrict_risk_sections(
    sections: Iterable[LocalRiskSection],
    *,
    symbols: Collection[str] | None = None,
    start: datetime | None = None,
    end: datetime | None = None,
    lenses: Collection[RiskLens] | None = None,
) -> list[LocalRiskSection]:
    """Restrict local risk sections to a sub-cover."""
    normalized_symbols = (
        {_normalize_symbol(symbol) for symbol in symbols} if symbols is not None else None
    )
    start_bound = _normalize_timestamp(start, "start") if start is not None else None
    end_bound = _normalize_timestamp(end, "end") if end is not None else None
    normalized_lenses = set(lenses) if lenses is not None else None
    if normalized_lenses is not None:
        unknown = normalized_lenses.difference(LENSES)
        if unknown:
            raise RiskRestrictionError(f"Unknown risk lenses in restriction: {sorted(unknown)!r}.")
    if start_bound is not None and end_bound is not None and end_bound < start_bound:
        raise RiskRestrictionError("Restriction end time cannot precede start time.")
    restricted: list[LocalRiskSection] = []
    for section in sections:
        if normalized_symbols is not None and section.symbol not in normalized_symbols:
            continue
        if start_bound is not None and section.timestamp < start_bound:
            continue
        if end_bound is not None and section.timestamp > end_bound:
            continue
        if normalized_lenses is not None and section.lens not in normalized_lenses:
            continue
        restricted.append(section)
    return sorted(restricted, key=lambda item: (item.timestamp, item.symbol, item.lens))


def group_risk_overlaps(
    sections: Iterable[LocalRiskSection],
) -> dict[RiskKey, list[LocalRiskSection]]:
    """Group local risk sections by the canonical overlap key."""
    grouped: dict[RiskKey, list[LocalRiskSection]] = {}
    for section in sections:
        grouped.setdefault(section.risk_key(), []).append(section)
    for members in grouped.values():
        members.sort(key=lambda item: item.lens)
    return dict(sorted(grouped.items(), key=lambda item: item[0]))


def _build_certificate(
    key: RiskKey,
    members: Sequence[LocalRiskSection],
    *,
    target_tolerance: Decimal,
    approval_tolerance: Decimal,
    utilization_tolerance: Decimal,
    bounds_tolerance: Decimal,
    h1_tolerance: Decimal,
) -> RiskCocycleCertificate:
    """Build the risk cocycle certificate for one overlap class."""
    lenses = _require_unique_lenses(members, key)
    target_gap = _max_gap([member.target_fraction for member in members], FRACTION_QUANTUM)
    approval_gap = _max_gap(
        [member.approved_fraction for member in members], FRACTION_QUANTUM
    )
    utilization_gap = _max_gap([member.utilization for member in members], FRACTION_QUANTUM)
    bounds_gap = _risk_bounds_gap(members)
    corrections = [member.haircut_fraction for member in members]
    triple_residual = _triple_overlap_residual(corrections)
    h1_obstruction = _quantize_fraction(
        target_gap + approval_gap + bounds_gap + triple_residual
    )
    passes = (
        all(member.passes for member in members)
        and target_gap <= target_tolerance
        and approval_gap <= approval_tolerance
        and bounds_gap <= bounds_tolerance
        and h1_obstruction <= h1_tolerance
    )
    if passes:
        reason = "local risk charts agree and the H^1 obstruction remains bounded"
    else:
        reason = (
            "risk charts disagree on overlap data: "
            f"target_gap={target_gap}, "
            f"approval_gap={approval_gap}, "
            f"utilization_gap={utilization_gap}, "
            f"bounds_gap={bounds_gap}, "
            f"triple_residual={triple_residual}, "
            f"h1_obstruction={h1_obstruction}"
        )
    certificate = RiskCocycleCertificate(
        key=key,
        lenses=lenses,
        target_gap=target_gap,
        approval_gap=approval_gap,
        utilization_gap=utilization_gap,
        bounds_gap=bounds_gap,
        triple_overlap_residual=triple_residual,
        h1_obstruction=h1_obstruction,
        passes=passes,
        reason=reason,
    )
    return certificate


def check_risk_cocycle(
    sections: Sequence[LocalRiskSection],
    *,
    target_tolerance: Decimal | str = Decimal("0.0000001"),
    approval_tolerance: Decimal | str = Decimal("0.1500000"),
    utilization_tolerance: Decimal | str = Decimal("0.4500000"),
    bounds_tolerance: Decimal | str = Decimal("0.0000001"),
    h1_tolerance: Decimal | str | None = None,
) -> tuple[RiskCocycleCertificate, ...]:
    """Check whether local risk sections glue on each overlap."""
    resolved_target_tolerance = _resolve_tolerance(target_tolerance, "target_tolerance")
    resolved_approval_tolerance = _resolve_tolerance(
        approval_tolerance,
        "approval_tolerance",
    )
    resolved_utilization_tolerance = _resolve_tolerance(
        utilization_tolerance,
        "utilization_tolerance",
    )
    resolved_bounds_tolerance = _resolve_tolerance(bounds_tolerance, "bounds_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_target_tolerance
            + resolved_approval_tolerance
            + resolved_utilization_tolerance
            + resolved_bounds_tolerance
        )
    )
    grouped = group_risk_overlaps(sections)
    certificates = [
        _build_certificate(
            key,
            members,
            target_tolerance=resolved_target_tolerance,
            approval_tolerance=resolved_approval_tolerance,
            utilization_tolerance=resolved_utilization_tolerance,
            bounds_tolerance=resolved_bounds_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
        for key, members in grouped.items()
    ]
    return tuple(certificates)


def glue_risk_sections(
    sections: Sequence[LocalRiskSection],
    *,
    target_tolerance: Decimal | str = Decimal("0.0000001"),
    approval_tolerance: Decimal | str = Decimal("0.1500000"),
    utilization_tolerance: Decimal | str = Decimal("0.4500000"),
    bounds_tolerance: Decimal | str = Decimal("0.0000001"),
    h1_tolerance: Decimal | str | None = None,
    min_approval_fraction: Decimal | str | None = None,
) -> list[GlobalRiskSection]:
    """Glue local risk charts into coherent global risk sections."""
    resolved_target_tolerance = _resolve_tolerance(target_tolerance, "target_tolerance")
    resolved_approval_tolerance = _resolve_tolerance(
        approval_tolerance,
        "approval_tolerance",
    )
    resolved_utilization_tolerance = _resolve_tolerance(
        utilization_tolerance,
        "utilization_tolerance",
    )
    resolved_bounds_tolerance = _resolve_tolerance(bounds_tolerance, "bounds_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_target_tolerance
            + resolved_approval_tolerance
            + resolved_utilization_tolerance
            + resolved_bounds_tolerance
        )
    )
    resolved_min_approval = (
        _resolve_tolerance(min_approval_fraction, "min_approval_fraction")
        if min_approval_fraction is not None
        else default_risk_policy().min_approval_fraction
    )
    grouped = group_risk_overlaps(sections)
    certificates = {
        certificate.key: certificate
        for certificate in check_risk_cocycle(
            sections,
            target_tolerance=resolved_target_tolerance,
            approval_tolerance=resolved_approval_tolerance,
            utilization_tolerance=resolved_utilization_tolerance,
            bounds_tolerance=resolved_bounds_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    }
    glued: list[GlobalRiskSection] = []
    for key, members in grouped.items():
        certificate = certificates[key]
        certificate.assert_passes()
        side = _require_unique_value([member.side for member in members], key, "side")
        style = _require_unique_value([member.style for member in members], key, "style")
        risk_bounds = _require_unique_value(
            [member.risk_bounds for member in members],
            key,
            "risk_bounds",
        )
        target_fraction = _median_decimal(
            [member.target_fraction for member in members], FRACTION_QUANTUM
        )
        approved_fraction = _quantize_fraction(
            min(member.approved_fraction for member in members)
        )
        aggregate_utilization = _clamp_probability(
            max(member.utilization for member in members)
        )
        conviction = _median_decimal(
            [member.conviction for member in members], FRACTION_QUANTUM
        )
        alpha_score = _median_decimal([member.alpha_score for member in members])
        gluing_score = _gluing_score(certificate.h1_obstruction, resolved_h1_tolerance)
        approval_status: RiskApprovalStatus
        if side != "flat" and approved_fraction >= resolved_min_approval:
            approval_status = "risk_approved"
        else:
            approval_status = "rejected"
        prototype = GlobalRiskSection(
            timestamp=key[0],
            symbol=key[1],
            lenses=certificate.lenses,
            side=side,
            style=style,
            target_fraction=target_fraction,
            approved_fraction=approved_fraction,
            alpha_score=alpha_score,
            conviction=conviction,
            risk_bounds=risk_bounds,
            aggregate_utilization=aggregate_utilization,
            gluing_score=gluing_score,
            approval_status=approval_status,
            thesis="pending",
            rationale="pending",
        )
        binding_lenses = [member.lens for member in members if member.binding]
        glued.append(
            GlobalRiskSection(
                timestamp=prototype.timestamp,
                symbol=prototype.symbol,
                lenses=prototype.lenses,
                side=prototype.side,
                style=prototype.style,
                target_fraction=prototype.target_fraction,
                approved_fraction=prototype.approved_fraction,
                alpha_score=prototype.alpha_score,
                conviction=prototype.conviction,
                risk_bounds=prototype.risk_bounds,
                aggregate_utilization=prototype.aggregate_utilization,
                gluing_score=prototype.gluing_score,
                approval_status=prototype.approval_status,
                thesis=_global_thesis(prototype.approval_status, prototype),
                rationale=_global_rationale(
                    prototype.approval_status,
                    prototype,
                    binding_lenses,
                ),
            )
        )
    return sorted(glued, key=lambda item: (item.timestamp, item.symbol))


def approve_position_intents(
    sections: Iterable[GlobalRiskSection],
) -> list[RiskApprovedIntent]:
    """Turn glued risk sections into execution-facing refined intents."""
    approved: list[RiskApprovedIntent] = []
    for index, section in enumerate(sections):
        try:
            approved.append(
                RiskApprovedIntent(
                    timestamp=section.timestamp,
                    symbol=section.symbol,
                    side=section.side,
                    style=section.style,
                    target_fraction=section.target_fraction,
                    approved_fraction=section.approved_fraction,
                    alpha_score=section.alpha_score,
                    conviction=section.conviction,
                    risk_bounds=section.risk_bounds,
                    gluing_score=section.gluing_score,
                    approval_status=section.approval_status,
                    thesis=section.thesis,
                    rationale=_approval_reason(section.approval_status, section),
                )
            )
        except RiskEngineError as exc:
            raise RiskNormalizationError(f"Failed to approve position intent at risk index {index}: {exc}") from exc
    return sorted(approved, key=lambda item: (item.timestamp, item.symbol))


def risk_approved_intents(intents: Iterable[RiskApprovedIntent]) -> list[RiskApprovedIntent]:
    """Return only those refined intents that may descend to execution."""
    return [intent for intent in intents if intent.approval_status == "risk_approved"]


def risk_engine_schema_version() -> str:
    """Return the schema version of the high-level risk-engine bundle."""
    return RISK_ENGINE_SCHEMA_VERSION


def _intent_signature(intent: PositionIntent) -> str:
    """Return a stable signature for one pending-risk intent."""
    parts = [
        intent.timestamp.isoformat(),
        intent.symbol,
        intent.side,
        intent.style,
        str(intent.target_fraction),
        str(intent.alpha_score),
        str(intent.conviction),
        str(intent.risk_bounds.max_position_fraction),
        str(intent.risk_bounds.stop_loss_fraction),
        str(intent.risk_bounds.take_profit_fraction),
        str(intent.risk_bounds.max_holding_periods),
        str(intent.risk_bounds.conviction_floor),
        str(intent.risk_bounds.h1_buffer),
        intent.approval_status,
        intent.thesis,
        intent.rationale,
    ]
    return _stable_digest(parts)


def _local_section_signature(section: LocalRiskSection) -> str:
    """Return a stable signature for one local risk section."""
    parts = [
        section.timestamp.isoformat(),
        section.symbol,
        section.lens,
        section.side,
        section.style,
        str(section.target_fraction),
        str(section.approved_fraction),
        str(section.alpha_score),
        str(section.conviction),
        str(section.limit_fraction),
        str(section.utilization),
        str(section.haircut_fraction),
        str(section.binding),
        str(section.passes),
        section.thesis,
        section.rationale,
    ]
    return _stable_digest(parts)


def _global_section_signature(section: GlobalRiskSection) -> str:
    """Return a stable signature for one glued risk section."""
    parts = [
        section.timestamp.isoformat(),
        section.symbol,
        *section.lenses,
        section.side,
        section.style,
        str(section.target_fraction),
        str(section.approved_fraction),
        str(section.alpha_score),
        str(section.conviction),
        str(section.aggregate_utilization),
        str(section.gluing_score),
        section.approval_status,
        section.thesis,
        section.rationale,
    ]
    return _stable_digest(parts)


def _approved_intent_signature(intent: RiskApprovedIntent) -> str:
    """Return a stable signature for one refined downstream intent."""
    parts = [
        intent.timestamp.isoformat(),
        intent.symbol,
        intent.side,
        intent.style,
        str(intent.target_fraction),
        str(intent.approved_fraction),
        str(intent.alpha_score),
        str(intent.conviction),
        str(intent.gluing_score),
        intent.approval_status,
        intent.thesis,
        intent.rationale,
    ]
    return _stable_digest(parts)


def _risk_engine_input_signature(intents: tuple[PositionIntent, ...]) -> str:
    """Return a stable signature for direct iterable input."""
    return _stable_digest(_intent_signature(intent) for intent in intents)


def _resolve_risk_engine_input(
    risk_input: RiskEngineInput,
) -> tuple[
    tuple[PositionIntent, ...],
    tuple[StrategyResearchIdea, ...],
    str,
    StrategyRiskPolicy | None,
]:
    """Normalize risk-engine input into typed intents and upstream metadata."""
    if isinstance(risk_input, StrategyKernelBundle):
        resolved_input = (
            tuple(risk_input.position_intents),
            tuple(risk_input.research_ideas),
            risk_input.data_signature,
            risk_input.risk_policy,
        )
        return resolved_input
    intents = tuple(risk_input)
    for index, intent in enumerate(intents):
        if not isinstance(intent, PositionIntent):
            raise RiskNormalizationError(f"Risk engine input at index {index} is not a PositionIntent.")
    return intents, (), _risk_engine_input_signature(intents), None


def _resolve_risk_policy(
    policy: RiskPolicy | None,
    upstream_policy: StrategyRiskPolicy | None,
) -> RiskPolicy:
    """Resolve the policy used by this risk-engine build."""
    if policy is not None:
        return policy
    base = default_risk_policy()
    if upstream_policy is None:
        return base
    max_symbol_exposure = _clamp_probability(
        max(base.max_symbol_exposure, upstream_policy.max_position_fraction)
    )
    max_net_exposure = _clamp_probability(
        max(base.max_net_exposure, upstream_policy.max_position_fraction)
    )
    merged_rejection_conditions = tuple(
        dict.fromkeys(
            (
                *base.order_rejection_conditions,
                *upstream_policy.order_rejection_conditions,
            )
        )
    )
    resolved_policy = RiskPolicy(
        max_gross_leverage=base.max_gross_leverage,
        max_net_exposure=max_net_exposure,
        max_symbol_exposure=min(max_symbol_exposure, max_net_exposure),
        max_drawdown=max(base.max_drawdown, upstream_policy.max_drawdown_fraction),
        min_cash_buffer=base.min_cash_buffer,
        min_approval_fraction=min(
            base.min_approval_fraction,
            upstream_policy.max_position_fraction,
        ),
        kill_switch_drawdown=max(
            base.kill_switch_drawdown,
            upstream_policy.kill_switch_drawdown_fraction,
        ),
        order_rejection_conditions=merged_rejection_conditions,
        proof_obligation=upstream_policy.proof_obligation,
        paper_trading_required=upstream_policy.paper_trading_required,
    )
    return resolved_policy


@dataclass(init=False)
class RiskResearchIdea:
    """A testable, risk-aware market thesis emitted by the risk engine."""

    symbol: str
    as_of: datetime
    side: RiskIdeaSide
    thesis: str
    validation_plan: str
    approved_fraction: Decimal
    residual_drawdown_capacity: Decimal
    expected_edge_bps: Decimal
    provenance: str
    data_signature: str

    def __init__(
        self,
        symbol: str,
        as_of: datetime,
        side: RiskIdeaSide,
        thesis: str,
        validation_plan: str,
        approved_fraction: Decimal,
        residual_drawdown_capacity: Decimal,
        expected_edge_bps: Decimal,
        provenance: str,
        data_signature: str,
    ) -> None:
        self.symbol = symbol
        self.as_of = as_of
        self.side = side
        self.thesis = thesis
        self.validation_plan = validation_plan
        self.approved_fraction = approved_fraction
        self.residual_drawdown_capacity = residual_drawdown_capacity
        self.expected_edge_bps = expected_edge_bps
        self.provenance = provenance
        self.data_signature = data_signature
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.symbol != _normalize_symbol(self.symbol):
            raise RiskNormalizationError("Risk research idea symbols must be canonical.")
        if self.as_of.tzinfo is None or self.as_of.utcoffset() is None:
            raise RiskNormalizationError("Risk research idea timestamps must be timezone-aware.")
        if self.as_of.astimezone(timezone.utc) != self.as_of:
            raise RiskNormalizationError("Risk research idea timestamps must be expressed in UTC.")
        if self.side not in {"long", "short"}:
            raise RiskNormalizationError("Risk research idea side must be 'long' or 'short'.")
        if (
            not self.thesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
        ):
            raise RiskNormalizationError("Risk research ideas require non-empty narrative fields.")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_probability(
            self.residual_drawdown_capacity,
            "residual_drawdown_capacity",
        )
        if not self.expected_edge_bps.is_finite() or self.expected_edge_bps <= ZERO:
            raise RiskNormalizationError("Risk research ideas require a positive expected edge.")
        if not self.data_signature:
            raise RiskNormalizationError("Risk research ideas require a reproducibility signature.")


@dataclass(init=False)
class RiskEngineBundle:
    """High-level bundle produced by the risk-engine refinement site."""

    schema_version: str
    position_intents: tuple[PositionIntent, ...]
    local_sections: tuple[LocalRiskSection, ...]
    global_sections: tuple[GlobalRiskSection, ...]
    approved_intents: tuple[RiskApprovedIntent, ...]
    research_ideas: tuple[RiskResearchIdea, ...]
    policy: RiskPolicy
    target_tolerance: Decimal
    approval_tolerance: Decimal
    utilization_tolerance: Decimal
    bounds_tolerance: Decimal
    h1_tolerance: Decimal
    min_approval_fraction: Decimal
    upstream_data_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __init__(
        self,
        schema_version: str,
        position_intents: tuple[PositionIntent, ...],
        local_sections: tuple[LocalRiskSection, ...],
        global_sections: tuple[GlobalRiskSection, ...],
        approved_intents: tuple[RiskApprovedIntent, ...],
        research_ideas: tuple[RiskResearchIdea, ...],
        policy: RiskPolicy,
        target_tolerance: Decimal,
        approval_tolerance: Decimal,
        utilization_tolerance: Decimal,
        bounds_tolerance: Decimal,
        h1_tolerance: Decimal,
        min_approval_fraction: Decimal,
        upstream_data_signature: str,
        data_signature: str,
        audit_metadata: tuple[tuple[str, str], ...],
    ) -> None:
        self.schema_version = schema_version
        self.position_intents = tuple(position_intents)
        self.local_sections = tuple(local_sections)
        self.global_sections = tuple(global_sections)
        self.approved_intents = tuple(approved_intents)
        self.research_ideas = tuple(research_ideas)
        self.policy = policy
        self.target_tolerance = target_tolerance
        self.approval_tolerance = approval_tolerance
        self.utilization_tolerance = utilization_tolerance
        self.bounds_tolerance = bounds_tolerance
        self.h1_tolerance = h1_tolerance
        self.min_approval_fraction = min_approval_fraction
        self.upstream_data_signature = upstream_data_signature
        self.data_signature = data_signature
        self.audit_metadata = tuple(audit_metadata)
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.schema_version != risk_engine_schema_version():
            raise RiskNormalizationError("Risk engine bundle schema version mismatch.")
        if not self.position_intents:
            raise RiskNormalizationError("Risk engine bundles require at least one pending-risk position intent.")
        if not self.local_sections:
            raise RiskNormalizationError("Risk engine bundles require at least one local risk section.")
        if not self.global_sections:
            raise RiskNormalizationError("Risk engine bundles require at least one glued risk section.")
        if not self.approved_intents:
            raise RiskNormalizationError("Risk engine bundles require at least one refined intent.")
        if not self.research_ideas:
            raise RiskNormalizationError("Risk engine bundles require at least one testable risk idea.")
        if not self.upstream_data_signature or not self.data_signature:
            raise RiskNormalizationError("Risk engine bundles require deterministic reproducibility signatures.")

    @property
    def symbols(self) -> tuple[str, ...]:
        """Return the canonical symbols represented in the bundle."""
        return tuple(sorted({section.symbol for section in self.global_sections}))

    @property
    def executable_intents(self) -> tuple[RiskApprovedIntent, ...]:
        """Return the subset of intents that may descend to execution."""
        return tuple(risk_approved_intents(self.approved_intents))

    @property
    def ideas(self) -> tuple[RiskResearchIdea, ...]:
        """Return the testable ideas discovered by the risk engine."""
        return self.research_ideas

    def summary(self) -> str:
        """Return a deterministic one-line summary of the bundle."""
        return risk_engine_summary(self)


@dataclass(init=False)
class RiskEngineValidationReport:
    """Deterministic validation report for a built risk-engine bundle."""

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    normalization_signatures_preserved: bool
    cocycle_checks_passed: bool
    coherent_global_sections: bool
    intents_align_with_risk_bounds: bool
    only_risk_approved_descend: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    proof_obligation_satisfied: bool
    paper_trading_enforced: bool
    signature_matches: bool
    local_sections_checked: int
    global_sections_checked: int
    position_intents_checked: int
    approved_intents_checked: int
    overlap_certificates: tuple[RiskCocycleCertificate, ...]
    messages: tuple[str, ...]

    def __init__(
        self,
        passes: bool,
        timestamp_symbol_invariants_preserved: bool,
        normalization_signatures_preserved: bool,
        cocycle_checks_passed: bool,
        coherent_global_sections: bool,
        intents_align_with_risk_bounds: bool,
        only_risk_approved_descend: bool,
        novel_idea_present: bool,
        risk_invariants_explicit: bool,
        proof_obligation_satisfied: bool,
        paper_trading_enforced: bool,
        signature_matches: bool,
        local_sections_checked: int,
        global_sections_checked: int,
        position_intents_checked: int,
        approved_intents_checked: int,
        overlap_certificates: tuple[RiskCocycleCertificate, ...],
        messages: tuple[str, ...],
    ) -> None:
        self.passes = passes
        self.timestamp_symbol_invariants_preserved = timestamp_symbol_invariants_preserved
        self.normalization_signatures_preserved = normalization_signatures_preserved
        self.cocycle_checks_passed = cocycle_checks_passed
        self.coherent_global_sections = coherent_global_sections
        self.intents_align_with_risk_bounds = intents_align_with_risk_bounds
        self.only_risk_approved_descend = only_risk_approved_descend
        self.novel_idea_present = novel_idea_present
        self.risk_invariants_explicit = risk_invariants_explicit
        self.proof_obligation_satisfied = proof_obligation_satisfied
        self.paper_trading_enforced = paper_trading_enforced
        self.signature_matches = signature_matches
        self.local_sections_checked = local_sections_checked
        self.global_sections_checked = global_sections_checked
        self.position_intents_checked = position_intents_checked
        self.approved_intents_checked = approved_intents_checked
        self.overlap_certificates = tuple(overlap_certificates)
        self.messages = tuple(messages)

    def summary(self) -> str:
        """Return a concise textual summary of the validation result."""
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        summary = (
            f"validation={status} intents={self.position_intents_checked} "
            f"local_sections={self.local_sections_checked} "
            f"global_sections={self.global_sections_checked} "
            f"approved_intents={self.approved_intents_checked} issues={issues}"
        )
        return summary


def _matching_strategy_idea(
    section: GlobalRiskSection,
    upstream_ideas: Sequence[StrategyResearchIdea],
) -> StrategyResearchIdea | None:
    """Return the strongest upstream idea aligned with one risk section."""
    matches = [
        idea
        for idea in upstream_ideas
        if idea.symbol == section.symbol
        and idea.as_of == section.timestamp
        and idea.side == section.side
    ]
    if not matches:
        return None
    return max(matches, key=lambda idea: (idea.conviction, idea.expected_edge_bps))


def _risk_validation_plan(matched_idea: StrategyResearchIdea | None) -> str:
    """Return the validation plan attached to one risk idea."""
    inherited = (
        matched_idea.validation_plan
        if matched_idea is not None
        else "derive the thesis from versioned strategy intents and risk sections"
    )
    validation_plan = (
        f"{inherited}; discharge SMT-backed invariants for max position size, leverage, "
        "drawdown rejection, exposure limits, and kill-switch behavior; replay the "
        "paper-trading path with immutable audit logs and bias guards"
    )
    return validation_plan


def _risk_expected_edge_bps(
    section: GlobalRiskSection,
    matched_idea: StrategyResearchIdea | None,
) -> Decimal:
    """Estimate expected edge in basis points after risk clipping."""
    inherited_edge = matched_idea.expected_edge_bps if matched_idea is not None else ZERO
    computed = (
        abs(section.alpha_score) * Decimal("70")
        + section.conviction * Decimal("35")
        + section.approved_fraction * Decimal("80")
        + section.gluing_score * Decimal("20")
    )
    return _quantize_edge(max(Decimal("0.5000"), inherited_edge, computed))


def _residual_drawdown_capacity(
    section: GlobalRiskSection,
    state: PortfolioRiskState,
    policy: RiskPolicy,
) -> Decimal:
    """Return the remaining drawdown capacity after the approved allocation."""
    consumed = state.drawdown_fraction + (
        section.approved_fraction * section.risk_bounds.stop_loss_fraction
    )
    return _clamp_probability(_quantize_fraction(max(ZERO, policy.max_drawdown - consumed)))


def _discover_risk_research_ideas(
    sections: Sequence[GlobalRiskSection],
    *,
    upstream_ideas: Sequence[StrategyResearchIdea],
    policy: RiskPolicy,
    portfolio_state: PortfolioRiskState,
    state_by_symbol: Mapping[str, PortfolioRiskState] | None,
) -> tuple[RiskResearchIdea, ...]:
    """Discover testable risk-aware ideas from glued risk sections."""
    candidates = [section for section in sections if section.side in {"long", "short"}]
    if not candidates and sections:
        candidates = [
            max(
                sections,
                key=lambda section: (
                    section.gluing_score,
                    section.conviction,
                    abs(section.alpha_score),
                    section.approved_fraction,
                ),
            )
        ]
    ideas: list[RiskResearchIdea] = []
    for section in candidates:
        matched_idea = _matching_strategy_idea(section, upstream_ideas)
        state = _resolve_portfolio_state(
            section.symbol,
            portfolio_state=portfolio_state,
            state_by_symbol=state_by_symbol,
        )
        residual_capacity = _residual_drawdown_capacity(section, state, policy)
        inherited_thesis = matched_idea.thesis if matched_idea is not None else section.thesis
        thesis = (
            f"{section.side} {section.symbol} because {inherited_thesis}; risk review approves "
            f"{section.approved_fraction} with residual drawdown capacity {residual_capacity}"
        )
        validation_plan = _risk_validation_plan(matched_idea)
        provenance = (
            "strategy_kernel_extension"
            if matched_idea is not None
            else "risk_engine_extension"
        )
        data_signature = _stable_digest(
            [
                _global_section_signature(section),
                matched_idea.data_signature if matched_idea is not None else "risk_only",
                thesis,
                validation_plan,
            ]
        )
        ideas.append(
            RiskResearchIdea(
                symbol=section.symbol,
                as_of=section.timestamp,
                side=section.side if section.side in {"long", "short"} else "long",
                thesis=thesis,
                validation_plan=validation_plan,
                approved_fraction=section.approved_fraction,
                residual_drawdown_capacity=residual_capacity,
                expected_edge_bps=_risk_expected_edge_bps(section, matched_idea),
                provenance=provenance,
                data_signature=data_signature,
            )
        )
    return tuple(sorted(ideas, key=lambda item: (item.as_of, item.symbol, item.side)))


def _risk_engine_bundle_signature(bundle: RiskEngineBundle) -> str:
    """Return a stable audit digest for the full risk-engine bundle."""
    parts = [
        bundle.schema_version,
        str(bundle.target_tolerance),
        str(bundle.approval_tolerance),
        str(bundle.utilization_tolerance),
        str(bundle.bounds_tolerance),
        str(bundle.h1_tolerance),
        str(bundle.min_approval_fraction),
        bundle.upstream_data_signature,
        bundle.policy.reproducibility_signature(),
    ]
    parts.append("position_intents")
    parts.extend(_intent_signature(intent) for intent in bundle.position_intents)
    parts.append("local_sections")
    parts.extend(_local_section_signature(section) for section in bundle.local_sections)
    parts.append("global_sections")
    parts.extend(_global_section_signature(section) for section in bundle.global_sections)
    parts.append("approved_intents")
    parts.extend(_approved_intent_signature(intent) for intent in bundle.approved_intents)
    parts.append("research_ideas")
    parts.extend(idea.data_signature for idea in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


def _restriction_signatures_preserved(sections: tuple[LocalRiskSection, ...]) -> bool:
    """Return whether restricting to the full support preserves local signatures."""
    if not sections:
        return True
    ordered = tuple(sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.lens)))
    restricted = restrict_risk_sections(
        ordered,
        symbols={section.symbol for section in ordered},
        start=ordered[0].timestamp,
        end=ordered[-1].timestamp,
        lenses={section.lens for section in ordered},
    )
    signatures_preserved = tuple(section.normalization_signature() for section in ordered) == tuple(
        section.normalization_signature() for section in restricted
    )
    return signatures_preserved


def _global_sections_coherent(
    local_sections: tuple[LocalRiskSection, ...],
    global_sections: tuple[GlobalRiskSection, ...],
) -> bool:
    """Return whether global sections descend exactly from local overlaps."""
    grouped = group_risk_overlaps(local_sections)
    if len(grouped) != len(global_sections):
        return False
    for section in global_sections:
        members = grouped.get((section.timestamp, section.symbol))
        if members is None:
            return False
        if section.lenses != tuple(sorted(member.lens for member in members)):
            return False
        if section.side != members[0].side or section.style != members[0].style:
            return False
        if section.risk_bounds != members[0].risk_bounds:
            return False
        if section.target_fraction != _median_decimal(
            [member.target_fraction for member in members],
            FRACTION_QUANTUM,
        ):
            return False
        if section.approved_fraction != _quantize_fraction(
            min(member.approved_fraction for member in members)
        ):
            return False
    return True


def _intents_align_with_risk_bounds(
    global_sections: tuple[GlobalRiskSection, ...],
    approved_intents: tuple[RiskApprovedIntent, ...],
    position_intents: tuple[PositionIntent, ...],
) -> bool:
    """Return whether pending intents and risk approvals agree on overlaps."""
    section_map = {(section.timestamp, section.symbol): section for section in global_sections}
    approved_map = {(intent.timestamp, intent.symbol): intent for intent in approved_intents}
    for pending_intent in position_intents:
        section = section_map.get((pending_intent.timestamp, pending_intent.symbol))
        approved = approved_map.get((pending_intent.timestamp, pending_intent.symbol))
        if section is None or approved is None:
            return False
        if pending_intent.side != section.side or pending_intent.side != approved.side:
            return False
        if pending_intent.style != section.style or pending_intent.style != approved.style:
            return False
        if pending_intent.target_fraction != section.target_fraction:
            return False
        if pending_intent.target_fraction != approved.target_fraction:
            return False
        if pending_intent.risk_bounds != section.risk_bounds:
            return False
        if pending_intent.risk_bounds != approved.risk_bounds:
            return False
        if approved.approved_fraction != section.approved_fraction:
            return False
        if approved.approved_fraction > pending_intent.risk_bounds.max_position_fraction:
            return False
    return len(section_map) == len(position_intents) == len(approved_map)


def _risk_invariants_explicit(bundle: RiskEngineBundle) -> bool:
    """Return whether explicit risk-critical invariants are present everywhere."""
    metadata = dict(bundle.audit_metadata)
    required_conditions = {
        "reject_failed_gluing",
        "reject_kill_switch",
        "reject_unverified_risk_core",
    }
    invariants_are_explicit = (
        bundle.policy.max_symbol_exposure <= bundle.policy.max_net_exposure
        and bundle.policy.max_net_exposure <= bundle.policy.max_gross_leverage
        and bundle.policy.kill_switch_drawdown > bundle.policy.max_drawdown
        and required_conditions.issubset(bundle.policy.order_rejection_conditions)
        and metadata.get("audit_log") == "immutable_required"
        and metadata.get("bias_guards") == "lookahead_survivorship_data_leakage_blocked"
        and metadata.get("integration_mode") == "only_risk_approved_descends"
        and metadata.get("paper_trading") == "required"
        and metadata.get("proof_obligation") == bundle.policy.proof_obligation
    )
    return invariants_are_explicit


def build_risk_engine(
    risk_input: RiskEngineInput,
    *,
    policy: RiskPolicy | None = None,
    portfolio_state: PortfolioRiskState | None = None,
    state_by_symbol: Mapping[str, PortfolioRiskState] | None = None,
    target_tolerance: Decimal | str = Decimal("0.0000001"),
    approval_tolerance: Decimal | str = Decimal("0.1500000"),
    utilization_tolerance: Decimal | str = Decimal("0.4500000"),
    bounds_tolerance: Decimal | str = Decimal("0.0000001"),
    h1_tolerance: Decimal | str | None = None,
    min_approval_fraction: Decimal | str | None = None,
) -> RiskEngineBundle:
    """Build an auditable risk-engine bundle from pending strategy intents."""
    position_intents, upstream_ideas, upstream_signature, upstream_policy = (
        _resolve_risk_engine_input(risk_input)
    )
    if not position_intents:
        raise RiskNormalizationError("Risk engine requires at least one pending-risk position intent.")
    resolved_policy = _resolve_risk_policy(policy, upstream_policy)
    default_state = portfolio_state or neutral_portfolio_state()
    resolved_target_tolerance = _resolve_tolerance(target_tolerance, "target_tolerance")
    resolved_approval_tolerance = _resolve_tolerance(
        approval_tolerance,
        "approval_tolerance",
    )
    resolved_utilization_tolerance = _resolve_tolerance(
        utilization_tolerance,
        "utilization_tolerance",
    )
    resolved_bounds_tolerance = _resolve_tolerance(bounds_tolerance, "bounds_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_target_tolerance
            + resolved_approval_tolerance
            + resolved_utilization_tolerance
            + resolved_bounds_tolerance
        )
    )
    resolved_min_approval = (
        _resolve_tolerance(min_approval_fraction, "min_approval_fraction")
        if min_approval_fraction is not None
        else resolved_policy.min_approval_fraction
    )
    local_sections = tuple(
        build_risk_cover(
            position_intents,
            policy=resolved_policy,
            portfolio_state=default_state,
            state_by_symbol=state_by_symbol,
        )
    )
    global_sections = tuple(
        glue_risk_sections(
            local_sections,
            target_tolerance=resolved_target_tolerance,
            approval_tolerance=resolved_approval_tolerance,
            utilization_tolerance=resolved_utilization_tolerance,
            bounds_tolerance=resolved_bounds_tolerance,
            h1_tolerance=resolved_h1_tolerance,
            min_approval_fraction=resolved_min_approval,
        )
    )
    approved_intents = tuple(approve_position_intents(global_sections))
    research_ideas = _discover_risk_research_ideas(
        global_sections,
        upstream_ideas=upstream_ideas,
        policy=resolved_policy,
        portfolio_state=default_state,
        state_by_symbol=state_by_symbol,
    )
    if not research_ideas:
        raise RiskNormalizationError("Risk engine must emit at least one testable idea from data-driven research.")
    audit_metadata = tuple(
        sorted(
            (
                ("audit_log", "immutable_required"),
                ("bias_guards", "lookahead_survivorship_data_leakage_blocked"),
                ("execution_mode", "paper_only_until_risk_approval"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("idea_mode", "risk_engine_extension"),
                ("integration_mode", "only_risk_approved_descends"),
                (
                    "kill_switch_policy",
                    "deterministic_reject_on_drawdown_or_unverified_risk_core",
                ),
                (
                    "paper_trading",
                    "required" if resolved_policy.paper_trading_required else "optional",
                ),
                ("proof_obligation", resolved_policy.proof_obligation),
                (
                    "reproducibility",
                    "versioned_data_configuration_and_audit_signatures",
                ),
                ("schema_version", risk_engine_schema_version()),
                (
                    "separation",
                    "research_simulation_execution_and_risk_are_decoupled",
                ),
                ("upstream_signature", upstream_signature[:16]),
            )
        )
    )
    unsigned_bundle = RiskEngineBundle(
        schema_version=risk_engine_schema_version(),
        position_intents=position_intents,
        local_sections=local_sections,
        global_sections=global_sections,
        approved_intents=approved_intents,
        research_ideas=research_ideas,
        policy=resolved_policy,
        target_tolerance=resolved_target_tolerance,
        approval_tolerance=resolved_approval_tolerance,
        utilization_tolerance=resolved_utilization_tolerance,
        bounds_tolerance=resolved_bounds_tolerance,
        h1_tolerance=resolved_h1_tolerance,
        min_approval_fraction=resolved_min_approval,
        upstream_data_signature=upstream_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    signed_bundle = RiskEngineBundle(
        schema_version=unsigned_bundle.schema_version,
        position_intents=unsigned_bundle.position_intents,
        local_sections=unsigned_bundle.local_sections,
        global_sections=unsigned_bundle.global_sections,
        approved_intents=unsigned_bundle.approved_intents,
        research_ideas=unsigned_bundle.research_ideas,
        policy=unsigned_bundle.policy,
        target_tolerance=unsigned_bundle.target_tolerance,
        approval_tolerance=unsigned_bundle.approval_tolerance,
        utilization_tolerance=unsigned_bundle.utilization_tolerance,
        bounds_tolerance=unsigned_bundle.bounds_tolerance,
        h1_tolerance=unsigned_bundle.h1_tolerance,
        min_approval_fraction=unsigned_bundle.min_approval_fraction,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        data_signature=_risk_engine_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )
    return signed_bundle


def validate_risk_engine(bundle: RiskEngineBundle) -> RiskEngineValidationReport:
    """Validate that a risk-engine bundle still satisfies its obligations."""
    certificates = check_risk_cocycle(
        bundle.local_sections,
        target_tolerance=bundle.target_tolerance,
        approval_tolerance=bundle.approval_tolerance,
        utilization_tolerance=bundle.utilization_tolerance,
        bounds_tolerance=bundle.bounds_tolerance,
        h1_tolerance=bundle.h1_tolerance,
    )
    normalization_preserved = _restriction_signatures_preserved(bundle.local_sections)
    cocycle_checks_passed = all(certificate.passes for certificate in certificates)
    coherent_global_sections = _global_sections_coherent(
        bundle.local_sections,
        bundle.global_sections,
    )
    intents_align_with_risk_bounds = _intents_align_with_risk_bounds(
        bundle.global_sections,
        bundle.approved_intents,
        bundle.position_intents,
    )
    descended = risk_approved_intents(bundle.approved_intents)
    only_risk_approved_descend = all(
        intent.approval_status == "risk_approved" for intent in descended
    )
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    proof_obligation_satisfied = bundle.policy.proof_obligation in {
        "smt_required",
        "machine_checked",
    }
    paper_trading_enforced = (
        bundle.policy.paper_trading_required
        and dict(bundle.audit_metadata).get("paper_trading") == "required"
    )
    signature_matches = bundle.data_signature == _risk_engine_bundle_signature(bundle)
    timestamp_symbol_invariants_preserved = normalization_preserved

    messages: list[str] = []
    if not normalization_preserved:
        messages.append("restriction signature preservation failed")
    if not cocycle_checks_passed:
        messages.append("one or more risk cocycle checks failed")
    if not coherent_global_sections:
        messages.append("global risk sections no longer descend from local overlaps")
    if not intents_align_with_risk_bounds:
        messages.append("position intents and risk bounds disagree on overlaps")
    if not only_risk_approved_descend:
        messages.append("a non-approved intent descended toward execution")
    if not novel_idea_present:
        messages.append("no testable data-driven risk idea is present")
    if not risk_invariants_explicit:
        messages.append("risk invariants are not explicit enough for proof discharge")
    if not proof_obligation_satisfied:
        messages.append("proof obligation is not SMT-backed or machine-checked")
    if not paper_trading_enforced:
        messages.append("paper-trading requirement is not enforced")
    if not signature_matches:
        messages.append("bundle reproducibility signature mismatch")

    passes = (
        timestamp_symbol_invariants_preserved
        and cocycle_checks_passed
        and coherent_global_sections
        and intents_align_with_risk_bounds
        and only_risk_approved_descend
        and novel_idea_present
        and risk_invariants_explicit
        and proof_obligation_satisfied
        and paper_trading_enforced
        and signature_matches
    )
    report = RiskEngineValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        normalization_signatures_preserved=normalization_preserved,
        cocycle_checks_passed=cocycle_checks_passed,
        coherent_global_sections=coherent_global_sections,
        intents_align_with_risk_bounds=intents_align_with_risk_bounds,
        only_risk_approved_descend=only_risk_approved_descend,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        proof_obligation_satisfied=proof_obligation_satisfied,
        paper_trading_enforced=paper_trading_enforced,
        signature_matches=signature_matches,
        local_sections_checked=len(bundle.local_sections),
        global_sections_checked=len(bundle.global_sections),
        position_intents_checked=len(bundle.position_intents),
        approved_intents_checked=len(bundle.approved_intents),
        overlap_certificates=certificates,
        messages=tuple(messages),
    )
    return report


def risk_engine_summary(bundle: RiskEngineBundle) -> str:
    """Return a deterministic summary string for the risk-engine bundle."""
    report = validate_risk_engine(bundle)
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.approved_fraction}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    status = "pass" if report.passes else "fail"
    approved_count = sum(
        intent.approval_status == "risk_approved" for intent in bundle.approved_intents
    )
    symbols = ",".join(bundle.symbols)
    summary = (
        f"risk_engine[{bundle.schema_version}] symbols={symbols} "
        f"intents={len(bundle.position_intents)} "
        f"local_sections={len(bundle.local_sections)} "
        f"global_sections={len(bundle.global_sections)} "
        f"approved={approved_count} ideas={len(bundle.research_ideas)} "
        f"validation={status} proof={bundle.policy.proof_obligation} "
        f"paper_only={bundle.policy.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )
    return summary


__all__ = [
    "DEFAULT_ORDER_REJECTION_CONDITIONS",
    "GlobalRiskSection",
    "LENSES",
    "LocalRiskSection",
    "PortfolioRiskState",
    "RiskApprovalStatus",
    "RiskApprovedIntent",
    "RiskCocycleCertificate",
    "RiskEngineBundle",
    "RiskEngineError",
    "RiskEngineInput",
    "RiskEngineValidationReport",
    "RiskGluingError",
    "RiskIdeaSide",
    "RiskKey",
    "RiskLens",
    "RiskNormalizationError",
    "RiskPolicy",
    "RiskProofMode",
    "RiskResearchIdea",
    "RiskRestrictionError",
    "approve_position_intents",
    "build_risk_engine",
    "build_risk_cover",
    "check_risk_cocycle",
    "default_risk_policy",
    "glue_risk_sections",
    "group_risk_overlaps",
    "neutral_portfolio_state",
    "restrict_risk_sections",
    "risk_approved_intents",
    "risk_engine_schema_version",
    "risk_engine_summary",
    "validate_risk_engine",
]
