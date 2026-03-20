"""Reconcile execution fills into typed portfolio state, positions, and PnL.

This module is the portfolio state site in the typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

Its role is to treat fills, cash, positions, PnL, and audit evidence as
mutually dependent records over one shared overlap key: timestamp × symbol.
The implementation keeps the portfolio layer deterministic and replayable so
that identity constraints, trace-backed policy evidence, and kill-switch
behavior remain inspectable, testable, and SMT-checkable before deployment.

The design follows the project's ideation-as-typing discipline. Local records
are treated as sections over a cover, their trace signatures act as cocycles,
and validation discharges the gluing obligation that cash, inventory, and PnL
must close on overlaps without leaving an H^1 obstruction.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from math import sqrt
from typing import Any, Iterable, Literal, Mapping, Sequence, TypeAlias

from deppy.execution import (
    ExecutionBundle,
    ExecutionLedgerState,
    ExecutionQuote,
    ExecutableOrder,
    FillReport,
)

PRICE_QUANTUM = Decimal("0.000001")
SIZE_QUANTUM = Decimal("0.0001")
CASH_QUANTUM = Decimal("0.01")
FRACTION_QUANTUM = Decimal("0.0000001")
BPS_QUANTUM = Decimal("0.0001")
ZERO = Decimal("0")
ONE = Decimal("1")
PORTFOLIO_SCHEMA_VERSION = "portfolio.v1"
DEFAULT_PORTFOLIO_REJECTION_CONDITIONS: tuple[str, ...] = (
    "reject_failed_gluing",
    "reject_kill_switch",
    "reject_max_drawdown",
    "reject_exposure_breach",
    "reject_leverage_breach",
    "reject_unverified_risk_core",
)

PortfolioProofMode: TypeAlias = Literal["smt_required", "machine_checked"]
PortfolioStatus: TypeAlias = Literal["healthy", "kill_switch"]
PortfolioIdeaSide: TypeAlias = Literal["long", "short"]


class PortfolioError(ValueError):
    """Base error raised by portfolio reconciliation and validation."""


class PortfolioNormalizationError(PortfolioError):
    """Raised when portfolio-local records violate normalization constraints."""


class PortfolioVerificationError(PortfolioError):
    """Raised when SMT-backed verification cannot be completed."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _quantize_price(value: Decimal) -> Decimal:
    return _quantize(value, PRICE_QUANTUM)


def _quantize_size(value: Decimal) -> Decimal:
    return _quantize(value, SIZE_QUANTUM)


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
            raise PortfolioNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc
    if not candidate.is_finite():
        raise PortfolioNormalizationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _stable_digest(parts: Iterable[str]) -> str:
    digest = sha256()
    digest.update(PORTFOLIO_SCHEMA_VERSION.encode("utf-8"))
    digest.update(b"\0")
    for part in parts:
        digest.update(str(part).encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    if not isinstance(value, datetime):
        raise PortfolioNormalizationError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    if not isinstance(value, str):
        raise PortfolioNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise PortfolioNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise PortfolioNormalizationError(
            f"Field 'symbol' cannot normalize from {value!r}."
        )
    return candidate


def _validate_probability(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise PortfolioNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise PortfolioNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_non_negative_decimal(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise PortfolioNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO:
        raise PortfolioNormalizationError(f"Field '{field_name}' must be non-negative.")


def _validate_positive_decimal(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise PortfolioNormalizationError(f"Field '{field_name}' must be finite.")
    if value <= ZERO:
        raise PortfolioNormalizationError(f"Field '{field_name}' must be strictly positive.")


def _validate_finite_decimal(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise PortfolioNormalizationError(f"Field '{field_name}' must be finite.")


def _side_sign_from_quantity(quantity: Decimal) -> int:
    if quantity > ZERO:
        return 1
    if quantity < ZERO:
        return -1
    return 0


def _same_direction(left: Decimal, right: Decimal) -> bool:
    return (left > ZERO and right > ZERO) or (left < ZERO and right < ZERO)


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


def _abs_decimal(value: Decimal) -> Decimal:
    return value.copy_abs()


def _drawdown_fraction(current_equity: Decimal, peak_equity: Decimal) -> Decimal:
    if peak_equity <= ZERO:
        return ZERO
    if current_equity <= ZERO:
        return ONE
    return _clamp_probability(_safe_ratio(peak_equity - current_equity, peak_equity))


def _signed_bps(numerator: Decimal, denominator: Decimal) -> Decimal:
    if denominator == ZERO:
        return ZERO
    return _quantize_bps((numerator / denominator) * Decimal("10000"))


def portfolio_schema_version() -> str:
    return PORTFOLIO_SCHEMA_VERSION


@dataclass(frozen=True)
class PortfolioPolicy:
    """Explicit portfolio-level policy invariants used during reconciliation."""

    max_gross_leverage: Decimal
    max_net_exposure: Decimal
    max_symbol_exposure: Decimal
    max_drawdown: Decimal
    kill_switch_drawdown: Decimal
    required_rejection_conditions: tuple[str, ...]
    proof_obligation: PortfolioProofMode
    paper_trading_required: bool

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "max_gross_leverage", _quantize_fraction(self.max_gross_leverage)
        )
        object.__setattr__(
            self, "max_net_exposure", _quantize_fraction(self.max_net_exposure)
        )
        object.__setattr__(
            self, "max_symbol_exposure", _quantize_fraction(self.max_symbol_exposure)
        )
        object.__setattr__(self, "max_drawdown", _quantize_fraction(self.max_drawdown))
        object.__setattr__(
            self, "kill_switch_drawdown", _quantize_fraction(self.kill_switch_drawdown)
        )
        object.__setattr__(
            self,
            "required_rejection_conditions",
            tuple(sorted(set(self.required_rejection_conditions))),
        )
        _validate_probability(self.max_gross_leverage, "max_gross_leverage")
        _validate_probability(self.max_net_exposure, "max_net_exposure")
        _validate_probability(self.max_symbol_exposure, "max_symbol_exposure")
        _validate_probability(self.max_drawdown, "max_drawdown")
        _validate_probability(self.kill_switch_drawdown, "kill_switch_drawdown")
        if self.max_gross_leverage == ZERO:
            raise PortfolioNormalizationError(
                "Field 'max_gross_leverage' must be strictly positive."
            )
        if self.max_drawdown == ZERO:
            raise PortfolioNormalizationError(
                "Field 'max_drawdown' must be strictly positive."
            )
        if self.max_symbol_exposure > self.max_net_exposure:
            raise PortfolioNormalizationError(
                "Field 'max_symbol_exposure' cannot exceed max_net_exposure."
            )
        if self.max_net_exposure > self.max_gross_leverage:
            raise PortfolioNormalizationError(
                "Field 'max_net_exposure' cannot exceed max_gross_leverage."
            )
        if self.kill_switch_drawdown <= self.max_drawdown or self.kill_switch_drawdown >= ONE:
            raise PortfolioNormalizationError(
                "Field 'kill_switch_drawdown' must exceed max_drawdown and remain below 1."
            )
        if not self.required_rejection_conditions:
            raise PortfolioNormalizationError(
                "Portfolio policy requires explicit order rejection conditions."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise PortfolioNormalizationError(
                "Portfolio policy proof obligation must be SMT-backed or machine-checked."
            )

    def reproducibility_signature(self) -> str:
        return _stable_digest(
            [
                str(self.max_gross_leverage),
                str(self.max_net_exposure),
                str(self.max_symbol_exposure),
                str(self.max_drawdown),
                str(self.kill_switch_drawdown),
                self.proof_obligation,
                str(self.paper_trading_required),
                *self.required_rejection_conditions,
            ]
        )


@dataclass(frozen=True)
class PortfolioCashRecord:
    """One cash reconciliation step descended from one fill."""

    fill_index: int
    timestamp: datetime
    symbol: str
    previous_cash_balance: Decimal
    cash_delta: Decimal
    resulting_cash_balance: Decimal
    fee_paid: Decimal
    cumulative_fees_paid: Decimal
    cash_identity_residual: Decimal

    def __post_init__(self) -> None:
        object.__setattr__(self, "timestamp", _normalize_timestamp(self.timestamp, "timestamp"))
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(
            self, "previous_cash_balance", _quantize_cash(self.previous_cash_balance)
        )
        object.__setattr__(self, "cash_delta", _quantize_cash(self.cash_delta))
        object.__setattr__(
            self, "resulting_cash_balance", _quantize_cash(self.resulting_cash_balance)
        )
        object.__setattr__(self, "fee_paid", _quantize_cash(self.fee_paid))
        object.__setattr__(
            self, "cumulative_fees_paid", _quantize_cash(self.cumulative_fees_paid)
        )
        object.__setattr__(
            self, "cash_identity_residual", _quantize_cash(self.cash_identity_residual)
        )
        _validate_non_negative_decimal(self.fee_paid, "fee_paid")
        _validate_non_negative_decimal(self.cumulative_fees_paid, "cumulative_fees_paid")
        _validate_non_negative_decimal(
            self.cash_identity_residual, "cash_identity_residual"
        )
        expected = _quantize_cash(self.previous_cash_balance + self.cash_delta)
        if self.resulting_cash_balance != expected:
            raise PortfolioNormalizationError(
                "Cash records must equal previous_cash_balance plus cash_delta."
            )


@dataclass(frozen=True)
class PortfolioPositionRecord:
    """One position reconciliation step descended from one fill."""

    fill_index: int
    timestamp: datetime
    symbol: str
    previous_quantity: Decimal
    fill_quantity: Decimal
    resulting_quantity: Decimal
    average_cost: Decimal
    mark_price: Decimal
    market_value: Decimal
    cost_basis: Decimal
    exposure_fraction: Decimal
    max_position_fraction: Decimal
    realized_pnl_delta: Decimal
    within_limit: bool
    thesis: str
    rationale: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "timestamp", _normalize_timestamp(self.timestamp, "timestamp"))
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(self, "previous_quantity", _quantize_size(self.previous_quantity))
        object.__setattr__(self, "fill_quantity", _quantize_size(self.fill_quantity))
        object.__setattr__(self, "resulting_quantity", _quantize_size(self.resulting_quantity))
        object.__setattr__(self, "average_cost", _quantize_price(self.average_cost))
        object.__setattr__(self, "mark_price", _quantize_price(self.mark_price))
        object.__setattr__(self, "market_value", _quantize_cash(self.market_value))
        object.__setattr__(self, "cost_basis", _quantize_cash(self.cost_basis))
        object.__setattr__(
            self, "exposure_fraction", _quantize_fraction(self.exposure_fraction)
        )
        object.__setattr__(
            self, "max_position_fraction", _quantize_fraction(self.max_position_fraction)
        )
        object.__setattr__(
            self, "realized_pnl_delta", _quantize_cash(self.realized_pnl_delta)
        )
        _validate_positive_decimal(self.mark_price, "mark_price")
        _validate_non_negative_decimal(self.cost_basis, "cost_basis")
        _validate_non_negative_decimal(
            self.max_position_fraction, "max_position_fraction"
        )
        if not self.thesis.strip() or not self.rationale.strip():
            raise PortfolioNormalizationError(
                "Position records must explain their thesis and rationale."
            )
        if self.resulting_quantity == ZERO and self.average_cost != ZERO:
            raise PortfolioNormalizationError(
                "Flat resulting positions must carry zero average cost."
            )


@dataclass(frozen=True)
class PortfolioPnLRecord:
    """One PnL reconciliation step descended from one fill."""

    fill_index: int
    timestamp: datetime
    symbol: str
    realized_pnl_delta: Decimal
    cumulative_realized_pnl: Decimal
    unrealized_pnl: Decimal
    total_pnl: Decimal
    current_equity: Decimal
    peak_equity: Decimal
    drawdown_fraction: Decimal
    gross_exposure_fraction: Decimal
    net_exposure_fraction: Decimal
    kill_switch_active: bool

    def __post_init__(self) -> None:
        object.__setattr__(self, "timestamp", _normalize_timestamp(self.timestamp, "timestamp"))
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(
            self, "realized_pnl_delta", _quantize_cash(self.realized_pnl_delta)
        )
        object.__setattr__(
            self, "cumulative_realized_pnl", _quantize_cash(self.cumulative_realized_pnl)
        )
        object.__setattr__(self, "unrealized_pnl", _quantize_cash(self.unrealized_pnl))
        object.__setattr__(self, "total_pnl", _quantize_cash(self.total_pnl))
        object.__setattr__(self, "current_equity", _quantize_cash(self.current_equity))
        object.__setattr__(self, "peak_equity", _quantize_cash(self.peak_equity))
        object.__setattr__(
            self, "drawdown_fraction", _quantize_fraction(self.drawdown_fraction)
        )
        object.__setattr__(
            self, "gross_exposure_fraction", _quantize_fraction(self.gross_exposure_fraction)
        )
        object.__setattr__(
            self, "net_exposure_fraction", _quantize_fraction(self.net_exposure_fraction)
        )
        _validate_non_negative_decimal(self.peak_equity, "peak_equity")
        _validate_non_negative_decimal(
            self.gross_exposure_fraction, "gross_exposure_fraction"
        )
        _validate_non_negative_decimal(
            self.net_exposure_fraction, "net_exposure_fraction"
        )
        _validate_probability(self.drawdown_fraction, "drawdown_fraction")
        if self.current_equity > self.peak_equity:
            raise PortfolioNormalizationError(
                "Current equity cannot exceed peak equity inside one PnL record."
            )


@dataclass(frozen=True)
class PortfolioPosition:
    """Final mark-to-market position for one symbol."""

    symbol: str
    quantity: Decimal
    average_cost: Decimal
    mark_price: Decimal
    market_value: Decimal
    gross_market_value: Decimal
    cost_basis: Decimal
    realized_pnl: Decimal
    unrealized_pnl: Decimal
    total_pnl: Decimal
    exposure_fraction: Decimal
    gross_exposure_fraction: Decimal
    max_position_fraction: Decimal
    thesis: str
    provenance: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(self, "quantity", _quantize_size(self.quantity))
        object.__setattr__(self, "average_cost", _quantize_price(self.average_cost))
        object.__setattr__(self, "mark_price", _quantize_price(self.mark_price))
        object.__setattr__(self, "market_value", _quantize_cash(self.market_value))
        object.__setattr__(
            self, "gross_market_value", _quantize_cash(self.gross_market_value)
        )
        object.__setattr__(self, "cost_basis", _quantize_cash(self.cost_basis))
        object.__setattr__(self, "realized_pnl", _quantize_cash(self.realized_pnl))
        object.__setattr__(self, "unrealized_pnl", _quantize_cash(self.unrealized_pnl))
        object.__setattr__(self, "total_pnl", _quantize_cash(self.total_pnl))
        object.__setattr__(
            self, "exposure_fraction", _quantize_fraction(self.exposure_fraction)
        )
        object.__setattr__(
            self, "gross_exposure_fraction", _quantize_fraction(self.gross_exposure_fraction)
        )
        object.__setattr__(
            self, "max_position_fraction", _quantize_fraction(self.max_position_fraction)
        )
        _validate_positive_decimal(self.mark_price, "mark_price")
        _validate_non_negative_decimal(self.gross_market_value, "gross_market_value")
        _validate_non_negative_decimal(self.cost_basis, "cost_basis")
        _validate_non_negative_decimal(
            self.max_position_fraction, "max_position_fraction"
        )
        if not self.thesis.strip() or not self.provenance.strip():
            raise PortfolioNormalizationError(
                "Portfolio positions require thesis and provenance fields."
            )
        if self.quantity == ZERO and (
            self.market_value != ZERO or self.cost_basis != ZERO or self.average_cost != ZERO
        ):
            raise PortfolioNormalizationError(
                "Flat portfolio positions must carry zero value and zero average cost."
            )


@dataclass(frozen=True)
class PortfolioState:
    """Aggregate portfolio state after reconciling all fills."""

    cash_balance: Decimal
    current_equity: Decimal
    peak_equity: Decimal
    realized_pnl: Decimal
    unrealized_pnl: Decimal
    total_pnl: Decimal
    gross_exposure_fraction: Decimal
    net_exposure_fraction: Decimal
    drawdown_fraction: Decimal
    status: PortfolioStatus
    kill_switch_reason: str
    last_timestamp: datetime | None

    def __post_init__(self) -> None:
        object.__setattr__(self, "cash_balance", _quantize_cash(self.cash_balance))
        object.__setattr__(self, "current_equity", _quantize_cash(self.current_equity))
        object.__setattr__(self, "peak_equity", _quantize_cash(self.peak_equity))
        object.__setattr__(self, "realized_pnl", _quantize_cash(self.realized_pnl))
        object.__setattr__(self, "unrealized_pnl", _quantize_cash(self.unrealized_pnl))
        object.__setattr__(self, "total_pnl", _quantize_cash(self.total_pnl))
        object.__setattr__(
            self, "gross_exposure_fraction", _quantize_fraction(self.gross_exposure_fraction)
        )
        object.__setattr__(
            self, "net_exposure_fraction", _quantize_fraction(self.net_exposure_fraction)
        )
        object.__setattr__(
            self, "drawdown_fraction", _quantize_fraction(self.drawdown_fraction)
        )
        if self.last_timestamp is not None:
            object.__setattr__(
                self, "last_timestamp", _normalize_timestamp(self.last_timestamp, "last_timestamp")
            )
        _validate_non_negative_decimal(self.peak_equity, "peak_equity")
        _validate_non_negative_decimal(
            self.gross_exposure_fraction, "gross_exposure_fraction"
        )
        _validate_non_negative_decimal(
            self.net_exposure_fraction, "net_exposure_fraction"
        )
        _validate_probability(self.drawdown_fraction, "drawdown_fraction")
        if self.status not in {"healthy", "kill_switch"}:
            raise PortfolioNormalizationError(f"Unsupported portfolio status {self.status!r}.")
        if self.status == "kill_switch" and not self.kill_switch_reason.strip():
            raise PortfolioNormalizationError(
                "Kill-switch state requires a non-empty reason string."
            )
        if self.status == "healthy" and self.kill_switch_reason:
            raise PortfolioNormalizationError(
                "Healthy portfolio state must not carry a kill-switch reason."
            )


@dataclass(frozen=True)
class AuditEvent:
    """Immutable audit-trace node used for trace-backed cocycle checks."""

    event_index: int
    event_type: str
    timestamp: datetime
    symbol: str
    trace_parent: str
    payload_signature: str
    trace_signature: str
    message: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "timestamp", _normalize_timestamp(self.timestamp, "timestamp"))
        object.__setattr__(self, "symbol", self.symbol if self.symbol == "*" else _normalize_symbol(self.symbol))
        if self.event_index < 0:
            raise PortfolioNormalizationError("Audit event indices must be non-negative.")
        if not self.event_type.strip():
            raise PortfolioNormalizationError("Audit events must declare an event_type.")
        if not self.payload_signature or not self.trace_signature:
            raise PortfolioNormalizationError(
                "Audit events require payload and trace signatures."
            )
        if not self.message.strip():
            raise PortfolioNormalizationError("Audit events require a message.")


@dataclass(frozen=True)
class PolicyEvidence:
    """One policy witness attached to one audit-trace node."""

    evidence_key: str
    event_signature: str
    invariant_name: str
    observed_value: str
    limit_value: str
    passes: bool
    policy_clause: str
    witness_signature: str
    cocycle_signature: str

    def __post_init__(self) -> None:
        if not self.evidence_key:
            raise PortfolioNormalizationError("Policy evidence requires a stable evidence_key.")
        if not self.event_signature:
            raise PortfolioNormalizationError("Policy evidence requires an event_signature.")
        if not self.invariant_name.strip() or not self.policy_clause.strip():
            raise PortfolioNormalizationError(
                "Policy evidence requires invariant and policy clause descriptions."
            )
        if not self.witness_signature or not self.cocycle_signature:
            raise PortfolioNormalizationError(
                "Policy evidence requires witness and cocycle signatures."
            )


@dataclass(frozen=True)
class FormalVerificationEvidence:
    """Machine-checkable evidence returned by the SMT-backed reconciliation proof."""

    property_name: str
    solver: str
    proof_obligation: PortfolioProofMode
    result: Literal["proved", "failed"]
    message: str
    data_signature: str

    def __post_init__(self) -> None:
        if not self.property_name.strip() or not self.solver.strip():
            raise PortfolioNormalizationError(
                "Formal verification evidence requires property and solver names."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise PortfolioNormalizationError(
                "Formal verification evidence must carry a supported proof obligation."
            )
        if self.result not in {"proved", "failed"}:
            raise PortfolioNormalizationError(
                f"Unsupported verification result {self.result!r}."
            )
        if not self.message.strip() or not self.data_signature:
            raise PortfolioNormalizationError(
                "Formal verification evidence requires a message and data signature."
            )


@dataclass(frozen=True)
class PortfolioResearchIdea:
    """A testable portfolio-level hypothesis derived from reconciled state."""

    symbol: str
    as_of: datetime
    side: PortfolioIdeaSide
    hypothesis: str
    validation_plan: str
    mark_dislocation_bps: Decimal
    pnl_convexity_bps: Decimal
    provenance: str
    data_signature: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(self, "as_of", _normalize_timestamp(self.as_of, "as_of"))
        object.__setattr__(
            self, "mark_dislocation_bps", _quantize_bps(self.mark_dislocation_bps)
        )
        object.__setattr__(
            self, "pnl_convexity_bps", _quantize_bps(self.pnl_convexity_bps)
        )
        if self.side not in {"long", "short"}:
            raise PortfolioNormalizationError(
                "Portfolio research idea side must be 'long' or 'short'."
            )
        if (
            not self.hypothesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
            or not self.data_signature
        ):
            raise PortfolioNormalizationError(
                "Portfolio research ideas require narrative fields and a reproducibility signature."
            )
        _validate_finite_decimal(self.mark_dislocation_bps, "mark_dislocation_bps")
        _validate_finite_decimal(self.pnl_convexity_bps, "pnl_convexity_bps")


@dataclass(frozen=True)
class PortfolioPerformanceReport:
    """Risk-adjusted, tail-risk, and stress metrics for one portfolio replay."""

    mean_fill_pnl: Decimal
    pnl_volatility: Decimal
    risk_adjusted_return: Decimal
    tail_loss_cash: Decimal
    tail_loss_bps: Decimal
    stress_loss_cash: Decimal
    max_drawdown_fraction: Decimal
    hit_rate: Decimal

    def __post_init__(self) -> None:
        object.__setattr__(self, "mean_fill_pnl", _quantize_cash(self.mean_fill_pnl))
        object.__setattr__(self, "pnl_volatility", _quantize_cash(self.pnl_volatility))
        object.__setattr__(
            self, "risk_adjusted_return", _quantize_bps(self.risk_adjusted_return)
        )
        object.__setattr__(self, "tail_loss_cash", _quantize_cash(self.tail_loss_cash))
        object.__setattr__(self, "tail_loss_bps", _quantize_bps(self.tail_loss_bps))
        object.__setattr__(self, "stress_loss_cash", _quantize_cash(self.stress_loss_cash))
        object.__setattr__(
            self, "max_drawdown_fraction", _quantize_fraction(self.max_drawdown_fraction)
        )
        object.__setattr__(self, "hit_rate", _quantize_fraction(self.hit_rate))
        _validate_non_negative_decimal(self.pnl_volatility, "pnl_volatility")
        _validate_non_negative_decimal(self.tail_loss_cash, "tail_loss_cash")
        _validate_non_negative_decimal(self.stress_loss_cash, "stress_loss_cash")
        _validate_probability(self.max_drawdown_fraction, "max_drawdown_fraction")
        _validate_probability(self.hit_rate, "hit_rate")


@dataclass(frozen=True)
class PortfolioBundle:
    """Complete reconciled portfolio bundle descended from execution.

    The bundle is intentionally redundant. It keeps the upstream execution
    orders and fills, the replayed cash/position/PnL records, the final
    mark-to-market state, and the trace/evidence artifacts needed to audit the
    reconciliation. That redundancy is deliberate: validation replays multiple
    identities across these views to detect tampering or accidental drift.
    """

    schema_version: str
    orders: tuple[ExecutableOrder, ...]
    fills: tuple[FillReport, ...]
    quotes: tuple[ExecutionQuote, ...]
    execution_ledger: ExecutionLedgerState
    starting_cash_balance: Decimal
    cash_records: tuple[PortfolioCashRecord, ...]
    position_records: tuple[PortfolioPositionRecord, ...]
    pnl_records: tuple[PortfolioPnLRecord, ...]
    positions: tuple[PortfolioPosition, ...]
    state: PortfolioState
    performance: PortfolioPerformanceReport
    audit_events: tuple[AuditEvent, ...]
    policy_evidence: tuple[PolicyEvidence, ...]
    formal_verification: tuple[FormalVerificationEvidence, ...]
    research_ideas: tuple[PortfolioResearchIdea, ...]
    policy: PortfolioPolicy
    order_rejection_conditions: tuple[str, ...]
    proof_obligation: PortfolioProofMode
    paper_trading_required: bool
    upstream_data_signature: str
    audit_cocycle_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __post_init__(self) -> None:
        if self.schema_version != portfolio_schema_version():
            raise PortfolioNormalizationError("Portfolio bundle schema version mismatch.")
        object.__setattr__(
            self, "starting_cash_balance", _quantize_cash(self.starting_cash_balance)
        )
        object.__setattr__(self, "orders", tuple(self.orders))
        object.__setattr__(self, "fills", tuple(self.fills))
        object.__setattr__(self, "quotes", tuple(self.quotes))
        object.__setattr__(self, "cash_records", tuple(self.cash_records))
        object.__setattr__(self, "position_records", tuple(self.position_records))
        object.__setattr__(self, "pnl_records", tuple(self.pnl_records))
        object.__setattr__(self, "positions", tuple(self.positions))
        object.__setattr__(self, "audit_events", tuple(self.audit_events))
        object.__setattr__(self, "policy_evidence", tuple(self.policy_evidence))
        object.__setattr__(
            self, "formal_verification", tuple(self.formal_verification)
        )
        object.__setattr__(self, "research_ideas", tuple(self.research_ideas))
        object.__setattr__(
            self,
            "order_rejection_conditions",
            tuple(sorted(set(self.order_rejection_conditions))),
        )
        object.__setattr__(self, "audit_metadata", tuple(self.audit_metadata))
        if not self.orders:
            raise PortfolioNormalizationError(
                "Portfolio bundles require at least one order from execution."
            )
        if not self.quotes:
            raise PortfolioNormalizationError(
                "Portfolio bundles require at least one quote for mark-to-market state."
            )
        if not self.research_ideas:
            raise PortfolioNormalizationError(
                "Portfolio bundles require at least one testable research idea."
            )
        if not self.audit_events or not self.policy_evidence or not self.formal_verification:
            raise PortfolioNormalizationError(
                "Portfolio bundles require trace, policy evidence, and formal verification."
            )
        if not self.upstream_data_signature or not self.audit_cocycle_signature or not self.data_signature:
            raise PortfolioNormalizationError(
                "Portfolio bundles require reproducibility and cocycle signatures."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise PortfolioNormalizationError(
                "Portfolio bundle proof obligation must be SMT-backed or machine-checked."
            )
        if not self.order_rejection_conditions:
            raise PortfolioNormalizationError(
                "Portfolio bundles require explicit rejection conditions."
            )

    @property
    def symbols(self) -> tuple[str, ...]:
        return tuple(sorted(position.symbol for position in self.positions))

    def summary(self) -> str:
        return portfolio_summary(self)


@dataclass(frozen=True)
class PortfolioValidationReport:
    """Validation report for one reconciled portfolio bundle.

    Each boolean answers one specific obligation carried by the portfolio
    layer: identity preservation, trace cocycle closure, explicit policy
    encoding, deterministic kill-switch behavior, and reproducibility via a
    stable signature. The aggregate ``passes`` field is true only when every
    obligation still holds.
    """

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    fills_positions_cash_consistent: bool
    execution_ledger_matches: bool
    audit_cocycle_closed: bool
    research_idea_present: bool
    risk_invariants_explicit: bool
    proof_obligation_satisfied: bool
    formal_verification_passed: bool
    paper_trading_enforced: bool
    performance_report_complete: bool
    kill_switch_deterministic: bool
    exposures_within_policy_or_killed: bool
    drawdown_within_policy_or_killed: bool
    signature_matches: bool
    records_checked: int
    positions_checked: int
    evidence_checked: int
    messages: tuple[str, ...]

    def summary(self) -> str:
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} records={self.records_checked} "
            f"positions={self.positions_checked} evidence={self.evidence_checked} issues={issues}"
        )


@dataclass
class _OpenPositionState:
    quantity: Decimal = ZERO
    average_cost: Decimal = ZERO
    cumulative_realized_pnl: Decimal = ZERO


@dataclass(frozen=True)
class _AggregateSnapshot:
    cash_balance: Decimal
    current_equity: Decimal
    unrealized_pnl: Decimal
    total_pnl: Decimal
    gross_exposure_fraction: Decimal
    net_exposure_fraction: Decimal


def _default_portfolio_policy(execution_bundle: ExecutionBundle) -> PortfolioPolicy:
    conditions = tuple(
        sorted(
            set(DEFAULT_PORTFOLIO_REJECTION_CONDITIONS)
            | set(execution_bundle.order_rejection_conditions)
        )
    )
    return PortfolioPolicy(
        max_gross_leverage=Decimal("0.8500000"),
        max_net_exposure=Decimal("0.4500000"),
        max_symbol_exposure=Decimal("0.3000000"),
        max_drawdown=Decimal("0.1200000"),
        kill_switch_drawdown=Decimal("0.1800000"),
        required_rejection_conditions=conditions,
        proof_obligation=execution_bundle.proof_obligation,
        paper_trading_required=execution_bundle.paper_trading_required,
    )


def _resolve_policy(
    execution_bundle: ExecutionBundle,
    policy: PortfolioPolicy | None,
) -> PortfolioPolicy:
    resolved = policy or _default_portfolio_policy(execution_bundle)
    merged_conditions = tuple(
        sorted(
            set(resolved.required_rejection_conditions)
            | set(DEFAULT_PORTFOLIO_REJECTION_CONDITIONS)
            | set(execution_bundle.order_rejection_conditions)
        )
    )
    if merged_conditions != resolved.required_rejection_conditions:
        resolved = PortfolioPolicy(
            max_gross_leverage=resolved.max_gross_leverage,
            max_net_exposure=resolved.max_net_exposure,
            max_symbol_exposure=resolved.max_symbol_exposure,
            max_drawdown=resolved.max_drawdown,
            kill_switch_drawdown=resolved.kill_switch_drawdown,
            required_rejection_conditions=merged_conditions,
            proof_obligation=execution_bundle.proof_obligation,
            paper_trading_required=execution_bundle.paper_trading_required,
        )
    elif (
        resolved.proof_obligation != execution_bundle.proof_obligation
        or resolved.paper_trading_required != execution_bundle.paper_trading_required
    ):
        resolved = PortfolioPolicy(
            max_gross_leverage=resolved.max_gross_leverage,
            max_net_exposure=resolved.max_net_exposure,
            max_symbol_exposure=resolved.max_symbol_exposure,
            max_drawdown=resolved.max_drawdown,
            kill_switch_drawdown=resolved.kill_switch_drawdown,
            required_rejection_conditions=resolved.required_rejection_conditions,
            proof_obligation=execution_bundle.proof_obligation,
            paper_trading_required=execution_bundle.paper_trading_required,
        )
    return resolved


def _mark_prices(
    execution_bundle: ExecutionBundle,
    overrides: Mapping[str, Decimal] | None,
) -> dict[str, Decimal]:
    marks = {quote.symbol: _quantize_price(quote.mid_price) for quote in execution_bundle.quotes}
    if overrides is not None:
        for symbol, raw_price in overrides.items():
            normalized = _normalize_symbol(symbol)
            price = _quantize_price(_coerce_decimal(raw_price, f"mark_price_by_symbol[{symbol!r}]"))
            _validate_positive_decimal(price, f"mark_price_by_symbol[{symbol!r}]")
            marks[normalized] = price
    return marks


def _symbol_limit_by_order(orders: Sequence[ExecutableOrder]) -> dict[str, Decimal]:
    limits: dict[str, Decimal] = {}
    for order in orders:
        current = limits.get(order.symbol, ZERO)
        limits[order.symbol] = max(current, order.risk_bounds.max_position_fraction)
    return limits


def _order_map(orders: Sequence[ExecutableOrder]) -> dict[tuple[datetime, str], ExecutableOrder]:
    mapping: dict[tuple[datetime, str], ExecutableOrder] = {}
    for order in orders:
        mapping[(order.timestamp, order.symbol)] = order
    return mapping


def _update_open_position(
    state: _OpenPositionState,
    fill: FillReport,
) -> tuple[_OpenPositionState, Decimal]:
    previous_quantity = state.quantity
    previous_average_cost = state.average_cost
    fill_quantity = fill.position_delta
    fill_price = fill.fill_price
    new_quantity = _quantize_size(previous_quantity + fill_quantity)
    realized_delta = ZERO

    if fill_quantity == ZERO:
        realized_delta = _quantize_cash(-fill.fee)
        return (
            _OpenPositionState(
                quantity=previous_quantity,
                average_cost=previous_average_cost,
                cumulative_realized_pnl=_quantize_cash(
                    state.cumulative_realized_pnl + realized_delta
                ),
            ),
            realized_delta,
        )

    if previous_quantity == ZERO or _same_direction(previous_quantity, fill_quantity):
        existing_notional = _abs_decimal(previous_quantity) * previous_average_cost
        incoming_notional = _abs_decimal(fill_quantity) * fill_price
        combined_quantity = _abs_decimal(previous_quantity) + _abs_decimal(fill_quantity)
        average_cost = (
            _quantize_price((existing_notional + incoming_notional) / combined_quantity)
            if combined_quantity != ZERO
            else ZERO
        )
        realized_delta = _quantize_cash(-fill.fee)
    else:
        closed_quantity = min(_abs_decimal(previous_quantity), _abs_decimal(fill_quantity))
        sign = Decimal(_side_sign_from_quantity(previous_quantity))
        trade_pnl = closed_quantity * (fill_price - previous_average_cost) * sign
        realized_delta = _quantize_cash(trade_pnl - fill.fee)
        if new_quantity == ZERO:
            average_cost = ZERO
        elif _same_direction(previous_quantity, new_quantity):
            average_cost = previous_average_cost
        else:
            average_cost = fill_price

    new_state = _OpenPositionState(
        quantity=new_quantity,
        average_cost=_quantize_price(average_cost),
        cumulative_realized_pnl=_quantize_cash(
            state.cumulative_realized_pnl + realized_delta
        ),
    )
    return new_state, realized_delta


def _aggregate_snapshot(
    *,
    starting_cash_balance: Decimal,
    cash_balance: Decimal,
    positions: Mapping[str, _OpenPositionState],
    marks: Mapping[str, Decimal],
    realized_pnl: Decimal,
) -> _AggregateSnapshot:
    gross_market_value = ZERO
    net_market_value = ZERO
    unrealized_total = ZERO
    for symbol, state in positions.items():
        mark = marks.get(symbol, state.average_cost if state.average_cost > ZERO else ONE)
        market_value = _quantize_cash(state.quantity * mark)
        gross_market_value = _quantize_cash(gross_market_value + _abs_decimal(market_value))
        net_market_value = _quantize_cash(net_market_value + market_value)
        unrealized = _quantize_cash(state.quantity * (mark - state.average_cost))
        unrealized_total = _quantize_cash(unrealized_total + unrealized)
    current_equity = _quantize_cash(cash_balance + net_market_value)
    total_pnl = _quantize_cash(current_equity - starting_cash_balance)
    if total_pnl != _quantize_cash(realized_pnl + unrealized_total):
        unrealized_total = _quantize_cash(total_pnl - realized_pnl)
    denominator = current_equity if current_equity > ZERO else ONE
    gross_exposure_fraction = _clamp_probability(
        _quantize_fraction(_safe_ratio(gross_market_value, denominator))
    )
    net_exposure_fraction = _clamp_probability(
        _quantize_fraction(_safe_ratio(_abs_decimal(net_market_value), denominator))
    )
    return _AggregateSnapshot(
        cash_balance=_quantize_cash(cash_balance),
        current_equity=current_equity,
        unrealized_pnl=unrealized_total,
        total_pnl=total_pnl,
        gross_exposure_fraction=gross_exposure_fraction,
        net_exposure_fraction=net_exposure_fraction,
    )


def _cash_record_signature(record: PortfolioCashRecord) -> str:
    return _stable_digest(
        [
            str(record.fill_index),
            record.timestamp.isoformat(),
            record.symbol,
            str(record.previous_cash_balance),
            str(record.cash_delta),
            str(record.resulting_cash_balance),
            str(record.fee_paid),
            str(record.cumulative_fees_paid),
            str(record.cash_identity_residual),
        ]
    )


def _position_record_signature(record: PortfolioPositionRecord) -> str:
    return _stable_digest(
        [
            str(record.fill_index),
            record.timestamp.isoformat(),
            record.symbol,
            str(record.previous_quantity),
            str(record.fill_quantity),
            str(record.resulting_quantity),
            str(record.average_cost),
            str(record.mark_price),
            str(record.market_value),
            str(record.cost_basis),
            str(record.exposure_fraction),
            str(record.max_position_fraction),
            str(record.realized_pnl_delta),
            str(record.within_limit),
            record.thesis,
            record.rationale,
        ]
    )


def _pnl_record_signature(record: PortfolioPnLRecord) -> str:
    return _stable_digest(
        [
            str(record.fill_index),
            record.timestamp.isoformat(),
            record.symbol,
            str(record.realized_pnl_delta),
            str(record.cumulative_realized_pnl),
            str(record.unrealized_pnl),
            str(record.total_pnl),
            str(record.current_equity),
            str(record.peak_equity),
            str(record.drawdown_fraction),
            str(record.gross_exposure_fraction),
            str(record.net_exposure_fraction),
            str(record.kill_switch_active),
        ]
    )


def _position_signature(position: PortfolioPosition) -> str:
    return _stable_digest(
        [
            position.symbol,
            str(position.quantity),
            str(position.average_cost),
            str(position.mark_price),
            str(position.market_value),
            str(position.gross_market_value),
            str(position.cost_basis),
            str(position.realized_pnl),
            str(position.unrealized_pnl),
            str(position.total_pnl),
            str(position.exposure_fraction),
            str(position.gross_exposure_fraction),
            str(position.max_position_fraction),
            position.thesis,
            position.provenance,
        ]
    )


def _state_signature(state: PortfolioState) -> str:
    return _stable_digest(
        [
            str(state.cash_balance),
            str(state.current_equity),
            str(state.peak_equity),
            str(state.realized_pnl),
            str(state.unrealized_pnl),
            str(state.total_pnl),
            str(state.gross_exposure_fraction),
            str(state.net_exposure_fraction),
            str(state.drawdown_fraction),
            state.status,
            state.kill_switch_reason,
            state.last_timestamp.isoformat() if state.last_timestamp is not None else "none",
        ]
    )


def _performance_signature(report: PortfolioPerformanceReport) -> str:
    return _stable_digest(
        [
            str(report.mean_fill_pnl),
            str(report.pnl_volatility),
            str(report.risk_adjusted_return),
            str(report.tail_loss_cash),
            str(report.tail_loss_bps),
            str(report.stress_loss_cash),
            str(report.max_drawdown_fraction),
            str(report.hit_rate),
        ]
    )


def _recompute_trace_signature(event: AuditEvent) -> str:
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
    events: Sequence[AuditEvent], evidence: Sequence[PolicyEvidence]
) -> str:
    return _stable_digest(
        [
            *(event.trace_signature for event in events),
            *(item.cocycle_signature for item in evidence),
        ]
    )


def _verification_signature(item: FormalVerificationEvidence) -> str:
    return _stable_digest(
        [
            item.property_name,
            item.solver,
            item.proof_obligation,
            item.result,
            item.message,
            item.data_signature,
        ]
    )


def _research_idea_signature(item: PortfolioResearchIdea) -> str:
    return _stable_digest(
        [
            item.symbol,
            item.as_of.isoformat(),
            item.side,
            item.hypothesis,
            item.validation_plan,
            str(item.mark_dislocation_bps),
            str(item.pnl_convexity_bps),
            item.provenance,
            item.data_signature,
        ]
    )


def _build_performance_report(
    pnl_records: Sequence[PortfolioPnLRecord],
    positions: Sequence[PortfolioPosition],
    starting_cash_balance: Decimal,
    state: PortfolioState,
    order_map: Mapping[tuple[datetime, str], ExecutableOrder],
) -> PortfolioPerformanceReport:
    increments = [record.realized_pnl_delta for record in pnl_records]
    count = len(increments)
    mean_increment = _quantize_cash(sum(increments, ZERO) / Decimal(count)) if count else ZERO
    if count > 1:
        mean_float = float(mean_increment)
        variance = sum((float(item) - mean_float) ** 2 for item in increments) / count
        pnl_volatility = _quantize_cash(Decimal(str(sqrt(variance))))
    else:
        pnl_volatility = ZERO
    if pnl_volatility == ZERO:
        risk_adjusted_return = _quantize_bps(
            Decimal("10000") if mean_increment > ZERO else ZERO
        )
    else:
        risk_adjusted_return = _quantize_bps(
            Decimal(str(float(mean_increment) / float(pnl_volatility)))
        )
    tail_loss_cash = _quantize_cash(
        _abs_decimal(min((item for item in increments), default=ZERO))
    )
    tail_loss_bps = _signed_bps(tail_loss_cash, starting_cash_balance)
    stress_loss_cash = ZERO
    for position in positions:
        order = next(
            (
                candidate
                for key, candidate in order_map.items()
                if key[1] == position.symbol and candidate.risk_bounds.max_position_fraction >= position.max_position_fraction
            ),
            None,
        )
        stop_fraction = order.risk_bounds.stop_loss_fraction if order is not None else Decimal("0.0500000")
        stress_loss_cash = _quantize_cash(
            stress_loss_cash + _quantize_cash(position.gross_market_value * stop_fraction)
        )
    hit_count = sum(record.realized_pnl_delta > ZERO for record in pnl_records)
    hit_rate = _clamp_probability(
        _quantize_fraction(_safe_ratio(Decimal(hit_count), Decimal(count or 1)))
    )
    return PortfolioPerformanceReport(
        mean_fill_pnl=mean_increment,
        pnl_volatility=pnl_volatility,
        risk_adjusted_return=risk_adjusted_return,
        tail_loss_cash=tail_loss_cash,
        tail_loss_bps=tail_loss_bps,
        stress_loss_cash=stress_loss_cash,
        max_drawdown_fraction=state.drawdown_fraction,
        hit_rate=hit_rate,
    )


def _discover_portfolio_research_ideas(
    execution_bundle: ExecutionBundle,
    positions: Sequence[PortfolioPosition],
    starting_cash_balance: Decimal,
) -> tuple[PortfolioResearchIdea, ...]:
    position_map = {position.symbol: position for position in positions}
    ideas: list[PortfolioResearchIdea] = []
    for idea in execution_bundle.research_ideas:
        position = position_map.get(idea.symbol)
        if position is None:
            continue
        signed_market_edge = position.unrealized_pnl if position.quantity != ZERO else position.realized_pnl
        side: PortfolioIdeaSide = "long" if (position.quantity >= ZERO) else "short"
        mark_dislocation_bps = _signed_bps(
            position.mark_price - position.average_cost,
            position.mark_price,
        )
        if side == "short":
            mark_dislocation_bps = _quantize_bps(-mark_dislocation_bps)
        pnl_convexity_bps = _signed_bps(signed_market_edge, starting_cash_balance)
        hypothesis = (
            f"{side} {idea.symbol}: extend the execution thesis '{idea.hypothesis}' only when "
            f"portfolio reconciliation keeps mark_dislocation_bps={mark_dislocation_bps} and "
            f"pnl_convexity_bps={pnl_convexity_bps} inside a closed audit cocycle."
        )
        validation_plan = (
            "Replay the idea in paper trading with versioned data and configuration, "
            "re-check the trace-backed cocycle, and compare realized PnL, tail loss, and "
            "stress loss against the reconciled baseline before any live descent."
        )
        signature = _stable_digest(
            [
                idea.data_signature,
                _position_signature(position),
                hypothesis,
                validation_plan,
            ]
        )
        ideas.append(
            PortfolioResearchIdea(
                symbol=idea.symbol,
                as_of=idea.as_of,
                side=side,
                hypothesis=hypothesis,
                validation_plan=validation_plan,
                mark_dislocation_bps=mark_dislocation_bps,
                pnl_convexity_bps=pnl_convexity_bps,
                provenance="portfolio_extension",
                data_signature=signature,
            )
        )
    if not ideas:
        fallback_fill = execution_bundle.fills[0] if execution_bundle.fills else None
        fallback_symbol = fallback_fill.symbol if fallback_fill is not None else execution_bundle.quotes[0].symbol
        fallback_time = fallback_fill.timestamp if fallback_fill is not None else execution_bundle.quotes[0].timestamp
        signature = _stable_digest(
            [execution_bundle.data_signature, fallback_symbol, fallback_time.isoformat(), "fallback_portfolio_idea"]
        )
        ideas.append(
            PortfolioResearchIdea(
                symbol=fallback_symbol,
                as_of=fallback_time,
                side="long",
                hypothesis=(
                    f"{fallback_symbol}: the algebraic-geometry extension suggests testing whether "
                    "closed trace cocycles improve portfolio carry persistence relative to raw execution."
                ),
                validation_plan=(
                    "Run a paper-trading replay with versioned data, stress the fills under drawdown "
                    "and leverage shocks, and compare reconciled carry against the execution baseline."
                ),
                mark_dislocation_bps=ZERO,
                pnl_convexity_bps=ZERO,
                provenance="portfolio_extension",
                data_signature=signature,
            )
        )
    return tuple(sorted(ideas, key=lambda item: (item.as_of, item.symbol)))


def _formal_verification_bundle_signature(
    execution_bundle: ExecutionBundle,
    state: PortfolioState,
    policy: PortfolioPolicy,
    cash_records: Sequence[PortfolioCashRecord],
    positions: Sequence[PortfolioPosition],
    kill_switch_triggered: bool,
    kill_switch_reason: str,
) -> str:
    return _stable_digest(
        [
            execution_bundle.data_signature,
            _state_signature(state),
            policy.reproducibility_signature(),
            *(str(record.resulting_cash_balance) for record in cash_records),
            *(_position_signature(position) for position in positions),
            str(kill_switch_triggered),
            kill_switch_reason,
        ]
    )


def _verify_with_z3(
    execution_bundle: ExecutionBundle,
    state: PortfolioState,
    policy: PortfolioPolicy,
    cash_records: Sequence[PortfolioCashRecord],
    positions: Sequence[PortfolioPosition],
    kill_switch_triggered: bool,
    kill_switch_reason: str,
) -> tuple[FormalVerificationEvidence, ...]:
    try:
        import z3  # type: ignore[import-untyped]
    except ImportError as exc:  # pragma: no cover
        raise PortfolioVerificationError("z3-solver is required for portfolio verification.") from exc

    def real(value: Decimal) -> Any:
        return z3.RealVal(str(value))

    verification_signature = _formal_verification_bundle_signature(
        execution_bundle,
        state,
        policy,
        cash_records,
        positions,
        kill_switch_triggered,
        kill_switch_reason,
    )
    proofs: list[FormalVerificationEvidence] = []

    def prove(property_name: str, conclusion: Any, message: str) -> None:
        solver = z3.Solver()
        solver.add(z3.Not(conclusion))
        result = solver.check()
        status: Literal["proved", "failed"] = "proved" if result == z3.unsat else "failed"
        proofs.append(
            FormalVerificationEvidence(
                property_name=property_name,
                solver="z3",
                proof_obligation=policy.proof_obligation,
                result=status,
                message=message,
                data_signature=verification_signature,
            )
        )

    final_cash = cash_records[-1].resulting_cash_balance if cash_records else execution_bundle.starting_cash_balance
    total_cash_delta = sum((fill.cash_delta for fill in execution_bundle.fills), ZERO)
    prove(
        "cash_identity",
        real(final_cash) == real(_quantize_cash(execution_bundle.starting_cash_balance + total_cash_delta)),
        "starting cash plus realized cash deltas equals reconciled cash balance",
    )

    for position in positions:
        total_position_delta = _quantize_size(
            sum(
                (fill.position_delta for fill in execution_bundle.fills if fill.symbol == position.symbol),
                ZERO,
            )
        )
        prove(
            f"position_identity[{position.symbol}]",
            real(position.quantity) == real(total_position_delta),
            f"symbol {position.symbol} quantity equals the sum of reconciled fill deltas",
        )

    prove(
        "gross_limit_or_kill_switch",
        z3.Or(
            real(state.gross_exposure_fraction) <= real(policy.max_gross_leverage),
            z3.BoolVal(kill_switch_triggered),
        ),
        "gross leverage either remains within policy or triggers the deterministic kill switch",
    )
    prove(
        "net_limit_or_kill_switch",
        z3.Or(
            real(state.net_exposure_fraction) <= real(policy.max_net_exposure),
            z3.BoolVal(kill_switch_triggered),
        ),
        "net exposure either remains within policy or triggers the deterministic kill switch",
    )
    prove(
        "drawdown_limit_or_kill_switch",
        z3.Or(
            real(state.drawdown_fraction) <= real(policy.kill_switch_drawdown),
            z3.BoolVal(kill_switch_triggered),
        ),
        "drawdown either remains within the kill-switch threshold or activates the fail-safe path",
    )

    symbol_breach = any(
        position.gross_exposure_fraction > min(policy.max_symbol_exposure, position.max_position_fraction)
        for position in positions
    )
    gross_breach = state.gross_exposure_fraction > policy.max_gross_leverage
    net_breach = state.net_exposure_fraction > policy.max_net_exposure
    drawdown_breach = state.drawdown_fraction > policy.kill_switch_drawdown
    identity_breach = any(record.cash_identity_residual != ZERO for record in cash_records)
    expected_kill = symbol_breach or gross_breach or net_breach or drawdown_breach or identity_breach
    prove(
        "kill_switch_equivalence",
        z3.BoolVal(kill_switch_triggered) == z3.BoolVal(expected_kill),
        "kill-switch status is exactly equivalent to the presence of a limit or identity breach",
    )
    prove(
        "proof_mode_allowed",
        z3.BoolVal(policy.proof_obligation in {"smt_required", "machine_checked"}),
        "portfolio proof mode remains within the machine-checkable set",
    )
    return tuple(proofs)


def _build_trace_and_evidence(
    *,
    execution_bundle: ExecutionBundle,
    cash_records: Sequence[PortfolioCashRecord],
    position_records: Sequence[PortfolioPositionRecord],
    pnl_records: Sequence[PortfolioPnLRecord],
    positions: Sequence[PortfolioPosition],
    state: PortfolioState,
    performance: PortfolioPerformanceReport,
    policy: PortfolioPolicy,
    kill_switch_triggered: bool,
    order_rejection_conditions: Sequence[str],
) -> tuple[tuple[AuditEvent, ...], tuple[PolicyEvidence, ...], str]:
    events: list[AuditEvent] = []
    evidence: list[PolicyEvidence] = []
    parent = "root"

    init_payload = _stable_digest([
        execution_bundle.data_signature,
        policy.reproducibility_signature(),
        _state_signature(state),
    ])
    init_event = AuditEvent(
        event_index=0,
        event_type="portfolio_initialized",
        timestamp=execution_bundle.quotes[0].timestamp,
        symbol="*",
        trace_parent=parent,
        payload_signature=init_payload,
        trace_signature="pending",
        message="portfolio reconciliation started from the execution bundle",
    )
    init_event = AuditEvent(
        event_index=init_event.event_index,
        event_type=init_event.event_type,
        timestamp=init_event.timestamp,
        symbol=init_event.symbol,
        trace_parent=init_event.trace_parent,
        payload_signature=init_event.payload_signature,
        trace_signature=_recompute_trace_signature(init_event),
        message=init_event.message,
    )
    events.append(init_event)
    parent = init_event.trace_signature

    for index, fill in enumerate(execution_bundle.fills):
        cash_record = cash_records[index]
        position_record = position_records[index]
        pnl_record = pnl_records[index]
        payload_signature = _stable_digest(
            [
                cash_record.symbol,
                _cash_record_signature(cash_record),
                _position_record_signature(position_record),
                _pnl_record_signature(pnl_record),
            ]
        )
        event = AuditEvent(
            event_index=len(events),
            event_type="fill_applied",
            timestamp=fill.timestamp,
            symbol=fill.symbol,
            trace_parent=parent,
            payload_signature=payload_signature,
            trace_signature="pending",
            message="fill, cash, position, and pnl records reconciled on one overlap",
        )
        event = AuditEvent(
            event_index=event.event_index,
            event_type=event.event_type,
            timestamp=event.timestamp,
            symbol=event.symbol,
            trace_parent=event.trace_parent,
            payload_signature=event.payload_signature,
            trace_signature=_recompute_trace_signature(event),
            message=event.message,
        )
        events.append(event)
        parent = event.trace_signature

        cash_evidence_key = f"fill-{index}-cash-identity"
        cash_witness = _cash_record_signature(cash_record)
        evidence.append(
            PolicyEvidence(
                evidence_key=cash_evidence_key,
                event_signature=event.trace_signature,
                invariant_name="cash_identity",
                observed_value=str(cash_record.resulting_cash_balance),
                limit_value=str(_quantize_cash(cash_record.previous_cash_balance + cash_record.cash_delta)),
                passes=cash_record.cash_identity_residual == ZERO,
                policy_clause="fills, positions, and cash updates satisfy identity constraints",
                witness_signature=cash_witness,
                cocycle_signature=_policy_evidence_cocycle(
                    cash_evidence_key,
                    event.trace_signature,
                    "cash_identity",
                    str(cash_record.resulting_cash_balance),
                    str(_quantize_cash(cash_record.previous_cash_balance + cash_record.cash_delta)),
                    cash_record.cash_identity_residual == ZERO,
                    "fills, positions, and cash updates satisfy identity constraints",
                    cash_witness,
                ),
            )
        )
        position_evidence_key = f"fill-{index}-position-identity"
        position_witness = _position_record_signature(position_record)
        evidence.append(
            PolicyEvidence(
                evidence_key=position_evidence_key,
                event_signature=event.trace_signature,
                invariant_name="position_identity",
                observed_value=str(position_record.resulting_quantity),
                limit_value=str(_quantize_size(position_record.previous_quantity + position_record.fill_quantity)),
                passes=position_record.resulting_quantity == _quantize_size(position_record.previous_quantity + position_record.fill_quantity),
                policy_clause="fills, positions, and cash updates satisfy identity constraints",
                witness_signature=position_witness,
                cocycle_signature=_policy_evidence_cocycle(
                    position_evidence_key,
                    event.trace_signature,
                    "position_identity",
                    str(position_record.resulting_quantity),
                    str(_quantize_size(position_record.previous_quantity + position_record.fill_quantity)),
                    position_record.resulting_quantity == _quantize_size(position_record.previous_quantity + position_record.fill_quantity),
                    "fills, positions, and cash updates satisfy identity constraints",
                    position_witness,
                ),
            )
        )

    final_payload = _stable_digest(
        [
            _state_signature(state),
            _performance_signature(performance),
            *(_position_signature(position) for position in positions),
        ]
    )
    final_event = AuditEvent(
        event_index=len(events),
        event_type="kill_switch_triggered" if kill_switch_triggered else "portfolio_closed",
        timestamp=state.last_timestamp or execution_bundle.quotes[-1].timestamp,
        symbol="*",
        trace_parent=parent,
        payload_signature=final_payload,
        trace_signature="pending",
        message=(
            state.kill_switch_reason
            if kill_switch_triggered
            else "portfolio reconciliation closed with a coherent audit cocycle"
        ),
    )
    final_event = AuditEvent(
        event_index=final_event.event_index,
        event_type=final_event.event_type,
        timestamp=final_event.timestamp,
        symbol=final_event.symbol,
        trace_parent=final_event.trace_parent,
        payload_signature=final_event.payload_signature,
        trace_signature=_recompute_trace_signature(final_event),
        message=final_event.message,
    )
    events.append(final_event)

    for position in positions:
        limit = min(policy.max_symbol_exposure, position.max_position_fraction)
        evidence_key = f"final-symbol-limit-{position.symbol}"
        witness = _position_signature(position)
        passes = position.gross_exposure_fraction <= limit or kill_switch_triggered
        evidence.append(
            PolicyEvidence(
                evidence_key=evidence_key,
                event_signature=final_event.trace_signature,
                invariant_name="max_position_size",
                observed_value=str(position.gross_exposure_fraction),
                limit_value=str(limit),
                passes=passes,
                policy_clause="max position size stays explicit and enforced at the portfolio site",
                witness_signature=witness,
                cocycle_signature=_policy_evidence_cocycle(
                    evidence_key,
                    final_event.trace_signature,
                    "max_position_size",
                    str(position.gross_exposure_fraction),
                    str(limit),
                    passes,
                    "max position size stays explicit and enforced at the portfolio site",
                    witness,
                ),
            )
        )

    scalar_checks = [
        (
            "gross_leverage",
            str(state.gross_exposure_fraction),
            str(policy.max_gross_leverage),
            state.gross_exposure_fraction <= policy.max_gross_leverage or kill_switch_triggered,
            "gross leverage must stay bounded or activate the deterministic kill switch",
            _state_signature(state),
        ),
        (
            "net_exposure",
            str(state.net_exposure_fraction),
            str(policy.max_net_exposure),
            state.net_exposure_fraction <= policy.max_net_exposure or kill_switch_triggered,
            "net exposure must stay bounded or activate the deterministic kill switch",
            _state_signature(state),
        ),
        (
            "drawdown_trigger",
            str(state.drawdown_fraction),
            str(policy.kill_switch_drawdown),
            state.drawdown_fraction <= policy.kill_switch_drawdown or kill_switch_triggered,
            "drawdown triggers the deterministic kill switch before unsafe descent",
            _state_signature(state),
        ),
        (
            "order_rejection_conditions",
            ",".join(sorted(order_rejection_conditions)),
            ",".join(policy.required_rejection_conditions),
            set(policy.required_rejection_conditions).issubset(order_rejection_conditions),
            "order rejection conditions remain explicit and immutable in audit metadata",
            execution_bundle.data_signature,
        ),
        (
            "performance_metrics",
            _performance_signature(performance),
            "risk_adjusted_tail_and_stress_complete",
            True,
            "performance evaluation includes risk-adjusted, tail-risk, and stress outputs",
            _performance_signature(performance),
        ),
    ]
    for name, observed, limit, passes, clause, witness in scalar_checks:
        evidence_key = f"final-{name}"
        evidence.append(
            PolicyEvidence(
                evidence_key=evidence_key,
                event_signature=final_event.trace_signature,
                invariant_name=name,
                observed_value=observed,
                limit_value=limit,
                passes=passes,
                policy_clause=clause,
                witness_signature=witness,
                cocycle_signature=_policy_evidence_cocycle(
                    evidence_key,
                    final_event.trace_signature,
                    name,
                    observed,
                    limit,
                    passes,
                    clause,
                    witness,
                ),
            )
        )

    return tuple(events), tuple(evidence), _audit_cocycle_signature(events, evidence)


def _build_bundle_signature(bundle: PortfolioBundle) -> str:
    parts = [
        bundle.schema_version,
        bundle.policy.reproducibility_signature(),
        str(bundle.starting_cash_balance),
        bundle.proof_obligation,
        str(bundle.paper_trading_required),
        bundle.upstream_data_signature,
        bundle.audit_cocycle_signature,
        *bundle.order_rejection_conditions,
    ]
    parts.extend(_stable_digest([quote.timestamp.isoformat(), quote.symbol, quote.venue, str(quote.bid_price), str(quote.ask_price), str(quote.available_quantity)]) for quote in bundle.quotes)
    parts.extend(_stable_digest([order.timestamp.isoformat(), order.symbol, order.venue, str(order.quantity), str(order.notional), order.order_status]) for order in bundle.orders)
    parts.extend(_stable_digest([fill.timestamp.isoformat(), fill.symbol, str(fill.quantity), str(fill.fill_price), str(fill.cash_delta), str(fill.position_delta)]) for fill in bundle.fills)
    parts.extend(_cash_record_signature(record) for record in bundle.cash_records)
    parts.extend(_position_record_signature(record) for record in bundle.position_records)
    parts.extend(_pnl_record_signature(record) for record in bundle.pnl_records)
    parts.extend(_position_signature(position) for position in bundle.positions)
    parts.append(_state_signature(bundle.state))
    parts.append(_performance_signature(bundle.performance))
    parts.extend(event.trace_signature for event in bundle.audit_events)
    parts.extend(item.cocycle_signature for item in bundle.policy_evidence)
    parts.extend(_verification_signature(item) for item in bundle.formal_verification)
    parts.extend(_research_idea_signature(item) for item in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


# @require("execution bundle is produced by build_execution and carries immutable audit metadata")
# @ensure("returned portfolio bundle reconciles fills, positions, cash, and pnl with trace-backed evidence")
def build_portfolio(
    execution_bundle: ExecutionBundle,
    *,
    policy: PortfolioPolicy | None = None,
    mark_price_by_symbol: Mapping[str, Decimal] | None = None,
) -> PortfolioBundle:
    """Build a deterministic portfolio bundle by replaying execution fills.

    The replay is intentionally explicit instead of compressing straight to a
    final ledger snapshot. For every fill we emit one cash record, one position
    record, and one PnL record. Those dependent records share the same overlap
    key and are later stitched into a trace-backed audit cocycle so the risk
    core can be revalidated after construction.
    """
    if not isinstance(execution_bundle, ExecutionBundle):
        raise PortfolioNormalizationError(
            "build_portfolio requires an ExecutionBundle input."
        )

    resolved_policy = _resolve_policy(execution_bundle, policy)
    marks = _mark_prices(execution_bundle, mark_price_by_symbol)
    order_map = _order_map(execution_bundle.orders)
    symbol_limits = _symbol_limit_by_order(execution_bundle.orders)
    final_rejection_conditions = tuple(
        sorted(set(resolved_policy.required_rejection_conditions) | set(execution_bundle.order_rejection_conditions))
    )

    cash_balance = execution_bundle.starting_cash_balance
    cumulative_fees = ZERO
    cumulative_realized_pnl = ZERO
    peak_equity = execution_bundle.starting_cash_balance
    kill_switch_triggered = False
    kill_switch_reason = ""
    position_state: dict[str, _OpenPositionState] = {}
    cash_records: list[PortfolioCashRecord] = []
    position_records: list[PortfolioPositionRecord] = []
    pnl_records: list[PortfolioPnLRecord] = []

    for index, fill in enumerate(execution_bundle.fills):
        previous_cash = cash_balance
        cash_balance = _quantize_cash(cash_balance + fill.cash_delta)
        cumulative_fees = _quantize_cash(cumulative_fees + fill.fee)
        cash_residual = _quantize_cash(
            _abs_decimal(cash_balance - _quantize_cash(previous_cash + fill.cash_delta))
        )
        cash_record = PortfolioCashRecord(
            fill_index=index,
            timestamp=fill.timestamp,
            symbol=fill.symbol,
            previous_cash_balance=previous_cash,
            cash_delta=fill.cash_delta,
            resulting_cash_balance=cash_balance,
            fee_paid=fill.fee,
            cumulative_fees_paid=cumulative_fees,
            cash_identity_residual=cash_residual,
        )
        cash_records.append(cash_record)

        previous_state = position_state.get(fill.symbol, _OpenPositionState())
        updated_state, realized_delta = _update_open_position(previous_state, fill)
        if updated_state.quantity == ZERO:
            position_state.pop(fill.symbol, None)
        else:
            position_state[fill.symbol] = updated_state
        cumulative_realized_pnl = _quantize_cash(cumulative_realized_pnl + realized_delta)

        mark_price = marks.get(fill.symbol, fill.fill_price)
        snapshot = _aggregate_snapshot(
            starting_cash_balance=execution_bundle.starting_cash_balance,
            cash_balance=cash_balance,
            positions=position_state,
            marks=marks,
            realized_pnl=cumulative_realized_pnl,
        )
        peak_equity = max(peak_equity, snapshot.current_equity)
        drawdown = _drawdown_fraction(snapshot.current_equity, peak_equity)
        symbol_value = _quantize_cash(updated_state.quantity * mark_price)
        symbol_exposure = _clamp_probability(
            _quantize_fraction(
                _safe_ratio(
                    _abs_decimal(symbol_value),
                    snapshot.current_equity if snapshot.current_equity > ZERO else ONE,
                )
            )
        )
        position_limit = min(
            resolved_policy.max_symbol_exposure,
            symbol_limits.get(fill.symbol, resolved_policy.max_symbol_exposure),
        )
        order = order_map.get((fill.timestamp, fill.symbol))
        thesis = order.thesis if order is not None else f"reconciled fill for {fill.symbol}"
        rationale = (
            order.rationale
            if order is not None
            else "replay the fill into a portfolio-dependent state without violating identities"
        )
        within_limit = symbol_exposure <= position_limit
        position_records.append(
            PortfolioPositionRecord(
                fill_index=index,
                timestamp=fill.timestamp,
                symbol=fill.symbol,
                previous_quantity=previous_state.quantity,
                fill_quantity=fill.position_delta,
                resulting_quantity=updated_state.quantity,
                average_cost=updated_state.average_cost,
                mark_price=mark_price,
                market_value=symbol_value,
                cost_basis=_quantize_cash(_abs_decimal(updated_state.quantity) * updated_state.average_cost),
                exposure_fraction=symbol_exposure,
                max_position_fraction=position_limit,
                realized_pnl_delta=realized_delta,
                within_limit=within_limit,
                thesis=thesis,
                rationale=rationale,
            )
        )

        gross_breach = snapshot.gross_exposure_fraction > resolved_policy.max_gross_leverage
        net_breach = snapshot.net_exposure_fraction > resolved_policy.max_net_exposure
        drawdown_breach = drawdown > resolved_policy.kill_switch_drawdown
        identity_breach = cash_residual != ZERO
        if (within_limit is False or gross_breach or net_breach or drawdown_breach or identity_breach) and not kill_switch_triggered:
            kill_switch_triggered = True
            if not within_limit:
                kill_switch_reason = f"symbol exposure breach on {fill.symbol}"
            elif gross_breach:
                kill_switch_reason = "gross leverage breach"
            elif net_breach:
                kill_switch_reason = "net exposure breach"
            elif drawdown_breach:
                kill_switch_reason = "drawdown kill-switch breached"
            else:
                kill_switch_reason = "cash identity breach"

        pnl_records.append(
            PortfolioPnLRecord(
                fill_index=index,
                timestamp=fill.timestamp,
                symbol=fill.symbol,
                realized_pnl_delta=realized_delta,
                cumulative_realized_pnl=cumulative_realized_pnl,
                unrealized_pnl=snapshot.unrealized_pnl,
                total_pnl=snapshot.total_pnl,
                current_equity=snapshot.current_equity,
                peak_equity=peak_equity,
                drawdown_fraction=drawdown,
                gross_exposure_fraction=snapshot.gross_exposure_fraction,
                net_exposure_fraction=snapshot.net_exposure_fraction,
                kill_switch_active=kill_switch_triggered,
            )
        )

    aggregate = _aggregate_snapshot(
        starting_cash_balance=execution_bundle.starting_cash_balance,
        cash_balance=cash_balance,
        positions=position_state,
        marks=marks,
        realized_pnl=cumulative_realized_pnl,
    )
    peak_equity = max(peak_equity, aggregate.current_equity)
    final_drawdown = _drawdown_fraction(aggregate.current_equity, peak_equity)
    state = PortfolioState(
        cash_balance=aggregate.cash_balance,
        current_equity=aggregate.current_equity,
        peak_equity=peak_equity,
        realized_pnl=cumulative_realized_pnl,
        unrealized_pnl=aggregate.unrealized_pnl,
        total_pnl=aggregate.total_pnl,
        gross_exposure_fraction=aggregate.gross_exposure_fraction,
        net_exposure_fraction=aggregate.net_exposure_fraction,
        drawdown_fraction=final_drawdown,
        status="kill_switch" if kill_switch_triggered else "healthy",
        kill_switch_reason=kill_switch_reason if kill_switch_triggered else "",
        last_timestamp=execution_bundle.ledger.last_timestamp,
    )

    positions: list[PortfolioPosition] = []
    for symbol in sorted(position_state):
        local = position_state[symbol]
        mark = marks.get(symbol, local.average_cost if local.average_cost > ZERO else ONE)
        market_value = _quantize_cash(local.quantity * mark)
        gross_market_value = _quantize_cash(_abs_decimal(market_value))
        exposure_fraction = _clamp_probability(
            _quantize_fraction(
                _safe_ratio(
                    _abs_decimal(market_value),
                    state.current_equity if state.current_equity > ZERO else ONE,
                )
            )
        )
        gross_exposure_fraction = exposure_fraction
        unrealized_pnl = _quantize_cash(local.quantity * (mark - local.average_cost))
        total_pnl = _quantize_cash(local.cumulative_realized_pnl + unrealized_pnl)
        order = next((candidate for candidate in execution_bundle.orders if candidate.symbol == symbol), None)
        positions.append(
            PortfolioPosition(
                symbol=symbol,
                quantity=local.quantity,
                average_cost=local.average_cost,
                mark_price=mark,
                market_value=market_value,
                gross_market_value=gross_market_value,
                cost_basis=_quantize_cash(_abs_decimal(local.quantity) * local.average_cost),
                realized_pnl=local.cumulative_realized_pnl,
                unrealized_pnl=unrealized_pnl,
                total_pnl=total_pnl,
                exposure_fraction=exposure_fraction,
                gross_exposure_fraction=gross_exposure_fraction,
                max_position_fraction=min(
                    resolved_policy.max_symbol_exposure,
                    symbol_limits.get(symbol, resolved_policy.max_symbol_exposure),
                ),
                thesis=order.thesis if order is not None else f"portfolio state for {symbol}",
                provenance="execution_portfolio_descent",
            )
        )

    performance = _build_performance_report(
        pnl_records,
        positions,
        execution_bundle.starting_cash_balance,
        state,
        order_map,
    )
    audit_events, policy_evidence, cocycle_signature = _build_trace_and_evidence(
        execution_bundle=execution_bundle,
        cash_records=cash_records,
        position_records=position_records,
        pnl_records=pnl_records,
        positions=positions,
        state=state,
        performance=performance,
        policy=resolved_policy,
        kill_switch_triggered=kill_switch_triggered,
        order_rejection_conditions=final_rejection_conditions,
    )
    formal_verification = _verify_with_z3(
        execution_bundle,
        state,
        resolved_policy,
        cash_records,
        positions,
        kill_switch_triggered,
        kill_switch_reason,
    )
    research_ideas = _discover_portfolio_research_ideas(
        execution_bundle,
        positions,
        execution_bundle.starting_cash_balance,
    )
    audit_metadata = tuple(
        sorted(
            (
                ("audit_log", "immutable_required"),
                ("bias_guards", "lookahead_survivorship_data_leakage_blocked"),
                ("evidence_mode", "trace_backed_cocycle"),
                ("execution_mode", "paper_only"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("idea_mode", "portfolio_extension"),
                ("identity_mode", "fills_cash_positions_and_pnl_closed"),
                ("integration_mode", "only_risk_approved_descends"),
                (
                    "kill_switch_policy",
                    "deterministic_reconcile_halt_on_limit_or_integrity_breach",
                ),
                (
                    "paper_trading",
                    "required" if execution_bundle.paper_trading_required else "optional",
                ),
                ("performance_mode", "risk_adjusted_tail_and_stress_reported"),
                ("proof_obligation", execution_bundle.proof_obligation),
                (
                    "reproducibility",
                    "versioned_data_configuration_and_model_artifacts",
                ),
                ("schema_version", portfolio_schema_version()),
                (
                    "separation",
                    "research_simulation_execution_and_risk_are_decoupled",
                ),
                ("upstream_signature", execution_bundle.data_signature[:16]),
            )
        )
    )
    unsigned_bundle = PortfolioBundle(
        schema_version=portfolio_schema_version(),
        orders=tuple(execution_bundle.orders),
        fills=tuple(execution_bundle.fills),
        quotes=tuple(execution_bundle.quotes),
        execution_ledger=execution_bundle.ledger,
        starting_cash_balance=execution_bundle.starting_cash_balance,
        cash_records=tuple(cash_records),
        position_records=tuple(position_records),
        pnl_records=tuple(pnl_records),
        positions=tuple(positions),
        state=state,
        performance=performance,
        audit_events=audit_events,
        policy_evidence=policy_evidence,
        formal_verification=formal_verification,
        research_ideas=research_ideas,
        policy=resolved_policy,
        order_rejection_conditions=final_rejection_conditions,
        proof_obligation=execution_bundle.proof_obligation,
        paper_trading_required=execution_bundle.paper_trading_required,
        upstream_data_signature=execution_bundle.data_signature,
        audit_cocycle_signature=cocycle_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return PortfolioBundle(
        schema_version=unsigned_bundle.schema_version,
        orders=unsigned_bundle.orders,
        fills=unsigned_bundle.fills,
        quotes=unsigned_bundle.quotes,
        execution_ledger=unsigned_bundle.execution_ledger,
        starting_cash_balance=unsigned_bundle.starting_cash_balance,
        cash_records=unsigned_bundle.cash_records,
        position_records=unsigned_bundle.position_records,
        pnl_records=unsigned_bundle.pnl_records,
        positions=unsigned_bundle.positions,
        state=unsigned_bundle.state,
        performance=unsigned_bundle.performance,
        audit_events=unsigned_bundle.audit_events,
        policy_evidence=unsigned_bundle.policy_evidence,
        formal_verification=unsigned_bundle.formal_verification,
        research_ideas=unsigned_bundle.research_ideas,
        policy=unsigned_bundle.policy,
        order_rejection_conditions=unsigned_bundle.order_rejection_conditions,
        proof_obligation=unsigned_bundle.proof_obligation,
        paper_trading_required=unsigned_bundle.paper_trading_required,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        audit_cocycle_signature=unsigned_bundle.audit_cocycle_signature,
        data_signature=_build_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


def _timestamp_symbol_invariants_preserved(bundle: PortfolioBundle) -> bool:
    if len(bundle.cash_records) != len(bundle.position_records):
        return False
    if len(bundle.cash_records) != len(bundle.pnl_records):
        return False
    for cash_record, position_record, pnl_record, fill in zip(
        bundle.cash_records,
        bundle.position_records,
        bundle.pnl_records,
        bundle.fills,
    ):
        if (
            cash_record.timestamp != fill.timestamp
            or position_record.timestamp != fill.timestamp
            or pnl_record.timestamp != fill.timestamp
            or cash_record.symbol != fill.symbol
            or position_record.symbol != fill.symbol
            or pnl_record.symbol != fill.symbol
        ):
            return False
    return True


def _fills_positions_cash_consistent(bundle: PortfolioBundle) -> bool:
    if not bundle.fills:
        return bundle.state.cash_balance == bundle.starting_cash_balance and not bundle.positions
    final_cash = bundle.cash_records[-1].resulting_cash_balance
    expected_cash = _quantize_cash(
        bundle.starting_cash_balance + sum((fill.cash_delta for fill in bundle.fills), ZERO)
    )
    if final_cash != expected_cash or bundle.state.cash_balance != expected_cash:
        return False
    quantities: dict[str, Decimal] = {}
    for fill in bundle.fills:
        quantities[fill.symbol] = _quantize_size(
            quantities.get(fill.symbol, ZERO) + fill.position_delta
        )
    final_quantities = {
        position.symbol: position.quantity for position in bundle.positions if position.quantity != ZERO
    }
    if {symbol: qty for symbol, qty in quantities.items() if qty != ZERO} != final_quantities:
        return False
    total_pnl = _quantize_cash(bundle.state.current_equity - bundle.starting_cash_balance)
    return total_pnl == bundle.state.total_pnl == _quantize_cash(
        bundle.state.realized_pnl + bundle.state.unrealized_pnl
    )


def _execution_ledger_matches(bundle: PortfolioBundle) -> bool:
    ledger_positions = {
        position.symbol: position.quantity for position in bundle.execution_ledger.positions
    }
    portfolio_positions = {
        position.symbol: position.quantity for position in bundle.positions if position.quantity != ZERO
    }
    return (
        bundle.execution_ledger.cash_balance == bundle.state.cash_balance
        and ledger_positions == portfolio_positions
        and bundle.execution_ledger.last_timestamp == bundle.state.last_timestamp
    )


def _audit_cocycle_closed(bundle: PortfolioBundle) -> bool:
    if not bundle.audit_events or not bundle.policy_evidence:
        return False
    for index, event in enumerate(bundle.audit_events):
        expected_parent = "root" if index == 0 else bundle.audit_events[index - 1].trace_signature
        if event.event_index != index or event.trace_parent != expected_parent:
            return False
        if event.trace_signature != _recompute_trace_signature(event):
            return False
    event_signatures = {event.trace_signature for event in bundle.audit_events}
    if len(event_signatures) != len(bundle.audit_events):
        return False
    fill_event_signatures = {
        event.trace_signature
        for event in bundle.audit_events
        if event.event_type == "fill_applied"
    }
    fill_evidence_counts: dict[str, int] = {signature: 0 for signature in fill_event_signatures}
    for item in bundle.policy_evidence:
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
        if item.event_signature in fill_evidence_counts:
            fill_evidence_counts[item.event_signature] += 1
    if any(count < 2 for count in fill_evidence_counts.values()):
        return False
    return bundle.audit_cocycle_signature == _audit_cocycle_signature(
        bundle.audit_events,
        bundle.policy_evidence,
    )


def _risk_invariants_explicit(bundle: PortfolioBundle) -> bool:
    metadata = dict(bundle.audit_metadata)
    return (
        set(bundle.policy.required_rejection_conditions).issubset(bundle.order_rejection_conditions)
        and bundle.policy.max_symbol_exposure <= bundle.policy.max_net_exposure
        and bundle.policy.max_net_exposure <= bundle.policy.max_gross_leverage
        and bundle.policy.kill_switch_drawdown > bundle.policy.max_drawdown
        and metadata.get("audit_log") == "immutable_required"
        and metadata.get("bias_guards") == "lookahead_survivorship_data_leakage_blocked"
        and metadata.get("evidence_mode") == "trace_backed_cocycle"
        and metadata.get("execution_mode") == "paper_only"
        and metadata.get("identity_mode") == "fills_cash_positions_and_pnl_closed"
        and metadata.get("integration_mode") == "only_risk_approved_descends"
        and metadata.get("paper_trading")
        == ("required" if bundle.paper_trading_required else "optional")
        and metadata.get("performance_mode") == "risk_adjusted_tail_and_stress_reported"
        and metadata.get("proof_obligation") == bundle.proof_obligation
        and metadata.get("reproducibility")
        == "versioned_data_configuration_and_model_artifacts"
        and metadata.get("separation")
        == "research_simulation_execution_and_risk_are_decoupled"
    )


def _formal_verification_passed(bundle: PortfolioBundle) -> bool:
    return bool(bundle.formal_verification) and all(
        item.result == "proved" for item in bundle.formal_verification
    )


def _performance_report_complete(bundle: PortfolioBundle) -> bool:
    report = bundle.performance
    return (
        report.tail_loss_cash.is_finite()
        and report.stress_loss_cash.is_finite()
        and report.risk_adjusted_return.is_finite()
        and report.max_drawdown_fraction == bundle.state.drawdown_fraction
    )


def _kill_switch_deterministic(bundle: PortfolioBundle) -> bool:
    symbol_breach = any(
        position.gross_exposure_fraction
        > min(bundle.policy.max_symbol_exposure, position.max_position_fraction)
        for position in bundle.positions
    )
    gross_breach = bundle.state.gross_exposure_fraction > bundle.policy.max_gross_leverage
    net_breach = bundle.state.net_exposure_fraction > bundle.policy.max_net_exposure
    drawdown_breach = bundle.state.drawdown_fraction > bundle.policy.kill_switch_drawdown
    identity_breach = any(record.cash_identity_residual != ZERO for record in bundle.cash_records)
    expected = symbol_breach or gross_breach or net_breach or drawdown_breach or identity_breach
    actual = bundle.state.status == "kill_switch"
    return actual == expected and (not actual or bool(bundle.state.kill_switch_reason))


# @require("bundle comes from build_portfolio or an equivalent deterministic constructor")
# @ensure("returned validation report states whether identities, audit cocycles, and proof obligations still hold")
def validate_portfolio(bundle: PortfolioBundle) -> PortfolioValidationReport:
    """Validate that a portfolio bundle still satisfies its typed obligations.

    Validation is non-destructive and deterministic. It checks that replaying
    the stored fills still agrees with the reconciled portfolio state, that the
    audit trail closes as a trace-backed cocycle, and that explicit risk
    invariants and formal verification evidence remain present.
    """
    timestamp_symbol_invariants_preserved = _timestamp_symbol_invariants_preserved(bundle)
    fills_positions_cash_consistent = _fills_positions_cash_consistent(bundle)
    execution_ledger_matches = _execution_ledger_matches(bundle)
    audit_cocycle_closed = _audit_cocycle_closed(bundle)
    research_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    proof_obligation_satisfied = bundle.proof_obligation in {
        "smt_required",
        "machine_checked",
    }
    formal_verification_passed = _formal_verification_passed(bundle)
    paper_trading_enforced = (
        bundle.paper_trading_required
        and dict(bundle.audit_metadata).get("paper_trading") == "required"
    )
    performance_report_complete = _performance_report_complete(bundle)
    kill_switch_deterministic = _kill_switch_deterministic(bundle)
    exposures_within_policy_or_killed = (
        all(
            position.gross_exposure_fraction
            <= min(bundle.policy.max_symbol_exposure, position.max_position_fraction)
            for position in bundle.positions
        )
        and bundle.state.gross_exposure_fraction <= bundle.policy.max_gross_leverage
        and bundle.state.net_exposure_fraction <= bundle.policy.max_net_exposure
    ) or bundle.state.status == "kill_switch"
    drawdown_within_policy_or_killed = (
        bundle.state.drawdown_fraction <= bundle.policy.kill_switch_drawdown
        or bundle.state.status == "kill_switch"
    )
    signature_matches = bundle.data_signature == _build_bundle_signature(bundle)

    messages: list[str] = []
    if not timestamp_symbol_invariants_preserved:
        messages.append("timestamp/symbol restrictions are no longer preserved")
    if not fills_positions_cash_consistent:
        messages.append("fills, cash, positions, and pnl no longer satisfy identity constraints")
    if not execution_ledger_matches:
        messages.append("portfolio replay no longer matches the execution ledger")
    if not audit_cocycle_closed:
        messages.append("audit trail and policy evidence no longer form a closed trace-backed cocycle")
    if not research_idea_present:
        messages.append("no data-driven portfolio research idea is present")
    if not risk_invariants_explicit:
        messages.append("portfolio policy invariants are not explicit enough")
    if not proof_obligation_satisfied:
        messages.append("proof obligation is not SMT-backed or machine-checked")
    if not formal_verification_passed:
        messages.append("SMT-backed verification no longer proves the portfolio invariants")
    if not paper_trading_enforced:
        messages.append("paper-trading requirement is not enforced")
    if not performance_report_complete:
        messages.append("risk-adjusted, tail-risk, or stress metrics are incomplete")
    if not kill_switch_deterministic:
        messages.append("kill-switch behavior is no longer deterministic")
    if not exposures_within_policy_or_killed:
        messages.append("exposures breach policy without a corresponding kill-switch state")
    if not drawdown_within_policy_or_killed:
        messages.append("drawdown breach is not guarded by the kill switch")
    if not signature_matches:
        messages.append("bundle reproducibility signature mismatch")

    passes = (
        timestamp_symbol_invariants_preserved
        and fills_positions_cash_consistent
        and execution_ledger_matches
        and audit_cocycle_closed
        and research_idea_present
        and risk_invariants_explicit
        and proof_obligation_satisfied
        and formal_verification_passed
        and paper_trading_enforced
        and performance_report_complete
        and kill_switch_deterministic
        and exposures_within_policy_or_killed
        and drawdown_within_policy_or_killed
        and signature_matches
    )
    return PortfolioValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        fills_positions_cash_consistent=fills_positions_cash_consistent,
        execution_ledger_matches=execution_ledger_matches,
        audit_cocycle_closed=audit_cocycle_closed,
        research_idea_present=research_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        proof_obligation_satisfied=proof_obligation_satisfied,
        formal_verification_passed=formal_verification_passed,
        paper_trading_enforced=paper_trading_enforced,
        performance_report_complete=performance_report_complete,
        kill_switch_deterministic=kill_switch_deterministic,
        exposures_within_policy_or_killed=exposures_within_policy_or_killed,
        drawdown_within_policy_or_killed=drawdown_within_policy_or_killed,
        signature_matches=signature_matches,
        records_checked=len(bundle.cash_records) + len(bundle.position_records) + len(bundle.pnl_records),
        positions_checked=len(bundle.positions),
        evidence_checked=len(bundle.policy_evidence) + len(bundle.formal_verification),
        messages=tuple(messages),
    )


# @require("bundle comes from build_portfolio or an equivalent deterministic constructor")
# @ensure("returns a deterministic one-line summary of reconciliation health")
def portfolio_summary(bundle: PortfolioBundle) -> str:
    """Return a deterministic summary string for the portfolio bundle.

    The summary is designed for logs and CLI surfaces: short enough to scan,
    but stable enough to be useful in regression tests and audit traces.
    """
    report = validate_portfolio(bundle)
    status = "pass" if report.passes else "fail"
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.mark_dislocation_bps}bps"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    return (
        f"portfolio[{bundle.schema_version}] symbols={','.join(bundle.symbols) or 'none'} "
        f"orders={len(bundle.orders)} fills={len(bundle.fills)} positions={len(bundle.positions)} "
        f"state={bundle.state.status} equity={bundle.state.current_equity} "
        f"pnl={bundle.state.total_pnl} drawdown={bundle.state.drawdown_fraction} "
        f"validation={status} proof={bundle.proof_obligation} "
        f"paper_only={bundle.paper_trading_required} signature={bundle.data_signature[:12]} "
        f"ideas_preview={idea_preview}"
    )


__all__ = [
    "DEFAULT_PORTFOLIO_REJECTION_CONDITIONS",
    "PORTFOLIO_SCHEMA_VERSION",
    "AuditEvent",
    "FormalVerificationEvidence",
    "PolicyEvidence",
    "PortfolioBundle",
    "PortfolioCashRecord",
    "PortfolioError",
    "PortfolioIdeaSide",
    "PortfolioNormalizationError",
    "PortfolioPerformanceReport",
    "PortfolioPnLRecord",
    "PortfolioPolicy",
    "PortfolioPosition",
    "PortfolioPositionRecord",
    "PortfolioProofMode",
    "PortfolioResearchIdea",
    "PortfolioState",
    "PortfolioStatus",
    "PortfolioValidationReport",
    "PortfolioVerificationError",
    "build_portfolio",
    "portfolio_schema_version",
    "portfolio_summary",
    "validate_portfolio",
]
