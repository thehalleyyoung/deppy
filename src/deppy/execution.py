"""Execution."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Collection, Iterable, Literal, Mapping, Sequence, TypeAlias

from deppy.risk_engine import RiskApprovedIntent, RiskEngineBundle, RiskResearchIdea
from deppy.strategy_kernel import RiskBounds

PRICE_QUANTUM = Decimal("0.000001")
SIZE_QUANTUM = Decimal("0.0001")
FRACTION_QUANTUM = Decimal("0.0000001")
CASH_QUANTUM = Decimal("0.01")
EDGE_QUANTUM = Decimal("0.0001")
ONE = Decimal("1")
ZERO = Decimal("0")
EXECUTION_SCHEMA_VERSION = "execution.v1"

ExecutionKey: TypeAlias = tuple[datetime, str]
ExecutionSlice: TypeAlias = Literal["arrival", "impact", "identity"]
OrderStatus: TypeAlias = Literal["blocked", "ready"]
FillStatus: TypeAlias = Literal["missed", "partial", "filled"]
ExecutionProofMode: TypeAlias = Literal["smt_required", "machine_checked"]
ExecutionInput: TypeAlias = RiskEngineBundle | Iterable[RiskApprovedIntent]

SLICES: tuple[ExecutionSlice, ...] = ("arrival", "impact", "identity")


class ExecutionError(ValueError):
    """Base error raised by execution refinement and settlement."""


class ExecutionNormalizationError(ExecutionError):
    """Raised when execution-local data violates normalization invariants."""


class ExecutionRestrictionError(ExecutionError):
    """Raised when a restriction map for execution sections is ill-formed."""


class ExecutionGluingError(ExecutionError):
    """Raised when execution-local sections fail to glue on overlaps."""


class FillApplicationError(ExecutionError):
    """Raised when fill application would violate ledger identity constraints."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    """Return *value* rounded onto the requested decimal lattice."""
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _quantize_price(value: Decimal) -> Decimal:
    """Quantize a price onto the execution price lattice."""
    return _quantize(value, PRICE_QUANTUM)


def _quantize_size(value: Decimal) -> Decimal:
    """Quantize a size onto the execution size lattice."""
    return _quantize(value, SIZE_QUANTUM)


def _quantize_fraction(value: Decimal) -> Decimal:
    """Quantize a fraction onto the shared fraction lattice."""
    return _quantize(value, FRACTION_QUANTUM)


def _quantize_cash(value: Decimal) -> Decimal:
    """Quantize a cash value onto the shared currency lattice."""
    return _quantize(value, CASH_QUANTUM)


def _quantize_edge(value: Decimal) -> Decimal:
    """Quantize an edge estimate in basis points."""
    return _quantize(value, EDGE_QUANTUM)


def _stable_digest(parts: Iterable[str]) -> str:
    """Return a deterministic digest over the supplied parts."""
    digest = sha256()
    digest.update(EXECUTION_SCHEMA_VERSION.encode("utf-8"))
    digest.update(b"\0")
    for part in parts:
        digest.update(str(part).encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    """Convert *value* to a finite :class:`Decimal`."""
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise ExecutionNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc

    if not candidate.is_finite():
        raise ExecutionNormalizationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    """Normalize *value* to a timezone-aware UTC timestamp."""
    if not isinstance(value, datetime):
        raise ExecutionRestrictionError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    """Return the canonical symbol representation used on overlaps."""
    if not isinstance(value, str):
        raise ExecutionNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise ExecutionNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise ExecutionNormalizationError(
            f"Field 'symbol' cannot normalize from {value!r}."
        )
    return candidate


def _normalize_name(value: str, field_name: str) -> str:
    """Normalize venue-like identifiers to a stable canonical name."""
    if not isinstance(value, str):
        raise ExecutionNormalizationError(
            f"Field '{field_name}' must be text, got {value!r}."
        )
    normalized = "_".join(value.strip().lower().split())
    if not normalized:
        raise ExecutionNormalizationError(f"Field '{field_name}' cannot be empty.")
    return normalized


def _resolve_tolerance(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a tolerance parameter to a non-negative finite decimal."""
    tolerance = _coerce_decimal(value, field_name)
    if tolerance < ZERO:
        raise ExecutionRestrictionError(
            f"Tolerance '{field_name}' must be non-negative."
        )
    return _quantize_fraction(tolerance)


def _clamp_probability(value: Decimal) -> Decimal:
    """Clamp *value* to the closed unit interval."""
    if not value.is_finite():
        raise ExecutionNormalizationError("Probabilistic scores must be finite.")
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize_fraction(value)


def _validate_probability(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in ``[0, 1]``."""
    if not value.is_finite():
        raise ExecutionNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise ExecutionNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_positive_decimal(value: Decimal, field_name: str) -> None:
    """Validate that *value* is finite and strictly positive."""
    if not value.is_finite():
        raise ExecutionNormalizationError(f"Field '{field_name}' must be finite.")
    if value <= ZERO:
        raise ExecutionNormalizationError(f"Field '{field_name}' must be strictly positive.")


def _validate_non_negative_decimal(value: Decimal, field_name: str) -> None:
    """Validate that *value* is finite and non-negative."""
    if not value.is_finite():
        raise ExecutionNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO:
        raise ExecutionNormalizationError(f"Field '{field_name}' must be non-negative.")


def _side_sign(side: str) -> int:
    """Return the signed direction encoded by *side*."""
    if side == "long":
        return 1
    if side == "short":
        return -1
    if side == "flat":
        return 0
    raise ExecutionNormalizationError(f"Unsupported trading side {side!r}.")


def _signed_quantity(side: str, quantity: Decimal) -> Decimal:
    """Apply the sign implied by *side* to *quantity*."""
    sign = _side_sign(side)
    if sign == 0:
        return ZERO
    return _quantize_size(quantity * Decimal(sign))


def _cash_delta(side: str, notional: Decimal, fee: Decimal) -> Decimal:
    """Return the cash delta induced by filling one order."""
    sign = _side_sign(side)
    if sign > 0:
        return _quantize_cash(-(notional + fee))
    if sign < 0:
        return _quantize_cash(notional - fee)
    return ZERO


def _safe_ratio(numerator: Decimal, denominator: Decimal) -> Decimal:
    """Return a quantized ratio, treating zero denominator as zero."""
    if denominator == ZERO:
        return ZERO
    return _quantize_fraction(numerator / denominator)


def _median_decimal(
    values: Sequence[Decimal], quantum: Decimal = FRACTION_QUANTUM
) -> Decimal:
    """Return the median of *values* on the requested decimal lattice."""
    if not values:
        raise ExecutionNormalizationError("Median is undefined for an empty value set.")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return _quantize(ordered[middle], quantum)
    return _quantize((ordered[middle - 1] + ordered[middle]) / Decimal("2"), quantum)


def _max_gap(values: Sequence[Decimal], quantum: Decimal = FRACTION_QUANTUM) -> Decimal:
    """Return the maximum gap between values on a shared overlap."""
    if not values:
        return ZERO
    return _quantize(max(values) - min(values), quantum)


def _triple_overlap_residual(values: Sequence[Decimal]) -> Decimal:
    """Return the H^1-style residual of corrections on triple overlaps."""
    if len(values) < 3:
        return ZERO
    median_value = _median_decimal(values)
    residual = max((abs(value - median_value) for value in values), default=ZERO)
    return _quantize_fraction(residual)


def _fraction_from_quantity(
    quantity: Decimal, reference_price: Decimal, reference_notional: Decimal
) -> Decimal:
    """Return the fraction represented by *quantity* at the given reference price."""
    if quantity == ZERO or reference_price == ZERO or reference_notional == ZERO:
        return ZERO
    return _clamp_probability(
        _quantize_fraction((quantity * reference_price) / reference_notional)
    )


def _limit_price(quote: "ExecutionQuote", side: str, buffer_fraction: Decimal) -> Decimal:
    """Return the conservative limit price for *side* around one quote."""
    if side == "long":
        return _quantize_price(quote.ask_price * (ONE + buffer_fraction))
    if side == "short":
        return _quantize_price(quote.bid_price * (ONE - buffer_fraction))
    return quote.mid_price


def _quantity_from_fraction(
    fraction: Decimal, reference_notional: Decimal, reference_price: Decimal
) -> Decimal:
    """Return the order quantity implied by *fraction* of the reference notional."""
    if fraction == ZERO or reference_notional == ZERO:
        return ZERO
    _validate_positive_decimal(reference_price, "reference_price")
    return _quantize_size((reference_notional * fraction) / reference_price)


def _trade_identity_residual(
    side: str,
    quantity: Decimal,
    notional: Decimal,
    fee: Decimal,
    cash_delta: Decimal,
    position_delta: Decimal,
    reference_price: Decimal,
) -> Decimal:
    """Return the cash-denominated residual of the fill identity equations."""
    expected_cash = _cash_delta(side, notional, fee)
    expected_position = _signed_quantity(side, quantity)
    cash_residual = abs(expected_cash - cash_delta)
    quantity_residual = abs(expected_position - position_delta) * reference_price
    return _quantize_cash(max(cash_residual, _quantize_cash(quantity_residual)))


def _gluing_score(obstruction: Decimal, h1_tolerance: Decimal) -> Decimal:
    """Convert an obstruction witness into a unit gluing score."""
    if h1_tolerance == ZERO:
        return ZERO if obstruction > ZERO else ONE
    return _clamp_probability(ONE - min(ONE, obstruction / h1_tolerance))


def _require_unique_slices(
    members: Sequence["LocalExecutionSection"], key: ExecutionKey
) -> tuple[ExecutionSlice, ...]:
    """Ensure an overlap contains at most one local section from each slice."""
    slice_names = [member.slice_name for member in members]
    unique = tuple(sorted(set(slice_names)))
    if len(unique) != len(slice_names):
        timestamp, symbol = key
        raise ExecutionGluingError(
            f"Execution overlap {symbol}@{timestamp.isoformat()} contains duplicate slices."
        )
    return unique


def _require_unique_value(
    values: Sequence[Any], key: ExecutionKey, field_name: str
) -> Any:
    """Ensure one overlap carries a single coherent value for *field_name*."""
    unique: list[Any] = []
    for value in values:
        if not any(value == candidate for candidate in unique):
            unique.append(value)
    if len(unique) != 1:
        timestamp, symbol = key
        raise ExecutionGluingError(
            f"Execution overlap {symbol}@{timestamp.isoformat()} disagrees on {field_name}."
        )
    return unique[0]


def _resolve_quote(
    symbol: str, quotes_by_symbol: Mapping[str, "ExecutionQuote"]
) -> "ExecutionQuote":
    """Resolve the quote to use for *symbol*."""
    normalized = {_normalize_symbol(key): value for key, value in quotes_by_symbol.items()}
    if symbol not in normalized:
        raise ExecutionNormalizationError(
            f"Missing execution quote for symbol {symbol!r}."
        )
    quote = normalized[symbol]
    if quote.symbol != symbol:
        raise ExecutionNormalizationError(
            f"Execution quote symbol mismatch for {symbol!r}; got {quote.symbol!r}."
        )
    return quote


def _local_thesis(slice_name: ExecutionSlice, intent: RiskApprovedIntent) -> str:
    """Return the thesis string for one local execution slice."""
    if slice_name == "arrival":
        return (
            "arrival slice: preserve the local quote topology while descending the "
            f"{intent.style} thesis into a limit order"
        )
    if slice_name == "impact":
        return (
            "impact slice: keep participation bounded so the order stays inside the "
            "same liquidity neighborhood"
        )
    return (
        "identity slice: require fills to induce exact cash and position updates so "
        "the execution coboundary remains closed"
    )


def _global_thesis(status: OrderStatus) -> str:
    """Return the thesis implied by one glued execution section."""
    if status == "ready":
        return (
            "execution slices glue coherently, so the risk-approved thesis descends "
            "to a placeable order"
        )
    return (
        "execution slices fail to leave a non-trivial common section, so the intent "
        "must remain blocked"
    )


def _global_rationale(
    status: OrderStatus,
    executable_fraction: Decimal,
    binding_slices: Sequence[ExecutionSlice],
) -> str:
    """Return a human-readable explanation for one glued execution decision."""
    binding_text = ", ".join(binding_slices) if binding_slices else "none"
    if status == "ready":
        return (
            "arrival, impact, and identity sections glue with bounded H^1 "
            f"obstruction; binding_slices={binding_text}; executable_fraction="
            f"{executable_fraction}"
        )
    return (
        "the common execution section is too small to descend to a placeable order; "
        f"binding_slices={binding_text}; executable_fraction={executable_fraction}"
    )


def _order_reason(status: OrderStatus) -> str:
    """Return the rationale for one ready or blocked order."""
    if status == "ready":
        return (
            "order is ready because only a coherent, risk-approved section descended "
            "through execution gluing"
        )
    return (
        "order is blocked because the execution cover does not leave a coherent "
        "executable allocation"
    )


@dataclass(init=False)
class ExecutionPolicy:
    """Static parameters that govern the final execution descent."""

    reference_notional: Decimal
    max_participation_rate: Decimal
    limit_buffer_fraction: Decimal
    fee_rate: Decimal
    min_order_fraction: Decimal

    def __init__(
        self,
        reference_notional: Decimal,
        max_participation_rate: Decimal,
        limit_buffer_fraction: Decimal,
        fee_rate: Decimal,
        min_order_fraction: Decimal,
    ) -> None:
        self.reference_notional = reference_notional
        self.max_participation_rate = max_participation_rate
        self.limit_buffer_fraction = limit_buffer_fraction
        self.fee_rate = fee_rate
        self.min_order_fraction = min_order_fraction
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the execution policy."""
        _validate_positive_decimal(self.reference_notional, "reference_notional")
        _validate_probability(self.max_participation_rate, "max_participation_rate")
        _validate_probability(self.limit_buffer_fraction, "limit_buffer_fraction")
        _validate_probability(self.fee_rate, "fee_rate")
        _validate_probability(self.min_order_fraction, "min_order_fraction")
        if self.max_participation_rate == ZERO:
            raise ExecutionNormalizationError(
                "Field 'max_participation_rate' must be strictly positive."
            )
        if self.min_order_fraction == ZERO:
            raise ExecutionNormalizationError(
                "Field 'min_order_fraction' must be strictly positive."
            )

    def reproducibility_signature(self) -> str:
        """Return a deterministic digest for execution-policy replay."""
        return _stable_digest(
            [
                str(self.reference_notional),
                str(self.max_participation_rate),
                str(self.limit_buffer_fraction),
                str(self.fee_rate),
                str(self.min_order_fraction),
            ]
        )


@dataclass(init=False)
class ExecutionQuote:
    """A normalized executable quote used to price and size one order."""

    timestamp: datetime
    symbol: str
    venue: str
    bid_price: Decimal
    ask_price: Decimal
    available_quantity: Decimal

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        venue: str,
        bid_price: Decimal,
        ask_price: Decimal,
        available_quantity: Decimal,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.venue = venue
        self.bid_price = bid_price
        self.ask_price = ask_price
        self.available_quantity = available_quantity
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate quote invariants."""
        normalized_timestamp = _normalize_timestamp(self.timestamp, "timestamp")
        normalized_symbol = _normalize_symbol(self.symbol)
        normalized_venue = _normalize_name(self.venue, "venue")
        bid_price = _quantize_price(self.bid_price)
        ask_price = _quantize_price(self.ask_price)
        available_quantity = _quantize_size(self.available_quantity)
        _validate_positive_decimal(bid_price, "bid_price")
        _validate_positive_decimal(ask_price, "ask_price")
        _validate_positive_decimal(available_quantity, "available_quantity")
        if bid_price > ask_price:
            raise ExecutionNormalizationError(
                "Execution quote bid_price cannot exceed ask_price."
            )
        self.timestamp = normalized_timestamp
        self.symbol = normalized_symbol
        self.venue = normalized_venue
        self.bid_price = bid_price
        self.ask_price = ask_price
        self.available_quantity = available_quantity

    @property
    def mid_price(self) -> Decimal:
        """Return the midpoint price of the executable quote."""
        return _quantize_price((self.bid_price + self.ask_price) / Decimal("2"))


@dataclass(init=False)
class LocalExecutionSection:
    """One local execution slice attached to a risk-approved intent."""

    timestamp: datetime
    symbol: str
    slice_name: ExecutionSlice
    venue: str
    side: str
    style: str
    approved_fraction: Decimal
    executable_fraction: Decimal
    reference_notional: Decimal
    reference_price: Decimal
    limit_price: Decimal
    quantity: Decimal
    notional: Decimal
    estimated_fee: Decimal
    participation_rate: Decimal
    fee_rate: Decimal
    cash_delta: Decimal
    position_delta: Decimal
    identity_residual: Decimal
    risk_bounds: RiskBounds
    binding: bool
    passes: bool
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        slice_name: ExecutionSlice,
        venue: str,
        side: str,
        style: str,
        approved_fraction: Decimal,
        executable_fraction: Decimal,
        reference_notional: Decimal,
        reference_price: Decimal,
        limit_price: Decimal,
        quantity: Decimal,
        notional: Decimal,
        estimated_fee: Decimal,
        participation_rate: Decimal,
        fee_rate: Decimal,
        cash_delta: Decimal,
        position_delta: Decimal,
        identity_residual: Decimal,
        risk_bounds: RiskBounds,
        binding: bool,
        passes: bool,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.slice_name = slice_name
        self.venue = venue
        self.side = side
        self.style = style
        self.approved_fraction = approved_fraction
        self.executable_fraction = executable_fraction
        self.reference_notional = reference_notional
        self.reference_price = reference_price
        self.limit_price = limit_price
        self.quantity = quantity
        self.notional = notional
        self.estimated_fee = estimated_fee
        self.participation_rate = participation_rate
        self.fee_rate = fee_rate
        self.cash_delta = cash_delta
        self.position_delta = position_delta
        self.identity_residual = identity_residual
        self.risk_bounds = risk_bounds
        self.binding = binding
        self.passes = passes
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate local section invariants."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise ExecutionNormalizationError(
                "Execution timestamps must be timezone-aware."
            )
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise ExecutionNormalizationError(
                "Execution timestamps must be expressed in UTC."
            )
        if self.symbol != _normalize_symbol(self.symbol):
            raise ExecutionNormalizationError("Execution symbols must be canonicalized.")
        if self.slice_name not in SLICES:
            raise ExecutionNormalizationError(
                f"Unknown execution slice {self.slice_name!r}."
            )
        if self.venue != _normalize_name(self.venue, "venue"):
            raise ExecutionNormalizationError("Execution venues must be canonicalized.")
        if self.side not in {"long", "short", "flat"}:
            raise ExecutionNormalizationError(
                f"Unsupported execution side {self.side!r}."
            )
        if not self.style.strip():
            raise ExecutionNormalizationError("Execution sections must carry a style.")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_probability(self.executable_fraction, "executable_fraction")
        _validate_positive_decimal(self.reference_notional, "reference_notional")
        _validate_positive_decimal(self.reference_price, "reference_price")
        _validate_positive_decimal(self.limit_price, "limit_price")
        _validate_non_negative_decimal(self.quantity, "quantity")
        _validate_non_negative_decimal(self.notional, "notional")
        _validate_non_negative_decimal(self.estimated_fee, "estimated_fee")
        _validate_probability(self.participation_rate, "participation_rate")
        _validate_probability(self.fee_rate, "fee_rate")
        _validate_non_negative_decimal(self.identity_residual, "identity_residual")
        if self.executable_fraction > self.approved_fraction:
            raise ExecutionNormalizationError(
                "Executable fraction cannot exceed the risk-approved fraction."
            )
        expected_notional = _quantize_cash(self.quantity * self.limit_price)
        if self.notional != expected_notional:
            raise ExecutionNormalizationError(
                "Execution notional must equal quantity times limit price."
            )
        expected_fee = _quantize_cash(self.notional * self.fee_rate)
        if self.estimated_fee != expected_fee:
            raise ExecutionNormalizationError(
                "Execution fee must equal fee_rate times notional."
            )
        expected_residual = _trade_identity_residual(
            self.side,
            self.quantity,
            self.notional,
            self.estimated_fee,
            self.cash_delta,
            self.position_delta,
            self.reference_price,
        )
        if self.identity_residual != expected_residual:
            raise ExecutionNormalizationError(
                "Identity residual must match the encoded cash and position updates."
            )
        if self.binding != (self.executable_fraction < self.approved_fraction):
            raise ExecutionNormalizationError(
                "Binding must match whether the approved fraction was clipped."
            )
        if self.quantity == ZERO and any(
            value != ZERO
            for value in (
                self.notional,
                self.estimated_fee,
                self.cash_delta,
                self.position_delta,
            )
        ):
            raise ExecutionNormalizationError(
                "Zero-quantity execution sections must carry zero trade deltas."
            )
        if not self.thesis.strip() or not self.rationale.strip():
            raise ExecutionNormalizationError(
                "Execution sections must explain their thesis and rationale."
            )

    def execution_key(self) -> ExecutionKey:
        """Return the restriction and gluing key for the local section."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, ExecutionSlice]:
        """Return the invariant signature that must persist under restriction."""
        return (self.timestamp, self.symbol, self.slice_name)


@dataclass(init=False)
class ExecutionCocycleCertificate:
    """Diagnostic evidence that local execution sections can be glued."""

    key: ExecutionKey
    slices: tuple[ExecutionSlice, ...]
    fraction_gap: Decimal
    price_gap: Decimal
    participation_gap: Decimal
    identity_gap: Decimal
    triple_overlap_residual: Decimal
    h1_obstruction: Decimal
    passes: bool
    reason: str

    def __init__(
        self,
        key: ExecutionKey,
        slices: tuple[ExecutionSlice, ...],
        fraction_gap: Decimal,
        price_gap: Decimal,
        participation_gap: Decimal,
        identity_gap: Decimal,
        triple_overlap_residual: Decimal,
        h1_obstruction: Decimal,
        passes: bool,
        reason: str,
    ) -> None:
        self.key = key
        self.slices = tuple(slices)
        self.fraction_gap = fraction_gap
        self.price_gap = price_gap
        self.participation_gap = participation_gap
        self.identity_gap = identity_gap
        self.triple_overlap_residual = triple_overlap_residual
        self.h1_obstruction = h1_obstruction
        self.passes = passes
        self.reason = reason

    def assert_passes(self) -> None:
        """Raise :class:`ExecutionGluingError` when the certificate fails."""
        if not self.passes:
            timestamp, symbol = self.key
            raise ExecutionGluingError(
                f"Execution overlap {symbol}@{timestamp.isoformat()} failed gluing: "
                f"{self.reason}"
            )


@dataclass(init=False)
class GlobalExecutionSection:
    """A coherent execution section obtained by gluing local execution slices."""

    timestamp: datetime
    symbol: str
    slices: tuple[ExecutionSlice, ...]
    venue: str
    side: str
    style: str
    approved_fraction: Decimal
    executable_fraction: Decimal
    reference_notional: Decimal
    reference_price: Decimal
    limit_price: Decimal
    quantity: Decimal
    notional: Decimal
    estimated_fee: Decimal
    fee_rate: Decimal
    cash_delta: Decimal
    position_delta: Decimal
    aggregate_participation: Decimal
    identity_residual: Decimal
    risk_bounds: RiskBounds
    gluing_score: Decimal
    order_status: OrderStatus
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        slices: tuple[ExecutionSlice, ...],
        venue: str,
        side: str,
        style: str,
        approved_fraction: Decimal,
        executable_fraction: Decimal,
        reference_notional: Decimal,
        reference_price: Decimal,
        limit_price: Decimal,
        quantity: Decimal,
        notional: Decimal,
        estimated_fee: Decimal,
        fee_rate: Decimal,
        cash_delta: Decimal,
        position_delta: Decimal,
        aggregate_participation: Decimal,
        identity_residual: Decimal,
        risk_bounds: RiskBounds,
        gluing_score: Decimal,
        order_status: OrderStatus,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.slices = tuple(slices)
        self.venue = venue
        self.side = side
        self.style = style
        self.approved_fraction = approved_fraction
        self.executable_fraction = executable_fraction
        self.reference_notional = reference_notional
        self.reference_price = reference_price
        self.limit_price = limit_price
        self.quantity = quantity
        self.notional = notional
        self.estimated_fee = estimated_fee
        self.fee_rate = fee_rate
        self.cash_delta = cash_delta
        self.position_delta = position_delta
        self.aggregate_participation = aggregate_participation
        self.identity_residual = identity_residual
        self.risk_bounds = risk_bounds
        self.gluing_score = gluing_score
        self.order_status = order_status
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate glued execution invariants."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise ExecutionNormalizationError(
                "Global execution timestamps must be timezone-aware."
            )
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise ExecutionNormalizationError(
                "Global execution timestamps must be expressed in UTC."
            )
        if self.symbol != _normalize_symbol(self.symbol):
            raise ExecutionNormalizationError(
                "Global execution symbols must be canonicalized."
            )
        if not self.slices:
            raise ExecutionNormalizationError(
                "Global execution sections must retain execution slices."
            )
        if self.venue != _normalize_name(self.venue, "venue"):
            raise ExecutionNormalizationError(
                "Global execution venues must be canonicalized."
            )
        if self.side not in {"long", "short", "flat"}:
            raise ExecutionNormalizationError(
                f"Unsupported global execution side {self.side!r}."
            )
        if not self.style.strip():
            raise ExecutionNormalizationError(
                "Global execution sections must carry a style."
            )
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_probability(self.executable_fraction, "executable_fraction")
        _validate_positive_decimal(self.reference_notional, "reference_notional")
        _validate_positive_decimal(self.reference_price, "reference_price")
        _validate_positive_decimal(self.limit_price, "limit_price")
        _validate_non_negative_decimal(self.quantity, "quantity")
        _validate_non_negative_decimal(self.notional, "notional")
        _validate_non_negative_decimal(self.estimated_fee, "estimated_fee")
        _validate_probability(self.fee_rate, "fee_rate")
        _validate_probability(self.aggregate_participation, "aggregate_participation")
        _validate_non_negative_decimal(self.identity_residual, "identity_residual")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.executable_fraction > self.approved_fraction:
            raise ExecutionNormalizationError(
                "Glued executable fraction cannot exceed the risk-approved fraction."
            )
        expected_notional = _quantize_cash(self.quantity * self.limit_price)
        if self.notional != expected_notional:
            raise ExecutionNormalizationError(
                "Global execution notional must equal quantity times limit price."
            )
        expected_fee = _quantize_cash(self.notional * self.fee_rate)
        if self.estimated_fee != expected_fee:
            raise ExecutionNormalizationError(
                "Global execution fee must equal fee_rate times notional."
            )
        expected_residual = _trade_identity_residual(
            self.side,
            self.quantity,
            self.notional,
            self.estimated_fee,
            self.cash_delta,
            self.position_delta,
            self.reference_price,
        )
        if self.identity_residual < expected_residual:
            raise ExecutionNormalizationError(
                "Global identity residual cannot understate the local execution defect."
            )
        if self.order_status not in {"blocked", "ready"}:
            raise ExecutionNormalizationError(
                f"Unsupported order status {self.order_status!r}."
            )
        if not self.thesis.strip() or not self.rationale.strip():
            raise ExecutionNormalizationError(
                "Global execution sections must explain their decision."
            )


@dataclass(init=False)
class ExecutableOrder:
    """A placeable order descended from one glued execution section."""

    timestamp: datetime
    symbol: str
    venue: str
    side: str
    style: str
    approved_fraction: Decimal
    executable_fraction: Decimal
    reference_notional: Decimal
    reference_price: Decimal
    limit_price: Decimal
    quantity: Decimal
    notional: Decimal
    estimated_fee: Decimal
    fee_rate: Decimal
    risk_bounds: RiskBounds
    gluing_score: Decimal
    order_status: OrderStatus
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        venue: str,
        side: str,
        style: str,
        approved_fraction: Decimal,
        executable_fraction: Decimal,
        reference_notional: Decimal,
        reference_price: Decimal,
        limit_price: Decimal,
        quantity: Decimal,
        notional: Decimal,
        estimated_fee: Decimal,
        fee_rate: Decimal,
        risk_bounds: RiskBounds,
        gluing_score: Decimal,
        order_status: OrderStatus,
        thesis: str,
        rationale: str,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.venue = venue
        self.side = side
        self.style = style
        self.approved_fraction = approved_fraction
        self.executable_fraction = executable_fraction
        self.reference_notional = reference_notional
        self.reference_price = reference_price
        self.limit_price = limit_price
        self.quantity = quantity
        self.notional = notional
        self.estimated_fee = estimated_fee
        self.fee_rate = fee_rate
        self.risk_bounds = risk_bounds
        self.gluing_score = gluing_score
        self.order_status = order_status
        self.thesis = thesis
        self.rationale = rationale
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate that the executable order is well-formed."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise ExecutionNormalizationError(
                "Executable order timestamps must be timezone-aware."
            )
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise ExecutionNormalizationError(
                "Executable order timestamps must be expressed in UTC."
            )
        if self.symbol != _normalize_symbol(self.symbol):
            raise ExecutionNormalizationError(
                "Executable order symbols must be canonicalized."
            )
        if self.venue != _normalize_name(self.venue, "venue"):
            raise ExecutionNormalizationError(
                "Executable order venues must be canonicalized."
            )
        if self.side not in {"long", "short", "flat"}:
            raise ExecutionNormalizationError(
                f"Unsupported executable order side {self.side!r}."
            )
        if not self.style.strip():
            raise ExecutionNormalizationError("Executable orders must carry a style.")
        _validate_probability(self.approved_fraction, "approved_fraction")
        _validate_probability(self.executable_fraction, "executable_fraction")
        _validate_positive_decimal(self.reference_notional, "reference_notional")
        _validate_positive_decimal(self.reference_price, "reference_price")
        _validate_positive_decimal(self.limit_price, "limit_price")
        _validate_non_negative_decimal(self.quantity, "quantity")
        _validate_non_negative_decimal(self.notional, "notional")
        _validate_non_negative_decimal(self.estimated_fee, "estimated_fee")
        _validate_probability(self.fee_rate, "fee_rate")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.executable_fraction > self.approved_fraction:
            raise ExecutionNormalizationError(
                "Executable order fraction cannot exceed the approved fraction."
            )
        expected_notional = _quantize_cash(self.quantity * self.limit_price)
        if self.notional != expected_notional:
            raise ExecutionNormalizationError(
                "Executable order notional must equal quantity times limit price."
            )
        expected_fee = _quantize_cash(self.notional * self.fee_rate)
        if self.estimated_fee != expected_fee:
            raise ExecutionNormalizationError(
                "Executable order fee must equal fee_rate times notional."
            )
        if self.order_status not in {"blocked", "ready"}:
            raise ExecutionNormalizationError(
                f"Unsupported executable order status {self.order_status!r}."
            )
        if not self.thesis.strip() or not self.rationale.strip():
            raise ExecutionNormalizationError(
                "Executable orders must explain their thesis and rationale."
            )

    def order_key(self) -> ExecutionKey:
        """Return the overlap key carried by the order."""
        return (self.timestamp, self.symbol)


@dataclass(init=False)
class FillReport:
    """A realized fill descended from one executable order."""

    timestamp: datetime
    symbol: str
    venue: str
    side: str
    style: str
    quantity: Decimal
    fill_price: Decimal
    gross_notional: Decimal
    fee: Decimal
    cash_delta: Decimal
    position_delta: Decimal
    fill_ratio: Decimal
    fill_status: FillStatus

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        venue: str,
        side: str,
        style: str,
        quantity: Decimal,
        fill_price: Decimal,
        gross_notional: Decimal,
        fee: Decimal,
        cash_delta: Decimal,
        position_delta: Decimal,
        fill_ratio: Decimal,
        fill_status: FillStatus,
    ) -> None:
        self.timestamp = timestamp
        self.symbol = symbol
        self.venue = venue
        self.side = side
        self.style = style
        self.quantity = quantity
        self.fill_price = fill_price
        self.gross_notional = gross_notional
        self.fee = fee
        self.cash_delta = cash_delta
        self.position_delta = position_delta
        self.fill_ratio = fill_ratio
        self.fill_status = fill_status
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the realized fill identities."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise ExecutionNormalizationError("Fill timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise ExecutionNormalizationError("Fill timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise ExecutionNormalizationError("Fill symbols must be canonicalized.")
        if self.venue != _normalize_name(self.venue, "venue"):
            raise ExecutionNormalizationError("Fill venues must be canonicalized.")
        if self.side not in {"long", "short", "flat"}:
            raise ExecutionNormalizationError(f"Unsupported fill side {self.side!r}.")
        if not self.style.strip():
            raise ExecutionNormalizationError("Fills must carry a style.")
        _validate_non_negative_decimal(self.quantity, "quantity")
        _validate_positive_decimal(self.fill_price, "fill_price")
        _validate_non_negative_decimal(self.gross_notional, "gross_notional")
        _validate_non_negative_decimal(self.fee, "fee")
        _validate_probability(self.fill_ratio, "fill_ratio")
        expected_notional = _quantize_cash(self.quantity * self.fill_price)
        if self.gross_notional != expected_notional:
            raise ExecutionNormalizationError(
                "Fill gross_notional must equal quantity times fill_price."
            )
        expected_residual = _trade_identity_residual(
            self.side,
            self.quantity,
            self.gross_notional,
            self.fee,
            self.cash_delta,
            self.position_delta,
            self.fill_price,
        )
        if expected_residual != ZERO:
            raise ExecutionNormalizationError(
                "Fills must satisfy exact cash and position identities."
            )
        if self.fill_status not in {"missed", "partial", "filled"}:
            raise ExecutionNormalizationError(
                f"Unsupported fill status {self.fill_status!r}."
            )


@dataclass(init=False)
class PositionBalance:
    """The signed quantity currently held for one symbol."""

    symbol: str
    quantity: Decimal

    def __init__(self, symbol: str, quantity: Decimal) -> None:
        self.symbol = symbol
        self.quantity = quantity
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the position balance."""
        if self.symbol != _normalize_symbol(self.symbol):
            raise ExecutionNormalizationError(
                "Position balance symbols must be canonicalized."
            )
        if not self.quantity.is_finite():
            raise ExecutionNormalizationError(
                "Position balance quantities must be finite."
            )


@dataclass(init=False)
class ExecutionLedgerState:
    """A canonical ledger snapshot after applying realized fills."""

    cash_balance: Decimal
    positions: tuple[PositionBalance, ...]
    total_fees_paid: Decimal
    last_timestamp: datetime | None

    def __init__(
        self,
        cash_balance: Decimal,
        positions: tuple[PositionBalance, ...],
        total_fees_paid: Decimal,
        last_timestamp: datetime | None,
    ) -> None:
        self.cash_balance = cash_balance
        self.positions = tuple(positions)
        self.total_fees_paid = total_fees_paid
        self.last_timestamp = last_timestamp
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the ledger state."""
        if not self.cash_balance.is_finite():
            raise ExecutionNormalizationError("Ledger cash_balance must be finite.")
        _validate_non_negative_decimal(self.total_fees_paid, "total_fees_paid")
        if self.last_timestamp is not None:
            if self.last_timestamp.tzinfo is None or self.last_timestamp.utcoffset() is None:
                raise ExecutionNormalizationError(
                    "Ledger timestamps must be timezone-aware when present."
                )
            if self.last_timestamp.astimezone(timezone.utc) != self.last_timestamp:
                raise ExecutionNormalizationError(
                    "Ledger timestamps must be expressed in UTC."
                )
        symbols = [position.symbol for position in self.positions]
        if symbols != sorted(symbols):
            raise ExecutionNormalizationError("Ledger positions must be sorted by symbol.")
        if len(set(symbols)) != len(symbols):
            raise ExecutionNormalizationError(
                "Ledger positions must not contain duplicate symbols."
            )


def default_execution_policy() -> ExecutionPolicy:
    """Return the default verified policy used by the execution layer."""
    return ExecutionPolicy(
        reference_notional=Decimal("100000.00"),
        max_participation_rate=Decimal("0.2500000"),
        limit_buffer_fraction=Decimal("0.0015000"),
        fee_rate=Decimal("0.0005000"),
        min_order_fraction=Decimal("0.0100000"),
    )


def empty_execution_ledger(
    *, cash_balance: Decimal | str = Decimal("100000.00")
) -> ExecutionLedgerState:
    """Return an empty execution ledger with no open positions."""
    normalized_cash = _quantize_cash(_coerce_decimal(cash_balance, "cash_balance"))
    return ExecutionLedgerState(
        cash_balance=normalized_cash,
        positions=(),
        total_fees_paid=ZERO,
        last_timestamp=None,
    )


def position_quantity(ledger: ExecutionLedgerState, symbol: str) -> Decimal:
    """Return the signed quantity currently held for *symbol*."""
    normalized_symbol = _normalize_symbol(symbol)
    for position in ledger.positions:
        if position.symbol == normalized_symbol:
            return position.quantity
    return ZERO


def _build_local_section(
    intent: RiskApprovedIntent,
    quote: ExecutionQuote,
    *,
    policy: ExecutionPolicy,
    slice_name: ExecutionSlice,
    executable_fraction: Decimal,
    rationale: str,
    passes: bool,
) -> LocalExecutionSection:
    """Build one normalized local execution section."""
    fraction = _clamp_probability(executable_fraction)
    quantity = _quantity_from_fraction(
        fraction,
        policy.reference_notional,
        quote.mid_price,
    )
    limit_price = _limit_price(quote, intent.side, policy.limit_buffer_fraction)
    notional = _quantize_cash(quantity * limit_price)
    estimated_fee = _quantize_cash(notional * policy.fee_rate)
    participation_rate = _clamp_probability(_safe_ratio(quantity, quote.available_quantity))
    cash_delta = _cash_delta(intent.side, notional, estimated_fee)
    position_delta = _signed_quantity(intent.side, quantity)
    identity_residual = _trade_identity_residual(
        intent.side,
        quantity,
        notional,
        estimated_fee,
        cash_delta,
        position_delta,
        quote.mid_price,
    )
    return LocalExecutionSection(
        timestamp=intent.timestamp,
        symbol=intent.symbol,
        slice_name=slice_name,
        venue=quote.venue,
        side=intent.side,
        style=intent.style,
        approved_fraction=intent.approved_fraction,
        executable_fraction=fraction,
        reference_notional=policy.reference_notional,
        reference_price=quote.mid_price,
        limit_price=limit_price,
        quantity=quantity,
        notional=notional,
        estimated_fee=estimated_fee,
        participation_rate=participation_rate,
        fee_rate=policy.fee_rate,
        cash_delta=cash_delta,
        position_delta=position_delta,
        identity_residual=identity_residual,
        risk_bounds=intent.risk_bounds,
        binding=fraction < intent.approved_fraction,
        passes=passes and identity_residual == ZERO,
        thesis=_local_thesis(slice_name, intent),
        rationale=rationale,
    )


def _build_arrival_section(
    intent: RiskApprovedIntent,
    quote: ExecutionQuote,
    policy: ExecutionPolicy,
) -> LocalExecutionSection:
    """Build the arrival-local section for one risk-approved intent."""
    rationale = (
        "limit price stays close to the current quote neighborhood so the descent "
        "respects local market topology"
    )
    return _build_local_section(
        intent,
        quote,
        policy=policy,
        slice_name="arrival",
        executable_fraction=intent.approved_fraction,
        rationale=rationale,
        passes=intent.approval_status == "risk_approved" and intent.side != "flat",
    )


def _build_impact_section(
    intent: RiskApprovedIntent,
    quote: ExecutionQuote,
    policy: ExecutionPolicy,
) -> LocalExecutionSection:
    """Build the impact-local section for one risk-approved intent."""
    max_quantity = _quantize_size(quote.available_quantity * policy.max_participation_rate)
    base_quantity = _quantity_from_fraction(
        intent.approved_fraction,
        policy.reference_notional,
        quote.mid_price,
    )
    executable_quantity = min(base_quantity, max_quantity)
    executable_fraction = _fraction_from_quantity(
        executable_quantity,
        quote.mid_price,
        policy.reference_notional,
    )
    rationale = (
        "local liquidity clips the trade onto the participation overlap when the "
        "full risk-approved target would be too large"
    )
    return _build_local_section(
        intent,
        quote,
        policy=policy,
        slice_name="impact",
        executable_fraction=executable_fraction,
        rationale=rationale,
        passes=executable_quantity > ZERO
        and _safe_ratio(executable_quantity, quote.available_quantity)
        <= policy.max_participation_rate,
    )


def _build_identity_section(
    intent: RiskApprovedIntent,
    quote: ExecutionQuote,
    policy: ExecutionPolicy,
) -> LocalExecutionSection:
    """Build the identity-local section for one risk-approved intent."""
    executable_fraction = (
        intent.approved_fraction
        if intent.approved_fraction >= policy.min_order_fraction
        else ZERO
    )
    rationale = (
        "cash and position updates remain exact only when the descended order is "
        "non-trivial on the execution lattice"
    )
    return _build_local_section(
        intent,
        quote,
        policy=policy,
        slice_name="identity",
        executable_fraction=executable_fraction,
        rationale=rationale,
        passes=executable_fraction >= policy.min_order_fraction,
    )


def build_execution_cover(
    intents: Iterable[RiskApprovedIntent],
    *,
    quotes_by_symbol: Mapping[str, ExecutionQuote],
    policy: ExecutionPolicy | None = None,
) -> list[LocalExecutionSection]:
    """Build the local execution cover for a batch of risk-approved intents."""
    resolved_policy = policy or default_execution_policy()
    sections: list[LocalExecutionSection] = []
    for index, intent in enumerate(intents):
        if intent.approval_status != "risk_approved":
            continue
        quote = _resolve_quote(intent.symbol, quotes_by_symbol)
        try:
            sections.extend(
                (
                    _build_arrival_section(intent, quote, resolved_policy),
                    _build_impact_section(intent, quote, resolved_policy),
                    _build_identity_section(intent, quote, resolved_policy),
                )
            )
        except ExecutionError as exc:
            raise ExecutionNormalizationError(
                f"Failed to build execution cover at intent index {index}: {exc}"
            ) from exc
    return sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.slice_name))


def restrict_execution_sections(
    sections: Iterable[LocalExecutionSection],
    *,
    symbols: Collection[str] | None = None,
    start: datetime | None = None,
    end: datetime | None = None,
    slices: Collection[ExecutionSlice] | None = None,
    venues: Collection[str] | None = None,
) -> list[LocalExecutionSection]:
    """Restrict local execution sections to a sub-cover."""
    normalized_symbols = (
        {_normalize_symbol(symbol) for symbol in symbols} if symbols is not None else None
    )
    start_bound = _normalize_timestamp(start, "start") if start is not None else None
    end_bound = _normalize_timestamp(end, "end") if end is not None else None
    normalized_slices = set(slices) if slices is not None else None
    normalized_venues = (
        {_normalize_name(venue, "venues") for venue in venues}
        if venues is not None
        else None
    )
    if normalized_slices is not None:
        unknown = normalized_slices.difference(SLICES)
        if unknown:
            raise ExecutionRestrictionError(
                f"Unknown execution slices in restriction: {sorted(unknown)!r}."
            )
    if start_bound is not None and end_bound is not None and end_bound < start_bound:
        raise ExecutionRestrictionError("Restriction end time cannot precede start time.")
    restricted: list[LocalExecutionSection] = []
    for section in sections:
        if normalized_symbols is not None and section.symbol not in normalized_symbols:
            continue
        if start_bound is not None and section.timestamp < start_bound:
            continue
        if end_bound is not None and section.timestamp > end_bound:
            continue
        if normalized_slices is not None and section.slice_name not in normalized_slices:
            continue
        if normalized_venues is not None and section.venue not in normalized_venues:
            continue
        restricted.append(section)
    return sorted(restricted, key=lambda item: (item.timestamp, item.symbol, item.slice_name))


def group_execution_overlaps(
    sections: Iterable[LocalExecutionSection],
) -> dict[ExecutionKey, list[LocalExecutionSection]]:
    """Group local execution sections by the overlap key of the trading cover."""
    grouped: dict[ExecutionKey, list[LocalExecutionSection]] = {}
    for section in sections:
        grouped.setdefault(section.execution_key(), []).append(section)
    for members in grouped.values():
        members.sort(key=lambda item: item.slice_name)
    return dict(sorted(grouped.items(), key=lambda item: item[0]))


def _build_certificate(
    key: ExecutionKey,
    members: Sequence[LocalExecutionSection],
    *,
    fraction_tolerance: Decimal,
    price_tolerance: Decimal,
    participation_tolerance: Decimal,
    identity_tolerance: Decimal,
    h1_tolerance: Decimal,
) -> ExecutionCocycleCertificate:
    """Build the execution cocycle certificate for one overlap class."""
    slices = _require_unique_slices(members, key)
    fraction_gap = _max_gap(
        [member.executable_fraction for member in members], FRACTION_QUANTUM
    )
    reference_price = _median_decimal(
        [member.reference_price for member in members], PRICE_QUANTUM
    )
    price_gap = _safe_ratio(
        _max_gap([member.limit_price for member in members], PRICE_QUANTUM),
        reference_price,
    )
    participation_gap = _max_gap(
        [member.participation_rate for member in members], FRACTION_QUANTUM
    )
    identity_gap = max(
        (
            _safe_ratio(member.identity_residual, member.reference_notional)
            for member in members
        ),
        default=ZERO,
    )
    corrections = [
        _quantize_fraction(member.approved_fraction - member.executable_fraction)
        for member in members
    ]
    triple_residual = _triple_overlap_residual(corrections)
    h1_obstruction = _quantize_fraction(
        fraction_gap + price_gap + participation_gap + identity_gap + triple_residual
    )
    passes = (
        all(member.passes for member in members)
        and fraction_gap <= fraction_tolerance
        and price_gap <= price_tolerance
        and participation_gap <= participation_tolerance
        and identity_gap <= identity_tolerance
        and h1_obstruction <= h1_tolerance
    )
    if passes:
        reason = "local execution slices agree and the H^1 obstruction remains bounded"
    else:
        reason = (
            "execution slices disagree on overlap data: "
            f"fraction_gap={fraction_gap}, "
            f"price_gap={price_gap}, "
            f"participation_gap={participation_gap}, "
            f"identity_gap={identity_gap}, "
            f"triple_residual={triple_residual}, "
            f"h1_obstruction={h1_obstruction}"
        )
    return ExecutionCocycleCertificate(
        key=key,
        slices=slices,
        fraction_gap=fraction_gap,
        price_gap=price_gap,
        participation_gap=participation_gap,
        identity_gap=identity_gap,
        triple_overlap_residual=triple_residual,
        h1_obstruction=h1_obstruction,
        passes=passes,
        reason=reason,
    )


def check_execution_cocycle(
    sections: Sequence[LocalExecutionSection],
    *,
    fraction_tolerance: Decimal | str = Decimal("0.1500000"),
    price_tolerance: Decimal | str = Decimal("0.0100000"),
    participation_tolerance: Decimal | str = Decimal("0.2500000"),
    identity_tolerance: Decimal | str = Decimal("0.0000100"),
    h1_tolerance: Decimal | str | None = None,
) -> tuple[ExecutionCocycleCertificate, ...]:
    """Check whether local execution sections glue on each overlap."""
    resolved_fraction_tolerance = _resolve_tolerance(
        fraction_tolerance, "fraction_tolerance"
    )
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_participation_tolerance = _resolve_tolerance(
        participation_tolerance, "participation_tolerance"
    )
    resolved_identity_tolerance = _resolve_tolerance(
        identity_tolerance, "identity_tolerance"
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_fraction_tolerance
            + resolved_price_tolerance
            + resolved_participation_tolerance
            + resolved_identity_tolerance
        )
    )
    grouped = group_execution_overlaps(sections)
    certificates = [
        _build_certificate(
            key,
            members,
            fraction_tolerance=resolved_fraction_tolerance,
            price_tolerance=resolved_price_tolerance,
            participation_tolerance=resolved_participation_tolerance,
            identity_tolerance=resolved_identity_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
        for key, members in grouped.items()
    ]
    return tuple(certificates)


def glue_execution_sections(
    sections: Sequence[LocalExecutionSection],
    *,
    fraction_tolerance: Decimal | str = Decimal("0.1500000"),
    price_tolerance: Decimal | str = Decimal("0.0100000"),
    participation_tolerance: Decimal | str = Decimal("0.2500000"),
    identity_tolerance: Decimal | str = Decimal("0.0000100"),
    h1_tolerance: Decimal | str | None = None,
    min_order_fraction: Decimal | str | None = None,
) -> list[GlobalExecutionSection]:
    """Glue local execution slices into coherent global execution sections."""
    resolved_fraction_tolerance = _resolve_tolerance(
        fraction_tolerance, "fraction_tolerance"
    )
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_participation_tolerance = _resolve_tolerance(
        participation_tolerance, "participation_tolerance"
    )
    resolved_identity_tolerance = _resolve_tolerance(
        identity_tolerance, "identity_tolerance"
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_fraction_tolerance
            + resolved_price_tolerance
            + resolved_participation_tolerance
            + resolved_identity_tolerance
        )
    )
    resolved_min_order = (
        _resolve_tolerance(min_order_fraction, "min_order_fraction")
        if min_order_fraction is not None
        else default_execution_policy().min_order_fraction
    )
    grouped = group_execution_overlaps(sections)
    certificates = {
        certificate.key: certificate
        for certificate in check_execution_cocycle(
            sections,
            fraction_tolerance=resolved_fraction_tolerance,
            price_tolerance=resolved_price_tolerance,
            participation_tolerance=resolved_participation_tolerance,
            identity_tolerance=resolved_identity_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    }
    glued: list[GlobalExecutionSection] = []
    for key, members in grouped.items():
        certificate = certificates[key]
        certificate.assert_passes()
        venue = _require_unique_value([member.venue for member in members], key, "venue")
        side = _require_unique_value([member.side for member in members], key, "side")
        style = _require_unique_value([member.style for member in members], key, "style")
        reference_notional = _require_unique_value(
            [member.reference_notional for member in members], key, "reference_notional"
        )
        fee_rate = _require_unique_value([member.fee_rate for member in members], key, "fee_rate")
        risk_bounds = _require_unique_value(
            [member.risk_bounds for member in members], key, "risk_bounds"
        )
        approved_fraction = _median_decimal(
            [member.approved_fraction for member in members], FRACTION_QUANTUM
        )
        quantity = min(member.quantity for member in members)
        reference_price = _median_decimal(
            [member.reference_price for member in members], PRICE_QUANTUM
        )
        executable_fraction = _fraction_from_quantity(
            quantity,
            reference_price,
            reference_notional,
        )
        limit_price = (
            min(member.limit_price for member in members)
            if side == "short"
            else max(member.limit_price for member in members)
        )
        notional = _quantize_cash(quantity * limit_price)
        estimated_fee = _quantize_cash(notional * fee_rate)
        cash_delta = _cash_delta(side, notional, estimated_fee)
        position_delta = _signed_quantity(side, quantity)
        aggregate_participation = _clamp_probability(
            max(member.participation_rate for member in members)
        )
        identity_residual = max(member.identity_residual for member in members)
        gluing_score = _gluing_score(certificate.h1_obstruction, resolved_h1_tolerance)
        order_status: OrderStatus
        if side != "flat" and executable_fraction >= resolved_min_order:
            order_status = "ready"
        else:
            order_status = "blocked"
        binding_slices = [member.slice_name for member in members if member.binding]
        glued.append(
            GlobalExecutionSection(
                timestamp=key[0],
                symbol=key[1],
                slices=certificate.slices,
                venue=venue,
                side=side,
                style=style,
                approved_fraction=approved_fraction,
                executable_fraction=executable_fraction,
                reference_notional=reference_notional,
                reference_price=reference_price,
                limit_price=limit_price,
                quantity=quantity,
                notional=notional,
                estimated_fee=estimated_fee,
                fee_rate=fee_rate,
                cash_delta=cash_delta,
                position_delta=position_delta,
                aggregate_participation=aggregate_participation,
                identity_residual=identity_residual,
                risk_bounds=risk_bounds,
                gluing_score=gluing_score,
                order_status=order_status,
                thesis=_global_thesis(order_status),
                rationale=_global_rationale(
                    order_status,
                    executable_fraction,
                    binding_slices,
                ),
            )
        )
    return sorted(glued, key=lambda item: (item.timestamp, item.symbol))


def place_orders(sections: Iterable[GlobalExecutionSection]) -> list[ExecutableOrder]:
    """Turn glued execution sections into placeable or explicitly blocked orders."""
    orders: list[ExecutableOrder] = []
    for index, section in enumerate(sections):
        try:
            orders.append(
                ExecutableOrder(
                    timestamp=section.timestamp,
                    symbol=section.symbol,
                    venue=section.venue,
                    side=section.side,
                    style=section.style,
                    approved_fraction=section.approved_fraction,
                    executable_fraction=section.executable_fraction,
                    reference_notional=section.reference_notional,
                    reference_price=section.reference_price,
                    limit_price=section.limit_price,
                    quantity=section.quantity,
                    notional=section.notional,
                    estimated_fee=section.estimated_fee,
                    fee_rate=section.fee_rate,
                    risk_bounds=section.risk_bounds,
                    gluing_score=section.gluing_score,
                    order_status=section.order_status,
                    thesis=section.thesis,
                    rationale=_order_reason(section.order_status),
                )
            )
        except ExecutionError as exc:
            raise ExecutionNormalizationError(
                f"Failed to place order at execution index {index}: {exc}"
            ) from exc
    return sorted(orders, key=lambda item: (item.timestamp, item.symbol))


def executable_orders(orders: Iterable[ExecutableOrder]) -> list[ExecutableOrder]:
    """Return only those execution candidates that are ready to be placed."""
    return [order for order in orders if order.order_status == "ready"]


def simulate_fills(
    orders: Iterable[ExecutableOrder],
    *,
    fill_ratio_by_symbol: Mapping[str, Decimal] | None = None,
    fill_price_by_symbol: Mapping[str, Decimal] | None = None,
) -> list[FillReport]:
    """Simulate fills for ready orders under simple deterministic execution rules."""
    ratio_mapping = (
        {_normalize_symbol(key): value for key, value in fill_ratio_by_symbol.items()}
        if fill_ratio_by_symbol is not None
        else {}
    )
    price_mapping = (
        {_normalize_symbol(key): value for key, value in fill_price_by_symbol.items()}
        if fill_price_by_symbol is not None
        else {}
    )
    fills: list[FillReport] = []
    for index, order in enumerate(orders):
        if order.order_status != "ready":
            continue
        try:
            raw_ratio = ratio_mapping.get(order.symbol, ONE)
            fill_ratio = _clamp_probability(_coerce_decimal(raw_ratio, "fill_ratio"))
            quantity = _quantize_size(order.quantity * fill_ratio)
            if quantity == ZERO:
                continue
            raw_fill_price = price_mapping.get(order.symbol, order.limit_price)
            fill_price = _quantize_price(_coerce_decimal(raw_fill_price, "fill_price"))
            if order.side == "long" and fill_price > order.limit_price:
                raise ExecutionNormalizationError(
                    "Long fills cannot occur above the order limit price."
                )
            if order.side == "short" and fill_price < order.limit_price:
                raise ExecutionNormalizationError(
                    "Short fills cannot occur below the order limit price."
                )
            gross_notional = _quantize_cash(quantity * fill_price)
            fee = _quantize_cash(gross_notional * order.fee_rate)
            cash_delta = _cash_delta(order.side, gross_notional, fee)
            position_delta = _signed_quantity(order.side, quantity)
            fill_status: FillStatus = "filled" if fill_ratio >= ONE else "partial"
            fills.append(
                FillReport(
                    timestamp=order.timestamp,
                    symbol=order.symbol,
                    venue=order.venue,
                    side=order.side,
                    style=order.style,
                    quantity=quantity,
                    fill_price=fill_price,
                    gross_notional=gross_notional,
                    fee=fee,
                    cash_delta=cash_delta,
                    position_delta=position_delta,
                    fill_ratio=fill_ratio,
                    fill_status=fill_status,
                )
            )
        except ExecutionError as exc:
            raise ExecutionNormalizationError(
                f"Failed to simulate fill at order index {index}: {exc}"
            ) from exc
    return sorted(fills, key=lambda item: (item.timestamp, item.symbol))


def apply_fills(
    ledger: ExecutionLedgerState,
    fills: Iterable[FillReport],
) -> ExecutionLedgerState:
    """Apply realized fills to the execution ledger."""
    cash_balance = ledger.cash_balance
    total_fees_paid = ledger.total_fees_paid
    last_timestamp = ledger.last_timestamp
    positions = {position.symbol: position.quantity for position in ledger.positions}
    for index, fill in enumerate(fills):
        try:
            cash_balance = _quantize_cash(cash_balance + fill.cash_delta)
            total_fees_paid = _quantize_cash(total_fees_paid + fill.fee)
            updated_quantity = _quantize_size(
                positions.get(fill.symbol, ZERO) + fill.position_delta
            )
            if updated_quantity == ZERO:
                positions.pop(fill.symbol, None)
            else:
                positions[fill.symbol] = updated_quantity
            if last_timestamp is None or fill.timestamp > last_timestamp:
                last_timestamp = fill.timestamp
        except (ArithmeticError, KeyError) as exc:
            raise FillApplicationError(
                f"Failed to apply fill at index {index}: {exc}"
            ) from exc
    canonical_positions = tuple(
        PositionBalance(symbol=symbol, quantity=quantity)
        for symbol, quantity in sorted(positions.items())
    )
    return ExecutionLedgerState(
        cash_balance=cash_balance,
        positions=canonical_positions,
        total_fees_paid=total_fees_paid,
        last_timestamp=last_timestamp,
    )


def execution_schema_version() -> str:
    """Return the schema version of the high-level execution bundle."""
    return EXECUTION_SCHEMA_VERSION


def _approved_intent_signature(intent: RiskApprovedIntent) -> str:
    """Return a stable signature for one risk-approved input intent."""
    return _stable_digest(
        [
            intent.timestamp.isoformat(),
            intent.symbol,
            intent.side,
            intent.style,
            str(intent.target_fraction),
            str(intent.approved_fraction),
            str(intent.alpha_score),
            str(intent.conviction),
            str(intent.risk_bounds.max_position_fraction),
            str(intent.risk_bounds.stop_loss_fraction),
            str(intent.risk_bounds.take_profit_fraction),
            str(intent.risk_bounds.max_holding_periods),
            str(intent.risk_bounds.conviction_floor),
            str(intent.risk_bounds.h1_buffer),
            str(intent.gluing_score),
            intent.approval_status,
            intent.thesis,
            intent.rationale,
        ]
    )


def _quote_signature(quote: ExecutionQuote) -> str:
    """Return a stable signature for one executable quote."""
    return _stable_digest(
        [
            quote.timestamp.isoformat(),
            quote.symbol,
            quote.venue,
            str(quote.bid_price),
            str(quote.ask_price),
            str(quote.available_quantity),
        ]
    )


def _local_execution_signature(section: LocalExecutionSection) -> str:
    """Return a stable signature for one local execution section."""
    return _stable_digest(
        [
            section.timestamp.isoformat(),
            section.symbol,
            section.slice_name,
            section.venue,
            section.side,
            section.style,
            str(section.approved_fraction),
            str(section.executable_fraction),
            str(section.reference_notional),
            str(section.reference_price),
            str(section.limit_price),
            str(section.quantity),
            str(section.notional),
            str(section.estimated_fee),
            str(section.participation_rate),
            str(section.fee_rate),
            str(section.cash_delta),
            str(section.position_delta),
            str(section.identity_residual),
            str(section.binding),
            str(section.passes),
            section.thesis,
            section.rationale,
        ]
    )


def _global_execution_signature(section: GlobalExecutionSection) -> str:
    """Return a stable signature for one glued execution section."""
    return _stable_digest(
        [
            section.timestamp.isoformat(),
            section.symbol,
            *section.slices,
            section.venue,
            section.side,
            section.style,
            str(section.approved_fraction),
            str(section.executable_fraction),
            str(section.reference_notional),
            str(section.reference_price),
            str(section.limit_price),
            str(section.quantity),
            str(section.notional),
            str(section.estimated_fee),
            str(section.fee_rate),
            str(section.cash_delta),
            str(section.position_delta),
            str(section.aggregate_participation),
            str(section.identity_residual),
            str(section.gluing_score),
            section.order_status,
            section.thesis,
            section.rationale,
        ]
    )


def _order_signature(order: ExecutableOrder) -> str:
    """Return a stable signature for one placeable order."""
    return _stable_digest(
        [
            order.timestamp.isoformat(),
            order.symbol,
            order.venue,
            order.side,
            order.style,
            str(order.approved_fraction),
            str(order.executable_fraction),
            str(order.reference_notional),
            str(order.reference_price),
            str(order.limit_price),
            str(order.quantity),
            str(order.notional),
            str(order.estimated_fee),
            str(order.fee_rate),
            str(order.gluing_score),
            order.order_status,
            order.thesis,
            order.rationale,
        ]
    )


def _fill_signature(fill: FillReport) -> str:
    """Return a stable signature for one realized fill."""
    return _stable_digest(
        [
            fill.timestamp.isoformat(),
            fill.symbol,
            fill.venue,
            fill.side,
            fill.style,
            str(fill.quantity),
            str(fill.fill_price),
            str(fill.gross_notional),
            str(fill.fee),
            str(fill.cash_delta),
            str(fill.position_delta),
            str(fill.fill_ratio),
            fill.fill_status,
        ]
    )


def _ledger_signature(ledger: ExecutionLedgerState) -> str:
    """Return a stable signature for one execution ledger state."""
    parts = [
        str(ledger.cash_balance),
        str(ledger.total_fees_paid),
        ledger.last_timestamp.isoformat() if ledger.last_timestamp is not None else "none",
    ]
    parts.extend(f"{position.symbol}:{position.quantity}" for position in ledger.positions)
    return _stable_digest(parts)


def _execution_input_signature(intents: tuple[RiskApprovedIntent, ...]) -> str:
    """Return a stable signature for direct execution input."""
    return _stable_digest(_approved_intent_signature(intent) for intent in intents)


def _resolve_execution_input(
    execution_input: ExecutionInput,
) -> tuple[
    tuple[RiskApprovedIntent, ...],
    tuple[RiskResearchIdea, ...],
    str,
    ExecutionProofMode,
    bool,
    tuple[str, ...],
]:
    """Normalize execution input into approved intents and upstream metadata."""
    if isinstance(execution_input, RiskEngineBundle):
        intents = tuple(execution_input.executable_intents)
        return (
            intents,
            tuple(execution_input.research_ideas),
            execution_input.data_signature,
            execution_input.policy.proof_obligation,
            execution_input.policy.paper_trading_required,
            execution_input.policy.order_rejection_conditions,
        )

    intents = tuple(execution_input)
    for index, intent in enumerate(intents):
        if not isinstance(intent, RiskApprovedIntent):
            raise ExecutionNormalizationError(
                f"Execution input at index {index} is not a RiskApprovedIntent."
            )
        if intent.approval_status != "risk_approved":
            raise ExecutionNormalizationError(
                "Execution build requires only risk-approved intents as direct input."
            )
    return (
        intents,
        (),
        _execution_input_signature(intents),
        "smt_required",
        True,
        (
            "reject_failed_gluing",
            "reject_kill_switch",
            "reject_unverified_risk_core",
        ),
    )


def _resolved_quotes(
    intents: Sequence[RiskApprovedIntent],
    quotes_by_symbol: Mapping[str, ExecutionQuote],
) -> tuple[ExecutionQuote, ...]:
    """Resolve one canonical quote for each approved symbol."""
    quotes = {
        intent.symbol: _resolve_quote(intent.symbol, quotes_by_symbol)
        for intent in intents
    }
    return tuple(sorted(quotes.values(), key=lambda item: (item.timestamp, item.symbol, item.venue)))


def _spread_bps(quote: ExecutionQuote) -> Decimal:
    """Return the normalized quoted spread in basis points."""
    return _quantize_edge(
        _safe_ratio(quote.ask_price - quote.bid_price, quote.mid_price) * Decimal("10000")
    )


def _matching_risk_idea(
    section: GlobalExecutionSection,
    upstream_ideas: Sequence[RiskResearchIdea],
) -> RiskResearchIdea | None:
    """Return the strongest upstream risk idea aligned with one execution section."""
    matches = [
        idea
        for idea in upstream_ideas
        if idea.symbol == section.symbol
        and idea.as_of == section.timestamp
        and idea.side == section.side
    ]
    if not matches:
        return None
    return max(
        matches,
        key=lambda idea: (idea.expected_edge_bps, idea.approved_fraction),
    )


def _execution_validation_plan(matched_idea: RiskResearchIdea | None) -> str:
    """Return the validation plan carried by one execution research idea."""
    inherited = (
        matched_idea.validation_plan
        if matched_idea is not None
        else "derive the thesis from versioned risk approvals and executable quotes"
    )
    return (
        f"{inherited}; replay paper-trading fills with immutable audit metadata; "
        "check arrival, impact, and identity cocycles under stress scenarios; "
        "verify no lookahead bias, survivorship bias, or data leakage contaminates the replay"
    )


def _execution_expected_edge_bps(
    section: GlobalExecutionSection,
    quote: ExecutionQuote,
    matched_idea: RiskResearchIdea | None,
) -> Decimal:
    """Estimate the edge preserved after execution-local clipping and spread."""
    inherited = matched_idea.expected_edge_bps if matched_idea is not None else ZERO
    spread_penalty = _spread_bps(quote)
    computed = (
        section.gluing_score * Decimal("18")
        + section.executable_fraction * Decimal("70")
        + (ONE - section.aggregate_participation) * Decimal("15")
        - spread_penalty
    )
    return _quantize_edge(max(Decimal("0.2500"), inherited, computed))


def _expected_slippage_bps(
    section: GlobalExecutionSection,
    quote: ExecutionQuote,
) -> Decimal:
    """Estimate expected slippage in basis points for one glued execution section."""
    price_distance = _safe_ratio(abs(section.limit_price - quote.mid_price), quote.mid_price)
    return _quantize_edge(
        price_distance * Decimal("10000")
        + section.aggregate_participation * Decimal("8")
    )


@dataclass(init=False)
class ExecutionResearchIdea:
    """A testable execution-aware market thesis descended from risk-approved ideas."""

    symbol: str
    as_of: datetime
    venue: str
    side: Literal["long", "short"]
    hypothesis: str
    validation_plan: str
    executable_fraction: Decimal
    expected_edge_bps: Decimal
    expected_slippage_bps: Decimal
    provenance: str
    data_signature: str

    def __init__(
        self,
        symbol: str,
        as_of: datetime,
        venue: str,
        side: Literal["long", "short"],
        hypothesis: str,
        validation_plan: str,
        executable_fraction: Decimal,
        expected_edge_bps: Decimal,
        expected_slippage_bps: Decimal,
        provenance: str,
        data_signature: str,
    ) -> None:
        self.symbol = symbol
        self.as_of = as_of
        self.venue = venue
        self.side = side
        self.hypothesis = hypothesis
        self.validation_plan = validation_plan
        self.executable_fraction = executable_fraction
        self.expected_edge_bps = expected_edge_bps
        self.expected_slippage_bps = expected_slippage_bps
        self.provenance = provenance
        self.data_signature = data_signature
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the execution research idea."""
        normalized_timestamp = _normalize_timestamp(self.as_of, "as_of")
        normalized_symbol = _normalize_symbol(self.symbol)
        normalized_venue = _normalize_name(self.venue, "venue")
        if self.side not in {"long", "short"}:
            raise ExecutionNormalizationError(
                "Execution research idea side must be 'long' or 'short'."
            )
        if (
            not self.hypothesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
            or not self.data_signature
        ):
            raise ExecutionNormalizationError(
                "Execution research ideas require narrative fields and a reproducibility signature."
            )
        _validate_probability(self.executable_fraction, "executable_fraction")
        if not self.expected_edge_bps.is_finite() or self.expected_edge_bps <= ZERO:
            raise ExecutionNormalizationError(
                "Execution research ideas require a positive expected edge."
            )
        if (
            not self.expected_slippage_bps.is_finite()
            or self.expected_slippage_bps < ZERO
        ):
            raise ExecutionNormalizationError(
                "Execution research ideas require a non-negative slippage estimate."
            )
        self.as_of = normalized_timestamp
        self.symbol = normalized_symbol
        self.venue = normalized_venue
        self.expected_edge_bps = _quantize_edge(self.expected_edge_bps)
        self.expected_slippage_bps = _quantize_edge(self.expected_slippage_bps)


def _discover_execution_research_ideas(
    sections: Sequence[GlobalExecutionSection],
    *,
    quotes: Mapping[str, ExecutionQuote],
    upstream_ideas: Sequence[RiskResearchIdea],
) -> tuple[ExecutionResearchIdea, ...]:
    """Discover execution-aware, testable ideas from glued execution sections."""
    candidates = [section for section in sections if section.side in {"long", "short"}]
    if not candidates and sections:
        candidates = [
            max(
                sections,
                key=lambda section: (
                    section.gluing_score,
                    section.executable_fraction,
                    ONE - section.aggregate_participation,
                ),
            )
        ]
    ideas: list[ExecutionResearchIdea] = []
    for section in candidates:
        quote = quotes[section.symbol]
        matched_idea = _matching_risk_idea(section, upstream_ideas)
        spread_bps = _spread_bps(quote)
        expected_edge_bps = _execution_expected_edge_bps(section, quote, matched_idea)
        expected_slippage_bps = _expected_slippage_bps(section, quote)
        inherited = matched_idea.thesis if matched_idea is not None else section.thesis
        hypothesis = (
            f"{section.side} {section.symbol} on {section.venue}: preserve the "
            f"risk-approved thesis '{inherited}' by routing through arrival/impact/identity "
            f"slices with gluing_score={section.gluing_score}, spread_bps={spread_bps}, "
            f"and executable_fraction={section.executable_fraction}"
        )
        validation_plan = _execution_validation_plan(matched_idea)
        provenance = (
            "risk_engine_extension"
            if matched_idea is not None
            else "execution_extension"
        )
        data_signature = _stable_digest(
            [
                _global_execution_signature(section),
                _quote_signature(quote),
                matched_idea.data_signature if matched_idea is not None else "execution_only",
                hypothesis,
                validation_plan,
            ]
        )
        ideas.append(
            ExecutionResearchIdea(
                symbol=section.symbol,
                as_of=section.timestamp,
                venue=section.venue,
                side=section.side if section.side in {"long", "short"} else "long",
                hypothesis=hypothesis,
                validation_plan=validation_plan,
                executable_fraction=section.executable_fraction,
                expected_edge_bps=expected_edge_bps,
                expected_slippage_bps=expected_slippage_bps,
                provenance=provenance,
                data_signature=data_signature,
            )
        )
    return tuple(sorted(ideas, key=lambda item: (item.as_of, item.symbol, item.venue)))


@dataclass(init=False)
class ExecutionBundle:
    """High-level bundle produced by the execution refinement site."""

    schema_version: str
    approved_intents: tuple[RiskApprovedIntent, ...]
    quotes: tuple[ExecutionQuote, ...]
    local_sections: tuple[LocalExecutionSection, ...]
    global_sections: tuple[GlobalExecutionSection, ...]
    orders: tuple[ExecutableOrder, ...]
    fills: tuple[FillReport, ...]
    ledger: ExecutionLedgerState
    research_ideas: tuple[ExecutionResearchIdea, ...]
    policy: ExecutionPolicy
    order_rejection_conditions: tuple[str, ...]
    proof_obligation: ExecutionProofMode
    paper_trading_required: bool
    fraction_tolerance: Decimal
    price_tolerance: Decimal
    participation_tolerance: Decimal
    identity_tolerance: Decimal
    h1_tolerance: Decimal
    min_order_fraction: Decimal
    starting_cash_balance: Decimal
    upstream_data_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __init__(
        self,
        schema_version: str,
        approved_intents: tuple[RiskApprovedIntent, ...],
        quotes: tuple[ExecutionQuote, ...],
        local_sections: tuple[LocalExecutionSection, ...],
        global_sections: tuple[GlobalExecutionSection, ...],
        orders: tuple[ExecutableOrder, ...],
        fills: tuple[FillReport, ...],
        ledger: ExecutionLedgerState,
        research_ideas: tuple[ExecutionResearchIdea, ...],
        policy: ExecutionPolicy,
        order_rejection_conditions: tuple[str, ...],
        proof_obligation: ExecutionProofMode,
        paper_trading_required: bool,
        fraction_tolerance: Decimal,
        price_tolerance: Decimal,
        participation_tolerance: Decimal,
        identity_tolerance: Decimal,
        h1_tolerance: Decimal,
        min_order_fraction: Decimal,
        starting_cash_balance: Decimal,
        upstream_data_signature: str,
        data_signature: str,
        audit_metadata: tuple[tuple[str, str], ...],
    ) -> None:
        self.schema_version = schema_version
        self.approved_intents = tuple(approved_intents)
        self.quotes = tuple(quotes)
        self.local_sections = tuple(local_sections)
        self.global_sections = tuple(global_sections)
        self.orders = tuple(orders)
        self.fills = tuple(fills)
        self.ledger = ledger
        self.research_ideas = tuple(research_ideas)
        self.policy = policy
        self.order_rejection_conditions = tuple(order_rejection_conditions)
        self.proof_obligation = proof_obligation
        self.paper_trading_required = paper_trading_required
        self.fraction_tolerance = fraction_tolerance
        self.price_tolerance = price_tolerance
        self.participation_tolerance = participation_tolerance
        self.identity_tolerance = identity_tolerance
        self.h1_tolerance = h1_tolerance
        self.min_order_fraction = min_order_fraction
        self.starting_cash_balance = starting_cash_balance
        self.upstream_data_signature = upstream_data_signature
        self.data_signature = data_signature
        self.audit_metadata = tuple(audit_metadata)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate top-level execution bundle invariants."""
        if self.schema_version != execution_schema_version():
            raise ExecutionNormalizationError("Execution bundle schema version mismatch.")
        if not self.approved_intents:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one risk-approved intent."
            )
        if not self.quotes:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one executable quote."
            )
        if not self.local_sections:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one local execution section."
            )
        if not self.global_sections:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one glued execution section."
            )
        if not self.orders:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one placeable or blocked order."
            )
        if not self.research_ideas:
            raise ExecutionNormalizationError(
                "Execution bundles require at least one testable execution research idea."
            )
        if not self.upstream_data_signature or not self.data_signature:
            raise ExecutionNormalizationError(
                "Execution bundles require deterministic reproducibility signatures."
            )
        _validate_probability(self.fraction_tolerance, "fraction_tolerance")
        _validate_probability(self.price_tolerance, "price_tolerance")
        _validate_probability(self.participation_tolerance, "participation_tolerance")
        _validate_probability(self.identity_tolerance, "identity_tolerance")
        _validate_probability(self.h1_tolerance, "h1_tolerance")
        _validate_probability(self.min_order_fraction, "min_order_fraction")
        if not self.starting_cash_balance.is_finite():
            raise ExecutionNormalizationError(
                "Execution bundle starting cash balance must be finite."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise ExecutionNormalizationError(
                "Execution bundle proof obligation must be SMT-backed or machine-checked."
            )
        if not self.order_rejection_conditions:
            raise ExecutionNormalizationError(
                "Execution bundles require explicit rejection conditions."
            )

    @property
    def symbols(self) -> tuple[str, ...]:
        """Return the canonical symbols represented in the bundle."""
        return tuple(sorted({section.symbol for section in self.global_sections}))

    @property
    def executable_orders(self) -> tuple[ExecutableOrder, ...]:
        """Return the subset of orders that are ready for paper execution."""
        return tuple(executable_orders(self.orders))

    def summary(self) -> str:
        """Return a deterministic one-line summary of the bundle."""
        return execution_summary(self)


@dataclass(init=False)
class ExecutionValidationReport:
    """Validation report for an execution bundle."""

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    normalization_signatures_preserved: bool
    cocycle_checks_passed: bool
    coherent_global_sections: bool
    only_risk_approved_descend: bool
    orders_align_with_global_sections: bool
    fills_satisfy_identities: bool
    ledger_matches_fills: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    proof_obligation_satisfied: bool
    paper_trading_enforced: bool
    signature_matches: bool
    local_sections_checked: int
    global_sections_checked: int
    orders_checked: int
    fills_checked: int
    overlap_certificates: tuple[ExecutionCocycleCertificate, ...]
    messages: tuple[str, ...]

    def __init__(
        self,
        passes: bool,
        timestamp_symbol_invariants_preserved: bool,
        normalization_signatures_preserved: bool,
        cocycle_checks_passed: bool,
        coherent_global_sections: bool,
        only_risk_approved_descend: bool,
        orders_align_with_global_sections: bool,
        fills_satisfy_identities: bool,
        ledger_matches_fills: bool,
        novel_idea_present: bool,
        risk_invariants_explicit: bool,
        proof_obligation_satisfied: bool,
        paper_trading_enforced: bool,
        signature_matches: bool,
        local_sections_checked: int,
        global_sections_checked: int,
        orders_checked: int,
        fills_checked: int,
        overlap_certificates: tuple[ExecutionCocycleCertificate, ...],
        messages: tuple[str, ...],
    ) -> None:
        self.passes = passes
        self.timestamp_symbol_invariants_preserved = timestamp_symbol_invariants_preserved
        self.normalization_signatures_preserved = normalization_signatures_preserved
        self.cocycle_checks_passed = cocycle_checks_passed
        self.coherent_global_sections = coherent_global_sections
        self.only_risk_approved_descend = only_risk_approved_descend
        self.orders_align_with_global_sections = orders_align_with_global_sections
        self.fills_satisfy_identities = fills_satisfy_identities
        self.ledger_matches_fills = ledger_matches_fills
        self.novel_idea_present = novel_idea_present
        self.risk_invariants_explicit = risk_invariants_explicit
        self.proof_obligation_satisfied = proof_obligation_satisfied
        self.paper_trading_enforced = paper_trading_enforced
        self.signature_matches = signature_matches
        self.local_sections_checked = local_sections_checked
        self.global_sections_checked = global_sections_checked
        self.orders_checked = orders_checked
        self.fills_checked = fills_checked
        self.overlap_certificates = tuple(overlap_certificates)
        self.messages = tuple(messages)

    def summary(self) -> str:
        """Return a concise textual summary of the validation result."""
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} local_sections={self.local_sections_checked} "
            f"global_sections={self.global_sections_checked} orders={self.orders_checked} "
            f"fills={self.fills_checked} issues={issues}"
        )


def _execution_bundle_signature(bundle: ExecutionBundle) -> str:
    """Return a stable audit digest for the full execution bundle."""
    parts = [
        bundle.schema_version,
        bundle.policy.reproducibility_signature(),
        str(bundle.fraction_tolerance),
        str(bundle.price_tolerance),
        str(bundle.participation_tolerance),
        str(bundle.identity_tolerance),
        str(bundle.h1_tolerance),
        str(bundle.min_order_fraction),
        str(bundle.starting_cash_balance),
        bundle.proof_obligation,
        str(bundle.paper_trading_required),
        bundle.upstream_data_signature,
        *bundle.order_rejection_conditions,
    ]
    parts.append("approved_intents")
    parts.extend(_approved_intent_signature(intent) for intent in bundle.approved_intents)
    parts.append("quotes")
    parts.extend(_quote_signature(quote) for quote in bundle.quotes)
    parts.append("local_sections")
    parts.extend(_local_execution_signature(section) for section in bundle.local_sections)
    parts.append("global_sections")
    parts.extend(_global_execution_signature(section) for section in bundle.global_sections)
    parts.append("orders")
    parts.extend(_order_signature(order) for order in bundle.orders)
    parts.append("fills")
    parts.extend(_fill_signature(fill) for fill in bundle.fills)
    parts.append("ledger")
    parts.append(_ledger_signature(bundle.ledger))
    parts.append("research_ideas")
    parts.extend(idea.data_signature for idea in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


def _restriction_signatures_preserved(
    sections: tuple[LocalExecutionSection, ...],
) -> bool:
    """Return whether restricting to full support preserves local signatures."""
    if not sections:
        return True
    ordered = tuple(
        sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.slice_name))
    )
    restricted = restrict_execution_sections(
        ordered,
        symbols={section.symbol for section in ordered},
        start=ordered[0].timestamp,
        end=ordered[-1].timestamp,
        slices={section.slice_name for section in ordered},
        venues={section.venue for section in ordered},
    )
    return tuple(section.normalization_signature() for section in ordered) == tuple(
        section.normalization_signature() for section in restricted
    )


def _global_sections_coherent(
    local_sections: tuple[LocalExecutionSection, ...],
    global_sections: tuple[GlobalExecutionSection, ...],
    *,
    min_order_fraction: Decimal,
) -> bool:
    """Return whether global execution sections descend exactly from local overlaps."""
    grouped = group_execution_overlaps(local_sections)
    if len(grouped) != len(global_sections):
        return False
    for section in global_sections:
        members = grouped.get((section.timestamp, section.symbol))
        if members is None:
            return False
        if section.slices != tuple(sorted(member.slice_name for member in members)):
            return False
        if section.venue != members[0].venue:
            return False
        if section.side != members[0].side or section.style != members[0].style:
            return False
        if any(member.risk_bounds != members[0].risk_bounds for member in members[1:]):
            return False
        approved_fraction = _median_decimal(
            [member.approved_fraction for member in members], FRACTION_QUANTUM
        )
        if section.approved_fraction != approved_fraction:
            return False
        reference_notional = members[0].reference_notional
        reference_price = _median_decimal(
            [member.reference_price for member in members], PRICE_QUANTUM
        )
        quantity = min(member.quantity for member in members)
        executable_fraction = _fraction_from_quantity(
            quantity,
            reference_price,
            reference_notional,
        )
        if section.executable_fraction != executable_fraction:
            return False
        limit_price = (
            min(member.limit_price for member in members)
            if section.side == "short"
            else max(member.limit_price for member in members)
        )
        if section.limit_price != limit_price:
            return False
        if section.aggregate_participation != _clamp_probability(
            max(member.participation_rate for member in members)
        ):
            return False
        expected_status = (
            "ready"
            if section.side != "flat" and section.executable_fraction >= min_order_fraction
            else "blocked"
        )
        if section.order_status != expected_status:
            return False
    return True


def _orders_align_with_global_sections(
    global_sections: tuple[GlobalExecutionSection, ...],
    orders: tuple[ExecutableOrder, ...],
) -> bool:
    """Return whether each order descends exactly from one glued execution section."""
    if len(global_sections) != len(orders):
        return False
    order_map = {order.order_key(): order for order in orders}
    if len(order_map) != len(orders):
        return False
    for section in global_sections:
        order = order_map.get((section.timestamp, section.symbol))
        if order is None:
            return False
        if (
            order.venue != section.venue
            or order.side != section.side
            or order.style != section.style
            or order.approved_fraction != section.approved_fraction
            or order.executable_fraction != section.executable_fraction
            or order.reference_notional != section.reference_notional
            or order.reference_price != section.reference_price
            or order.limit_price != section.limit_price
            or order.quantity != section.quantity
            or order.notional != section.notional
            or order.estimated_fee != section.estimated_fee
            or order.fee_rate != section.fee_rate
            or order.risk_bounds != section.risk_bounds
            or order.gluing_score != section.gluing_score
            or order.order_status != section.order_status
        ):
            return False
    return True


def _fills_satisfy_identities(
    orders: tuple[ExecutableOrder, ...],
    fills: tuple[FillReport, ...],
) -> bool:
    """Return whether fills remain exact descendants of ready orders."""
    ready_orders = {
        order.order_key(): order
        for order in orders
        if order.order_status == "ready" and order.quantity > ZERO
    }
    if len(fills) != len(ready_orders):
        return False
    for fill in fills:
        order = ready_orders.get((fill.timestamp, fill.symbol))
        if order is None:
            return False
        if (
            fill.venue != order.venue
            or fill.side != order.side
            or fill.style != order.style
            or fill.quantity > order.quantity
        ):
            return False
        if fill.side == "long" and fill.fill_price > order.limit_price:
            return False
        if fill.side == "short" and fill.fill_price < order.limit_price:
            return False
        if _trade_identity_residual(
            fill.side,
            fill.quantity,
            fill.gross_notional,
            fill.fee,
            fill.cash_delta,
            fill.position_delta,
            fill.fill_price,
        ) != ZERO:
            return False
    return True


def _ledger_matches_fills(bundle: ExecutionBundle) -> bool:
    """Return whether the stored ledger equals replaying the stored fills."""
    expected = apply_fills(
        empty_execution_ledger(cash_balance=bundle.starting_cash_balance),
        bundle.fills,
    )
    return expected == bundle.ledger


def _risk_invariants_explicit(bundle: ExecutionBundle) -> bool:
    """Return whether the bundle carries explicit risk-critical execution metadata."""
    metadata = dict(bundle.audit_metadata)
    required_conditions = {
        "reject_failed_gluing",
        "reject_kill_switch",
        "reject_unverified_risk_core",
    }
    return (
        required_conditions.issubset(bundle.order_rejection_conditions)
        and metadata.get("audit_log") == "immutable_required"
        and metadata.get("bias_guards")
        == "lookahead_survivorship_data_leakage_blocked"
        and metadata.get("execution_mode") == "paper_only"
        and metadata.get("fill_mode") == "deterministic_paper_replay"
        and metadata.get("identity_mode") == "cash_position_coboundary_closed"
        and metadata.get("integration_mode") == "only_risk_approved_descends"
        and metadata.get("proof_obligation") == bundle.proof_obligation
        and metadata.get("paper_trading")
        == ("required" if bundle.paper_trading_required else "optional")
        and metadata.get("reproducibility")
        == "versioned_data_configuration_and_audit_signatures"
        and metadata.get("separation")
        == "research_simulation_execution_and_risk_are_decoupled"
    )


def build_execution(
    execution_input: ExecutionInput,
    *,
    quotes_by_symbol: Mapping[str, ExecutionQuote],
    policy: ExecutionPolicy | None = None,
    fraction_tolerance: Decimal | str = Decimal("0.1500000"),
    price_tolerance: Decimal | str = Decimal("0.0100000"),
    participation_tolerance: Decimal | str = Decimal("0.2500000"),
    identity_tolerance: Decimal | str = Decimal("0.0000100"),
    h1_tolerance: Decimal | str | None = None,
    min_order_fraction: Decimal | str | None = None,
    starting_cash_balance: Decimal | str | None = None,
    fill_ratio_by_symbol: Mapping[str, Decimal] | None = None,
    fill_price_by_symbol: Mapping[str, Decimal] | None = None,
) -> ExecutionBundle:
    """Build an auditable execution bundle from risk-approved intents."""
    approved_intents, upstream_ideas, upstream_signature, proof_obligation, paper_required, rejection_conditions = _resolve_execution_input(
        execution_input
    )
    if not approved_intents:
        raise ExecutionNormalizationError(
            "Execution requires at least one risk-approved intent."
        )
    resolved_policy = policy or default_execution_policy()
    resolved_fraction_tolerance = _resolve_tolerance(
        fraction_tolerance,
        "fraction_tolerance",
    )
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_participation_tolerance = _resolve_tolerance(
        participation_tolerance,
        "participation_tolerance",
    )
    resolved_identity_tolerance = _resolve_tolerance(
        identity_tolerance,
        "identity_tolerance",
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_fraction_tolerance
            + resolved_price_tolerance
            + resolved_participation_tolerance
            + resolved_identity_tolerance
        )
    )
    resolved_min_order = (
        _resolve_tolerance(min_order_fraction, "min_order_fraction")
        if min_order_fraction is not None
        else resolved_policy.min_order_fraction
    )
    resolved_starting_cash = _quantize_cash(
        _coerce_decimal(
            starting_cash_balance
            if starting_cash_balance is not None
            else resolved_policy.reference_notional,
            "starting_cash_balance",
        )
    )
    quotes = _resolved_quotes(approved_intents, quotes_by_symbol)
    quote_map = {quote.symbol: quote for quote in quotes}
    local_sections = tuple(
        build_execution_cover(
            approved_intents,
            quotes_by_symbol=quote_map,
            policy=resolved_policy,
        )
    )
    global_sections = tuple(
        glue_execution_sections(
            local_sections,
            fraction_tolerance=resolved_fraction_tolerance,
            price_tolerance=resolved_price_tolerance,
            participation_tolerance=resolved_participation_tolerance,
            identity_tolerance=resolved_identity_tolerance,
            h1_tolerance=resolved_h1_tolerance,
            min_order_fraction=resolved_min_order,
        )
    )
    orders = tuple(place_orders(global_sections))
    fills = tuple(
        simulate_fills(
            executable_orders(orders),
            fill_ratio_by_symbol=fill_ratio_by_symbol,
            fill_price_by_symbol=fill_price_by_symbol,
        )
    )
    ledger = apply_fills(
        empty_execution_ledger(cash_balance=resolved_starting_cash),
        fills,
    )
    research_ideas = _discover_execution_research_ideas(
        global_sections,
        quotes=quote_map,
        upstream_ideas=upstream_ideas,
    )
    if not research_ideas:
        raise ExecutionNormalizationError(
            "Execution must emit at least one testable idea from data-driven research."
        )
    audit_metadata = tuple(
        sorted(
            (
                ("audit_log", "immutable_required"),
                ("bias_guards", "lookahead_survivorship_data_leakage_blocked"),
                ("execution_mode", "paper_only"),
                ("fill_mode", "deterministic_paper_replay"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("identity_mode", "cash_position_coboundary_closed"),
                ("idea_mode", "execution_extension"),
                ("integration_mode", "only_risk_approved_descends"),
                (
                    "kill_switch_policy",
                    "deterministic_reject_on_unverified_or_breached_limits",
                ),
                (
                    "paper_trading",
                    "required" if paper_required else "optional",
                ),
                ("proof_obligation", proof_obligation),
                (
                    "reproducibility",
                    "versioned_data_configuration_and_audit_signatures",
                ),
                ("schema_version", execution_schema_version()),
                (
                    "separation",
                    "research_simulation_execution_and_risk_are_decoupled",
                ),
                ("upstream_signature", upstream_signature[:16]),
            )
        )
    )
    unsigned_bundle = ExecutionBundle(
        schema_version=execution_schema_version(),
        approved_intents=approved_intents,
        quotes=quotes,
        local_sections=local_sections,
        global_sections=global_sections,
        orders=orders,
        fills=fills,
        ledger=ledger,
        research_ideas=research_ideas,
        policy=resolved_policy,
        order_rejection_conditions=tuple(rejection_conditions),
        proof_obligation=proof_obligation,
        paper_trading_required=paper_required,
        fraction_tolerance=resolved_fraction_tolerance,
        price_tolerance=resolved_price_tolerance,
        participation_tolerance=resolved_participation_tolerance,
        identity_tolerance=resolved_identity_tolerance,
        h1_tolerance=resolved_h1_tolerance,
        min_order_fraction=resolved_min_order,
        starting_cash_balance=resolved_starting_cash,
        upstream_data_signature=upstream_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return ExecutionBundle(
        schema_version=unsigned_bundle.schema_version,
        approved_intents=unsigned_bundle.approved_intents,
        quotes=unsigned_bundle.quotes,
        local_sections=unsigned_bundle.local_sections,
        global_sections=unsigned_bundle.global_sections,
        orders=unsigned_bundle.orders,
        fills=unsigned_bundle.fills,
        ledger=unsigned_bundle.ledger,
        research_ideas=unsigned_bundle.research_ideas,
        policy=unsigned_bundle.policy,
        order_rejection_conditions=unsigned_bundle.order_rejection_conditions,
        proof_obligation=unsigned_bundle.proof_obligation,
        paper_trading_required=unsigned_bundle.paper_trading_required,
        fraction_tolerance=unsigned_bundle.fraction_tolerance,
        price_tolerance=unsigned_bundle.price_tolerance,
        participation_tolerance=unsigned_bundle.participation_tolerance,
        identity_tolerance=unsigned_bundle.identity_tolerance,
        h1_tolerance=unsigned_bundle.h1_tolerance,
        min_order_fraction=unsigned_bundle.min_order_fraction,
        starting_cash_balance=unsigned_bundle.starting_cash_balance,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        data_signature=_execution_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


def validate_execution(bundle: ExecutionBundle) -> ExecutionValidationReport:
    """Validate that an execution bundle still satisfies its obligations."""
    certificates = check_execution_cocycle(
        bundle.local_sections,
        fraction_tolerance=bundle.fraction_tolerance,
        price_tolerance=bundle.price_tolerance,
        participation_tolerance=bundle.participation_tolerance,
        identity_tolerance=bundle.identity_tolerance,
        h1_tolerance=bundle.h1_tolerance,
    )
    normalization_preserved = _restriction_signatures_preserved(bundle.local_sections)
    cocycle_checks_passed = all(certificate.passes for certificate in certificates)
    coherent_global_sections = _global_sections_coherent(
        bundle.local_sections,
        bundle.global_sections,
        min_order_fraction=bundle.min_order_fraction,
    )
    approved_keys = {intent.intent_key() for intent in bundle.approved_intents}
    only_risk_approved_descend = (
        all(intent.approval_status == "risk_approved" for intent in bundle.approved_intents)
        and all(section.execution_key() in approved_keys for section in bundle.local_sections)
    )
    orders_align_with_global_sections = _orders_align_with_global_sections(
        bundle.global_sections,
        bundle.orders,
    )
    fills_satisfy_identities = _fills_satisfy_identities(bundle.orders, bundle.fills)
    ledger_matches_fills = _ledger_matches_fills(bundle)
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    proof_obligation_satisfied = bundle.proof_obligation in {
        "smt_required",
        "machine_checked",
    }
    paper_trading_enforced = (
        bundle.paper_trading_required
        and dict(bundle.audit_metadata).get("paper_trading") == "required"
    )
    signature_matches = bundle.data_signature == _execution_bundle_signature(bundle)
    timestamp_symbol_invariants_preserved = normalization_preserved

    messages: list[str] = []
    if not normalization_preserved:
        messages.append("restriction signature preservation failed")
    if not cocycle_checks_passed:
        messages.append("one or more execution cocycle checks failed")
    if not coherent_global_sections:
        messages.append("global execution sections no longer descend from local overlaps")
    if not only_risk_approved_descend:
        messages.append("a non-approved intent descended toward order placement")
    if not orders_align_with_global_sections:
        messages.append("orders no longer agree with glued execution sections")
    if not fills_satisfy_identities:
        messages.append("fills no longer satisfy exact cash and position identities")
    if not ledger_matches_fills:
        messages.append("ledger state no longer matches replaying stored fills")
    if not novel_idea_present:
        messages.append("no testable data-driven execution idea is present")
    if not risk_invariants_explicit:
        messages.append("execution audit metadata does not encode explicit risk invariants")
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
        and only_risk_approved_descend
        and orders_align_with_global_sections
        and fills_satisfy_identities
        and ledger_matches_fills
        and novel_idea_present
        and risk_invariants_explicit
        and proof_obligation_satisfied
        and paper_trading_enforced
        and signature_matches
    )
    return ExecutionValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        normalization_signatures_preserved=normalization_preserved,
        cocycle_checks_passed=cocycle_checks_passed,
        coherent_global_sections=coherent_global_sections,
        only_risk_approved_descend=only_risk_approved_descend,
        orders_align_with_global_sections=orders_align_with_global_sections,
        fills_satisfy_identities=fills_satisfy_identities,
        ledger_matches_fills=ledger_matches_fills,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        proof_obligation_satisfied=proof_obligation_satisfied,
        paper_trading_enforced=paper_trading_enforced,
        signature_matches=signature_matches,
        local_sections_checked=len(bundle.local_sections),
        global_sections_checked=len(bundle.global_sections),
        orders_checked=len(bundle.orders),
        fills_checked=len(bundle.fills),
        overlap_certificates=certificates,
        messages=tuple(messages),
    )


def execution_summary(bundle: ExecutionBundle) -> str:
    """Return a deterministic summary string for the execution bundle."""
    report = validate_execution(bundle)
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.executable_fraction}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    status = "pass" if report.passes else "fail"
    ready_count = sum(order.order_status == "ready" for order in bundle.orders)
    return (
        f"execution[{bundle.schema_version}] symbols={','.join(bundle.symbols)} "
        f"approved={len(bundle.approved_intents)} local_sections={len(bundle.local_sections)} "
        f"global_sections={len(bundle.global_sections)} orders={len(bundle.orders)} "
        f"ready={ready_count} fills={len(bundle.fills)} ideas={len(bundle.research_ideas)} "
        f"validation={status} proof={bundle.proof_obligation} "
        f"paper_only={bundle.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )


__all__ = [
    "EXECUTION_SCHEMA_VERSION",
    "ExecutionCocycleCertificate",
    "ExecutionBundle",
    "ExecutionError",
    "ExecutionGluingError",
    "ExecutionInput",
    "ExecutionKey",
    "ExecutionLedgerState",
    "ExecutionNormalizationError",
    "ExecutionPolicy",
    "ExecutionProofMode",
    "ExecutionQuote",
    "ExecutionResearchIdea",
    "ExecutionRestrictionError",
    "ExecutionSlice",
    "ExecutionValidationReport",
    "ExecutableOrder",
    "FillApplicationError",
    "FillReport",
    "FillStatus",
    "GlobalExecutionSection",
    "LocalExecutionSection",
    "OrderStatus",
    "PositionBalance",
    "SLICES",
    "apply_fills",
    "build_execution",
    "build_execution_cover",
    "check_execution_cocycle",
    "default_execution_policy",
    "empty_execution_ledger",
    "execution_schema_version",
    "execution_summary",
    "executable_orders",
    "glue_execution_sections",
    "group_execution_overlaps",
    "place_orders",
    "position_quantity",
    "restrict_execution_sections",
    "simulate_fills",
    "validate_execution",
]
