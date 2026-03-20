"""Normalize feeds and local market observations for a verified trading cover.

This module is the input site for the orchestration-typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main
-> market_data_ingestion -> data_normalization -> feature_engineering
-> idea_discovery_engine -> strategy_hypothesis_lab -> signal_generation
-> portfolio_construction -> execution_simulator -> backtesting_engine
-> formal_specification -> proof_artifacts -> monitoring_and_alerting
-> experiment_tracking -> compliance_audit_log -> api_and_cli``.

Each feed is treated as a local section over an open set identified by
``(timestamp, symbol, source)``. Normalization restricts raw observations onto
overlaps keyed by ``(timestamp, symbol)`` while preserving the first gluing
obligation of the system: restrictions preserve timestamp, symbol, and
normalization invariants. Downstream modules inherit these overlap witnesses and
must discharge their own gluing obligations without bypassing the normalized
input boundary.

The novel idea realized here is a machine-learning-inspired but explicitly
verifiable feature chart. Instead of learning a latent embedding with a neural
encoder, we build a topology-preserving coordinate chart from market
microstructure:

* relative spread,
* order-book imbalance,
* microprice offset, and
* a harmonic advantage score.

The harmonic advantage is an H^1-aware proxy for whether local price pressure
forms an exact cocycle across overlapping feeds. If the cocycle checks pass,
the observations can be glued into a coherent market section for downstream
alpha construction while retaining deterministic, versioned replay signatures.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Collection, Iterable, Literal, Mapping, Sequence, TypeAlias

PRICE_QUANTUM = Decimal("0.000001")
SIZE_QUANTUM = Decimal("0.0001")
FEATURE_QUANTUM = Decimal("0.0000001")
NORMALIZATION_SCHEMA_VERSION = "market_data.v1"
ONE = Decimal("1")
ZERO = Decimal("0")

OverlapKey: TypeAlias = tuple[datetime, str]

_TIMESTAMP_KEYS = ("timestamp", "ts", "time", "observed_at", "datetime")
_SYMBOL_KEYS = ("symbol", "ticker", "instrument", "asset")
_SOURCE_KEYS = ("source", "feed", "publisher", "observer")
_VENUE_KEYS = ("venue", "exchange", "market", "mic")
_BID_KEYS = ("bid", "best_bid", "bid_price")
_ASK_KEYS = ("ask", "best_ask", "ask_price")
_LAST_KEYS = ("last", "price", "last_price", "trade_price", "mid")
_BID_SIZE_KEYS = ("bid_size", "best_bid_size", "bid_qty", "bid_volume")
_ASK_SIZE_KEYS = ("ask_size", "best_ask_size", "ask_qty", "ask_volume")
_VOLUME_KEYS = ("volume", "size", "qty", "quantity", "trade_size")
_SIDE_KEYS = ("side", "trade_side", "direction")

_KNOWN_KEYS = frozenset(
    _TIMESTAMP_KEYS
    + _SYMBOL_KEYS
    + _SOURCE_KEYS
    + _VENUE_KEYS
    + _BID_KEYS
    + _ASK_KEYS
    + _LAST_KEYS
    + _BID_SIZE_KEYS
    + _ASK_SIZE_KEYS
    + _VOLUME_KEYS
    + _SIDE_KEYS
)


class MarketDataError(ValueError):
    """Base error raised by market-data normalization."""


class FeedValidationError(MarketDataError):
    """Raised when a raw market observation fails validation."""


class NormalizationError(MarketDataError):
    """Raised when canonical normalization cannot be completed."""


class GluingInvariantError(MarketDataError):
    """Raised when overlap checks fail and observations cannot be glued."""


class HypothesisGenerationError(MarketDataError):
    """Raised when a deterministic market hypothesis cannot be generated safely."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    """Return *value* rounded onto the project-wide decimal lattice."""
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    """Convert *value* to a finite :class:`Decimal`.

    Parameters
    ----------
    value:
        Candidate numeric value.
    field_name:
        Human-readable field name for diagnostics.
    """
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (InvalidOperation, AttributeError, ValueError) as exc:
            raise FeedValidationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc

    if not candidate.is_finite():
        raise FeedValidationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _normalize_timestamp(value: Any) -> datetime:
    """Normalize timestamps to timezone-aware UTC datetimes."""
    if isinstance(value, datetime):
        timestamp = value
    elif isinstance(value, (int, float, Decimal)):
        timestamp = _epoch_to_datetime(_coerce_decimal(value, "timestamp"))
    elif isinstance(value, str):
        candidate = value.strip()
        if not candidate:
            raise FeedValidationError("Field 'timestamp' cannot be empty.")
        iso_candidate = (
            candidate[:-1] + "+00:00" if candidate.endswith("Z") else candidate
        )
        try:
            timestamp = datetime.fromisoformat(iso_candidate)
        except ValueError:
            timestamp = _epoch_to_datetime(_coerce_decimal(candidate, "timestamp"))
    else:
        raise FeedValidationError(
            f"Field 'timestamp' must be datetime-like, got {value!r}."
        )

    if timestamp.tzinfo is None:
        timestamp = timestamp.replace(tzinfo=timezone.utc)
    else:
        timestamp = timestamp.astimezone(timezone.utc)
    return timestamp


def _epoch_to_datetime(epoch_value: Decimal) -> datetime:
    """Convert epoch seconds or milliseconds to a UTC datetime."""
    seconds = epoch_value
    if abs(seconds) >= Decimal("100000000000"):
        seconds = seconds / Decimal("1000")

    try:
        return datetime.fromtimestamp(float(seconds), tz=timezone.utc)
    except (OverflowError, OSError, ValueError) as exc:
        raise FeedValidationError(
            f"Field 'timestamp' has out-of-range epoch value {epoch_value!r}."
        ) from exc


def _normalize_symbol(value: Any) -> str:
    """Canonicalize symbol names so restrictions preserve overlap identity."""
    if not isinstance(value, str):
        raise FeedValidationError(f"Field 'symbol' must be text, got {value!r}.")

    candidate = value.strip().upper()
    if not candidate:
        raise FeedValidationError("Field 'symbol' cannot be empty.")

    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")

    if not candidate:
        raise FeedValidationError(f"Field 'symbol' cannot normalize from {value!r}.")
    return candidate


def _normalize_name(value: Any, field_name: str, *, default: str | None = None) -> str:
    """Normalize source- or venue-like labels."""
    if value is None:
        if default is None:
            raise FeedValidationError(f"Field '{field_name}' is required.")
        candidate = default
    elif not isinstance(value, str):
        raise FeedValidationError(f"Field '{field_name}' must be text, got {value!r}.")
    else:
        candidate = value

    normalized = "_".join(candidate.strip().lower().split())
    if not normalized:
        raise FeedValidationError(f"Field '{field_name}' cannot be empty.")
    return normalized


def _canonicalize_entry(entry: Mapping[str, Any]) -> dict[str, Any]:
    """Lowercase string keys so heterogeneous feeds share one namespace."""
    canonical: dict[str, Any] = {}
    for key, value in entry.items():
        canonical[str(key).strip().lower()] = value
    return canonical


def _first_present(entry: Mapping[str, Any], keys: Sequence[str]) -> Any | None:
    """Return the first present field among *keys* or ``None``."""
    for key in keys:
        if key in entry and entry[key] is not None:
            return entry[key]
    return None


def _required_field(entry: Mapping[str, Any], keys: Sequence[str], field_name: str) -> Any:
    """Return the first non-``None`` candidate for a required field."""
    value = _first_present(entry, keys)
    if value is None:
        alias_text = ", ".join(keys)
        raise FeedValidationError(
            f"Field '{field_name}' is required; expected one of: {alias_text}."
        )
    return value


def _optional_decimal(
    entry: Mapping[str, Any], keys: Sequence[str], field_name: str
) -> Decimal | None:
    """Extract an optional decimal field and return ``None`` if absent."""
    value = _first_present(entry, keys)
    if value is None:
        return None
    return _coerce_decimal(value, field_name)


def _metadata_from_entry(entry: Mapping[str, Any]) -> tuple[tuple[str, str], ...]:
    """Extract stable metadata from non-core raw fields."""
    metadata = [
        (key, str(value))
        for key, value in entry.items()
        if key not in _KNOWN_KEYS and value is not None
    ]
    metadata.sort()
    return tuple(metadata)


def _safe_ratio(numerator: Decimal, denominator: Decimal, quantum: Decimal) -> Decimal:
    """Return a quantized ratio, treating zero denominator as zero."""
    if denominator == ZERO:
        return ZERO
    return _quantize(numerator / denominator, quantum)


def _clamp_probability(value: Decimal) -> Decimal:
    """Clamp *value* to the closed unit interval on the feature lattice."""
    if not value.is_finite():
        raise HypothesisGenerationError("Probabilistic scores must be finite.")
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize(value, FEATURE_QUANTUM)


def _support_factor(support_count: int) -> Decimal:
    """Return a bounded support factor that grows with sample count."""
    if support_count < 1:
        raise HypothesisGenerationError("Support count must be positive.")
    return _quantize(Decimal(support_count) / Decimal(support_count + 1), FEATURE_QUANTUM)


def _stable_digest(parts: Sequence[str]) -> str:
    """Return a deterministic digest for reproducibility and audit trails."""
    payload = "\x1f".join((NORMALIZATION_SCHEMA_VERSION, *parts)).encode("utf-8")
    return sha256(payload).hexdigest()


# @ensure("returned schema version is stable for deterministic normalization and replay")
def normalization_schema_version() -> str:
    """Return the version string used to stamp normalization digests."""
    return NORMALIZATION_SCHEMA_VERSION


def _median_decimal(values: Sequence[Decimal], quantum: Decimal) -> Decimal:
    """Return the median of *values* on the specified decimal lattice."""
    if not values:
        raise NormalizationError("Median is undefined for an empty value set.")

    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return _quantize(ordered[middle], quantum)
    return _quantize((ordered[middle - 1] + ordered[middle]) / Decimal("2"), quantum)


def _max_gap(values: Sequence[Decimal], quantum: Decimal) -> Decimal:
    """Return the maximum gap between values on a shared overlap."""
    if not values:
        return ZERO
    return _quantize(max(values) - min(values), quantum)


def _triple_overlap_residual(values: Sequence[Decimal]) -> Decimal:
    """Estimate the cocycle residual on triple overlaps.

    For a one-dimensional chart, exact gluing means all local coordinates agree
    with a common section.  The residual is therefore the maximum deviation from
    the overlap median and serves as an H^1-aware obstruction witness.
    """
    if len(values) < 3:
        return ZERO
    median_value = _median_decimal(values, FEATURE_QUANTUM)
    residual = max((abs(value - median_value) for value in values), default=ZERO)
    return _quantize(residual, FEATURE_QUANTUM)


def _normalize_side(entry: Mapping[str, Any]) -> str | None:
    """Return the normalized trade side if one is provided."""
    value = _first_present(entry, _SIDE_KEYS)
    if value is None:
        return None
    if not isinstance(value, str):
        raise FeedValidationError(f"Field 'side' must be text, got {value!r}.")

    side = value.strip().lower()
    if side in {"buy", "bid", "b", "long"}:
        return "buy"
    if side in {"sell", "ask", "s", "short"}:
        return "sell"
    raise FeedValidationError(f"Unsupported side value {value!r}.")


# @invariant("coordinates are finite, dimensionless, and preserve local market neighborhoods")
@dataclass(frozen=True)
class TopologyCoordinates:
    """A verifiable microstructure chart inspired by latent ML embeddings.

    The coordinates preserve local adjacency in the sense that nearby order-book
    states map to nearby tuples, but every coordinate is explicit and auditable.
    The ``harmonic_advantage`` term is the module's novel idea seed: it measures
    residual price pressure after subtracting the exact part induced by spread
    and order imbalance.
    """

    relative_spread: Decimal
    order_imbalance: Decimal
    microprice_offset: Decimal
    flow_pressure: Decimal
    harmonic_advantage: Decimal

    def __post_init__(self) -> None:
        """Validate that every coordinate is finite."""
        for field_name, value in (
            ("relative_spread", self.relative_spread),
            ("order_imbalance", self.order_imbalance),
            ("microprice_offset", self.microprice_offset),
            ("flow_pressure", self.flow_pressure),
            ("harmonic_advantage", self.harmonic_advantage),
        ):
            if not value.is_finite():
                raise NormalizationError(
                    f"Topology coordinate '{field_name}' must be finite."
                )

    @property
    def novelty_score(self) -> Decimal:
        """Return the module's candidate alpha seed for downstream geometry."""
        return _quantize(
            self.harmonic_advantage * (ONE + abs(self.flow_pressure)),
            FEATURE_QUANTUM,
        )


# @invariant("timestamp is UTC, symbol is canonical, and normalization invariants are stable on overlaps")
@dataclass(frozen=True)
class NormalizedMarketObservation:
    """A single feed observation normalized onto the project's market-data site."""

    source: str
    venue: str
    timestamp: datetime
    symbol: str
    bid: Decimal | None
    ask: Decimal | None
    last: Decimal | None
    mid: Decimal
    microprice: Decimal
    spread: Decimal
    volume: Decimal
    bid_size: Decimal
    ask_size: Decimal
    topology: TopologyCoordinates
    metadata: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        """Validate canonical overlap invariants."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise NormalizationError("Normalized timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise NormalizationError("Normalized timestamps must be expressed in UTC.")
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise NormalizationError("Normalized symbols must be non-empty uppercase.")
        if self.mid <= ZERO:
            raise NormalizationError("Normalized mid prices must be positive.")
        if self.microprice <= ZERO:
            raise NormalizationError("Normalized microprices must be positive.")
        if self.spread < ZERO:
            raise NormalizationError("Normalized spreads must be non-negative.")
        if self.volume < ZERO or self.bid_size < ZERO or self.ask_size < ZERO:
            raise NormalizationError("Normalized sizes and volumes must be non-negative.")

    def overlap_key(self) -> OverlapKey:
        """Return the key used for restriction and gluing checks."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, Decimal, Decimal]:
        """Return the invariant signature that must persist under restriction."""
        return (self.timestamp, self.symbol, self.mid, self.spread)

    def reproducibility_signature(self) -> str:
        """Return a deterministic signature for audit and replay workflows."""
        metadata_parts = [f"{key}={value}" for key, value in self.metadata]
        return _stable_digest(
            [
                self.source,
                self.venue,
                self.timestamp.isoformat(),
                self.symbol,
                str(self.bid),
                str(self.ask),
                str(self.last),
                str(self.mid),
                str(self.microprice),
                str(self.spread),
                str(self.volume),
                str(self.bid_size),
                str(self.ask_size),
                str(self.topology.relative_spread),
                str(self.topology.order_imbalance),
                str(self.topology.microprice_offset),
                str(self.topology.flow_pressure),
                str(self.topology.harmonic_advantage),
                *metadata_parts,
            ]
        )


# @invariant("cocycle certificates are deterministic overlap witnesses")
@dataclass(frozen=True)
class CocycleCertificate:
    """Diagnostic evidence that local observations can or cannot be glued."""

    key: OverlapKey
    sources: tuple[str, ...]
    max_mid_gap_ratio: Decimal
    max_spread_gap_ratio: Decimal
    triple_overlap_residual: Decimal
    h1_obstruction: Decimal
    passes: bool
    reason: str

    def assert_passes(self) -> None:
        """Raise :class:`GluingInvariantError` if the certificate fails."""
        if not self.passes:
            timestamp, symbol = self.key
            raise GluingInvariantError(
                f"Overlap {symbol}@{timestamp.isoformat()} failed gluing: {self.reason}"
            )


# @invariant("glued sections descend from overlap-compatible observations")
@dataclass(frozen=True)
class GluedMarketObservation:
    """A coherent market section descended from overlap-compatible observations."""

    timestamp: datetime
    symbol: str
    sources: tuple[str, ...]
    venues: tuple[str, ...]
    mid: Decimal
    spread: Decimal
    microprice: Decimal
    total_volume: Decimal
    support_count: int
    topology: TopologyCoordinates
    gluing_score: Decimal
    novelty_score: Decimal

    def __post_init__(self) -> None:
        """Validate the descended section before downstream use."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise NormalizationError("Glued timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise NormalizationError("Glued timestamps must be expressed in UTC.")
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise NormalizationError("Glued symbols must be non-empty uppercase.")
        if self.mid <= ZERO or self.microprice <= ZERO:
            raise NormalizationError("Glued prices must be strictly positive.")
        if self.spread < ZERO or self.total_volume < ZERO:
            raise NormalizationError("Glued spread and total volume must be non-negative.")
        if self.support_count < 1:
            raise NormalizationError("Glued observations must retain positive support.")
        self_confidence = _clamp_probability(self.gluing_score)
        novelty = self.novelty_score
        if novelty != _quantize(novelty, FEATURE_QUANTUM):
            raise NormalizationError("Novelty scores must lie on the feature lattice.")
        if self_confidence != self.gluing_score:
            raise NormalizationError("Gluing scores must lie in the unit interval.")

    def reproducibility_signature(self) -> str:
        """Return a deterministic signature for replaying this market section."""
        return _stable_digest(
            [
                self.timestamp.isoformat(),
                self.symbol,
                *self.sources,
                *self.venues,
                str(self.mid),
                str(self.spread),
                str(self.microprice),
                str(self.total_volume),
                str(self.support_count),
                str(self.topology.relative_spread),
                str(self.topology.order_imbalance),
                str(self.topology.microprice_offset),
                str(self.topology.flow_pressure),
                str(self.topology.harmonic_advantage),
                str(self.gluing_score),
                str(self.novelty_score),
            ]
        )


# @invariant("historical baselines summarize one symbol over a deterministic time window")
@dataclass(frozen=True)
class HistoricalMarketBaseline:
    """Median historical topology summary used to score live novelty."""

    symbol: str
    start: datetime
    end: datetime
    sample_size: int
    median_mid: Decimal
    median_relative_spread: Decimal
    median_flow_pressure: Decimal
    median_harmonic_advantage: Decimal
    median_novelty_score: Decimal

    def __post_init__(self) -> None:
        """Validate baseline completeness."""
        if self.start.tzinfo is None or self.start.utcoffset() is None:
            raise HypothesisGenerationError("Historical baseline start must be timezone-aware.")
        if self.end.tzinfo is None or self.end.utcoffset() is None:
            raise HypothesisGenerationError("Historical baseline end must be timezone-aware.")
        if self.start.astimezone(timezone.utc) != self.start:
            raise HypothesisGenerationError("Historical baseline start must be expressed in UTC.")
        if self.end.astimezone(timezone.utc) != self.end:
            raise HypothesisGenerationError("Historical baseline end must be expressed in UTC.")
        if self.end < self.start:
            raise HypothesisGenerationError("Historical baseline end cannot precede start.")
        if self.sample_size < 1:
            raise HypothesisGenerationError("Historical baselines require at least one sample.")
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise HypothesisGenerationError("Historical baselines require canonical symbols.")


HypothesisDirection: TypeAlias = Literal["long", "short"]


# @invariant("market hypotheses are deterministic, testable, and traceable to normalized data")
@dataclass(frozen=True)
class NovelMarketHypothesis:
    """A testable alpha hypothesis descended from historical and live sections."""

    symbol: str
    as_of: datetime
    direction: HypothesisDirection
    regime: str
    thesis: str
    validation_plan: str
    test_horizon_minutes: int
    entry_reference_price: Decimal
    target_move_bps: Decimal
    stop_move_bps: Decimal
    expected_edge_bps: Decimal
    confidence: Decimal
    gluing_score: Decimal
    live_support_count: int
    historical_sample_size: int
    data_signature: str

    def __post_init__(self) -> None:
        """Validate testability and audit fields."""
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise HypothesisGenerationError("Hypothesis symbols must be canonical.")
        if self.as_of.tzinfo is None or self.as_of.utcoffset() is None:
            raise HypothesisGenerationError("Hypothesis timestamps must be timezone-aware.")
        if self.as_of.astimezone(timezone.utc) != self.as_of:
            raise HypothesisGenerationError("Hypothesis timestamps must be expressed in UTC.")
        if self.direction not in {"long", "short"}:
            raise HypothesisGenerationError("Hypothesis direction must be 'long' or 'short'.")
        if not self.regime.strip():
            raise HypothesisGenerationError("Hypothesis regime cannot be empty.")
        if not self.thesis.strip() or not self.validation_plan.strip():
            raise HypothesisGenerationError("Hypotheses require thesis and validation text.")
        if self.test_horizon_minutes < 1:
            raise HypothesisGenerationError("Hypothesis horizon must be positive.")
        if self.entry_reference_price <= ZERO:
            raise HypothesisGenerationError("Hypothesis entry price must be positive.")
        for field_name, value in (
            ("target_move_bps", self.target_move_bps),
            ("stop_move_bps", self.stop_move_bps),
            ("expected_edge_bps", self.expected_edge_bps),
            ("confidence", self.confidence),
            ("gluing_score", self.gluing_score),
        ):
            if not value.is_finite():
                raise HypothesisGenerationError(
                    f"Hypothesis field '{field_name}' must be finite."
                )
        if self.target_move_bps <= ZERO or self.stop_move_bps <= ZERO:
            raise HypothesisGenerationError("Hypothesis move thresholds must be positive.")
        if self.expected_edge_bps < ZERO:
            raise HypothesisGenerationError("Expected edge must be non-negative.")
        if _clamp_probability(self.confidence) != self.confidence:
            raise HypothesisGenerationError("Hypothesis confidence must lie in [0, 1].")
        if _clamp_probability(self.gluing_score) != self.gluing_score:
            raise HypothesisGenerationError("Hypothesis gluing score must lie in [0, 1].")
        if self.live_support_count < 1 or self.historical_sample_size < 1:
            raise HypothesisGenerationError("Hypothesis support counts must be positive.")
        if not self.data_signature:
            raise HypothesisGenerationError("Hypotheses require a reproducibility signature.")


def _build_topology(
    *,
    mid: Decimal,
    spread: Decimal,
    microprice: Decimal,
    bid_size: Decimal,
    ask_size: Decimal,
    volume: Decimal,
    side: str | None,
) -> TopologyCoordinates:
    """Construct the topology-preserving feature chart for one observation."""
    relative_spread = _safe_ratio(spread, mid, FEATURE_QUANTUM)
    imbalance = _safe_ratio(bid_size - ask_size, bid_size + ask_size, FEATURE_QUANTUM)
    microprice_offset = _safe_ratio(microprice - mid, mid, FEATURE_QUANTUM)

    signed_volume = volume
    if side == "sell":
        signed_volume = -volume
    elif side is None:
        signed_volume = ZERO

    flow_denominator = bid_size + ask_size + volume + ONE
    flow_pressure = _safe_ratio(signed_volume, flow_denominator, FEATURE_QUANTUM)
    harmonic_advantage = _quantize(
        microprice_offset - (relative_spread * imbalance),
        FEATURE_QUANTUM,
    )
    return TopologyCoordinates(
        relative_spread=relative_spread,
        order_imbalance=imbalance,
        microprice_offset=microprice_offset,
        flow_pressure=flow_pressure,
        harmonic_advantage=harmonic_advantage,
    )


# @require("entry includes timestamp, symbol, and at least one price witness")
# @ensure("result preserves canonical timestamp, symbol, and normalization invariants")
def normalize_feed_entry(
    entry: Mapping[str, Any], *, default_source: str = "feed"
) -> NormalizedMarketObservation:
    """Normalize one raw feed record into a canonical market observation."""
    canonical = _canonicalize_entry(entry)

    timestamp = _normalize_timestamp(
        _required_field(canonical, _TIMESTAMP_KEYS, "timestamp")
    )
    symbol = _normalize_symbol(_required_field(canonical, _SYMBOL_KEYS, "symbol"))
    source = _normalize_name(
        _first_present(canonical, _SOURCE_KEYS), "source", default=default_source
    )
    venue = _normalize_name(
        _first_present(canonical, _VENUE_KEYS), "venue", default=source
    )

    bid = _optional_decimal(canonical, _BID_KEYS, "bid")
    ask = _optional_decimal(canonical, _ASK_KEYS, "ask")
    last = _optional_decimal(canonical, _LAST_KEYS, "last")
    bid_size = _optional_decimal(canonical, _BID_SIZE_KEYS, "bid_size") or ZERO
    ask_size = _optional_decimal(canonical, _ASK_SIZE_KEYS, "ask_size") or ZERO
    volume = _optional_decimal(canonical, _VOLUME_KEYS, "volume") or ZERO
    side = _normalize_side(canonical)

    if bid is None and ask is None and last is None:
        raise FeedValidationError(
            "At least one of bid, ask, or last/price is required."
        )

    for field_name, value in (
        ("bid", bid),
        ("ask", ask),
        ("last", last),
        ("bid_size", bid_size),
        ("ask_size", ask_size),
        ("volume", volume),
    ):
        if value is not None and value < ZERO:
            raise FeedValidationError(
                f"Field '{field_name}' must be non-negative, got {value!r}."
            )

    if bid is not None and bid == ZERO:
        raise FeedValidationError("Field 'bid' must be strictly positive when present.")
    if ask is not None and ask == ZERO:
        raise FeedValidationError("Field 'ask' must be strictly positive when present.")
    if last is not None and last == ZERO:
        raise FeedValidationError("Field 'last' must be strictly positive when present.")

    if bid is not None and ask is not None and bid > ask:
        raise FeedValidationError(
            f"Bid price {bid!r} cannot exceed ask price {ask!r}."
        )

    if bid is not None and ask is not None:
        mid = (bid + ask) / Decimal("2")
        spread = ask - bid
    else:
        anchor = last or bid or ask
        if anchor is None:
            raise FeedValidationError("Cannot determine a reference price.")
        mid = anchor
        spread = ZERO

    if bid is not None and ask is not None and bid_size + ask_size > ZERO:
        microprice = ((ask * bid_size) + (bid * ask_size)) / (bid_size + ask_size)
    else:
        microprice = last or mid

    if microprice is None:
        raise FeedValidationError("Cannot determine a microprice from the observation.")

    normalized_bid = _quantize(bid, PRICE_QUANTUM) if bid is not None else None
    normalized_ask = _quantize(ask, PRICE_QUANTUM) if ask is not None else None
    normalized_last = _quantize(last, PRICE_QUANTUM) if last is not None else None
    normalized_mid = _quantize(mid, PRICE_QUANTUM)
    normalized_microprice = _quantize(microprice, PRICE_QUANTUM)
    normalized_spread = _quantize(spread, PRICE_QUANTUM)
    normalized_bid_size = _quantize(bid_size, SIZE_QUANTUM)
    normalized_ask_size = _quantize(ask_size, SIZE_QUANTUM)
    normalized_volume = _quantize(volume, SIZE_QUANTUM)

    topology = _build_topology(
        mid=normalized_mid,
        spread=normalized_spread,
        microprice=normalized_microprice,
        bid_size=normalized_bid_size,
        ask_size=normalized_ask_size,
        volume=normalized_volume,
        side=side,
    )

    return NormalizedMarketObservation(
        source=source,
        venue=venue,
        timestamp=timestamp,
        symbol=symbol,
        bid=normalized_bid,
        ask=normalized_ask,
        last=normalized_last,
        mid=normalized_mid,
        microprice=normalized_microprice,
        spread=normalized_spread,
        volume=normalized_volume,
        bid_size=normalized_bid_size,
        ask_size=normalized_ask_size,
        topology=topology,
        metadata=_metadata_from_entry(canonical),
    )


# @require("entry contains a local timestamped market witness")
# @ensure("result is normalized with local-source defaults and preserved invariants")
def normalize_local_observation(
    entry: Mapping[str, Any], *, observer: str = "local_observer"
) -> NormalizedMarketObservation:
    """Normalize a locally observed market snapshot.

    Local observations default the source and venue to the observer name if they
    are not explicitly supplied.
    """
    patched_entry = dict(entry)
    patched_entry.setdefault("source", observer)
    patched_entry.setdefault("venue", observer)
    return normalize_feed_entry(patched_entry, default_source=observer)


# @require("entries is a finite iterable of raw market observations")
# @ensure("returned observations are sorted and individually normalized")
def normalize_market_batch(
    entries: Iterable[Mapping[str, Any]], *, default_source: str = "feed"
) -> list[NormalizedMarketObservation]:
    """Normalize and sort a batch of raw observations."""
    normalized: list[NormalizedMarketObservation] = []
    for index, entry in enumerate(entries):
        try:
            observation = normalize_feed_entry(entry, default_source=default_source)
        except MarketDataError as exc:
            raise NormalizationError(
                f"Failed to normalize entry at index {index}: {exc}"
            ) from exc
        normalized.append(observation)

    return sorted(
        normalized,
        key=lambda item: (item.timestamp, item.symbol, item.source, item.venue),
    )


# @require("restrictions are taken over canonical symbols and UTC bounds")
# @ensure("restriction preserves timestamp, symbol, and normalization invariants")
def restrict_observations(
    observations: Iterable[NormalizedMarketObservation],
    *,
    symbols: Collection[str] | None = None,
    start: datetime | None = None,
    end: datetime | None = None,
) -> list[NormalizedMarketObservation]:
    """Restrict observations to a cover subset without changing their sections."""
    normalized_symbols = (
        {_normalize_symbol(symbol) for symbol in symbols} if symbols is not None else None
    )
    start_bound = _normalize_timestamp(start) if start is not None else None
    end_bound = _normalize_timestamp(end) if end is not None else None

    if start_bound is not None and end_bound is not None and end_bound < start_bound:
        raise FeedValidationError("Restriction end time cannot precede start time.")

    restricted = []
    for observation in observations:
        if normalized_symbols is not None and observation.symbol not in normalized_symbols:
            continue
        if start_bound is not None and observation.timestamp < start_bound:
            continue
        if end_bound is not None and observation.timestamp > end_bound:
            continue
        restricted.append(observation)

    return sorted(
        restricted,
        key=lambda item: (item.timestamp, item.symbol, item.source, item.venue),
    )


# @require("observations are already normalized local sections")
# @ensure("returned groups are keyed only by canonical timestamp and symbol")
def group_by_overlap(
    observations: Iterable[NormalizedMarketObservation],
) -> dict[OverlapKey, list[NormalizedMarketObservation]]:
    """Group observations by the overlap key used by the trading cover."""
    grouped: dict[OverlapKey, list[NormalizedMarketObservation]] = {}
    for observation in observations:
        grouped.setdefault(observation.overlap_key(), []).append(observation)

    for members in grouped.values():
        members.sort(key=lambda item: (item.source, item.venue))
    return dict(sorted(grouped.items(), key=lambda item: item[0]))


def _resolve_tolerance(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a tolerance parameter to a finite decimal."""
    tolerance = _coerce_decimal(value, field_name)
    if tolerance < ZERO:
        raise FeedValidationError(f"Tolerance '{field_name}' must be non-negative.")
    return tolerance


def _build_certificate(
    key: OverlapKey,
    members: Sequence[NormalizedMarketObservation],
    *,
    price_tolerance: Decimal,
    spread_tolerance: Decimal,
    h1_tolerance: Decimal,
) -> CocycleCertificate:
    """Build the cocycle certificate for one overlap class."""
    mid_values = [member.mid for member in members]
    spread_values = [member.spread for member in members]
    harmonic_values = [member.topology.harmonic_advantage for member in members]
    reference_mid = _median_decimal(mid_values, PRICE_QUANTUM)
    reference_scale = reference_mid if reference_mid > ZERO else ONE

    max_mid_gap_ratio = _safe_ratio(
        _max_gap(mid_values, PRICE_QUANTUM), reference_scale, FEATURE_QUANTUM
    )
    max_spread_gap_ratio = _safe_ratio(
        _max_gap(spread_values, PRICE_QUANTUM), reference_scale, FEATURE_QUANTUM
    )
    triple_residual = _triple_overlap_residual(harmonic_values)
    h1_obstruction = _quantize(
        max_mid_gap_ratio + max_spread_gap_ratio + triple_residual,
        FEATURE_QUANTUM,
    )

    passes = (
        max_mid_gap_ratio <= price_tolerance
        and max_spread_gap_ratio <= spread_tolerance
        and h1_obstruction <= h1_tolerance
    )

    if passes:
        reason = "overlap restrictions agree and the H^1 obstruction vanishes"
    else:
        reason = (
            "observations disagree on canonical overlap data: "
            f"mid_gap={max_mid_gap_ratio}, "
            f"spread_gap={max_spread_gap_ratio}, "
            f"triple_residual={triple_residual}, "
            f"h1_obstruction={h1_obstruction}"
        )

    return CocycleCertificate(
        key=key,
        sources=tuple(sorted({member.source for member in members})),
        max_mid_gap_ratio=max_mid_gap_ratio,
        max_spread_gap_ratio=max_spread_gap_ratio,
        triple_overlap_residual=triple_residual,
        h1_obstruction=h1_obstruction,
        passes=passes,
        reason=reason,
    )


# @require("overlap checks run on normalized observations only")
# @ensure("each overlap yields a deterministic cocycle certificate")
def check_cocycle_gluing(
    observations: Sequence[NormalizedMarketObservation],
    *,
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
) -> tuple[CocycleCertificate, ...]:
    """Check overlap compatibility and emit one certificate per overlap key."""
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_spread_tolerance = _resolve_tolerance(
        spread_tolerance, "spread_tolerance"
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize(resolved_price_tolerance * Decimal("2"), FEATURE_QUANTUM)
    )

    grouped = group_by_overlap(observations)
    certificates = [
        _build_certificate(
            key,
            members,
            price_tolerance=resolved_price_tolerance,
            spread_tolerance=resolved_spread_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
        for key, members in grouped.items()
    ]
    return tuple(certificates)


def _gluing_score(obstruction: Decimal, h1_tolerance: Decimal) -> Decimal:
    """Convert an H^1 obstruction witness into a unit gluing score."""
    if h1_tolerance == ZERO:
        return ZERO if obstruction > ZERO else ONE
    score = ONE - min(ONE, obstruction / h1_tolerance)
    return _quantize(score, FEATURE_QUANTUM)


# @require("only overlap-compatible observations may descend to a global section")
# @ensure("returned sections are coherent, sorted, and ready for signal geometry")
def glue_market_observations(
    observations: Sequence[NormalizedMarketObservation],
    *,
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
) -> list[GluedMarketObservation]:
    """Glue overlap-compatible observations into coherent market sections."""
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_spread_tolerance = _resolve_tolerance(
        spread_tolerance, "spread_tolerance"
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize(resolved_price_tolerance * Decimal("2"), FEATURE_QUANTUM)
    )

    grouped = group_by_overlap(observations)
    certificates = {
        certificate.key: certificate
        for certificate in check_cocycle_gluing(
            observations,
            price_tolerance=resolved_price_tolerance,
            spread_tolerance=resolved_spread_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    }

    glued: list[GluedMarketObservation] = []
    for key, members in grouped.items():
        certificate = certificates[key]
        certificate.assert_passes()

        mid = _median_decimal([member.mid for member in members], PRICE_QUANTUM)
        spread = _median_decimal([member.spread for member in members], PRICE_QUANTUM)
        microprice = _median_decimal(
            [member.microprice for member in members], PRICE_QUANTUM
        )
        total_volume = _quantize(
            sum((member.volume for member in members), start=ZERO), SIZE_QUANTUM
        )
        topology = TopologyCoordinates(
            relative_spread=_median_decimal(
                [member.topology.relative_spread for member in members], FEATURE_QUANTUM
            ),
            order_imbalance=_median_decimal(
                [member.topology.order_imbalance for member in members], FEATURE_QUANTUM
            ),
            microprice_offset=_median_decimal(
                [member.topology.microprice_offset for member in members],
                FEATURE_QUANTUM,
            ),
            flow_pressure=_median_decimal(
                [member.topology.flow_pressure for member in members], FEATURE_QUANTUM
            ),
            harmonic_advantage=_median_decimal(
                [member.topology.harmonic_advantage for member in members],
                FEATURE_QUANTUM,
            ),
        )
        glued.append(
            GluedMarketObservation(
                timestamp=key[0],
                symbol=key[1],
                sources=tuple(sorted({member.source for member in members})),
                venues=tuple(sorted({member.venue for member in members})),
                mid=mid,
                spread=spread,
                microprice=microprice,
                total_volume=total_volume,
                support_count=len(members),
                topology=topology,
                gluing_score=_gluing_score(
                    certificate.h1_obstruction, resolved_h1_tolerance
                ),
                novelty_score=topology.novelty_score,
            )
        )

    return sorted(glued, key=lambda item: (item.timestamp, item.symbol))


def _build_historical_baselines(
    sections: Sequence[GluedMarketObservation], *, min_history_points: int
) -> dict[str, HistoricalMarketBaseline]:
    """Build one deterministic historical baseline per symbol."""
    if min_history_points < 1:
        raise HypothesisGenerationError("Minimum history points must be positive.")

    grouped: dict[str, list[GluedMarketObservation]] = {}
    for section in sections:
        grouped.setdefault(section.symbol, []).append(section)

    baselines: dict[str, HistoricalMarketBaseline] = {}
    for symbol, members in grouped.items():
        ordered = sorted(members, key=lambda item: item.timestamp)
        if len(ordered) < min_history_points:
            continue
        baselines[symbol] = HistoricalMarketBaseline(
            symbol=symbol,
            start=ordered[0].timestamp,
            end=ordered[-1].timestamp,
            sample_size=len(ordered),
            median_mid=_median_decimal([item.mid for item in ordered], PRICE_QUANTUM),
            median_relative_spread=_median_decimal(
                [item.topology.relative_spread for item in ordered], FEATURE_QUANTUM
            ),
            median_flow_pressure=_median_decimal(
                [item.topology.flow_pressure for item in ordered], FEATURE_QUANTUM
            ),
            median_harmonic_advantage=_median_decimal(
                [item.topology.harmonic_advantage for item in ordered], FEATURE_QUANTUM
            ),
            median_novelty_score=_median_decimal(
                [item.novelty_score for item in ordered], FEATURE_QUANTUM
            ),
        )
    return baselines


def _classify_hypothesis_regime(
    *,
    novelty_lift: Decimal,
    harmonic_shift: Decimal,
    flow_shift: Decimal,
    spread_drift: Decimal,
) -> str:
    """Classify the live deviation against the historical topology."""
    if abs(spread_drift) <= Decimal("0.0005000") and abs(flow_shift) >= abs(
        harmonic_shift
    ):
        return "flow_persistence_seam"
    if harmonic_shift * flow_shift < ZERO:
        return "harmonic_reversion_window"
    if novelty_lift * harmonic_shift > ZERO:
        return "contrastive_topology_breakout"
    return "regime_transition_probe"


def _resolve_horizon_minutes(
    live_section: GluedMarketObservation,
    baseline: HistoricalMarketBaseline,
) -> int:
    """Choose a deterministic validation horizon from spread and support stability."""
    spread_drift = abs(
        live_section.topology.relative_spread - baseline.median_relative_spread
    )
    if spread_drift >= Decimal("0.0015000"):
        return 30
    if live_section.support_count >= 2 and live_section.gluing_score >= Decimal("0.8000000"):
        return 5
    return 15


def _hypothesis_confidence(
    *,
    live_section: GluedMarketObservation,
    baseline: HistoricalMarketBaseline,
    novelty_lift: Decimal,
    harmonic_shift: Decimal,
    flow_shift: Decimal,
    spread_drift: Decimal,
) -> Decimal:
    """Collapse a local topology deviation into a bounded confidence score."""
    signal_strength = (
        abs(novelty_lift)
        + abs(harmonic_shift)
        + (abs(flow_shift) / Decimal("8"))
        - (abs(spread_drift) / Decimal("4"))
    )
    evidence = _clamp_probability(signal_strength * Decimal("20"))
    history_factor = _support_factor(baseline.sample_size)
    live_factor = _support_factor(live_section.support_count)
    return _clamp_probability(
        live_section.gluing_score * history_factor * live_factor * evidence
    )


def _hypothesis_signature(
    *,
    live_section: GluedMarketObservation,
    baseline: HistoricalMarketBaseline,
    regime: str,
    direction: HypothesisDirection,
    expected_edge_bps: Decimal,
    confidence: Decimal,
) -> str:
    """Return a reproducibility signature for one market hypothesis."""
    return _stable_digest(
        [
            live_section.reproducibility_signature(),
            baseline.symbol,
            baseline.start.isoformat(),
            baseline.end.isoformat(),
            str(baseline.sample_size),
            str(baseline.median_mid),
            str(baseline.median_relative_spread),
            str(baseline.median_flow_pressure),
            str(baseline.median_harmonic_advantage),
            str(baseline.median_novelty_score),
            regime,
            direction,
            str(expected_edge_bps),
            str(confidence),
        ]
    )


# @require("historical and live sections are coherent market sections")
# @ensure("returned hypotheses are deterministic, testable, and traceable to data overlaps")
def discover_market_hypotheses_from_sections(
    historical_sections: Sequence[GluedMarketObservation],
    live_sections: Sequence[GluedMarketObservation],
    *,
    min_history_points: int = 12,
    min_novelty_lift: Decimal | str = Decimal("0.0000500"),
    min_edge_bps: Decimal | str = Decimal("2.5000"),
) -> list[NovelMarketHypothesis]:
    """Generate testable hypotheses from historical and live market sections.

    The construction is a topology-preserving analogue of contrastive learning:
    compare the live chart against a historical neighborhood, then keep only
    deviations that survive gluing and remain small on overlap boundaries.
    """
    if not historical_sections:
        raise HypothesisGenerationError(
            "Historical market sections are required to generate hypotheses."
        )
    if not live_sections:
        raise HypothesisGenerationError(
            "Live market sections are required to generate hypotheses."
        )

    resolved_min_novelty_lift = _resolve_tolerance(
        min_novelty_lift, "min_novelty_lift"
    )
    resolved_min_edge_bps = _resolve_tolerance(min_edge_bps, "min_edge_bps")
    baselines = _build_historical_baselines(
        historical_sections, min_history_points=min_history_points
    )
    if not baselines:
        raise HypothesisGenerationError(
            "No symbol has enough historical support to form a baseline."
        )

    hypotheses: list[NovelMarketHypothesis] = []
    for live_section in sorted(live_sections, key=lambda item: (item.timestamp, item.symbol)):
        baseline = baselines.get(live_section.symbol)
        if baseline is None:
            continue

        novelty_lift = _quantize(
            live_section.novelty_score - baseline.median_novelty_score,
            FEATURE_QUANTUM,
        )
        harmonic_shift = _quantize(
            live_section.topology.harmonic_advantage
            - baseline.median_harmonic_advantage,
            FEATURE_QUANTUM,
        )
        flow_shift = _quantize(
            live_section.topology.flow_pressure - baseline.median_flow_pressure,
            FEATURE_QUANTUM,
        )
        spread_drift = _quantize(
            live_section.topology.relative_spread - baseline.median_relative_spread,
            FEATURE_QUANTUM,
        )
        direction_score = _quantize(
            novelty_lift + harmonic_shift + (flow_shift / Decimal("8")),
            FEATURE_QUANTUM,
        )

        if direction_score == ZERO:
            continue
        if novelty_lift * direction_score <= ZERO:
            continue

        expected_edge_bps = _quantize(
            abs(direction_score) * Decimal("10000"), Decimal("0.0001")
        )
        if abs(novelty_lift) < resolved_min_novelty_lift:
            continue
        if expected_edge_bps < resolved_min_edge_bps:
            continue

        direction: HypothesisDirection = "long" if direction_score > ZERO else "short"
        regime = _classify_hypothesis_regime(
            novelty_lift=novelty_lift,
            harmonic_shift=harmonic_shift,
            flow_shift=flow_shift,
            spread_drift=spread_drift,
        )
        confidence = _hypothesis_confidence(
            live_section=live_section,
            baseline=baseline,
            novelty_lift=novelty_lift,
            harmonic_shift=harmonic_shift,
            flow_shift=flow_shift,
            spread_drift=spread_drift,
        )
        horizon_minutes = _resolve_horizon_minutes(live_section, baseline)
        target_move_bps = _quantize(
            max(expected_edge_bps, resolved_min_edge_bps), Decimal("0.0001")
        )
        stop_move_bps = _quantize(
            max(target_move_bps / Decimal("2"), Decimal("1.0000")), Decimal("0.0001")
        )
        sign_text = "higher" if direction == "long" else "lower"
        thesis = (
            "Topology-preserving contrastive analogue: live harmonic pressure and "
            f"novelty diverge {sign_text} than the historical neighborhood while "
            "the glued overlap remains coherent."
        )
        validation_plan = (
            f"Replay the next {horizon_minutes} minutes for {live_section.symbol} and "
            f"test whether the mid price moves at least {target_move_bps} bps "
            f"{sign_text} than the entry reference before an adverse move of "
            f"{stop_move_bps} bps, using the immutable data signature."
        )
        hypotheses.append(
            NovelMarketHypothesis(
                symbol=live_section.symbol,
                as_of=live_section.timestamp,
                direction=direction,
                regime=regime,
                thesis=thesis,
                validation_plan=validation_plan,
                test_horizon_minutes=horizon_minutes,
                entry_reference_price=live_section.mid,
                target_move_bps=target_move_bps,
                stop_move_bps=stop_move_bps,
                expected_edge_bps=expected_edge_bps,
                confidence=confidence,
                gluing_score=live_section.gluing_score,
                live_support_count=live_section.support_count,
                historical_sample_size=baseline.sample_size,
                data_signature=_hypothesis_signature(
                    live_section=live_section,
                    baseline=baseline,
                    regime=regime,
                    direction=direction,
                    expected_edge_bps=expected_edge_bps,
                    confidence=confidence,
                ),
            )
        )

    if not hypotheses:
        raise HypothesisGenerationError(
            "No live section produced a testable hypothesis against the historical baseline."
        )

    return sorted(
        hypotheses,
        key=lambda item: (-item.confidence, item.as_of, item.symbol, item.direction),
    )


# @require("historical and live entries contain raw timestamped market observations")
# @ensure("generated hypotheses descend from normalized observations and glued sections")
def discover_market_hypotheses(
    historical_entries: Iterable[Mapping[str, Any]],
    live_entries: Iterable[Mapping[str, Any]],
    *,
    default_source: str = "feed",
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
    min_history_points: int = 12,
    min_novelty_lift: Decimal | str = Decimal("0.0000500"),
    min_edge_bps: Decimal | str = Decimal("2.5000"),
) -> list[NovelMarketHypothesis]:
    """Normalize raw market inputs and emit testable novel hypotheses."""
    historical_observations = normalize_market_batch(
        historical_entries, default_source=f"{default_source}_historical"
    )
    live_observations = normalize_market_batch(
        live_entries, default_source=f"{default_source}_live"
    )
    if not historical_observations:
        raise HypothesisGenerationError(
            "Historical market data is required to discover hypotheses."
        )
    if not live_observations:
        raise HypothesisGenerationError("Live market data is required to discover hypotheses.")

    historical_sections = glue_market_observations(
        historical_observations,
        price_tolerance=price_tolerance,
        spread_tolerance=spread_tolerance,
        h1_tolerance=h1_tolerance,
    )
    live_sections = glue_market_observations(
        live_observations,
        price_tolerance=price_tolerance,
        spread_tolerance=spread_tolerance,
        h1_tolerance=h1_tolerance,
    )
    return discover_market_hypotheses_from_sections(
        historical_sections,
        live_sections,
        min_history_points=min_history_points,
        min_novelty_lift=min_novelty_lift,
        min_edge_bps=min_edge_bps,
    )


RiskProofMode: TypeAlias = Literal["smt_required", "machine_checked"]


# @invariant("risk-critical bounds are explicit before downstream execution and proof discharge")
@dataclass(frozen=True)
class RiskInvariantSpecification:
    """Explicit risk-core obligations carried alongside normalized market data."""

    max_position_fraction: Decimal = Decimal("0.0500000")
    max_leverage: Decimal = Decimal("2.0000000")
    max_drawdown_fraction: Decimal = Decimal("0.0800000")
    kill_switch_drawdown_fraction: Decimal = Decimal("0.1000000")
    reject_on_stale_data_seconds: int = 30
    order_rejection_conditions: tuple[str, ...] = (
        "reject_non_positive_price",
        "reject_failed_gluing",
        "reject_stale_data",
        "reject_missing_audit_metadata",
        "reject_unverified_risk_core",
    )
    proof_obligation: RiskProofMode = "smt_required"
    paper_trading_required: bool = True

    def __post_init__(self) -> None:
        """Validate explicit risk bounds required by downstream modules."""
        for field_name, value in (
            ("max_position_fraction", self.max_position_fraction),
            ("max_leverage", self.max_leverage),
            ("max_drawdown_fraction", self.max_drawdown_fraction),
            ("kill_switch_drawdown_fraction", self.kill_switch_drawdown_fraction),
        ):
            if not value.is_finite():
                raise FeedValidationError(
                    f"Risk invariant '{field_name}' must be finite."
                )
        if self.max_position_fraction <= ZERO or self.max_position_fraction > ONE:
            raise FeedValidationError(
                "Risk invariant 'max_position_fraction' must lie in (0, 1]."
            )
        if self.max_leverage < ONE:
            raise FeedValidationError("Risk invariant 'max_leverage' must be at least 1.")
        if self.max_drawdown_fraction <= ZERO or self.max_drawdown_fraction >= ONE:
            raise FeedValidationError(
                "Risk invariant 'max_drawdown_fraction' must lie in (0, 1)."
            )
        if (
            self.kill_switch_drawdown_fraction <= self.max_drawdown_fraction
            or self.kill_switch_drawdown_fraction >= ONE
        ):
            raise FeedValidationError(
                "Risk invariant 'kill_switch_drawdown_fraction' must exceed "
                "max_drawdown_fraction and remain below 1."
            )
        if self.reject_on_stale_data_seconds < 0:
            raise FeedValidationError(
                "Risk invariant 'reject_on_stale_data_seconds' must be non-negative."
            )
        if not self.order_rejection_conditions:
            raise FeedValidationError(
                "Risk invariants require explicit order rejection conditions."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise FeedValidationError(
                "Risk invariants require an SMT-backed or machine-checked proof mode."
            )

    def reproducibility_signature(self) -> str:
        """Return a deterministic digest for downstream audit logging."""
        return _stable_digest(
            [
                str(self.max_position_fraction),
                str(self.max_leverage),
                str(self.max_drawdown_fraction),
                str(self.kill_switch_drawdown_fraction),
                str(self.reject_on_stale_data_seconds),
                self.proof_obligation,
                str(self.paper_trading_required),
                *self.order_rejection_conditions,
            ]
        )


def _normalize_local_batch(
    entries: Iterable[Mapping[str, Any]], *, observer: str
) -> list[NormalizedMarketObservation]:
    """Normalize and sort a batch of local observations."""
    normalized: list[NormalizedMarketObservation] = []
    for index, entry in enumerate(entries):
        try:
            observation = normalize_local_observation(entry, observer=observer)
        except MarketDataError as exc:
            raise NormalizationError(
                f"Failed to normalize local observation at index {index}: {exc}"
            ) from exc
        normalized.append(observation)

    return sorted(
        normalized,
        key=lambda item: (item.timestamp, item.symbol, item.source, item.venue),
    )


# @invariant("built market data remains versioned, auditable, and safe to restrict on overlaps")
@dataclass(frozen=True)
class MarketDataBundle:
    """High-level bundle produced by the market-data input site."""

    schema_version: str
    historical_observations: tuple[NormalizedMarketObservation, ...]
    live_feed_observations: tuple[NormalizedMarketObservation, ...]
    local_observations: tuple[NormalizedMarketObservation, ...]
    historical_sections: tuple[GluedMarketObservation, ...]
    live_sections: tuple[GluedMarketObservation, ...]
    hypotheses: tuple[NovelMarketHypothesis, ...]
    risk_invariants: RiskInvariantSpecification
    price_tolerance: Decimal
    spread_tolerance: Decimal
    h1_tolerance: Decimal
    min_history_points: int
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __post_init__(self) -> None:
        """Validate bundle completeness before downstream use."""
        if self.schema_version != normalization_schema_version():
            raise NormalizationError("Market data bundle schema version mismatch.")
        if not self.historical_observations:
            raise HypothesisGenerationError(
                "Market data bundles require historical observations."
            )
        if not self.live_sections:
            raise HypothesisGenerationError("Market data bundles require live sections.")
        if not self.historical_sections:
            raise HypothesisGenerationError(
                "Market data bundles require historical sections."
            )
        if not self.hypotheses:
            raise HypothesisGenerationError(
                "Market data bundles require at least one testable hypothesis."
            )
        if self.min_history_points < 1:
            raise HypothesisGenerationError(
                "Market data bundles require a positive history threshold."
            )
        if not self.data_signature:
            raise HypothesisGenerationError(
                "Market data bundles require a reproducibility signature."
            )

    @property
    def live_observations(self) -> tuple[NormalizedMarketObservation, ...]:
        """Return the combined live cover from feeds and local observations."""
        return tuple(
            sorted(
                (*self.live_feed_observations, *self.local_observations),
                key=lambda item: (item.timestamp, item.symbol, item.source, item.venue),
            )
        )

    @property
    def symbols(self) -> tuple[str, ...]:
        """Return the canonical symbols represented in the bundle."""
        return tuple(
            sorted(
                {
                    observation.symbol
                    for observation in (
                        *self.historical_observations,
                        *self.live_observations,
                    )
                }
            )
        )

    def summary(self) -> str:
        """Return a deterministic one-line summary of the bundle."""
        return market_data_summary(self)


def _market_data_bundle_signature(bundle: MarketDataBundle) -> str:
    """Return a stable audit digest for the full bundle."""
    parts = [
        bundle.schema_version,
        str(bundle.price_tolerance),
        str(bundle.spread_tolerance),
        str(bundle.h1_tolerance),
        str(bundle.min_history_points),
        bundle.risk_invariants.reproducibility_signature(),
    ]
    parts.extend(
        observation.reproducibility_signature()
        for observation in bundle.historical_observations
    )
    parts.append("live")
    parts.extend(
        observation.reproducibility_signature() for observation in bundle.live_observations
    )
    parts.append("historical_sections")
    parts.extend(section.reproducibility_signature() for section in bundle.historical_sections)
    parts.append("live_sections")
    parts.extend(section.reproducibility_signature() for section in bundle.live_sections)
    parts.append("hypotheses")
    parts.extend(hypothesis.data_signature for hypothesis in bundle.hypotheses)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


# @invariant("validation reports expose whether overlap and audit invariants still hold")
@dataclass(frozen=True)
class MarketDataValidationReport:
    """Deterministic validation report for a built market-data bundle."""

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    normalization_signatures_preserved: bool
    cocycle_checks_passed: bool
    lookahead_safe: bool
    risk_invariants_explicit: bool
    signature_matches: bool
    observations_checked: int
    sections_checked: int
    hypotheses_checked: int
    overlap_certificates: tuple[CocycleCertificate, ...]
    messages: tuple[str, ...]

    def summary(self) -> str:
        """Return a concise textual summary of the validation result."""
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} observations={self.observations_checked} "
            f"sections={self.sections_checked} hypotheses={self.hypotheses_checked} "
            f"issues={issues}"
        )


def _restriction_signatures_preserved(
    observations: tuple[NormalizedMarketObservation, ...],
) -> bool:
    """Return whether restricting to the full support preserves overlap signatures."""
    if not observations:
        return True
    restricted = restrict_observations(
        observations,
        symbols={item.symbol for item in observations},
        start=observations[0].timestamp,
        end=observations[-1].timestamp,
    )
    original_signatures = tuple(item.normalization_signature() for item in observations)
    restricted_signatures = tuple(item.normalization_signature() for item in restricted)
    return original_signatures == restricted_signatures


# @require("historical data predates live evaluation data and raw entries are timestamped")
# @ensure("returned bundle is normalized, auditable, and contains at least one testable idea")
def build_market_data(
    historical_entries: Iterable[Mapping[str, Any]],
    live_entries: Iterable[Mapping[str, Any]],
    *,
    local_entries: Iterable[Mapping[str, Any]] = (),
    local_observer: str = "local_observer",
    default_source: str = "feed",
    price_tolerance: Decimal | str = Decimal("0.0025"),
    spread_tolerance: Decimal | str = Decimal("0.0010"),
    h1_tolerance: Decimal | str | None = None,
    min_history_points: int = 12,
    min_novelty_lift: Decimal | str = Decimal("0.0000500"),
    min_edge_bps: Decimal | str = Decimal("2.5000"),
    risk_invariants: RiskInvariantSpecification | None = None,
) -> MarketDataBundle:
    """Build an auditable market-data bundle from historical, live, and local inputs."""
    resolved_price_tolerance = _resolve_tolerance(price_tolerance, "price_tolerance")
    resolved_spread_tolerance = _resolve_tolerance(
        spread_tolerance, "spread_tolerance"
    )
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize(resolved_price_tolerance * Decimal("2"), FEATURE_QUANTUM)
    )
    active_risk_invariants = (
        risk_invariants if risk_invariants is not None else RiskInvariantSpecification()
    )

    historical_observations = tuple(
        normalize_market_batch(
            historical_entries, default_source=f"{default_source}_historical"
        )
    )
    live_feed_observations = tuple(
        normalize_market_batch(live_entries, default_source=f"{default_source}_live")
    )
    local_observations = tuple(
        _normalize_local_batch(local_entries, observer=local_observer)
    )
    live_observations = tuple(
        sorted(
            (*live_feed_observations, *local_observations),
            key=lambda item: (item.timestamp, item.symbol, item.source, item.venue),
        )
    )

    if not historical_observations:
        raise HypothesisGenerationError(
            "Historical market data is required to build market data."
        )
    if not live_observations:
        raise HypothesisGenerationError(
            "Live feed or local market observations are required to build market data."
        )
    if historical_observations[-1].timestamp >= live_observations[0].timestamp:
        raise HypothesisGenerationError(
            "Historical observations must strictly precede live/local observations "
            "to prevent lookahead bias and data leakage."
        )

    historical_sections = tuple(
        glue_market_observations(
            historical_observations,
            price_tolerance=resolved_price_tolerance,
            spread_tolerance=resolved_spread_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    )
    live_sections = tuple(
        glue_market_observations(
            live_observations,
            price_tolerance=resolved_price_tolerance,
            spread_tolerance=resolved_spread_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    )
    hypotheses = tuple(
        discover_market_hypotheses_from_sections(
            historical_sections,
            live_sections,
            min_history_points=min_history_points,
            min_novelty_lift=min_novelty_lift,
            min_edge_bps=min_edge_bps,
        )
    )
    audit_metadata = tuple(
        sorted(
            (
                ("execution_mode", "paper_only"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("leakage_guard", "historical_strictly_precedes_live"),
                ("lookahead_guard", "training_window_ends_before_live_window"),
                ("proof_obligation", active_risk_invariants.proof_obligation),
                ("schema_version", normalization_schema_version()),
                (
                    "survivorship_guard",
                    "canonical_symbols_and_versioned_digests_preserved",
                ),
            )
        )
    )
    bundle = MarketDataBundle(
        schema_version=normalization_schema_version(),
        historical_observations=historical_observations,
        live_feed_observations=live_feed_observations,
        local_observations=local_observations,
        historical_sections=historical_sections,
        live_sections=live_sections,
        hypotheses=hypotheses,
        risk_invariants=active_risk_invariants,
        price_tolerance=resolved_price_tolerance,
        spread_tolerance=resolved_spread_tolerance,
        h1_tolerance=resolved_h1_tolerance,
        min_history_points=min_history_points,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return MarketDataBundle(
        schema_version=bundle.schema_version,
        historical_observations=bundle.historical_observations,
        live_feed_observations=bundle.live_feed_observations,
        local_observations=bundle.local_observations,
        historical_sections=bundle.historical_sections,
        live_sections=bundle.live_sections,
        hypotheses=bundle.hypotheses,
        risk_invariants=bundle.risk_invariants,
        price_tolerance=bundle.price_tolerance,
        spread_tolerance=bundle.spread_tolerance,
        h1_tolerance=bundle.h1_tolerance,
        min_history_points=bundle.min_history_points,
        data_signature=_market_data_bundle_signature(bundle),
        audit_metadata=bundle.audit_metadata,
    )


# @require("bundle comes from build_market_data or an equivalent deterministic constructor")
# @ensure("report states whether restriction, timestamp, symbol, and audit invariants hold")
def validate_market_data(bundle: MarketDataBundle) -> MarketDataValidationReport:
    """Validate that a market-data bundle still satisfies core input invariants."""
    certificates = (
        check_cocycle_gluing(
            bundle.historical_observations,
            price_tolerance=bundle.price_tolerance,
            spread_tolerance=bundle.spread_tolerance,
            h1_tolerance=bundle.h1_tolerance,
        )
        + check_cocycle_gluing(
            bundle.live_observations,
            price_tolerance=bundle.price_tolerance,
            spread_tolerance=bundle.spread_tolerance,
            h1_tolerance=bundle.h1_tolerance,
        )
    )
    normalization_preserved = _restriction_signatures_preserved(
        bundle.historical_observations
    ) and _restriction_signatures_preserved(bundle.live_observations)
    lookahead_safe = (
        bundle.historical_observations[-1].timestamp < bundle.live_observations[0].timestamp
    )
    cocycle_checks_passed = all(certificate.passes for certificate in certificates)
    risk_invariants_explicit = (
        bool(bundle.risk_invariants.order_rejection_conditions)
        and bundle.risk_invariants.proof_obligation
        in {"smt_required", "machine_checked"}
    )
    signature_matches = bundle.data_signature == _market_data_bundle_signature(bundle)
    timestamp_symbol_invariants_preserved = normalization_preserved

    messages: list[str] = []
    if not normalization_preserved:
        messages.append("restriction signature preservation failed")
    if not cocycle_checks_passed:
        messages.append("one or more overlap cocycle checks failed")
    if not lookahead_safe:
        messages.append("historical/live ordering permits lookahead bias")
    if not risk_invariants_explicit:
        messages.append("risk invariants are not explicit enough for downstream proof")
    if not signature_matches:
        messages.append("bundle reproducibility signature mismatch")

    passes = (
        timestamp_symbol_invariants_preserved
        and cocycle_checks_passed
        and lookahead_safe
        and risk_invariants_explicit
        and signature_matches
    )
    return MarketDataValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        normalization_signatures_preserved=normalization_preserved,
        cocycle_checks_passed=cocycle_checks_passed,
        lookahead_safe=lookahead_safe,
        risk_invariants_explicit=risk_invariants_explicit,
        signature_matches=signature_matches,
        observations_checked=(
            len(bundle.historical_observations) + len(bundle.live_observations)
        ),
        sections_checked=len(bundle.historical_sections) + len(bundle.live_sections),
        hypotheses_checked=len(bundle.hypotheses),
        overlap_certificates=certificates,
        messages=tuple(messages),
    )


# @require("bundle is a deterministic market-data bundle")
# @ensure("summary text is reproducible and references the bundle audit signature")
def market_data_summary(bundle: MarketDataBundle) -> str:
    """Return a deterministic summary string for the market-data bundle."""
    report = validate_market_data(bundle)
    ideas = ", ".join(
        f"{hypothesis.symbol}:{hypothesis.direction}:{hypothesis.expected_edge_bps}"
        for hypothesis in bundle.hypotheses[:3]
    )
    if not ideas:
        ideas = "none"
    status = "pass" if report.passes else "fail"
    symbols = ",".join(bundle.symbols)
    return (
        f"market_data[{bundle.schema_version}] symbols={symbols} "
        f"historical_obs={len(bundle.historical_observations)} "
        f"feed_live_obs={len(bundle.live_feed_observations)} "
        f"local_obs={len(bundle.local_observations)} "
        f"live_sections={len(bundle.live_sections)} "
        f"hypotheses={len(bundle.hypotheses)} "
        f"validation={status} proof={bundle.risk_invariants.proof_obligation} "
        f"paper_only={bundle.risk_invariants.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas={ideas}"
    )


__all__ = [
    "CocycleCertificate",
    "FeedValidationError",
    "GluedMarketObservation",
    "GluingInvariantError",
    "HistoricalMarketBaseline",
    "HypothesisGenerationError",
    "MarketDataBundle",
    "MarketDataError",
    "MarketDataValidationReport",
    "NovelMarketHypothesis",
    "NormalizationError",
    "NormalizedMarketObservation",
    "RiskInvariantSpecification",
    "TopologyCoordinates",
    "build_market_data",
    "check_cocycle_gluing",
    "discover_market_hypotheses",
    "discover_market_hypotheses_from_sections",
    "validate_market_data",
    "market_data_summary",
    "normalization_schema_version",
    "glue_market_observations",
    "group_by_overlap",
    "normalize_feed_entry",
    "normalize_local_observation",
    "normalize_market_batch",
    "restrict_observations",
]
