"""Encode a verified trading thesis as a pi/sigma strategy kernel.

This module is the pi/sigma core of the typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

`signal_geometry` produces a coherent global alpha section over the trading
cover.  This module refines that section into explicit strategy rules and
position intents.  The design borrows a machine-learning intuition without
introducing opaque latent state:

* ``sigma`` is an interpretable evidence sum over explicit coordinates,
* ``pi`` is an agreement gate that rewards overlap-compatible local sections,
* cocycle checks witness whether rule-local corrections glue with vanishing
  H¹ obstruction, and
* the resulting intents are marked as pending-risk rather than executable so
  downstream modules can discharge the final risk and execution obligations.

The novel idea is a verified analogue of prototype learning.  Instead of
discovering a hidden trading manifold with a black-box encoder, we construct
three explicit strategy prototypes and require them to preserve local
topological neighborhoods.  When their corrections agree on overlaps, the
strategy thesis descends to one coherent section that can be handed to the risk
engine as typed position intent.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Collection, Iterable, Literal, Sequence, TypeAlias

from deppy.signal_geometry import (
    GlobalSignalSection,
    SignalCoordinates,
    SignalGeometryBundle,
    SignalResearchIdea,
)

FEATURE_QUANTUM = Decimal("0.0000001")
FRACTION_QUANTUM = Decimal("0.0000001")
ONE = Decimal("1")
ZERO = Decimal("0")
HALF = Decimal("0.5")
INTENT_SIDE_THRESHOLD = Decimal("0.0150000")
MIN_TARGET_THRESHOLD = Decimal("0.0200000")
EDGE_QUANTUM = Decimal("0.0001")
STRATEGY_KERNEL_SCHEMA_VERSION = "strategy_kernel.v1"
DEFAULT_ORDER_REJECTION_CONDITIONS: tuple[str, ...] = (
    "reject_non_positive_price",
    "reject_failed_gluing",
    "reject_stale_data",
    "reject_missing_audit_metadata",
    "reject_unverified_risk_core",
)

StrategyKey: TypeAlias = tuple[datetime, str]
RuleName: TypeAlias = Literal["transport", "harmonic_reversion", "novelty_breakout"]
IntentStatus: TypeAlias = Literal["blocked", "pending_risk"]
ProofMode: TypeAlias = Literal["smt_required", "machine_checked"]
StrategyIdeaSide: TypeAlias = Literal["long", "short"]
StrategyKernelInput: TypeAlias = SignalGeometryBundle | Iterable[GlobalSignalSection]

RULES: tuple[RuleName, ...] = ("transport", "harmonic_reversion", "novelty_breakout")


class StrategyKernelError(ValueError):
    """Base error raised by the strategy kernel."""


class StrategyNormalizationError(StrategyKernelError):
    """Raised when a strategy section violates normalization invariants."""


class StrategyRestrictionError(StrategyKernelError):
    """Raised when a restriction map for strategy sections is ill-formed."""


class StrategyGluingError(StrategyKernelError):
    """Raised when strategy-local sections fail to glue on overlaps."""


class StrategyIdeaGenerationError(StrategyKernelError):
    """Raised when the strategy kernel cannot emit a testable research idea."""


def _quantize(value: Decimal, quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    """Return *value* rounded onto the project-wide decimal lattice."""
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    """Convert *value* to a finite :class:`Decimal`."""
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise StrategyNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc

    if not candidate.is_finite():
        raise StrategyNormalizationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    """Normalize *value* to a timezone-aware UTC timestamp."""
    if not isinstance(value, datetime):
        raise StrategyRestrictionError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    """Return the canonical symbol representation used on overlaps."""
    if not isinstance(value, str):
        raise StrategyNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise StrategyNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise StrategyNormalizationError(
            f"Field 'symbol' cannot normalize from {value!r}."
        )
    return candidate


def _safe_ratio(numerator: Decimal, denominator: Decimal) -> Decimal:
    """Return a quantized ratio, treating zero denominator as zero."""
    if denominator == ZERO:
        return ZERO
    return _quantize(numerator / denominator, FRACTION_QUANTUM)


def _median_decimal(
    values: Sequence[Decimal], quantum: Decimal = FEATURE_QUANTUM
) -> Decimal:
    """Return the median of *values* on the requested decimal lattice."""
    if not values:
        raise StrategyNormalizationError("Median is undefined for an empty value set.")

    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return _quantize(ordered[middle], quantum)
    return _quantize((ordered[middle - 1] + ordered[middle]) / Decimal("2"), quantum)


def _max_gap(values: Sequence[Decimal], quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    """Return the maximum gap between values on a shared overlap."""
    if not values:
        return ZERO
    return _quantize(max(values) - min(values), quantum)


def _triple_overlap_residual(values: Sequence[Decimal]) -> Decimal:
    """Return the H¹-style residual of corrections on triple overlaps."""
    if len(values) < 3:
        return ZERO
    median_value = _median_decimal(values)
    residual = max((abs(value - median_value) for value in values), default=ZERO)
    return _quantize(residual)


def _resolve_tolerance(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a tolerance parameter to a non-negative finite decimal."""
    tolerance = _coerce_decimal(value, field_name)
    if tolerance < ZERO:
        raise StrategyRestrictionError(f"Tolerance '{field_name}' must be non-negative.")
    return _quantize(tolerance)


def _squash_signal(value: Decimal) -> Decimal:
    """Map an arbitrary finite decimal into the interval ``[-1, 1]``."""
    if not value.is_finite():
        raise StrategyNormalizationError("Signal values must be finite before squashing.")
    scale = ONE + abs(value)
    return _quantize(value / scale)


def _clamp_probability(value: Decimal) -> Decimal:
    """Clamp *value* to the closed unit interval."""
    if not value.is_finite():
        raise StrategyNormalizationError("Probabilistic scores must be finite.")
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize(value, FRACTION_QUANTUM)


def _gluing_score(obstruction: Decimal, h1_tolerance: Decimal) -> Decimal:
    """Convert an obstruction witness into a unit gluing score."""
    if h1_tolerance == ZERO:
        return ZERO if obstruction > ZERO else ONE
    return _clamp_probability(ONE - min(ONE, obstruction / h1_tolerance))


def _support_factor(support_count: int) -> Decimal:
    """Return a bounded support factor for one glued signal section."""
    if support_count < 1:
        raise StrategyNormalizationError("Support count must be positive.")
    return _quantize(Decimal(support_count) / Decimal(support_count + 1))


def _validate_unit_signal(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in ``[-1, 1]``."""
    if not value.is_finite():
        raise StrategyNormalizationError(f"Field '{field_name}' must be finite.")
    if abs(value) > ONE:
        raise StrategyNormalizationError(f"Field '{field_name}' must lie in [-1, 1].")


def _validate_probability(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in ``[0, 1]``."""
    if not value.is_finite():
        raise StrategyNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise StrategyNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_positive_decimal(value: Decimal, field_name: str) -> None:
    """Validate that *value* is finite and strictly positive."""
    if not value.is_finite():
        raise StrategyNormalizationError(f"Field '{field_name}' must be finite.")
    if value <= ZERO:
        raise StrategyNormalizationError(f"Field '{field_name}' must be strictly positive.")


def _quantize_fraction(value: Decimal) -> Decimal:
    """Quantize *value* onto the strategy-fraction lattice."""
    return _quantize(value, FRACTION_QUANTUM)


def _quantize_edge(value: Decimal) -> Decimal:
    """Quantize expected edge values in basis points."""
    return _quantize(value, EDGE_QUANTUM)


def _stable_digest(parts: Sequence[str]) -> str:
    """Return a deterministic digest for audit and replay workflows."""
    payload = "\x1f".join((STRATEGY_KERNEL_SCHEMA_VERSION, *parts)).encode("utf-8")
    return sha256(payload).hexdigest()


def strategy_kernel_schema_version() -> str:
    """Return the schema version used for strategy-kernel audit digests."""
    return STRATEGY_KERNEL_SCHEMA_VERSION


def _regime_match_score(rule: "StrategyRule", regime: str) -> Decimal:
    """Return how naturally *rule* matches a signal *regime*."""
    if regime in rule.preferred_regimes:
        return ONE
    if regime == "balanced_probe":
        return Decimal("0.7500000")
    return Decimal("0.5500000")


def _sigma_core(rule_name: RuleName, coordinates: SignalCoordinates) -> Decimal:
    """Return the interpretable sigma evidence for one strategy rule."""
    if rule_name == "transport":
        value = (
            coordinates.continuation_bias
            + (coordinates.topology_memory * Decimal("0.50"))
            + (coordinates.novelty_lift * Decimal("0.25"))
            - (coordinates.crowding_pressure * Decimal("0.20"))
        )
        return _squash_signal(value)
    if rule_name == "harmonic_reversion":
        value = (
            coordinates.mean_reversion_bias
            - (coordinates.continuation_bias * Decimal("0.35"))
            - (coordinates.crowding_pressure * Decimal("0.20"))
            + (coordinates.regime_curvature * Decimal("0.15"))
        )
        return _squash_signal(value)
    value = (
        coordinates.novelty_lift
        + (coordinates.topology_memory * Decimal("0.35"))
        + (coordinates.regime_curvature * Decimal("0.25"))
        - (coordinates.crowding_pressure * Decimal("0.25"))
    )
    return _squash_signal(value)


def _local_conviction(
    signal: GlobalSignalSection, pi_score: Decimal, alpha_score: Decimal
) -> Decimal:
    """Return a bounded conviction score for one local strategy section."""
    coherence = _clamp_probability(ONE - (abs(alpha_score - signal.alpha_score) * HALF))
    conviction = (
        pi_score * Decimal("0.55")
        + signal.conviction * Decimal("0.30")
        + coherence * Decimal("0.15")
    )
    return _clamp_probability(conviction)


def _local_target_fraction(
    signal: GlobalSignalSection,
    rule: "StrategyRule",
    alpha_score: Decimal,
    conviction: Decimal,
) -> Decimal:
    """Return the proposed position fraction for one local strategy section."""
    crowding_drag = _clamp_probability(ONE - abs(signal.coordinates.crowding_pressure))
    target_core = (
        conviction * Decimal("0.45")
        + abs(alpha_score) * Decimal("0.30")
        + crowding_drag * Decimal("0.15")
        + signal.gluing_score * Decimal("0.10")
    )
    bounded = min(rule.size_cap, _clamp_probability(target_core) * rule.size_cap)
    return _quantize_fraction(bounded)


def _holding_period_for_rule(rule_name: RuleName) -> int:
    """Return the maximum holding periods allowed for one strategy rule."""
    if rule_name == "transport":
        return 8
    if rule_name == "harmonic_reversion":
        return 4
    return 6


def _build_risk_bounds(
    signal: GlobalSignalSection,
    rule: "StrategyRule",
    alpha_score: Decimal,
    pi_score: Decimal,
    target_fraction: Decimal,
) -> "RiskBounds":
    """Build local risk bounds that must agree on overlaps."""
    coordinates = signal.coordinates
    stop_base = (
        Decimal("0.0100000")
        + abs(coordinates.regime_curvature) * Decimal("0.0200000")
        + abs(coordinates.crowding_pressure) * Decimal("0.0150000")
    )
    if rule.name == "harmonic_reversion":
        stop_base += Decimal("0.0050000")
        take_multiplier = Decimal("1.4000000")
    elif rule.name == "novelty_breakout":
        stop_base += Decimal("0.0075000")
        take_multiplier = Decimal("2.1000000")
    else:
        take_multiplier = Decimal("1.8000000")

    stop_loss_fraction = _clamp_probability(_quantize_fraction(stop_base))
    take_profit_fraction = _clamp_probability(
        _quantize_fraction((stop_loss_fraction * take_multiplier) + abs(alpha_score) * Decimal("0.0500000"))
    )
    max_position_fraction = max(
        target_fraction,
        _clamp_probability(
            min(
                rule.size_cap,
                target_fraction
                + (signal.conviction * Decimal("0.0800000"))
                + (signal.gluing_score * Decimal("0.0400000")),
            )
        ),
    )
    conviction_floor = _clamp_probability(
        (signal.conviction * Decimal("0.5500000")) + (pi_score * Decimal("0.2000000"))
    )
    h1_buffer = _clamp_probability(
        Decimal("0.0500000")
        + ((ONE - signal.gluing_score) * Decimal("0.3000000"))
        + (abs(alpha_score - signal.alpha_score) * Decimal("0.2000000"))
    )
    return RiskBounds(
        max_position_fraction=_quantize_fraction(max_position_fraction),
        stop_loss_fraction=stop_loss_fraction,
        take_profit_fraction=take_profit_fraction,
        max_holding_periods=_holding_period_for_rule(rule.name),
        conviction_floor=conviction_floor,
        h1_buffer=h1_buffer,
    )


def _infer_side(
    alpha_score: Decimal, conviction: Decimal, target_fraction: Decimal
) -> str:
    """Map a glued alpha signal to a trading side."""
    if (
        conviction < Decimal("0.2500000")
        or abs(alpha_score) < INTENT_SIDE_THRESHOLD
        or target_fraction < MIN_TARGET_THRESHOLD
    ):
        return "flat"
    if alpha_score > ZERO:
        return "long"
    return "short"


def _local_thesis(rule_name: RuleName, regime: str, alpha_score: Decimal) -> str:
    """Return a thesis string for one local strategy rule."""
    direction = "upside" if alpha_score >= ZERO else "downside"
    if rule_name == "transport":
        return (
            "transport rule: follow persistent "
            f"{direction} flow when {regime} neighborhoods stay topology-preserving"
        )
    if rule_name == "harmonic_reversion":
        return (
            "harmonic reversion rule: fade displaced "
            f"{direction} pressure only when overlap corrections remain exact"
        )
    return (
        "novelty breakout rule: admit the "
        f"{direction} prototype only when it survives H^1-aware gluing"
    )


def _global_style(regime: str, rules: Sequence[RuleName], target_fraction: Decimal) -> str:
    """Infer the global style of the glued strategy section."""
    rule_set = set(rules)
    if regime == "trend_persistence" and "transport" in rule_set:
        return "transport_stack"
    if regime == "harmonic_reversion" and "harmonic_reversion" in rule_set:
        return "harmonic_stack"
    if "novelty_breakout" in rule_set and target_fraction >= Decimal("0.1000000"):
        return "novelty_probe"
    return "balanced_kernel"


def _global_thesis(style: str, side: str) -> str:
    """Return the thesis implied by one glued strategy section."""
    if side == "flat":
        return "stay neutral until the local strategy rules agree more strongly on overlaps"
    if style == "transport_stack":
        return "press the transport thesis because pi-agreement and sigma evidence glue coherently"
    if style == "harmonic_stack":
        return "trade the harmonic pullback because the exact correction remains stable under gluing"
    if style == "novelty_probe":
        return "deploy the novelty probe cautiously because the new idea survives overlap checks"
    return "size the idea lightly while the kernel remains balanced but coherent"


def _intent_reason(status: IntentStatus, section: "GlobalStrategySection") -> str:
    """Return a human-readable reason for one position intent status."""
    if status == "pending_risk":
        return "intent is coherent enough to descend to the risk engine for approval"
    return (
        "intent is blocked before risk review because conviction, side, or target "
        "fraction is too weak"
    )


def _mode_label(labels: Sequence[str]) -> str:
    """Return the most common label, breaking ties lexicographically."""
    if not labels:
        raise StrategyNormalizationError("Cannot choose a mode from an empty label set.")
    counts: dict[str, int] = {}
    for label in labels:
        counts[label] = counts.get(label, 0) + 1
    best_count = max(counts.values())
    winners = sorted(label for label, count in counts.items() if count == best_count)
    return winners[0]


def _require_unique_rules(
    members: Sequence["LocalStrategySection"], key: StrategyKey
) -> tuple[RuleName, ...]:
    """Ensure an overlap contains at most one local section from each rule."""
    rule_names = [member.rule for member in members]
    unique = tuple(sorted(set(rule_names)))
    if len(unique) != len(rule_names):
        timestamp, symbol = key
        raise StrategyGluingError(
            f"Strategy overlap {symbol}@{timestamp.isoformat()} contains duplicate rules."
        )
    return unique


def _risk_gap(members: Sequence["LocalStrategySection"]) -> Decimal:
    """Return the largest disagreement among local risk bounds."""
    bounds = [member.risk_bounds for member in members]
    holding_gap = _safe_ratio(
        Decimal(max(bound.max_holding_periods for bound in bounds) - min(bound.max_holding_periods for bound in bounds)),
        Decimal("100"),
    )
    return _quantize(
        max(
            _max_gap([bound.max_position_fraction for bound in bounds], FRACTION_QUANTUM),
            _max_gap([bound.stop_loss_fraction for bound in bounds], FRACTION_QUANTUM),
            _max_gap([bound.take_profit_fraction for bound in bounds], FRACTION_QUANTUM),
            _max_gap([bound.conviction_floor for bound in bounds], FRACTION_QUANTUM),
            _max_gap([bound.h1_buffer for bound in bounds], FRACTION_QUANTUM),
            holding_gap,
        ),
        FRACTION_QUANTUM,
    )


def _resolve_rule(
    rule: "StrategyRule | RuleName", rules: Sequence["StrategyRule"] | None = None
) -> "StrategyRule":
    """Resolve *rule* against the provided rulebook."""
    rulebook = rules or default_rulebook()
    mapping = {member.name: member for member in rulebook}
    if len(mapping) != len(rulebook):
        raise StrategyNormalizationError("Rulebook contains duplicate rule names.")
    if isinstance(rule, StrategyRule):
        return mapping.get(rule.name, rule)
    if rule not in mapping:
        raise StrategyNormalizationError(f"Unknown strategy rule {rule!r}.")
    return mapping[rule]


@dataclass(frozen=True)
class StrategyRule:
    """A typed strategy prototype used to evaluate one global signal section."""

    name: RuleName
    preferred_regimes: tuple[str, ...]
    sigma_weight: Decimal
    pi_weight: Decimal
    size_cap: Decimal
    thesis: str

    def __init__(
        self,
        name: RuleName,
        preferred_regimes: tuple[str, ...],
        sigma_weight: Decimal,
        pi_weight: Decimal,
        size_cap: Decimal,
        thesis: str,
    ) -> None:
        """Initialize and validate the typed rule specification."""
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "preferred_regimes", preferred_regimes)
        object.__setattr__(self, "sigma_weight", sigma_weight)
        object.__setattr__(self, "pi_weight", pi_weight)
        object.__setattr__(self, "size_cap", size_cap)
        object.__setattr__(self, "thesis", thesis)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the rule specification."""
        if self.name not in RULES:
            raise StrategyNormalizationError(f"Unknown strategy rule {self.name!r}.")
        if not self.preferred_regimes:
            raise StrategyNormalizationError("Strategy rules must prefer at least one regime.")
        _validate_probability(self.sigma_weight, "sigma_weight")
        _validate_probability(self.pi_weight, "pi_weight")
        _validate_positive_decimal(self.size_cap, "size_cap")
        if self.size_cap > ONE:
            raise StrategyNormalizationError("Field 'size_cap' must lie in (0, 1].")
        if not self.thesis.strip():
            raise StrategyNormalizationError("Strategy rules must carry a non-empty thesis.")


@dataclass(frozen=True)
class RiskBounds:
    """Risk bounds attached to one local or global trading thesis."""

    max_position_fraction: Decimal
    stop_loss_fraction: Decimal
    take_profit_fraction: Decimal
    max_holding_periods: int
    conviction_floor: Decimal
    h1_buffer: Decimal

    def __init__(
        self,
        max_position_fraction: Decimal,
        stop_loss_fraction: Decimal,
        take_profit_fraction: Decimal,
        max_holding_periods: int,
        conviction_floor: Decimal,
        h1_buffer: Decimal,
    ) -> None:
        """Initialize and validate the bounded risk envelope."""
        object.__setattr__(self, "max_position_fraction", max_position_fraction)
        object.__setattr__(self, "stop_loss_fraction", stop_loss_fraction)
        object.__setattr__(self, "take_profit_fraction", take_profit_fraction)
        object.__setattr__(self, "max_holding_periods", max_holding_periods)
        object.__setattr__(self, "conviction_floor", conviction_floor)
        object.__setattr__(self, "h1_buffer", h1_buffer)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate that the risk envelope is bounded and non-degenerate."""
        _validate_probability(self.max_position_fraction, "max_position_fraction")
        _validate_probability(self.stop_loss_fraction, "stop_loss_fraction")
        _validate_probability(self.take_profit_fraction, "take_profit_fraction")
        _validate_probability(self.conviction_floor, "conviction_floor")
        _validate_probability(self.h1_buffer, "h1_buffer")
        if self.stop_loss_fraction == ZERO:
            raise StrategyNormalizationError(
                "Field 'stop_loss_fraction' must be strictly positive."
            )
        if self.take_profit_fraction < self.stop_loss_fraction:
            raise StrategyNormalizationError(
                "Field 'take_profit_fraction' must be at least stop_loss_fraction."
            )
        if self.max_holding_periods < 1:
            raise StrategyNormalizationError(
                "Field 'max_holding_periods' must be a positive integer."
            )


@dataclass(frozen=True)
class LocalStrategySection:
    """A local strategy rule attached to one glued global signal section."""

    timestamp: datetime
    symbol: str
    rule: RuleName
    regime: str
    charts: tuple[str, ...]
    sources: tuple[str, ...]
    venues: tuple[str, ...]
    support_count: int
    signal_gluing_score: Decimal
    pi_score: Decimal
    sigma_score: Decimal
    alpha_score: Decimal
    conviction: Decimal
    target_fraction: Decimal
    risk_bounds: RiskBounds
    thesis: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        rule: RuleName,
        regime: str,
        charts: tuple[str, ...],
        sources: tuple[str, ...],
        venues: tuple[str, ...],
        support_count: int,
        signal_gluing_score: Decimal,
        pi_score: Decimal,
        sigma_score: Decimal,
        alpha_score: Decimal,
        conviction: Decimal,
        target_fraction: Decimal,
        risk_bounds: RiskBounds,
        thesis: str,
    ) -> None:
        """Initialize and validate one local strategy section."""
        object.__setattr__(self, "timestamp", timestamp)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "rule", rule)
        object.__setattr__(self, "regime", regime)
        object.__setattr__(self, "charts", charts)
        object.__setattr__(self, "sources", sources)
        object.__setattr__(self, "venues", venues)
        object.__setattr__(self, "support_count", support_count)
        object.__setattr__(self, "signal_gluing_score", signal_gluing_score)
        object.__setattr__(self, "pi_score", pi_score)
        object.__setattr__(self, "sigma_score", sigma_score)
        object.__setattr__(self, "alpha_score", alpha_score)
        object.__setattr__(self, "conviction", conviction)
        object.__setattr__(self, "target_fraction", target_fraction)
        object.__setattr__(self, "risk_bounds", risk_bounds)
        object.__setattr__(self, "thesis", thesis)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate local section invariants."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise StrategyNormalizationError("Strategy timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise StrategyNormalizationError("Strategy timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise StrategyNormalizationError("Strategy symbols must be canonicalized.")
        if self.rule not in RULES:
            raise StrategyNormalizationError(f"Unknown strategy rule {self.rule!r}.")
        if not self.regime.strip():
            raise StrategyNormalizationError("Strategy sections must name a regime.")
        if not self.charts:
            raise StrategyNormalizationError("Strategy sections must retain signal charts.")
        if not self.sources:
            raise StrategyNormalizationError("Strategy sections must retain source support.")
        if not self.venues:
            raise StrategyNormalizationError("Strategy sections must retain venue support.")
        if self.support_count < 1:
            raise StrategyNormalizationError("Strategy sections must have positive support.")
        _validate_probability(self.signal_gluing_score, "signal_gluing_score")
        _validate_probability(self.pi_score, "pi_score")
        _validate_unit_signal(self.sigma_score, "sigma_score")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.target_fraction, "target_fraction")
        if self.target_fraction > self.risk_bounds.max_position_fraction:
            raise StrategyNormalizationError(
                "Target fraction cannot exceed the local maximum position fraction."
            )
        if not self.thesis.strip():
            raise StrategyNormalizationError("Strategy sections must carry a non-empty thesis.")

    def strategy_key(self) -> StrategyKey:
        """Return the restriction and gluing key for the section."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, RuleName]:
        """Return the invariant signature that must persist under restriction."""
        return (self.timestamp, self.symbol, self.rule)


@dataclass(frozen=True)
class StrategyCocycleCertificate:
    """Diagnostic evidence that local strategy rules can be glued."""

    key: StrategyKey
    rules: tuple[RuleName, ...]
    alpha_gap: Decimal
    target_gap: Decimal
    risk_gap: Decimal
    triple_overlap_residual: Decimal
    h1_obstruction: Decimal
    passes: bool
    reason: str

    def __init__(
        self,
        key: StrategyKey,
        rules: tuple[RuleName, ...],
        alpha_gap: Decimal,
        target_gap: Decimal,
        risk_gap: Decimal,
        triple_overlap_residual: Decimal,
        h1_obstruction: Decimal,
        passes: bool,
        reason: str,
    ) -> None:
        """Initialize one deterministic cocycle certificate."""
        object.__setattr__(self, "key", key)
        object.__setattr__(self, "rules", rules)
        object.__setattr__(self, "alpha_gap", alpha_gap)
        object.__setattr__(self, "target_gap", target_gap)
        object.__setattr__(self, "risk_gap", risk_gap)
        object.__setattr__(self, "triple_overlap_residual", triple_overlap_residual)
        object.__setattr__(self, "h1_obstruction", h1_obstruction)
        object.__setattr__(self, "passes", passes)
        object.__setattr__(self, "reason", reason)

    def assert_passes(self) -> None:
        """Raise :class:`StrategyGluingError` when the certificate fails."""
        if not self.passes:
            timestamp, symbol = self.key
            raise StrategyGluingError(
                f"Strategy overlap {symbol}@{timestamp.isoformat()} failed gluing: "
                f"{self.reason}"
            )


@dataclass(frozen=True)
class GlobalStrategySection:
    """A coherent strategy thesis obtained by gluing local rule sections."""

    timestamp: datetime
    symbol: str
    rules: tuple[RuleName, ...]
    charts: tuple[str, ...]
    sources: tuple[str, ...]
    venues: tuple[str, ...]
    support_count: int
    local_section_count: int
    regime: str
    style: str
    alpha_score: Decimal
    conviction: Decimal
    side: str
    target_fraction: Decimal
    risk_bounds: RiskBounds
    gluing_score: Decimal
    thesis: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        rules: tuple[RuleName, ...],
        charts: tuple[str, ...],
        sources: tuple[str, ...],
        venues: tuple[str, ...],
        support_count: int,
        local_section_count: int,
        regime: str,
        style: str,
        alpha_score: Decimal,
        conviction: Decimal,
        side: str,
        target_fraction: Decimal,
        risk_bounds: RiskBounds,
        gluing_score: Decimal,
        thesis: str,
    ) -> None:
        """Initialize and validate one glued strategy section."""
        object.__setattr__(self, "timestamp", timestamp)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "rules", rules)
        object.__setattr__(self, "charts", charts)
        object.__setattr__(self, "sources", sources)
        object.__setattr__(self, "venues", venues)
        object.__setattr__(self, "support_count", support_count)
        object.__setattr__(self, "local_section_count", local_section_count)
        object.__setattr__(self, "regime", regime)
        object.__setattr__(self, "style", style)
        object.__setattr__(self, "alpha_score", alpha_score)
        object.__setattr__(self, "conviction", conviction)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "target_fraction", target_fraction)
        object.__setattr__(self, "risk_bounds", risk_bounds)
        object.__setattr__(self, "gluing_score", gluing_score)
        object.__setattr__(self, "thesis", thesis)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate global strategy invariants."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise StrategyNormalizationError(
                "Global strategy timestamps must be timezone-aware."
            )
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise StrategyNormalizationError(
                "Global strategy timestamps must be expressed in UTC."
            )
        if self.symbol != _normalize_symbol(self.symbol):
            raise StrategyNormalizationError("Global strategy symbols must be canonicalized.")
        if not self.rules:
            raise StrategyNormalizationError("Global strategies must retain at least one rule.")
        if not self.charts:
            raise StrategyNormalizationError("Global strategies must retain signal charts.")
        if self.support_count < 1 or self.local_section_count < 1:
            raise StrategyNormalizationError("Global strategies must retain positive support.")
        if not self.regime.strip() or not self.style.strip():
            raise StrategyNormalizationError("Global strategies must carry regime and style.")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.target_fraction, "target_fraction")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.target_fraction > self.risk_bounds.max_position_fraction:
            raise StrategyNormalizationError(
                "Global target fraction cannot exceed the glued risk bound."
            )
        if self.side not in {"long", "short", "flat"}:
            raise StrategyNormalizationError(f"Unsupported strategy side {self.side!r}.")
        if not self.thesis.strip():
            raise StrategyNormalizationError("Global strategies must carry a non-empty thesis.")


@dataclass(frozen=True)
class PositionIntent:
    """A typed position intent emitted by the strategy kernel."""

    timestamp: datetime
    symbol: str
    side: str
    style: str
    target_fraction: Decimal
    alpha_score: Decimal
    conviction: Decimal
    risk_bounds: RiskBounds
    approval_status: IntentStatus
    thesis: str
    rationale: str

    def __init__(
        self,
        timestamp: datetime,
        symbol: str,
        side: str,
        style: str,
        target_fraction: Decimal,
        alpha_score: Decimal,
        conviction: Decimal,
        risk_bounds: RiskBounds,
        approval_status: IntentStatus,
        thesis: str,
        rationale: str,
    ) -> None:
        """Initialize and validate one position intent."""
        object.__setattr__(self, "timestamp", timestamp)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "style", style)
        object.__setattr__(self, "target_fraction", target_fraction)
        object.__setattr__(self, "alpha_score", alpha_score)
        object.__setattr__(self, "conviction", conviction)
        object.__setattr__(self, "risk_bounds", risk_bounds)
        object.__setattr__(self, "approval_status", approval_status)
        object.__setattr__(self, "thesis", thesis)
        object.__setattr__(self, "rationale", rationale)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate that the intent is well-formed and risk-gated."""
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise StrategyNormalizationError("Intent timestamps must be timezone-aware.")
        if self.timestamp.astimezone(timezone.utc) != self.timestamp:
            raise StrategyNormalizationError("Intent timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise StrategyNormalizationError("Intent symbols must be canonicalized.")
        if self.side not in {"long", "short", "flat"}:
            raise StrategyNormalizationError(f"Unsupported intent side {self.side!r}.")
        if not self.style.strip():
            raise StrategyNormalizationError("Position intents must carry a style.")
        _validate_probability(self.target_fraction, "target_fraction")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        if self.target_fraction > self.risk_bounds.max_position_fraction:
            raise StrategyNormalizationError(
                "Intent target fraction cannot exceed the approved risk envelope."
            )
        if self.approval_status not in {"blocked", "pending_risk"}:
            raise StrategyNormalizationError(
                f"Unsupported intent approval status {self.approval_status!r}."
            )
        if not self.thesis.strip() or not self.rationale.strip():
            raise StrategyNormalizationError("Position intents must explain their thesis and rationale.")

    def intent_key(self) -> StrategyKey:
        """Return the overlap key carried by the intent."""
        return (self.timestamp, self.symbol)


_DEFAULT_RULEBOOK: tuple[StrategyRule, ...] = (
    StrategyRule(
        name="transport",
        preferred_regimes=("trend_persistence", "balanced_probe"),
        sigma_weight=Decimal("0.3500000"),
        pi_weight=Decimal("0.3000000"),
        size_cap=Decimal("0.2800000"),
        thesis="follow persistent transport when the glued signal section stays exact",
    ),
    StrategyRule(
        name="harmonic_reversion",
        preferred_regimes=("harmonic_reversion", "balanced_probe"),
        sigma_weight=Decimal("0.3000000"),
        pi_weight=Decimal("0.2500000"),
        size_cap=Decimal("0.2200000"),
        thesis="trade the exact correction when displaced quotes collapse back to the median",
    ),
    StrategyRule(
        name="novelty_breakout",
        preferred_regimes=("trend_persistence", "crowded_rotation", "balanced_probe"),
        sigma_weight=Decimal("0.4000000"),
        pi_weight=Decimal("0.3500000"),
        size_cap=Decimal("0.2500000"),
        thesis="promote only the novel idea that survives all overlap witnesses",
    ),
)


def default_rulebook() -> tuple[StrategyRule, ...]:
    """Return the default typed strategy rulebook for the pi/sigma kernel."""
    return _DEFAULT_RULEBOOK


def build_local_strategy_section(
    signal: GlobalSignalSection,
    *,
    rule: StrategyRule | RuleName = "transport",
    rules: Sequence[StrategyRule] | None = None,
) -> LocalStrategySection:
    """Lift one glued signal section into a local typed strategy rule."""
    resolved_rule = _resolve_rule(rule, rules)
    sigma_core = _sigma_core(resolved_rule.name, signal.coordinates)
    sigma_score = _squash_signal(
        (signal.alpha_score * (ONE - resolved_rule.sigma_weight))
        + (sigma_core * resolved_rule.sigma_weight)
    )
    pi_score = _clamp_probability(
        signal.gluing_score * Decimal("0.4500000")
        + signal.conviction * Decimal("0.2500000")
        + _regime_match_score(resolved_rule, signal.regime) * Decimal("0.2000000")
        + _support_factor(signal.support_count) * Decimal("0.1000000")
    )
    alpha_score = _squash_signal(
        (signal.alpha_score * (ONE - resolved_rule.pi_weight))
        + (sigma_score * resolved_rule.pi_weight)
    )
    conviction = _local_conviction(signal, pi_score, alpha_score)
    target_fraction = _local_target_fraction(signal, resolved_rule, alpha_score, conviction)
    risk_bounds = _build_risk_bounds(
        signal,
        resolved_rule,
        alpha_score,
        pi_score,
        target_fraction,
    )
    return LocalStrategySection(
        timestamp=signal.timestamp,
        symbol=signal.symbol,
        rule=resolved_rule.name,
        regime=signal.regime,
        charts=tuple(sorted(signal.charts)),
        sources=tuple(sorted(signal.sources)),
        venues=tuple(sorted(signal.venues)),
        support_count=signal.support_count,
        signal_gluing_score=_clamp_probability(signal.gluing_score),
        pi_score=pi_score,
        sigma_score=sigma_score,
        alpha_score=alpha_score,
        conviction=conviction,
        target_fraction=target_fraction,
        risk_bounds=risk_bounds,
        thesis=_local_thesis(resolved_rule.name, signal.regime, alpha_score),
    )


def build_strategy_cover(
    signals: Iterable[GlobalSignalSection],
    *,
    rules: Sequence[StrategyRule] | None = None,
) -> list[LocalStrategySection]:
    """Build the local strategy cover for a batch of coherent signal sections."""
    rulebook = rules or default_rulebook()
    sections: list[LocalStrategySection] = []
    for index, signal in enumerate(signals):
        try:
            for rule in rulebook:
                sections.append(build_local_strategy_section(signal, rule=rule, rules=rulebook))
        except StrategyKernelError as exc:
            raise StrategyNormalizationError(
                f"Failed to build strategy cover at signal index {index}: {exc}"
            ) from exc
    return sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.rule))


def restrict_strategy_sections(
    sections: Iterable[LocalStrategySection],
    *,
    symbols: Collection[str] | None = None,
    start: datetime | None = None,
    end: datetime | None = None,
    rules: Collection[RuleName] | None = None,
) -> list[LocalStrategySection]:
    """Restrict local strategy sections to a sub-cover."""
    normalized_symbols = (
        {_normalize_symbol(symbol) for symbol in symbols} if symbols is not None else None
    )
    start_bound = _normalize_timestamp(start, "start") if start is not None else None
    end_bound = _normalize_timestamp(end, "end") if end is not None else None
    normalized_rules = set(rules) if rules is not None else None

    if normalized_rules is not None:
        unknown = normalized_rules.difference(RULES)
        if unknown:
            raise StrategyRestrictionError(
                f"Unknown strategy rules in restriction: {sorted(unknown)!r}."
            )
    if start_bound is not None and end_bound is not None and end_bound < start_bound:
        raise StrategyRestrictionError("Restriction end time cannot precede start time.")

    restricted: list[LocalStrategySection] = []
    for section in sections:
        if normalized_symbols is not None and section.symbol not in normalized_symbols:
            continue
        if start_bound is not None and section.timestamp < start_bound:
            continue
        if end_bound is not None and section.timestamp > end_bound:
            continue
        if normalized_rules is not None and section.rule not in normalized_rules:
            continue
        restricted.append(section)

    return sorted(restricted, key=lambda item: (item.timestamp, item.symbol, item.rule))


def group_strategy_overlaps(
    sections: Iterable[LocalStrategySection],
) -> dict[StrategyKey, list[LocalStrategySection]]:
    """Group local strategy sections by the overlap key of the trading cover."""
    grouped: dict[StrategyKey, list[LocalStrategySection]] = {}
    for section in sections:
        grouped.setdefault(section.strategy_key(), []).append(section)

    for members in grouped.values():
        members.sort(key=lambda item: item.rule)
    return dict(sorted(grouped.items(), key=lambda item: item[0]))


def _build_certificate(
    key: StrategyKey,
    members: Sequence[LocalStrategySection],
    *,
    alpha_tolerance: Decimal,
    target_tolerance: Decimal,
    risk_tolerance: Decimal,
    h1_tolerance: Decimal,
) -> StrategyCocycleCertificate:
    """Build the strategy cocycle certificate for one overlap class."""
    rules = _require_unique_rules(members, key)
    alpha_gap = _max_gap([member.alpha_score for member in members])
    target_gap = _max_gap(
        [member.target_fraction for member in members],
        FRACTION_QUANTUM,
    )
    risk_gap = _risk_gap(members)
    corrections = [member.alpha_score - member.sigma_score for member in members]
    triple_residual = _triple_overlap_residual(corrections)
    h1_obstruction = _quantize(
        alpha_gap + target_gap + risk_gap + triple_residual,
        FRACTION_QUANTUM,
    )
    passes = (
        alpha_gap <= alpha_tolerance
        and target_gap <= target_tolerance
        and risk_gap <= risk_tolerance
        and h1_obstruction <= h1_tolerance
    )

    if passes:
        reason = "local strategy rules agree and the H^1 obstruction vanishes"
    else:
        reason = (
            "strategy rules disagree on overlap data: "
            f"alpha_gap={alpha_gap}, "
            f"target_gap={target_gap}, "
            f"risk_gap={risk_gap}, "
            f"triple_residual={triple_residual}, "
            f"h1_obstruction={h1_obstruction}"
        )

    return StrategyCocycleCertificate(
        key=key,
        rules=rules,
        alpha_gap=alpha_gap,
        target_gap=target_gap,
        risk_gap=risk_gap,
        triple_overlap_residual=triple_residual,
        h1_obstruction=h1_obstruction,
        passes=passes,
        reason=reason,
    )


def check_strategy_cocycle(
    sections: Sequence[LocalStrategySection],
    *,
    alpha_tolerance: Decimal | str = Decimal("0.1800000"),
    target_tolerance: Decimal | str = Decimal("0.1200000"),
    risk_tolerance: Decimal | str = Decimal("0.1000000"),
    h1_tolerance: Decimal | str | None = None,
) -> tuple[StrategyCocycleCertificate, ...]:
    """Check whether local strategy rules glue on each overlap."""
    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_target_tolerance = _resolve_tolerance(target_tolerance, "target_tolerance")
    resolved_risk_tolerance = _resolve_tolerance(risk_tolerance, "risk_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize(
            resolved_alpha_tolerance
            + resolved_target_tolerance
            + (resolved_risk_tolerance * HALF),
            FRACTION_QUANTUM,
        )
    )

    grouped = group_strategy_overlaps(sections)
    certificates = [
        _build_certificate(
            key,
            members,
            alpha_tolerance=resolved_alpha_tolerance,
            target_tolerance=resolved_target_tolerance,
            risk_tolerance=resolved_risk_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
        for key, members in grouped.items()
    ]
    return tuple(certificates)


def glue_strategy_sections(
    sections: Sequence[LocalStrategySection],
    *,
    alpha_tolerance: Decimal | str = Decimal("0.1800000"),
    target_tolerance: Decimal | str = Decimal("0.1200000"),
    risk_tolerance: Decimal | str = Decimal("0.1000000"),
    h1_tolerance: Decimal | str | None = None,
) -> list[GlobalStrategySection]:
    """Glue local strategy rules into coherent global strategy sections."""
    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_target_tolerance = _resolve_tolerance(target_tolerance, "target_tolerance")
    resolved_risk_tolerance = _resolve_tolerance(risk_tolerance, "risk_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize(
            resolved_alpha_tolerance
            + resolved_target_tolerance
            + (resolved_risk_tolerance * HALF),
            FRACTION_QUANTUM,
        )
    )

    grouped = group_strategy_overlaps(sections)
    certificates = {
        certificate.key: certificate
        for certificate in check_strategy_cocycle(
            sections,
            alpha_tolerance=resolved_alpha_tolerance,
            target_tolerance=resolved_target_tolerance,
            risk_tolerance=resolved_risk_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    }

    glued: list[GlobalStrategySection] = []
    for key, members in grouped.items():
        certificate = certificates[key]
        certificate.assert_passes()

        alpha_score = _median_decimal([member.alpha_score for member in members])
        target_fraction = _median_decimal(
            [member.target_fraction for member in members],
            FRACTION_QUANTUM,
        )
        gluing_score = _gluing_score(certificate.h1_obstruction, resolved_h1_tolerance)
        conviction = _clamp_probability(
            _median_decimal(
                [member.conviction for member in members],
                FRACTION_QUANTUM,
            )
            * gluing_score
        )
        regime = _mode_label([member.regime for member in members])
        style = _global_style(regime, certificate.rules, target_fraction)
        side = _infer_side(alpha_score, conviction, target_fraction)
        max_position_fraction = max(
            target_fraction,
            _median_decimal(
                [member.risk_bounds.max_position_fraction for member in members],
                FRACTION_QUANTUM,
            ),
        )
        risk_bounds = RiskBounds(
            max_position_fraction=_quantize_fraction(max_position_fraction),
            stop_loss_fraction=max(
                member.risk_bounds.stop_loss_fraction for member in members
            ),
            take_profit_fraction=_median_decimal(
                [member.risk_bounds.take_profit_fraction for member in members],
                FRACTION_QUANTUM,
            ),
            max_holding_periods=min(
                member.risk_bounds.max_holding_periods for member in members
            ),
            conviction_floor=max(
                member.risk_bounds.conviction_floor for member in members
            ),
            h1_buffer=max(member.risk_bounds.h1_buffer for member in members),
        )
        glued.append(
            GlobalStrategySection(
                timestamp=key[0],
                symbol=key[1],
                rules=certificate.rules,
                charts=tuple(sorted({chart for member in members for chart in member.charts})),
                sources=tuple(sorted({source for member in members for source in member.sources})),
                venues=tuple(sorted({venue for member in members for venue in member.venues})),
                support_count=max(member.support_count for member in members),
                local_section_count=len(members),
                regime=regime,
                style=style,
                alpha_score=alpha_score,
                conviction=conviction,
                side=side,
                target_fraction=target_fraction,
                risk_bounds=risk_bounds,
                gluing_score=gluing_score,
                thesis=_global_thesis(style, side),
            )
        )

    return sorted(glued, key=lambda item: (item.timestamp, item.symbol))


def derive_position_intents(
    sections: Iterable[GlobalStrategySection],
    *,
    min_conviction: Decimal | str = Decimal("0.3000000"),
    min_target_fraction: Decimal | str = Decimal("0.0400000"),
) -> list[PositionIntent]:
    """Turn coherent global strategy sections into typed position intents."""
    conviction_floor = _resolve_tolerance(min_conviction, "min_conviction")
    target_floor = _resolve_tolerance(min_target_fraction, "min_target_fraction")

    intents: list[PositionIntent] = []
    for index, section in enumerate(sections):
        try:
            status: IntentStatus
            if (
                section.side != "flat"
                and section.conviction >= conviction_floor
                and section.target_fraction >= target_floor
                and section.conviction >= section.risk_bounds.conviction_floor
            ):
                status = "pending_risk"
            else:
                status = "blocked"
            intents.append(
                PositionIntent(
                    timestamp=section.timestamp,
                    symbol=section.symbol,
                    side=section.side,
                    style=section.style,
                    target_fraction=section.target_fraction,
                    alpha_score=section.alpha_score,
                    conviction=section.conviction,
                    risk_bounds=section.risk_bounds,
                    approval_status=status,
                    thesis=section.thesis,
                    rationale=_intent_reason(status, section),
                )
            )
        except StrategyKernelError as exc:
            raise StrategyNormalizationError(
                f"Failed to derive position intent at strategy index {index}: {exc}"
            ) from exc
    return sorted(intents, key=lambda item: (item.timestamp, item.symbol))


def pending_risk_intents(intents: Iterable[PositionIntent]) -> list[PositionIntent]:
    """Return only those intents that may descend to the risk engine."""
    return [intent for intent in intents if intent.approval_status == "pending_risk"]


@dataclass(frozen=True)
class StrategyRiskPolicy:
    """Explicit risk-critical policy carried by the strategy kernel bundle."""

    max_position_fraction: Decimal = Decimal("0.2800000")
    max_leverage: Decimal = Decimal("2.0000000")
    max_drawdown_fraction: Decimal = Decimal("0.0800000")
    kill_switch_drawdown_fraction: Decimal = Decimal("0.1000000")
    reject_on_stale_data_seconds: int = 30
    order_rejection_conditions: tuple[str, ...] = DEFAULT_ORDER_REJECTION_CONDITIONS
    proof_obligation: ProofMode = "smt_required"
    paper_trading_required: bool = True

    def __init__(
        self,
        max_position_fraction: Decimal = Decimal("0.2800000"),
        max_leverage: Decimal = Decimal("2.0000000"),
        max_drawdown_fraction: Decimal = Decimal("0.0800000"),
        kill_switch_drawdown_fraction: Decimal = Decimal("0.1000000"),
        reject_on_stale_data_seconds: int = 30,
        order_rejection_conditions: tuple[str, ...] = DEFAULT_ORDER_REJECTION_CONDITIONS,
        proof_obligation: ProofMode = "smt_required",
        paper_trading_required: bool = True,
    ) -> None:
        """Initialize and validate the explicit strategy risk policy."""
        object.__setattr__(self, "max_position_fraction", max_position_fraction)
        object.__setattr__(self, "max_leverage", max_leverage)
        object.__setattr__(self, "max_drawdown_fraction", max_drawdown_fraction)
        object.__setattr__(
            self,
            "kill_switch_drawdown_fraction",
            kill_switch_drawdown_fraction,
        )
        object.__setattr__(
            self,
            "reject_on_stale_data_seconds",
            reject_on_stale_data_seconds,
        )
        object.__setattr__(
            self,
            "order_rejection_conditions",
            order_rejection_conditions,
        )
        object.__setattr__(self, "proof_obligation", proof_obligation)
        object.__setattr__(self, "paper_trading_required", paper_trading_required)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate the explicit strategy risk policy."""
        _validate_probability(self.max_position_fraction, "max_position_fraction")
        if self.max_position_fraction == ZERO:
            raise StrategyNormalizationError(
                "Field 'max_position_fraction' must be strictly positive."
            )
        _validate_positive_decimal(self.max_leverage, "max_leverage")
        _validate_probability(self.max_drawdown_fraction, "max_drawdown_fraction")
        _validate_probability(
            self.kill_switch_drawdown_fraction, "kill_switch_drawdown_fraction"
        )
        if self.max_drawdown_fraction == ZERO or self.max_drawdown_fraction >= ONE:
            raise StrategyNormalizationError(
                "Field 'max_drawdown_fraction' must lie in (0, 1)."
            )
        if (
            self.kill_switch_drawdown_fraction <= self.max_drawdown_fraction
            or self.kill_switch_drawdown_fraction >= ONE
        ):
            raise StrategyNormalizationError(
                "Field 'kill_switch_drawdown_fraction' must exceed "
                "max_drawdown_fraction and remain below 1."
            )
        if self.reject_on_stale_data_seconds < 0:
            raise StrategyNormalizationError(
                "Field 'reject_on_stale_data_seconds' must be non-negative."
            )
        if not self.order_rejection_conditions:
            raise StrategyNormalizationError(
                "Strategy risk policy requires explicit order rejection conditions."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise StrategyNormalizationError(
                "Strategy risk policy requires an SMT-backed or machine-checked proof mode."
            )

    def reproducibility_signature(self) -> str:
        """Return a deterministic digest for audit logging."""
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


@dataclass(frozen=True)
class StrategyResearchIdea:
    """A testable strategy thesis emitted by the pi/sigma kernel."""

    symbol: str
    as_of: datetime
    side: StrategyIdeaSide
    rule: RuleName
    style: str
    thesis: str
    validation_plan: str
    test_horizon_periods: int
    alpha_score: Decimal
    conviction: Decimal
    target_fraction: Decimal
    expected_edge_bps: Decimal
    provenance: str
    data_signature: str

    def __init__(
        self,
        symbol: str,
        as_of: datetime,
        side: StrategyIdeaSide,
        rule: RuleName,
        style: str,
        thesis: str,
        validation_plan: str,
        test_horizon_periods: int,
        alpha_score: Decimal,
        conviction: Decimal,
        target_fraction: Decimal,
        expected_edge_bps: Decimal,
        provenance: str,
        data_signature: str,
    ) -> None:
        """Initialize and validate one auditable strategy research idea."""
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "as_of", as_of)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "rule", rule)
        object.__setattr__(self, "style", style)
        object.__setattr__(self, "thesis", thesis)
        object.__setattr__(self, "validation_plan", validation_plan)
        object.__setattr__(self, "test_horizon_periods", test_horizon_periods)
        object.__setattr__(self, "alpha_score", alpha_score)
        object.__setattr__(self, "conviction", conviction)
        object.__setattr__(self, "target_fraction", target_fraction)
        object.__setattr__(self, "expected_edge_bps", expected_edge_bps)
        object.__setattr__(self, "provenance", provenance)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate that the research idea is concrete and auditable."""
        if self.symbol != _normalize_symbol(self.symbol):
            raise StrategyIdeaGenerationError("Strategy idea symbols must be canonical.")
        if self.as_of.tzinfo is None or self.as_of.utcoffset() is None:
            raise StrategyIdeaGenerationError(
                "Strategy idea timestamps must be timezone-aware."
            )
        if self.as_of.astimezone(timezone.utc) != self.as_of:
            raise StrategyIdeaGenerationError(
                "Strategy idea timestamps must be expressed in UTC."
            )
        if self.side not in {"long", "short"}:
            raise StrategyIdeaGenerationError(
                "Strategy idea side must be 'long' or 'short'."
            )
        if self.rule not in RULES:
            raise StrategyIdeaGenerationError("Strategy idea rule must be known.")
        if not self.style.strip():
            raise StrategyIdeaGenerationError("Strategy ideas must carry a style.")
        if (
            not self.thesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
        ):
            raise StrategyIdeaGenerationError(
                "Strategy ideas require non-empty narrative fields."
            )
        if self.test_horizon_periods < 1:
            raise StrategyIdeaGenerationError(
                "Strategy idea horizons must be positive."
            )
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.target_fraction, "target_fraction")
        if not self.expected_edge_bps.is_finite() or self.expected_edge_bps <= ZERO:
            raise StrategyIdeaGenerationError(
                "Strategy ideas require a positive expected edge."
            )
        if not self.data_signature:
            raise StrategyIdeaGenerationError(
                "Strategy ideas require a reproducibility signature."
            )


@dataclass(frozen=True)
class StrategyKernelBundle:
    """High-level bundle produced by the strategy-kernel site."""

    schema_version: str
    signal_sections: tuple[GlobalSignalSection, ...]
    local_sections: tuple[LocalStrategySection, ...]
    global_sections: tuple[GlobalStrategySection, ...]
    position_intents: tuple[PositionIntent, ...]
    research_ideas: tuple[StrategyResearchIdea, ...]
    risk_policy: StrategyRiskPolicy
    rulebook: tuple[StrategyRule, ...]
    alpha_tolerance: Decimal
    target_tolerance: Decimal
    risk_tolerance: Decimal
    h1_tolerance: Decimal
    min_conviction: Decimal
    min_target_fraction: Decimal
    upstream_data_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __init__(
        self,
        schema_version: str,
        signal_sections: tuple[GlobalSignalSection, ...],
        local_sections: tuple[LocalStrategySection, ...],
        global_sections: tuple[GlobalStrategySection, ...],
        position_intents: tuple[PositionIntent, ...],
        research_ideas: tuple[StrategyResearchIdea, ...],
        risk_policy: StrategyRiskPolicy,
        rulebook: tuple[StrategyRule, ...],
        alpha_tolerance: Decimal,
        target_tolerance: Decimal,
        risk_tolerance: Decimal,
        h1_tolerance: Decimal,
        min_conviction: Decimal,
        min_target_fraction: Decimal,
        upstream_data_signature: str,
        data_signature: str,
        audit_metadata: tuple[tuple[str, str], ...],
    ) -> None:
        """Initialize and validate one strategy-kernel bundle."""
        object.__setattr__(self, "schema_version", schema_version)
        object.__setattr__(self, "signal_sections", signal_sections)
        object.__setattr__(self, "local_sections", local_sections)
        object.__setattr__(self, "global_sections", global_sections)
        object.__setattr__(self, "position_intents", position_intents)
        object.__setattr__(self, "research_ideas", research_ideas)
        object.__setattr__(self, "risk_policy", risk_policy)
        object.__setattr__(self, "rulebook", rulebook)
        object.__setattr__(self, "alpha_tolerance", alpha_tolerance)
        object.__setattr__(self, "target_tolerance", target_tolerance)
        object.__setattr__(self, "risk_tolerance", risk_tolerance)
        object.__setattr__(self, "h1_tolerance", h1_tolerance)
        object.__setattr__(self, "min_conviction", min_conviction)
        object.__setattr__(self, "min_target_fraction", min_target_fraction)
        object.__setattr__(self, "upstream_data_signature", upstream_data_signature)
        object.__setattr__(self, "data_signature", data_signature)
        object.__setattr__(self, "audit_metadata", audit_metadata)
        self.__post_init__()

    def __post_init__(self) -> None:
        """Validate bundle-level non-emptiness and reproducibility."""
        if self.schema_version != strategy_kernel_schema_version():
            raise StrategyNormalizationError(
                "Strategy kernel bundle schema version mismatch."
            )
        if not self.signal_sections:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one signal section."
            )
        if not self.local_sections:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one local strategy section."
            )
        if not self.global_sections:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one global strategy section."
            )
        if not self.position_intents:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one position intent."
            )
        if not self.research_ideas:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one testable strategy idea."
            )
        if not self.rulebook:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require at least one strategy rule."
            )
        if not self.upstream_data_signature or not self.data_signature:
            raise StrategyIdeaGenerationError(
                "Strategy kernel bundles require deterministic reproducibility signatures."
            )

    @property
    def symbols(self) -> tuple[str, ...]:
        """Return the canonical symbols represented in the bundle."""
        return tuple(sorted({section.symbol for section in self.global_sections}))

    @property
    def local_strategy_sections(self) -> tuple[LocalStrategySection, ...]:
        """Return the local rule sections for downstream compatibility."""
        return self.local_sections

    @property
    def glued_sections(self) -> tuple[GlobalStrategySection, ...]:
        """Return the coherent global sections for downstream compatibility."""
        return self.global_sections

    @property
    def ideas(self) -> tuple[StrategyResearchIdea, ...]:
        """Return the testable strategy ideas discovered by the bundle."""
        return self.research_ideas

    def summary(self) -> str:
        """Return a deterministic one-line summary of the bundle."""
        return strategy_kernel_summary(self)


@dataclass(frozen=True)
class StrategyKernelValidationReport:
    """Deterministic validation report for a built strategy-kernel bundle."""

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    normalization_signatures_preserved: bool
    cocycle_checks_passed: bool
    coherent_global_sections: bool
    intents_align_with_risk_bounds: bool
    pending_risk_intent_present: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    signature_matches: bool
    signal_sections_checked: int
    local_sections_checked: int
    global_sections_checked: int
    position_intents_checked: int
    overlap_certificates: tuple[StrategyCocycleCertificate, ...]
    messages: tuple[str, ...]

    def __init__(
        self,
        passes: bool,
        timestamp_symbol_invariants_preserved: bool,
        normalization_signatures_preserved: bool,
        cocycle_checks_passed: bool,
        coherent_global_sections: bool,
        intents_align_with_risk_bounds: bool,
        pending_risk_intent_present: bool,
        novel_idea_present: bool,
        risk_invariants_explicit: bool,
        signature_matches: bool,
        signal_sections_checked: int,
        local_sections_checked: int,
        global_sections_checked: int,
        position_intents_checked: int,
        overlap_certificates: tuple[StrategyCocycleCertificate, ...],
        messages: tuple[str, ...],
    ) -> None:
        """Initialize one deterministic strategy-kernel validation report."""
        object.__setattr__(self, "passes", passes)
        object.__setattr__(
            self,
            "timestamp_symbol_invariants_preserved",
            timestamp_symbol_invariants_preserved,
        )
        object.__setattr__(
            self,
            "normalization_signatures_preserved",
            normalization_signatures_preserved,
        )
        object.__setattr__(self, "cocycle_checks_passed", cocycle_checks_passed)
        object.__setattr__(self, "coherent_global_sections", coherent_global_sections)
        object.__setattr__(
            self,
            "intents_align_with_risk_bounds",
            intents_align_with_risk_bounds,
        )
        object.__setattr__(
            self,
            "pending_risk_intent_present",
            pending_risk_intent_present,
        )
        object.__setattr__(self, "novel_idea_present", novel_idea_present)
        object.__setattr__(self, "risk_invariants_explicit", risk_invariants_explicit)
        object.__setattr__(self, "signature_matches", signature_matches)
        object.__setattr__(self, "signal_sections_checked", signal_sections_checked)
        object.__setattr__(self, "local_sections_checked", local_sections_checked)
        object.__setattr__(self, "global_sections_checked", global_sections_checked)
        object.__setattr__(
            self,
            "position_intents_checked",
            position_intents_checked,
        )
        object.__setattr__(self, "overlap_certificates", overlap_certificates)
        object.__setattr__(self, "messages", messages)

    def summary(self) -> str:
        """Return a concise textual summary of the validation result."""
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} signal_sections={self.signal_sections_checked} "
            f"local_sections={self.local_sections_checked} "
            f"global_sections={self.global_sections_checked} "
            f"position_intents={self.position_intents_checked} issues={issues}"
        )


def default_strategy_risk_policy() -> StrategyRiskPolicy:
    """Return the default explicit risk policy used by the strategy kernel."""
    return StrategyRiskPolicy()


def _strategy_rule_signature(rule: StrategyRule) -> str:
    """Return a deterministic signature for one strategy rule."""
    return _stable_digest(
        [
            rule.name,
            *rule.preferred_regimes,
            str(rule.sigma_weight),
            str(rule.pi_weight),
            str(rule.size_cap),
            rule.thesis,
        ]
    )


def _risk_bounds_signature(bounds: RiskBounds) -> str:
    """Return a deterministic signature for one risk-bound record."""
    return _stable_digest(
        [
            str(bounds.max_position_fraction),
            str(bounds.stop_loss_fraction),
            str(bounds.take_profit_fraction),
            str(bounds.max_holding_periods),
            str(bounds.conviction_floor),
            str(bounds.h1_buffer),
        ]
    )


def _local_section_signature(section: LocalStrategySection) -> str:
    """Return a deterministic signature for one local strategy section."""
    return _stable_digest(
        [
            section.timestamp.isoformat(),
            section.symbol,
            section.rule,
            section.regime,
            *section.charts,
            *section.sources,
            *section.venues,
            str(section.support_count),
            str(section.signal_gluing_score),
            str(section.pi_score),
            str(section.sigma_score),
            str(section.alpha_score),
            str(section.conviction),
            str(section.target_fraction),
            _risk_bounds_signature(section.risk_bounds),
            section.thesis,
        ]
    )


def _global_section_signature(section: GlobalStrategySection) -> str:
    """Return a deterministic signature for one global strategy section."""
    return _stable_digest(
        [
            section.timestamp.isoformat(),
            section.symbol,
            *section.rules,
            *section.charts,
            *section.sources,
            *section.venues,
            str(section.support_count),
            str(section.local_section_count),
            section.regime,
            section.style,
            str(section.alpha_score),
            str(section.conviction),
            section.side,
            str(section.target_fraction),
            _risk_bounds_signature(section.risk_bounds),
            str(section.gluing_score),
            section.thesis,
        ]
    )


def _intent_signature(intent: PositionIntent) -> str:
    """Return a deterministic signature for one position intent."""
    return _stable_digest(
        [
            intent.timestamp.isoformat(),
            intent.symbol,
            intent.side,
            intent.style,
            str(intent.target_fraction),
            str(intent.alpha_score),
            str(intent.conviction),
            _risk_bounds_signature(intent.risk_bounds),
            intent.approval_status,
            intent.thesis,
            intent.rationale,
        ]
    )


def _coerce_order_conditions(value: Any) -> tuple[str, ...]:
    """Normalize explicit order rejection conditions."""
    if value is None:
        return DEFAULT_ORDER_REJECTION_CONDITIONS
    if isinstance(value, tuple) and all(isinstance(item, str) for item in value):
        normalized = tuple(item.strip() for item in value if item.strip())
        return normalized or DEFAULT_ORDER_REJECTION_CONDITIONS
    if isinstance(value, Iterable) and not isinstance(value, (str, bytes)):
        normalized = tuple(str(item).strip() for item in value if str(item).strip())
        return normalized or DEFAULT_ORDER_REJECTION_CONDITIONS
    return DEFAULT_ORDER_REJECTION_CONDITIONS


def _resolve_risk_policy(
    source: Any | None,
    sections: Sequence[GlobalStrategySection] = (),
) -> StrategyRiskPolicy:
    """Resolve an upstream risk specification into the local strategy policy."""
    if isinstance(source, StrategyRiskPolicy):
        base = source
    else:
        base = default_strategy_risk_policy()
        if source is not None:
            base = StrategyRiskPolicy(
                max_position_fraction=_coerce_decimal(
                    getattr(source, "max_position_fraction", base.max_position_fraction),
                    "max_position_fraction",
                ),
                max_leverage=_coerce_decimal(
                    getattr(source, "max_leverage", base.max_leverage),
                    "max_leverage",
                ),
                max_drawdown_fraction=_coerce_decimal(
                    getattr(source, "max_drawdown_fraction", base.max_drawdown_fraction),
                    "max_drawdown_fraction",
                ),
                kill_switch_drawdown_fraction=_coerce_decimal(
                    getattr(
                        source,
                        "kill_switch_drawdown_fraction",
                        base.kill_switch_drawdown_fraction,
                    ),
                    "kill_switch_drawdown_fraction",
                ),
                reject_on_stale_data_seconds=int(
                    getattr(
                        source,
                        "reject_on_stale_data_seconds",
                        base.reject_on_stale_data_seconds,
                    )
                ),
                order_rejection_conditions=_coerce_order_conditions(
                    getattr(
                        source,
                        "order_rejection_conditions",
                        base.order_rejection_conditions,
                    )
                ),
                proof_obligation=getattr(source, "proof_obligation", base.proof_obligation),
                paper_trading_required=bool(
                    getattr(source, "paper_trading_required", base.paper_trading_required)
                ),
            )
    observed_max_position = max(
        (section.risk_bounds.max_position_fraction for section in sections),
        default=ZERO,
    )
    return StrategyRiskPolicy(
        max_position_fraction=max(base.max_position_fraction, observed_max_position),
        max_leverage=base.max_leverage,
        max_drawdown_fraction=base.max_drawdown_fraction,
        kill_switch_drawdown_fraction=base.kill_switch_drawdown_fraction,
        reject_on_stale_data_seconds=base.reject_on_stale_data_seconds,
        order_rejection_conditions=base.order_rejection_conditions,
        proof_obligation=base.proof_obligation,
        paper_trading_required=base.paper_trading_required,
    )


def _sections_input_signature(sections: tuple[GlobalSignalSection, ...]) -> str:
    """Return a deterministic signature for direct signal-section inputs."""
    return _stable_digest(
        [
            _stable_digest(
                [
                    section.timestamp.isoformat(),
                    section.symbol,
                    *section.charts,
                    *section.sources,
                    *section.venues,
                    str(section.support_count),
                    str(section.local_section_count),
                    str(section.coordinates.continuation_bias),
                    str(section.coordinates.mean_reversion_bias),
                    str(section.coordinates.crowding_pressure),
                    str(section.coordinates.topology_memory),
                    str(section.coordinates.novelty_lift),
                    str(section.coordinates.regime_curvature),
                    str(section.alpha_score),
                    str(section.conviction),
                    section.regime,
                    section.side,
                    str(section.gluing_score),
                    section.thesis,
                ]
            )
            for section in sections
        ]
    )


def _resolve_strategy_kernel_input(
    signal_input: StrategyKernelInput,
) -> tuple[
    tuple[GlobalSignalSection, ...],
    tuple[SignalResearchIdea, ...],
    str,
    Any | None,
]:
    """Normalize upstream input into signals, ideas, signature, and risk source."""
    if isinstance(signal_input, SignalGeometryBundle):
        return (
            tuple(signal_input.global_sections),
            tuple(signal_input.research_ideas),
            signal_input.data_signature,
            getattr(signal_input, "risk_invariants", None),
        )
    sections = tuple(sorted(signal_input, key=lambda item: (item.timestamp, item.symbol)))
    return (sections, (), _sections_input_signature(sections), None)


def _strategy_rule_for_section(section: GlobalStrategySection) -> RuleName:
    """Choose the prototype rule that best explains one global strategy section."""
    if section.style == "transport_stack" and "transport" in section.rules:
        return "transport"
    if section.style == "harmonic_stack" and "harmonic_reversion" in section.rules:
        return "harmonic_reversion"
    if section.style == "novelty_probe" and "novelty_breakout" in section.rules:
        return "novelty_breakout"
    if section.side == "long" and "transport" in section.rules:
        return "transport"
    if section.side == "short" and "harmonic_reversion" in section.rules:
        return "harmonic_reversion"
    if "novelty_breakout" in section.rules:
        return "novelty_breakout"
    return section.rules[0]


def _matching_signal_idea(
    section: GlobalStrategySection,
    upstream_ideas: Sequence[SignalResearchIdea],
) -> SignalResearchIdea | None:
    """Return the strongest upstream signal idea aligned with one strategy section."""
    matches = [
        idea
        for idea in upstream_ideas
        if idea.symbol == section.symbol
        and idea.as_of == section.timestamp
        and (idea.side == section.side or section.side == "flat")
    ]
    if not matches:
        return None
    return max(matches, key=lambda idea: (idea.conviction, idea.expected_edge_bps))


def _strategy_validation_plan(
    matched_signal_idea: SignalResearchIdea | None,
) -> str:
    """Return the deterministic validation plan for a strategy idea."""
    inherited = (
        matched_signal_idea.validation_plan
        if matched_signal_idea is not None
        else "derive the thesis from versioned signal sections"
    )
    return (
        f"{inherited}; run walk-forward simulation with point-in-time universes, "
        "ban lookahead bias and data leakage, stress tail scenarios, "
        "log immutable audit metadata, and require paper trading before live use"
    )


def _strategy_expected_edge_bps(
    section: GlobalStrategySection,
    matched_signal_idea: SignalResearchIdea | None,
) -> Decimal:
    """Estimate expected edge in basis points for one strategy idea."""
    inherited_edge = (
        matched_signal_idea.expected_edge_bps if matched_signal_idea is not None else ZERO
    )
    kernel_edge = (
        abs(section.alpha_score) * Decimal("90")
        + section.conviction * Decimal("40")
        + section.target_fraction * Decimal("120")
        + section.gluing_score * Decimal("15")
    )
    return _quantize_edge(max(Decimal("0.5000"), inherited_edge, kernel_edge))


def _discover_strategy_research_ideas(
    sections: Sequence[GlobalStrategySection],
    *,
    upstream_ideas: Sequence[SignalResearchIdea] = (),
) -> tuple[StrategyResearchIdea, ...]:
    """Discover testable strategy ideas from glued strategy sections."""
    candidates = [section for section in sections if section.side in {"long", "short"}]
    if not candidates and sections:
        strongest = max(
            sections,
            key=lambda section: (
                abs(section.alpha_score),
                section.conviction,
                section.target_fraction,
            ),
        )
        if strongest.alpha_score != ZERO:
            side: StrategyIdeaSide = "long" if strongest.alpha_score > ZERO else "short"
            candidates = [strongest]
        else:
            candidates = []
    ideas: list[StrategyResearchIdea] = []
    for section in candidates:
        matched_signal_idea = _matching_signal_idea(section, upstream_ideas)
        rule = _strategy_rule_for_section(section)
        side: StrategyIdeaSide = (
            section.side
            if section.side in {"long", "short"}
            else ("long" if section.alpha_score > ZERO else "short")
        )
        thesis = (
            f"{side} {section.symbol} via {rule} because {section.thesis}"
            if matched_signal_idea is None
            else (
                f"{side} {section.symbol} via {rule}: {matched_signal_idea.thesis}; "
                f"strategy style {section.style} preserves the signal cocycle "
                "under pi/sigma gluing"
            )
        )
        validation_plan = _strategy_validation_plan(matched_signal_idea)
        ideas.append(
            StrategyResearchIdea(
                symbol=section.symbol,
                as_of=section.timestamp,
                side=side,
                rule=rule,
                style=section.style,
                thesis=thesis,
                validation_plan=validation_plan,
                test_horizon_periods=section.risk_bounds.max_holding_periods,
                alpha_score=section.alpha_score,
                conviction=section.conviction,
                target_fraction=section.target_fraction,
                expected_edge_bps=_strategy_expected_edge_bps(
                    section, matched_signal_idea
                ),
                provenance=(
                    "signal_geometry_extension"
                    if matched_signal_idea is not None
                    else "strategy_kernel_extension"
                ),
                data_signature=_stable_digest(
                    [
                        _global_section_signature(section),
                        matched_signal_idea.data_signature
                        if matched_signal_idea is not None
                        else "kernel_only",
                        rule,
                        validation_plan,
                    ]
                ),
            )
        )
    return tuple(
        sorted(ideas, key=lambda item: (item.as_of, item.symbol, item.rule, item.side))
    )


def _strategy_kernel_bundle_signature(bundle: StrategyKernelBundle) -> str:
    """Return a stable audit digest for the full strategy-kernel bundle."""
    parts = [
        bundle.schema_version,
        str(bundle.alpha_tolerance),
        str(bundle.target_tolerance),
        str(bundle.risk_tolerance),
        str(bundle.h1_tolerance),
        str(bundle.min_conviction),
        str(bundle.min_target_fraction),
        bundle.upstream_data_signature,
        bundle.risk_policy.reproducibility_signature(),
    ]
    parts.extend(_strategy_rule_signature(rule) for rule in bundle.rulebook)
    parts.append("signal_sections")
    parts.extend(_sections_input_signature((section,)) for section in bundle.signal_sections)
    parts.append("local_sections")
    parts.extend(_local_section_signature(section) for section in bundle.local_sections)
    parts.append("global_sections")
    parts.extend(_global_section_signature(section) for section in bundle.global_sections)
    parts.append("position_intents")
    parts.extend(_intent_signature(intent) for intent in bundle.position_intents)
    parts.append("research_ideas")
    parts.extend(idea.data_signature for idea in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


def _restriction_signatures_preserved(
    sections: tuple[LocalStrategySection, ...],
) -> bool:
    """Return whether restricting to the full support preserves local signatures."""
    if not sections:
        return True
    restricted = restrict_strategy_sections(
        sections,
        symbols={section.symbol for section in sections},
        start=sections[0].timestamp,
        end=sections[-1].timestamp,
        rules={section.rule for section in sections},
    )
    original = tuple(section.normalization_signature() for section in sections)
    restricted_signatures = tuple(
        section.normalization_signature() for section in restricted
    )
    return original == restricted_signatures


def _global_sections_coherent(
    local_sections: tuple[LocalStrategySection, ...],
    global_sections: tuple[GlobalStrategySection, ...],
) -> bool:
    """Return whether global strategy sections descend from the local overlaps."""
    grouped = group_strategy_overlaps(local_sections)
    if len(grouped) != len(global_sections):
        return False
    for section in global_sections:
        members = grouped.get((section.timestamp, section.symbol))
        if members is None:
            return False
        expected_rules = tuple(sorted(member.rule for member in members))
        if section.rules != expected_rules:
            return False
        if section.local_section_count != len(members):
            return False
        if section.support_count != max(member.support_count for member in members):
            return False
        if section.target_fraction > section.risk_bounds.max_position_fraction:
            return False
    return True


def _intents_align_with_sections(
    sections: tuple[GlobalStrategySection, ...],
    intents: tuple[PositionIntent, ...],
) -> bool:
    """Return whether position intents agree with the glued strategy sections."""
    section_map = {(section.timestamp, section.symbol): section for section in sections}
    for intent in intents:
        section = section_map.get(intent.intent_key())
        if section is None:
            return False
        if intent.side != section.side or intent.style != section.style:
            return False
        if intent.target_fraction != section.target_fraction:
            return False
        if intent.risk_bounds != section.risk_bounds:
            return False
        if intent.target_fraction > intent.risk_bounds.max_position_fraction:
            return False
    return len(section_map) == len(intents)


def _risk_invariants_explicit(bundle: StrategyKernelBundle) -> bool:
    """Return whether explicit strategy risk invariants are present everywhere."""
    policy = bundle.risk_policy
    if (
        not policy.order_rejection_conditions
        or "reject_unverified_risk_core" not in policy.order_rejection_conditions
        or policy.proof_obligation not in {"smt_required", "machine_checked"}
        or not policy.paper_trading_required
    ):
        return False
    return True


def build_strategy_kernel(
    signal_input: StrategyKernelInput,
    *,
    rules: Sequence[StrategyRule] | None = None,
    alpha_tolerance: Decimal | str = Decimal("0.1800000"),
    target_tolerance: Decimal | str = Decimal("0.1200000"),
    risk_tolerance: Decimal | str = Decimal("0.1000000"),
    h1_tolerance: Decimal | str | None = None,
    min_conviction: Decimal | str = Decimal("0.3000000"),
    min_target_fraction: Decimal | str = Decimal("0.0400000"),
) -> StrategyKernelBundle:
    """Build an auditable strategy-kernel bundle from signal geometry."""
    signal_sections, upstream_ideas, upstream_signature, upstream_risk_source = (
        _resolve_strategy_kernel_input(signal_input)
    )
    if not signal_sections:
        raise StrategyIdeaGenerationError(
            "Strategy kernel requires at least one coherent global signal section."
        )
    resolved_rulebook = tuple(rules or default_rulebook())
    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_target_tolerance = _resolve_tolerance(
        target_tolerance, "target_tolerance"
    )
    resolved_risk_tolerance = _resolve_tolerance(risk_tolerance, "risk_tolerance")
    resolved_h1_tolerance = (
        _resolve_tolerance(h1_tolerance, "h1_tolerance")
        if h1_tolerance is not None
        else _quantize_fraction(
            resolved_alpha_tolerance
            + resolved_target_tolerance
            + (resolved_risk_tolerance * HALF)
        )
    )
    resolved_min_conviction = _resolve_tolerance(min_conviction, "min_conviction")
    resolved_min_target_fraction = _resolve_tolerance(
        min_target_fraction, "min_target_fraction"
    )

    local_sections = tuple(build_strategy_cover(signal_sections, rules=resolved_rulebook))
    global_sections = tuple(
        glue_strategy_sections(
            local_sections,
            alpha_tolerance=resolved_alpha_tolerance,
            target_tolerance=resolved_target_tolerance,
            risk_tolerance=resolved_risk_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    )
    position_intents = tuple(
        derive_position_intents(
            global_sections,
            min_conviction=resolved_min_conviction,
            min_target_fraction=resolved_min_target_fraction,
        )
    )
    research_ideas = _discover_strategy_research_ideas(
        global_sections,
        upstream_ideas=upstream_ideas,
    )
    if not research_ideas:
        raise StrategyIdeaGenerationError(
            "Strategy kernel must emit at least one testable idea from data-driven research."
        )
    risk_policy = _resolve_risk_policy(upstream_risk_source, global_sections)
    audit_metadata = tuple(
        sorted(
            (
                ("audit_log", "immutable_required"),
                ("bias_guards", "lookahead_survivorship_data_leakage_blocked"),
                ("execution_mode", "paper_only_until_risk_engine_approval"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("idea_mode", "topology_preserving_prototype_extension"),
                (
                    "kill_switch_policy",
                    "deterministic_reject_on_drawdown_stale_data_or_unverified_risk_core",
                ),
                ("proof_obligation", risk_policy.proof_obligation),
                ("reproducibility", "versioned_data_rulebook_and_signatures"),
                ("schema_version", strategy_kernel_schema_version()),
                ("upstream_signature", upstream_signature[:16]),
            )
        )
    )
    unsigned_bundle = StrategyKernelBundle(
        schema_version=strategy_kernel_schema_version(),
        signal_sections=signal_sections,
        local_sections=local_sections,
        global_sections=global_sections,
        position_intents=position_intents,
        research_ideas=research_ideas,
        risk_policy=risk_policy,
        rulebook=resolved_rulebook,
        alpha_tolerance=resolved_alpha_tolerance,
        target_tolerance=resolved_target_tolerance,
        risk_tolerance=resolved_risk_tolerance,
        h1_tolerance=resolved_h1_tolerance,
        min_conviction=resolved_min_conviction,
        min_target_fraction=resolved_min_target_fraction,
        upstream_data_signature=upstream_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return StrategyKernelBundle(
        schema_version=unsigned_bundle.schema_version,
        signal_sections=unsigned_bundle.signal_sections,
        local_sections=unsigned_bundle.local_sections,
        global_sections=unsigned_bundle.global_sections,
        position_intents=unsigned_bundle.position_intents,
        research_ideas=unsigned_bundle.research_ideas,
        risk_policy=unsigned_bundle.risk_policy,
        rulebook=unsigned_bundle.rulebook,
        alpha_tolerance=unsigned_bundle.alpha_tolerance,
        target_tolerance=unsigned_bundle.target_tolerance,
        risk_tolerance=unsigned_bundle.risk_tolerance,
        h1_tolerance=unsigned_bundle.h1_tolerance,
        min_conviction=unsigned_bundle.min_conviction,
        min_target_fraction=unsigned_bundle.min_target_fraction,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        data_signature=_strategy_kernel_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


def validate_strategy_kernel(
    bundle: StrategyKernelBundle,
) -> StrategyKernelValidationReport:
    """Validate that a strategy-kernel bundle still satisfies its obligations."""
    certificates = check_strategy_cocycle(
        bundle.local_sections,
        alpha_tolerance=bundle.alpha_tolerance,
        target_tolerance=bundle.target_tolerance,
        risk_tolerance=bundle.risk_tolerance,
        h1_tolerance=bundle.h1_tolerance,
    )
    normalization_preserved = _restriction_signatures_preserved(bundle.local_sections)
    cocycle_checks_passed = all(certificate.passes for certificate in certificates)
    coherent_global_sections = _global_sections_coherent(
        bundle.local_sections,
        bundle.global_sections,
    )
    intents_align_with_risk_bounds = _intents_align_with_sections(
        bundle.global_sections,
        bundle.position_intents,
    )
    pending_risk_intent_present = any(
        intent.approval_status == "pending_risk" for intent in bundle.position_intents
    )
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    signature_matches = (
        bundle.data_signature == _strategy_kernel_bundle_signature(bundle)
    )
    timestamp_symbol_invariants_preserved = normalization_preserved

    messages: list[str] = []
    if not normalization_preserved:
        messages.append("restriction signature preservation failed")
    if not cocycle_checks_passed:
        messages.append("one or more strategy cocycle checks failed")
    if not coherent_global_sections:
        messages.append("global strategy sections no longer descend from local overlaps")
    if not intents_align_with_risk_bounds:
        messages.append("position intents and risk bounds disagree on overlaps")
    if not pending_risk_intent_present:
        messages.append("no coherent pending-risk intent is present")
    if not novel_idea_present:
        messages.append("no testable data-driven strategy idea is present")
    if not risk_invariants_explicit:
        messages.append("risk invariants are not explicit enough for proof discharge")
    if not signature_matches:
        messages.append("bundle reproducibility signature mismatch")

    passes = (
        timestamp_symbol_invariants_preserved
        and cocycle_checks_passed
        and coherent_global_sections
        and intents_align_with_risk_bounds
        and pending_risk_intent_present
        and novel_idea_present
        and risk_invariants_explicit
        and signature_matches
    )
    return StrategyKernelValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        normalization_signatures_preserved=normalization_preserved,
        cocycle_checks_passed=cocycle_checks_passed,
        coherent_global_sections=coherent_global_sections,
        intents_align_with_risk_bounds=intents_align_with_risk_bounds,
        pending_risk_intent_present=pending_risk_intent_present,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        signature_matches=signature_matches,
        signal_sections_checked=len(bundle.signal_sections),
        local_sections_checked=len(bundle.local_sections),
        global_sections_checked=len(bundle.global_sections),
        position_intents_checked=len(bundle.position_intents),
        overlap_certificates=certificates,
        messages=tuple(messages),
    )


def strategy_kernel_summary(bundle: StrategyKernelBundle) -> str:
    """Return a deterministic summary string for the strategy-kernel bundle."""
    report = validate_strategy_kernel(bundle)
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.rule}:{idea.expected_edge_bps}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    status = "pass" if report.passes else "fail"
    symbols = ",".join(bundle.symbols)
    pending_count = sum(
        intent.approval_status == "pending_risk" for intent in bundle.position_intents
    )
    return (
        f"strategy_kernel[{bundle.schema_version}] symbols={symbols} "
        f"signal_sections={len(bundle.signal_sections)} "
        f"local_sections={len(bundle.local_sections)} "
        f"global_sections={len(bundle.global_sections)} "
        f"intents={len(bundle.position_intents)} "
        f"pending_risk={pending_count} ideas={len(bundle.research_ideas)} "
        f"validation={status} proof={bundle.risk_policy.proof_obligation} "
        f"paper_only={bundle.risk_policy.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )


__all__ = [
    "GlobalStrategySection",
    "IntentStatus",
    "LocalStrategySection",
    "PositionIntent",
    "RULES",
    "RiskBounds",
    "RuleName",
    "StrategyIdeaGenerationError",
    "StrategyIdeaSide",
    "StrategyKernelBundle",
    "StrategyCocycleCertificate",
    "StrategyGluingError",
    "StrategyKernelInput",
    "StrategyKernelError",
    "StrategyKernelValidationReport",
    "StrategyNormalizationError",
    "StrategyResearchIdea",
    "StrategyRiskPolicy",
    "StrategyRestrictionError",
    "StrategyRule",
    "build_local_strategy_section",
    "build_strategy_kernel",
    "build_strategy_cover",
    "check_strategy_cocycle",
    "default_rulebook",
    "default_strategy_risk_policy",
    "derive_position_intents",
    "glue_strategy_sections",
    "group_strategy_overlaps",
    "pending_risk_intents",
    "restrict_strategy_sections",
    "strategy_kernel_schema_version",
    "strategy_kernel_summary",
    "validate_strategy_kernel",
]
