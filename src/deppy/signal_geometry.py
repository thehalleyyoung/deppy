"""Turn local alpha charts into a gluable global signal section.

This module is the ideation site of the typed trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

`market_data` produces coherent market sections on overlaps keyed by
``(timestamp, symbol)``. The job of this module is to turn those coherent local
sections into an explicit signal atlas with deterministic diagnostics,
restriction maps, gluing certificates, and auditable research ideas.

The module avoids opaque latent representations. Instead it exposes a compact,
interpretable coordinate chart:

* ``persistence`` measures transport-like directional pressure,
* ``reversion`` measures exact corrections toward the overlap median, and
* ``novelty`` measures residual alpha that survives after the other charts glue.

When those local charts agree on their shared overlap, they descend to one
coherent global signal section that downstream modules can refine into position
intents. The bundle also carries explicit risk-core obligations so that the
risk-critical path can be machine-checked before deployment.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Collection, Iterable, Literal, Sequence, TypeAlias

from deppy.market_data import (
    GluedMarketObservation,
    MarketDataBundle,
    RiskInvariantSpecification,
)

FEATURE_QUANTUM = Decimal("0.0000001")
ONE = Decimal("1")
ZERO = Decimal("0")
HALF = Decimal("0.5")
SIGNAL_SIDE_THRESHOLD = Decimal("0.1000000")
IDEA_EDGE_QUANTUM = Decimal("0.0001")
SIGNAL_GEOMETRY_SCHEMA_VERSION = "signal_geometry.v1"

SignalKey: TypeAlias = tuple[datetime, str]
ChartName: TypeAlias = Literal["persistence", "reversion", "novelty"]
SignalIdeaSide: TypeAlias = Literal["long", "short"]
SignalGeometryInput: TypeAlias = MarketDataBundle | Iterable[GluedMarketObservation]

CHARTS: tuple[ChartName, ...] = ("persistence", "reversion", "novelty")


class SignalGeometryError(ValueError):
    """Base error raised by signal geometry."""


class SignalNormalizationError(SignalGeometryError):
    """Raised when a signal section violates normalization invariants."""


class SignalRestrictionError(SignalGeometryError):
    """Raised when a restriction map is ill-formed."""


class SignalGluingError(SignalGeometryError):
    """Raised when local signal sections fail to glue."""


class SignalIdeaGenerationError(SignalGeometryError):
    """Raised when signal geometry cannot produce a testable data-driven idea."""


def _quantize(value: Decimal, quantum: Decimal = FEATURE_QUANTUM) -> Decimal:
    """Return *value* rounded onto the project-wide signal lattice."""
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    """Convert *value* to a finite decimal."""
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise SignalNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc

    if not candidate.is_finite():
        raise SignalNormalizationError(
            f"Field '{field_name}' must be finite, got {value!r}."
        )
    return candidate


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    """Normalize *value* to a timezone-aware UTC timestamp."""
    if not isinstance(value, datetime):
        raise SignalRestrictionError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    """Return the canonical symbol representation used on overlaps."""
    if not isinstance(value, str):
        raise SignalNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise SignalNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise SignalNormalizationError(
            f"Field 'symbol' cannot normalize from {value!r}."
        )
    return candidate


def _median_decimal(values: Sequence[Decimal]) -> Decimal:
    """Return the median of *values* on the signal lattice."""
    if not values:
        raise SignalNormalizationError("Median is undefined for an empty value set.")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return _quantize(ordered[middle])
    return _quantize((ordered[middle - 1] + ordered[middle]) / Decimal("2"))


def _max_gap(values: Sequence[Decimal]) -> Decimal:
    """Return the maximum gap between values on a shared overlap."""
    if not values:
        return ZERO
    return _quantize(max(values) - min(values))


def _triple_overlap_residual(values: Sequence[Decimal]) -> Decimal:
    """Return an H1-style residual for a correction family on triple overlaps."""
    if len(values) < 3:
        return ZERO
    median_value = _median_decimal(values)
    residual = max((abs(value - median_value) for value in values), default=ZERO)
    return _quantize(residual)


def _resolve_tolerance(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a tolerance parameter to a non-negative finite decimal."""
    tolerance = _coerce_decimal(value, field_name)
    if tolerance < ZERO:
        raise SignalRestrictionError(f"Tolerance '{field_name}' must be non-negative.")
    return _quantize(tolerance)


def _resolve_probability_floor(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a probability threshold to the unit interval."""
    floor = _resolve_tolerance(value, field_name)
    if floor > ONE:
        raise SignalRestrictionError(f"Threshold '{field_name}' must lie in [0, 1].")
    return floor


def _resolve_unit_signal_floor(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize an absolute signal threshold to the unit interval."""
    floor = _resolve_tolerance(value, field_name)
    if floor > ONE:
        raise SignalRestrictionError(f"Threshold '{field_name}' must lie in [0, 1].")
    return floor


def _resolve_non_negative_decimal(value: Decimal | str, field_name: str) -> Decimal:
    """Normalize a non-negative numeric threshold."""
    candidate = _coerce_decimal(value, field_name)
    if candidate < ZERO:
        raise SignalRestrictionError(f"Threshold '{field_name}' must be non-negative.")
    return candidate


def _stable_digest(parts: Sequence[str]) -> str:
    """Return a deterministic digest for audit and replay workflows."""
    payload = "\x1f".join((SIGNAL_GEOMETRY_SCHEMA_VERSION, *parts)).encode("utf-8")
    return sha256(payload).hexdigest()


def signal_geometry_schema_version() -> str:
    """Return the schema version used for signal-geometry audit digests."""
    return SIGNAL_GEOMETRY_SCHEMA_VERSION


def _squash_signal(value: Decimal) -> Decimal:
    """Map an arbitrary finite decimal into the interval ``[-1, 1]``."""
    if not value.is_finite():
        raise SignalNormalizationError("Signal values must be finite before squashing.")
    scale = ONE + abs(value)
    return _quantize(value / scale)


def _clamp_probability(value: Decimal) -> Decimal:
    """Clamp *value* to the closed unit interval."""
    if not value.is_finite():
        raise SignalNormalizationError("Probabilistic scores must be finite.")
    if value <= ZERO:
        return ZERO
    if value >= ONE:
        return ONE
    return _quantize(value)


def _gluing_score(obstruction: Decimal, h1_tolerance: Decimal) -> Decimal:
    """Convert an obstruction witness into a unit gluing score."""
    if h1_tolerance == ZERO:
        return ZERO if obstruction > ZERO else ONE
    return _clamp_probability(ONE - min(ONE, obstruction / h1_tolerance))


def _support_factor(support_count: int) -> Decimal:
    """Return a bounded support factor for one glued market section."""
    if support_count < 1:
        raise SignalNormalizationError("Support count must be positive.")
    return _quantize(Decimal(support_count) / Decimal(support_count + 1))


def _stability_factor(observation: GluedMarketObservation) -> Decimal:
    """Estimate local stability from the normalized market topology."""
    topology = observation.topology
    stress = min(
        ONE,
        abs(topology.relative_spread)
        + abs(topology.microprice_offset)
        + (abs(topology.flow_pressure) * HALF),
    )
    return _quantize(ONE - stress)


def _validate_unit_signal(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in ``[-1, 1]``."""
    if not value.is_finite():
        raise SignalNormalizationError(f"Field '{field_name}' must be finite.")
    if abs(value) > ONE:
        raise SignalNormalizationError(f"Field '{field_name}' must lie in [-1, 1].")


def _validate_probability(value: Decimal, field_name: str) -> None:
    """Validate that *value* lies in ``[0, 1]``."""
    if not value.is_finite():
        raise SignalNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise SignalNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


@dataclass(frozen=True)
class SignalCoordinates:
    """Explicit coordinates for the local signal atlas."""

    continuation_bias: Decimal
    mean_reversion_bias: Decimal
    crowding_pressure: Decimal
    topology_memory: Decimal
    novelty_lift: Decimal
    regime_curvature: Decimal

    def __post_init__(self) -> None:
        for field_name, value in (
            ("continuation_bias", self.continuation_bias),
            ("mean_reversion_bias", self.mean_reversion_bias),
            ("crowding_pressure", self.crowding_pressure),
            ("topology_memory", self.topology_memory),
            ("novelty_lift", self.novelty_lift),
            ("regime_curvature", self.regime_curvature),
        ):
            _validate_unit_signal(value, field_name)

    @property
    def alpha_seed(self) -> Decimal:
        """Return the chart-independent alpha seed before local corrections."""
        raw_alpha = (
            self.continuation_bias
            + self.mean_reversion_bias
            + self.topology_memory
            + self.novelty_lift
            - self.crowding_pressure
        )
        return _squash_signal(raw_alpha)


@dataclass(frozen=True)
class LocalSignalSection:
    """A local alpha chart attached to one normalized market overlap."""

    timestamp: datetime
    symbol: str
    chart: ChartName
    sources: tuple[str, ...]
    venues: tuple[str, ...]
    support_count: int
    gluing_score: Decimal
    coordinates: SignalCoordinates
    alpha_score: Decimal
    confidence: Decimal
    thesis: str

    def __post_init__(self) -> None:
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise SignalNormalizationError("Signal timestamps must be timezone-aware.")
        if self.timestamp.utcoffset() != timezone.utc.utcoffset(self.timestamp):
            raise SignalNormalizationError("Signal timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise SignalNormalizationError("Signal symbols must be canonicalized.")
        if self.chart not in CHARTS:
            raise SignalNormalizationError(f"Unknown signal chart {self.chart!r}.")
        if not self.sources:
            raise SignalNormalizationError("Signal sections must retain source support.")
        if not self.venues:
            raise SignalNormalizationError("Signal sections must retain venue support.")
        if self.support_count < 1:
            raise SignalNormalizationError("Signal sections must have positive support.")
        _validate_probability(self.gluing_score, "gluing_score")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.confidence, "confidence")
        if not self.thesis.strip():
            raise SignalNormalizationError("Signal sections must carry a non-empty thesis.")

    def signal_key(self) -> SignalKey:
        """Return the restriction and gluing key for the section."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, ChartName]:
        """Return the invariant signature that must persist under restriction."""
        return (self.timestamp, self.symbol, self.chart)

    def reproducibility_signature(self) -> str:
        """Return a deterministic signature for replaying this local section."""
        return _stable_digest(
            [
                self.timestamp.isoformat(),
                self.symbol,
                self.chart,
                *self.sources,
                *self.venues,
                str(self.support_count),
                str(self.gluing_score),
                str(self.coordinates.continuation_bias),
                str(self.coordinates.mean_reversion_bias),
                str(self.coordinates.crowding_pressure),
                str(self.coordinates.topology_memory),
                str(self.coordinates.novelty_lift),
                str(self.coordinates.regime_curvature),
                str(self.alpha_score),
                str(self.confidence),
                self.thesis,
            ]
        )


@dataclass(frozen=True)
class SignalCocycleCertificate:
    """Diagnostic evidence that local signal charts can be glued."""

    key: SignalKey
    charts: tuple[ChartName, ...]
    alpha_gap: Decimal
    confidence_gap: Decimal
    triple_overlap_residual: Decimal
    h1_obstruction: Decimal
    passes: bool
    reason: str

    def assert_passes(self) -> None:
        """Raise :class:`SignalGluingError` when the certificate fails."""
        if self.passes:
            return
        timestamp, symbol = self.key
        raise SignalGluingError(
            f"Signal overlap {symbol}@{timestamp.isoformat()} failed gluing: {self.reason}"
        )


@dataclass(frozen=True)
class GlobalSignalSection:
    """A coherent strategy-ready signal obtained by gluing local charts."""

    timestamp: datetime
    symbol: str
    charts: tuple[ChartName, ...]
    sources: tuple[str, ...]
    venues: tuple[str, ...]
    support_count: int
    local_section_count: int
    coordinates: SignalCoordinates
    alpha_score: Decimal
    conviction: Decimal
    regime: str
    side: str
    gluing_score: Decimal
    thesis: str

    def __post_init__(self) -> None:
        if self.timestamp.tzinfo is None or self.timestamp.utcoffset() is None:
            raise SignalNormalizationError("Global signal timestamps must be timezone-aware.")
        if self.timestamp.utcoffset() != timezone.utc.utcoffset(self.timestamp):
            raise SignalNormalizationError("Global signal timestamps must be expressed in UTC.")
        if self.symbol != _normalize_symbol(self.symbol):
            raise SignalNormalizationError("Global signal symbols must be canonicalized.")
        if not self.charts:
            raise SignalNormalizationError("Global signals must track at least one chart.")
        if self.support_count < 1 or self.local_section_count < 1:
            raise SignalNormalizationError("Global signals must retain positive support.")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_probability(self.gluing_score, "gluing_score")
        if self.side not in {"long", "short", "flat"}:
            raise SignalNormalizationError(f"Unsupported signal side {self.side!r}.")
        if not self.regime.strip():
            raise SignalNormalizationError("Global signals must name a regime.")
        if not self.thesis.strip():
            raise SignalNormalizationError("Global signals must carry a non-empty thesis.")

    def signal_key(self) -> SignalKey:
        """Return the overlap key shared with the contributing local charts."""
        return (self.timestamp, self.symbol)

    def normalization_signature(self) -> tuple[datetime, str, tuple[ChartName, ...]]:
        """Return the invariant signature preserved across global restrictions."""
        return (self.timestamp, self.symbol, self.charts)

    def reproducibility_signature(self) -> str:
        """Return a deterministic signature for replaying this global section."""
        return _stable_digest(
            [
                self.timestamp.isoformat(),
                self.symbol,
                *self.charts,
                *self.sources,
                *self.venues,
                str(self.support_count),
                str(self.local_section_count),
                str(self.coordinates.continuation_bias),
                str(self.coordinates.mean_reversion_bias),
                str(self.coordinates.crowding_pressure),
                str(self.coordinates.topology_memory),
                str(self.coordinates.novelty_lift),
                str(self.coordinates.regime_curvature),
                str(self.alpha_score),
                str(self.conviction),
                self.regime,
                self.side,
                str(self.gluing_score),
                self.thesis,
            ]
        )


@dataclass(frozen=True)
class SignalResearchIdea:
    """A testable market idea discovered from glued signal geometry."""

    symbol: str
    as_of: datetime
    side: SignalIdeaSide
    regime: str
    thesis: str
    validation_plan: str
    test_horizon_minutes: int
    alpha_score: Decimal
    conviction: Decimal
    novelty_lift: Decimal
    gluing_score: Decimal
    expected_edge_bps: Decimal
    data_signature: str

    def __post_init__(self) -> None:
        if self.symbol != _normalize_symbol(self.symbol):
            raise SignalIdeaGenerationError("Signal idea symbols must be canonical.")
        if self.as_of.tzinfo is None or self.as_of.utcoffset() is None:
            raise SignalIdeaGenerationError("Signal idea timestamps must be timezone-aware.")
        if self.as_of.utcoffset() != timezone.utc.utcoffset(self.as_of):
            raise SignalIdeaGenerationError("Signal idea timestamps must be expressed in UTC.")
        if self.side not in {"long", "short"}:
            raise SignalIdeaGenerationError("Signal idea side must be 'long' or 'short'.")
        if not self.regime.strip() or not self.thesis.strip() or not self.validation_plan.strip():
            raise SignalIdeaGenerationError("Signal ideas require non-empty narrative fields.")
        if self.test_horizon_minutes < 1:
            raise SignalIdeaGenerationError("Signal idea horizons must be positive.")
        _validate_unit_signal(self.alpha_score, "alpha_score")
        _validate_probability(self.conviction, "conviction")
        _validate_unit_signal(self.novelty_lift, "novelty_lift")
        _validate_probability(self.gluing_score, "gluing_score")
        if not self.expected_edge_bps.is_finite() or self.expected_edge_bps <= ZERO:
            raise SignalIdeaGenerationError("Signal ideas require a positive expected edge.")
        if not self.data_signature:
            raise SignalIdeaGenerationError("Signal ideas require a reproducibility signature.")


@dataclass(frozen=True)
class SignalGeometryBundle:
    """High-level bundle produced by the signal-geometry ideation site."""

    schema_version: str
    market_sections: tuple[GluedMarketObservation, ...]
    local_sections: tuple[LocalSignalSection, ...]
    global_sections: tuple[GlobalSignalSection, ...]
    research_ideas: tuple[SignalResearchIdea, ...]
    risk_invariants: RiskInvariantSpecification
    alpha_tolerance: Decimal
    confidence_tolerance: Decimal
    h1_tolerance: Decimal
    min_idea_conviction: Decimal
    min_idea_novelty: Decimal
    upstream_data_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __post_init__(self) -> None:
        if self.schema_version != signal_geometry_schema_version():
            raise SignalNormalizationError("Signal geometry bundle schema version mismatch.")
        if not self.market_sections:
            raise SignalIdeaGenerationError(
                "Signal geometry bundles require at least one glued market section."
            )
        if not self.local_sections:
            raise SignalIdeaGenerationError(
                "Signal geometry bundles require at least one local signal section."
            )
        if not self.global_sections:
            raise SignalIdeaGenerationError(
                "Signal geometry bundles require at least one global signal section."
            )
        if not self.research_ideas:
            raise SignalIdeaGenerationError(
                "Signal geometry bundles require at least one testable signal idea."
            )
        if not self.upstream_data_signature or not self.data_signature:
            raise SignalIdeaGenerationError(
                "Signal geometry bundles require deterministic reproducibility signatures."
            )

    @property
    def symbols(self) -> tuple[str, ...]:
        """Return the canonical symbols represented in the bundle."""
        return tuple(sorted({section.symbol for section in self.global_sections}))

    @property
    def local_signal_sections(self) -> tuple[LocalSignalSection, ...]:
        """Return the local chart sections for compatibility with downstream callers."""
        return self.local_sections

    @property
    def glued_sections(self) -> tuple[GlobalSignalSection, ...]:
        """Return the coherent global sections for compatibility with downstream callers."""
        return self.global_sections

    @property
    def ideas(self) -> tuple[SignalResearchIdea, ...]:
        """Return the testable signal ideas discovered by the bundle."""
        return self.research_ideas

    def summary(self) -> str:
        """Return a deterministic one-line summary of the bundle."""
        return signal_geometry_summary(self)


@dataclass(frozen=True)
class SignalGeometryValidationReport:
    """Deterministic validation report for a built signal-geometry bundle."""

    passes: bool
    timestamp_symbol_invariants_preserved: bool
    normalization_signatures_preserved: bool
    cocycle_checks_passed: bool
    coherent_global_sections: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    signature_matches: bool
    market_sections_checked: int
    local_sections_checked: int
    global_sections_checked: int
    overlap_certificates: tuple[SignalCocycleCertificate, ...]
    messages: tuple[str, ...]

    def summary(self) -> str:
        """Return a concise textual summary of the validation result."""
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} market_sections={self.market_sections_checked} "
            f"local_sections={self.local_sections_checked} "
            f"global_sections={self.global_sections_checked} issues={issues}"
        )


def _build_coordinates(observation: GluedMarketObservation) -> SignalCoordinates:
    """Build the explicit signal atlas coordinates for one market section."""
    topology = observation.topology
    continuation_bias = _squash_signal(
        topology.harmonic_advantage
        + topology.flow_pressure
        + (topology.order_imbalance * HALF)
    )
    mean_reversion_bias = _squash_signal(
        (-topology.microprice_offset)
        + (topology.relative_spread * HALF)
        - (topology.flow_pressure * HALF)
    )
    crowding_pressure = _squash_signal(
        abs(topology.order_imbalance)
        * (topology.relative_spread + abs(topology.flow_pressure))
    )
    topology_memory = _squash_signal(
        observation.novelty_score + topology.harmonic_advantage - topology.relative_spread
    )
    novelty_lift = _squash_signal(
        (observation.gluing_score * topology_memory)
        + topology.harmonic_advantage
        - (crowding_pressure * HALF)
    )
    regime_curvature = _squash_signal(
        continuation_bias - mean_reversion_bias + (topology_memory * HALF)
    )
    return SignalCoordinates(
        continuation_bias=continuation_bias,
        mean_reversion_bias=mean_reversion_bias,
        crowding_pressure=crowding_pressure,
        topology_memory=topology_memory,
        novelty_lift=novelty_lift,
        regime_curvature=regime_curvature,
    )


def _chart_alpha(chart: ChartName, coordinates: SignalCoordinates) -> Decimal:
    """Return the alpha proposed by one local chart."""
    if chart == "persistence":
        raw_alpha = (
            coordinates.continuation_bias
            + (coordinates.topology_memory * HALF)
            + (coordinates.novelty_lift * HALF)
            - (coordinates.crowding_pressure * HALF)
        )
    elif chart == "reversion":
        raw_alpha = (
            coordinates.mean_reversion_bias
            - (coordinates.continuation_bias * HALF)
            - (coordinates.crowding_pressure * HALF)
        )
    else:
        raw_alpha = (
            coordinates.topology_memory
            + coordinates.novelty_lift
            + (coordinates.regime_curvature * HALF)
            - coordinates.crowding_pressure
        )
    return _squash_signal(raw_alpha)


def _chart_thesis(chart: ChartName, alpha_score: Decimal) -> str:
    """Return a short thesis for one local chart."""
    direction = "upside" if alpha_score >= ZERO else "downside"
    if chart == "persistence":
        return (
            "transport chart: follow persistent "
            f"{direction} pressure only when the overlap cocycle stays exact"
        )
    if chart == "reversion":
        return (
            "reversion chart: fade displaced quotes toward the overlap median "
            f"with a {direction} correction"
        )
    return (
        "novelty chart: promote only the "
        f"{direction} idea that survives gluing across the signal atlas"
    )


def _chart_confidence(
    observation: GluedMarketObservation,
    coordinates: SignalCoordinates,
    alpha_score: Decimal,
) -> Decimal:
    """Compute a bounded confidence score for one local chart."""
    support = _support_factor(observation.support_count)
    stability = _stability_factor(observation)
    alignment = _clamp_probability(ONE - abs(alpha_score - coordinates.alpha_seed))
    confidence = (
        observation.gluing_score * Decimal("0.55")
        + support * Decimal("0.20")
        + stability * Decimal("0.15")
        + alignment * Decimal("0.10")
    )
    return _clamp_probability(confidence)


def build_local_signal_section(
    observation: GluedMarketObservation,
    *,
    chart: ChartName = "persistence",
) -> LocalSignalSection:
    """Lift one glued market observation into a local signal chart."""
    if chart not in CHARTS:
        raise SignalNormalizationError(f"Unknown signal chart {chart!r}.")
    coordinates = _build_coordinates(observation)
    alpha_score = _chart_alpha(chart, coordinates)
    confidence = _chart_confidence(observation, coordinates, alpha_score)
    return LocalSignalSection(
        timestamp=observation.timestamp,
        symbol=observation.symbol,
        chart=chart,
        sources=tuple(sorted(observation.sources)),
        venues=tuple(sorted(observation.venues)),
        support_count=observation.support_count,
        gluing_score=_clamp_probability(observation.gluing_score),
        coordinates=coordinates,
        alpha_score=alpha_score,
        confidence=confidence,
        thesis=_chart_thesis(chart, alpha_score),
    )


def build_signal_cover(
    observations: Iterable[GluedMarketObservation],
) -> list[LocalSignalSection]:
    """Build the local signal cover for a batch of coherent market sections."""
    sections: list[LocalSignalSection] = []
    for index, observation in enumerate(observations):
        try:
            for chart in CHARTS:
                sections.append(build_local_signal_section(observation, chart=chart))
        except SignalGeometryError as exc:
            raise SignalNormalizationError(
                f"Failed to build signal cover at observation index {index}: {exc}"
            ) from exc
    return sorted(sections, key=lambda item: (item.timestamp, item.symbol, item.chart))


def restrict_signal_sections(
    sections: Iterable[LocalSignalSection],
    *,
    symbols: Collection[str] | None = None,
    start: datetime | None = None,
    end: datetime | None = None,
    charts: Collection[ChartName] | None = None,
) -> list[LocalSignalSection]:
    """Restrict signal sections to a sub-cover without changing the sections."""
    normalized_symbols = (
        {_normalize_symbol(symbol) for symbol in symbols} if symbols is not None else None
    )
    start_bound = _normalize_timestamp(start, "start") if start is not None else None
    end_bound = _normalize_timestamp(end, "end") if end is not None else None
    normalized_charts = set(charts) if charts is not None else None

    if normalized_charts is not None:
        unknown = normalized_charts.difference(CHARTS)
        if unknown:
            raise SignalRestrictionError(f"Unknown charts in restriction: {sorted(unknown)!r}.")
    if start_bound is not None and end_bound is not None and end_bound < start_bound:
        raise SignalRestrictionError("Restriction end time cannot precede start time.")

    restricted: list[LocalSignalSection] = []
    for section in sections:
        if normalized_symbols is not None and section.symbol not in normalized_symbols:
            continue
        if start_bound is not None and section.timestamp < start_bound:
            continue
        if end_bound is not None and section.timestamp > end_bound:
            continue
        if normalized_charts is not None and section.chart not in normalized_charts:
            continue
        restricted.append(section)
    return sorted(restricted, key=lambda item: (item.timestamp, item.symbol, item.chart))


def group_signal_overlaps(
    sections: Iterable[LocalSignalSection],
) -> dict[SignalKey, list[LocalSignalSection]]:
    """Group local signal sections by the overlap key of the trading cover."""
    grouped: dict[SignalKey, list[LocalSignalSection]] = {}
    for section in sections:
        grouped.setdefault(section.signal_key(), []).append(section)
    for members in grouped.values():
        members.sort(key=lambda item: item.chart)
    return dict(sorted(grouped.items(), key=lambda item: item[0]))


def _require_unique_charts(
    members: Sequence[LocalSignalSection], key: SignalKey
) -> tuple[ChartName, ...]:
    """Ensure an overlap contains at most one section from each chart."""
    chart_names = [member.chart for member in members]
    unique = tuple(sorted(set(chart_names)))
    if len(unique) != len(chart_names):
        timestamp, symbol = key
        raise SignalGluingError(
            f"Signal overlap {symbol}@{timestamp.isoformat()} contains duplicate charts."
        )
    return unique


def _resolve_h1_tolerance(
    alpha_tolerance: Decimal,
    confidence_tolerance: Decimal,
    h1_tolerance: Decimal | str | None,
) -> Decimal:
    """Resolve the gluing tolerance for the obstruction witness."""
    if h1_tolerance is not None:
        return _resolve_tolerance(h1_tolerance, "h1_tolerance")
    return _quantize(alpha_tolerance + (confidence_tolerance * HALF))


def _build_certificate(
    key: SignalKey,
    members: Sequence[LocalSignalSection],
    *,
    alpha_tolerance: Decimal,
    confidence_tolerance: Decimal,
    h1_tolerance: Decimal,
) -> SignalCocycleCertificate:
    """Build the signal cocycle certificate for one overlap class."""
    charts = _require_unique_charts(members, key)
    alpha_values = [member.alpha_score for member in members]
    confidence_values = [member.confidence for member in members]
    corrections = [member.alpha_score - member.coordinates.alpha_seed for member in members]

    alpha_gap = _max_gap(alpha_values)
    confidence_gap = _max_gap(confidence_values)
    triple_residual = _triple_overlap_residual(corrections)
    h1_obstruction = _quantize(alpha_gap + confidence_gap + triple_residual)
    passes = (
        alpha_gap <= alpha_tolerance
        and confidence_gap <= confidence_tolerance
        and h1_obstruction <= h1_tolerance
    )

    if passes:
        reason = "local alpha charts agree and the H1 obstruction vanishes"
    else:
        reason = (
            "signal charts disagree on overlap data: "
            f"alpha_gap={alpha_gap}, "
            f"confidence_gap={confidence_gap}, "
            f"triple_residual={triple_residual}, "
            f"h1_obstruction={h1_obstruction}"
        )

    return SignalCocycleCertificate(
        key=key,
        charts=charts,
        alpha_gap=alpha_gap,
        confidence_gap=confidence_gap,
        triple_overlap_residual=triple_residual,
        h1_obstruction=h1_obstruction,
        passes=passes,
        reason=reason,
    )


def check_signal_cocycle(
    sections: Sequence[LocalSignalSection],
    *,
    alpha_tolerance: Decimal | str = Decimal("0.4500000"),
    confidence_tolerance: Decimal | str = Decimal("0.3500000"),
    h1_tolerance: Decimal | str | None = None,
) -> tuple[SignalCocycleCertificate, ...]:
    """Check whether local signal charts glue on each overlap."""
    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_confidence_tolerance = _resolve_tolerance(
        confidence_tolerance, "confidence_tolerance"
    )
    resolved_h1_tolerance = _resolve_h1_tolerance(
        resolved_alpha_tolerance,
        resolved_confidence_tolerance,
        h1_tolerance,
    )
    grouped = group_signal_overlaps(sections)
    certificates = [
        _build_certificate(
            key,
            members,
            alpha_tolerance=resolved_alpha_tolerance,
            confidence_tolerance=resolved_confidence_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
        for key, members in grouped.items()
    ]
    return tuple(certificates)


def _infer_regime(coordinates: SignalCoordinates) -> str:
    """Classify the local regime from the glued coordinates."""
    if (
        abs(coordinates.continuation_bias) >= abs(coordinates.mean_reversion_bias)
        and abs(coordinates.topology_memory) >= Decimal("0.0500000")
    ):
        return "trend_persistence"
    if abs(coordinates.mean_reversion_bias) > abs(coordinates.continuation_bias):
        return "harmonic_reversion"
    if coordinates.crowding_pressure >= Decimal("0.2000000"):
        return "crowded_rotation"
    return "balanced_probe"


def _infer_side(alpha_score: Decimal, conviction: Decimal) -> str:
    """Map a glued alpha signal to a trading side."""
    if conviction < Decimal("0.2000000") or abs(alpha_score) < SIGNAL_SIDE_THRESHOLD:
        return "flat"
    if alpha_score > ZERO:
        return "long"
    return "short"


def _global_thesis(regime: str, side: str) -> str:
    """Return the strategy thesis implied by a glued signal section."""
    if side == "flat":
        return "hold neutral until the local signal charts agree more strongly on overlaps"
    if regime == "trend_persistence":
        return "follow the transport chart because continuation and novelty glue coherently"
    if regime == "harmonic_reversion":
        return "fade the local displacement because the exact correction survives gluing"
    if regime == "crowded_rotation":
        return "size the idea cautiously because crowding dominates the local charts"
    return "probe the idea lightly while the atlas remains balanced but coherent"


def glue_signal_sections(
    sections: Sequence[LocalSignalSection],
    *,
    alpha_tolerance: Decimal | str = Decimal("0.4500000"),
    confidence_tolerance: Decimal | str = Decimal("0.3500000"),
    h1_tolerance: Decimal | str | None = None,
) -> list[GlobalSignalSection]:
    """Glue local signal charts into coherent strategy-ready sections."""
    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_confidence_tolerance = _resolve_tolerance(
        confidence_tolerance, "confidence_tolerance"
    )
    resolved_h1_tolerance = _resolve_h1_tolerance(
        resolved_alpha_tolerance,
        resolved_confidence_tolerance,
        h1_tolerance,
    )

    grouped = group_signal_overlaps(sections)
    certificates = {
        certificate.key: certificate
        for certificate in check_signal_cocycle(
            sections,
            alpha_tolerance=resolved_alpha_tolerance,
            confidence_tolerance=resolved_confidence_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    }

    glued: list[GlobalSignalSection] = []
    for key, members in grouped.items():
        certificate = certificates[key]
        certificate.assert_passes()
        coordinates = SignalCoordinates(
            continuation_bias=_median_decimal(
                [member.coordinates.continuation_bias for member in members]
            ),
            mean_reversion_bias=_median_decimal(
                [member.coordinates.mean_reversion_bias for member in members]
            ),
            crowding_pressure=_median_decimal(
                [member.coordinates.crowding_pressure for member in members]
            ),
            topology_memory=_median_decimal(
                [member.coordinates.topology_memory for member in members]
            ),
            novelty_lift=_median_decimal(
                [member.coordinates.novelty_lift for member in members]
            ),
            regime_curvature=_median_decimal(
                [member.coordinates.regime_curvature for member in members]
            ),
        )
        alpha_score = _median_decimal([member.alpha_score for member in members])
        confidence = _median_decimal([member.confidence for member in members])
        gluing_score = _gluing_score(certificate.h1_obstruction, resolved_h1_tolerance)
        conviction = _clamp_probability(confidence * gluing_score)
        regime = _infer_regime(coordinates)
        side = _infer_side(alpha_score, conviction)
        support_count = max(member.support_count for member in members)
        glued.append(
            GlobalSignalSection(
                timestamp=key[0],
                symbol=key[1],
                charts=certificate.charts,
                sources=tuple(sorted({source for member in members for source in member.sources})),
                venues=tuple(sorted({venue for member in members for venue in member.venues})),
                support_count=support_count,
                local_section_count=len(members),
                coordinates=coordinates,
                alpha_score=alpha_score,
                conviction=conviction,
                regime=regime,
                side=side,
                gluing_score=gluing_score,
                thesis=_global_thesis(regime, side),
            )
        )
    return sorted(glued, key=lambda item: (item.timestamp, item.symbol))


def _quantize_idea_edge(value: Decimal) -> Decimal:
    """Quantize a projected signal edge onto a basis-point lattice."""
    return _quantize(value, IDEA_EDGE_QUANTUM)


def _idea_expected_edge_bps(section: GlobalSignalSection) -> Decimal:
    """Project a glued signal section onto an expected edge in basis points."""
    support = _support_factor(section.support_count)
    projected = (
        abs(section.alpha_score)
        * (ONE + abs(section.coordinates.novelty_lift))
        * section.conviction
        * support
        * (ONE + section.gluing_score)
        * Decimal("100")
    )
    return _quantize_idea_edge(projected)


def _idea_side(section: GlobalSignalSection) -> SignalIdeaSide | None:
    """Infer a paper-trade probe direction for a coherent section."""
    if section.side in {"long", "short"}:
        return section.side
    probe_score = (
        section.alpha_score
        + section.coordinates.novelty_lift
        + (section.coordinates.topology_memory * HALF)
    )
    if probe_score > ZERO:
        return "long"
    if probe_score < ZERO:
        return "short"
    return None


def _idea_validation_plan(section: GlobalSignalSection) -> str:
    """Return a deterministic validation plan for one signal idea."""
    return (
        "paper-trade the glued idea on versioned market sections, "
        "replay immutable audit metadata, reject stale or tampered inputs, "
        "and evaluate risk-adjusted return, tail loss, and stress scenarios "
        "without lookahead leakage"
    )


def discover_signal_research_ideas(
    sections: Iterable[GlobalSignalSection],
    *,
    min_conviction: Decimal | str = Decimal("0.1500000"),
    min_novelty_lift: Decimal | str = Decimal("0.0000500"),
    min_edge_bps: Decimal | str = Decimal("1.5000"),
) -> list[SignalResearchIdea]:
    """Discover testable signal ideas from glued global sections."""
    resolved_conviction = _resolve_probability_floor(min_conviction, "min_conviction")
    resolved_novelty = _resolve_unit_signal_floor(min_novelty_lift, "min_novelty_lift")
    resolved_edge = _resolve_non_negative_decimal(min_edge_bps, "min_edge_bps")

    ideas: list[SignalResearchIdea] = []
    for section in sorted(sections, key=lambda item: (item.timestamp, item.symbol)):
        idea_side = _idea_side(section)
        expected_edge_bps = _idea_expected_edge_bps(section)
        if idea_side is None:
            continue
        if section.conviction < resolved_conviction:
            continue
        if abs(section.coordinates.novelty_lift) < resolved_novelty:
            continue
        if expected_edge_bps < resolved_edge:
            continue
        ideas.append(
            SignalResearchIdea(
                symbol=section.symbol,
                as_of=section.timestamp,
                side=idea_side,
                regime=section.regime,
                thesis=(
                    f"{idea_side} {section.symbol} because {section.thesis}; "
                    "the novelty chart remains non-exact and therefore testable"
                ),
                validation_plan=_idea_validation_plan(section),
                test_horizon_minutes=30 + (section.local_section_count * 10),
                alpha_score=section.alpha_score,
                conviction=section.conviction,
                novelty_lift=section.coordinates.novelty_lift,
                gluing_score=section.gluing_score,
                expected_edge_bps=expected_edge_bps,
                data_signature=section.reproducibility_signature(),
            )
        )
    return ideas


def _sections_input_signature(sections: tuple[GluedMarketObservation, ...]) -> str:
    """Return a deterministic signature for direct market-section inputs."""
    return _stable_digest([section.reproducibility_signature() for section in sections])


def _resolve_signal_geometry_input(
    signal_input: SignalGeometryInput,
) -> tuple[tuple[GluedMarketObservation, ...], str, RiskInvariantSpecification]:
    """Normalize upstream input into market sections, signature, and risk spec."""
    if isinstance(signal_input, MarketDataBundle):
        return (
            tuple(signal_input.live_sections),
            signal_input.data_signature,
            signal_input.risk_invariants,
        )
    sections = tuple(sorted(signal_input, key=lambda item: (item.timestamp, item.symbol)))
    return (sections, _sections_input_signature(sections), RiskInvariantSpecification())


def _signal_geometry_bundle_signature(bundle: SignalGeometryBundle) -> str:
    """Return a stable audit digest for the full signal-geometry bundle."""
    parts = [
        bundle.schema_version,
        str(bundle.alpha_tolerance),
        str(bundle.confidence_tolerance),
        str(bundle.h1_tolerance),
        str(bundle.min_idea_conviction),
        str(bundle.min_idea_novelty),
        bundle.upstream_data_signature,
        bundle.risk_invariants.reproducibility_signature(),
    ]
    parts.extend(section.reproducibility_signature() for section in bundle.market_sections)
    parts.append("local_sections")
    parts.extend(section.reproducibility_signature() for section in bundle.local_sections)
    parts.append("global_sections")
    parts.extend(section.reproducibility_signature() for section in bundle.global_sections)
    parts.append("research_ideas")
    parts.extend(idea.data_signature for idea in bundle.research_ideas)
    parts.extend(f"{key}={value}" for key, value in bundle.audit_metadata)
    return _stable_digest(parts)


def build_signal_geometry(
    signal_input: SignalGeometryInput,
    *,
    alpha_tolerance: Decimal | str = Decimal("0.4500000"),
    confidence_tolerance: Decimal | str = Decimal("0.3500000"),
    h1_tolerance: Decimal | str | None = None,
    min_idea_conviction: Decimal | str = Decimal("0.1500000"),
    min_idea_novelty: Decimal | str = Decimal("0.0000500"),
    min_edge_bps: Decimal | str = Decimal("1.5000"),
    risk_invariants: RiskInvariantSpecification | None = None,
) -> SignalGeometryBundle:
    """Build an auditable signal-geometry bundle from market sections."""
    market_sections, upstream_signature, inherited_risk_invariants = _resolve_signal_geometry_input(
        signal_input
    )
    if not market_sections:
        raise SignalIdeaGenerationError(
            "Signal geometry requires at least one glued market section."
        )

    resolved_alpha_tolerance = _resolve_tolerance(alpha_tolerance, "alpha_tolerance")
    resolved_confidence_tolerance = _resolve_tolerance(
        confidence_tolerance, "confidence_tolerance"
    )
    resolved_h1_tolerance = _resolve_h1_tolerance(
        resolved_alpha_tolerance,
        resolved_confidence_tolerance,
        h1_tolerance,
    )
    resolved_min_idea_conviction = _resolve_probability_floor(
        min_idea_conviction, "min_idea_conviction"
    )
    resolved_min_idea_novelty = _resolve_unit_signal_floor(
        min_idea_novelty, "min_idea_novelty"
    )
    active_risk_invariants = (
        risk_invariants if risk_invariants is not None else inherited_risk_invariants
    )

    local_sections = tuple(build_signal_cover(market_sections))
    global_sections = tuple(
        glue_signal_sections(
            local_sections,
            alpha_tolerance=resolved_alpha_tolerance,
            confidence_tolerance=resolved_confidence_tolerance,
            h1_tolerance=resolved_h1_tolerance,
        )
    )
    research_ideas = tuple(
        discover_signal_research_ideas(
            global_sections,
            min_conviction=resolved_min_idea_conviction,
            min_novelty_lift=resolved_min_idea_novelty,
            min_edge_bps=min_edge_bps,
        )
    )
    if not research_ideas:
        raise SignalIdeaGenerationError(
            "Signal geometry must emit at least one testable idea from glued sections."
        )

    audit_metadata = tuple(
        sorted(
            (
                ("execution_mode", "paper_only"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("idea_mode", "data_driven_signal_probe"),
                (
                    "kill_switch_policy",
                    "inherit_risk_engine_drawdown_and_stale_data_guards",
                ),
                ("proof_obligation", active_risk_invariants.proof_obligation),
                ("schema_version", signal_geometry_schema_version()),
                ("upstream_signature", upstream_signature[:16]),
            )
        )
    )
    unsigned_bundle = SignalGeometryBundle(
        schema_version=signal_geometry_schema_version(),
        market_sections=market_sections,
        local_sections=local_sections,
        global_sections=global_sections,
        research_ideas=research_ideas,
        risk_invariants=active_risk_invariants,
        alpha_tolerance=resolved_alpha_tolerance,
        confidence_tolerance=resolved_confidence_tolerance,
        h1_tolerance=resolved_h1_tolerance,
        min_idea_conviction=resolved_min_idea_conviction,
        min_idea_novelty=resolved_min_idea_novelty,
        upstream_data_signature=upstream_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return SignalGeometryBundle(
        schema_version=unsigned_bundle.schema_version,
        market_sections=unsigned_bundle.market_sections,
        local_sections=unsigned_bundle.local_sections,
        global_sections=unsigned_bundle.global_sections,
        research_ideas=unsigned_bundle.research_ideas,
        risk_invariants=unsigned_bundle.risk_invariants,
        alpha_tolerance=unsigned_bundle.alpha_tolerance,
        confidence_tolerance=unsigned_bundle.confidence_tolerance,
        h1_tolerance=unsigned_bundle.h1_tolerance,
        min_idea_conviction=unsigned_bundle.min_idea_conviction,
        min_idea_novelty=unsigned_bundle.min_idea_novelty,
        upstream_data_signature=unsigned_bundle.upstream_data_signature,
        data_signature=_signal_geometry_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


def _restriction_signatures_preserved(
    sections: tuple[LocalSignalSection, ...],
) -> bool:
    """Return whether restricting to the full support preserves local signatures."""
    if not sections:
        return True
    restricted = restrict_signal_sections(
        sections,
        symbols={section.symbol for section in sections},
        start=sections[0].timestamp,
        end=sections[-1].timestamp,
        charts={section.chart for section in sections},
    )
    original = tuple(section.normalization_signature() for section in sections)
    restricted_signatures = tuple(section.normalization_signature() for section in restricted)
    return original == restricted_signatures


def _global_sections_coherent(
    local_sections: tuple[LocalSignalSection, ...],
    global_sections: tuple[GlobalSignalSection, ...],
) -> bool:
    """Return whether global sections descend exactly from the local overlaps."""
    grouped = group_signal_overlaps(local_sections)
    if len(grouped) != len(global_sections):
        return False
    for section in global_sections:
        members = grouped.get(section.signal_key())
        if members is None:
            return False
        expected_charts = tuple(sorted(member.chart for member in members))
        if section.charts != expected_charts:
            return False
        if section.local_section_count != len(members):
            return False
        if section.support_count != max(member.support_count for member in members):
            return False
    return True


def validate_signal_geometry(bundle: SignalGeometryBundle) -> SignalGeometryValidationReport:
    """Validate that a signal-geometry bundle still satisfies its obligations."""
    certificates = check_signal_cocycle(
        bundle.local_sections,
        alpha_tolerance=bundle.alpha_tolerance,
        confidence_tolerance=bundle.confidence_tolerance,
        h1_tolerance=bundle.h1_tolerance,
    )
    normalization_preserved = _restriction_signatures_preserved(bundle.local_sections)
    cocycle_checks_passed = all(certificate.passes for certificate in certificates)
    coherent_global_sections = _global_sections_coherent(
        bundle.local_sections,
        bundle.global_sections,
    )
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = (
        bool(bundle.risk_invariants.order_rejection_conditions)
        and "reject_unverified_risk_core"
        in bundle.risk_invariants.order_rejection_conditions
        and bundle.risk_invariants.proof_obligation in {"smt_required", "machine_checked"}
    )
    signature_matches = bundle.data_signature == _signal_geometry_bundle_signature(bundle)
    timestamp_symbol_invariants_preserved = normalization_preserved

    messages: list[str] = []
    if not normalization_preserved:
        messages.append("restriction signature preservation failed")
    if not cocycle_checks_passed:
        messages.append("one or more signal cocycle checks failed")
    if not coherent_global_sections:
        messages.append("global sections no longer descend from local overlaps")
    if not novel_idea_present:
        messages.append("no testable data-driven signal idea is present")
    if not risk_invariants_explicit:
        messages.append("risk invariants are not explicit enough for proof discharge")
    if not signature_matches:
        messages.append("bundle reproducibility signature mismatch")

    passes = (
        timestamp_symbol_invariants_preserved
        and cocycle_checks_passed
        and coherent_global_sections
        and novel_idea_present
        and risk_invariants_explicit
        and signature_matches
    )
    return SignalGeometryValidationReport(
        passes=passes,
        timestamp_symbol_invariants_preserved=timestamp_symbol_invariants_preserved,
        normalization_signatures_preserved=normalization_preserved,
        cocycle_checks_passed=cocycle_checks_passed,
        coherent_global_sections=coherent_global_sections,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        signature_matches=signature_matches,
        market_sections_checked=len(bundle.market_sections),
        local_sections_checked=len(bundle.local_sections),
        global_sections_checked=len(bundle.global_sections),
        overlap_certificates=certificates,
        messages=tuple(messages),
    )


def signal_geometry_summary(bundle: SignalGeometryBundle) -> str:
    """Return a deterministic summary string for the signal-geometry bundle."""
    report = validate_signal_geometry(bundle)
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.expected_edge_bps}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    status = "pass" if report.passes else "fail"
    symbols = ",".join(bundle.symbols)
    return (
        f"signal_geometry[{bundle.schema_version}] symbols={symbols} "
        f"market_sections={len(bundle.market_sections)} "
        f"local_sections={len(bundle.local_sections)} "
        f"global_sections={len(bundle.global_sections)} "
        f"ideas={len(bundle.research_ideas)} "
        f"validation={status} proof={bundle.risk_invariants.proof_obligation} "
        f"paper_only={bundle.risk_invariants.paper_trading_required} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )


__all__ = [
    "CHARTS",
    "GlobalSignalSection",
    "SignalGeometryBundle",
    "SignalGeometryInput",
    "SignalGeometryValidationReport",
    "SignalIdeaGenerationError",
    "SignalResearchIdea",
    "LocalSignalSection",
    "SignalCocycleCertificate",
    "SignalCoordinates",
    "SignalGeometryError",
    "SignalGluingError",
    "SignalNormalizationError",
    "SignalRestrictionError",
    "build_local_signal_section",
    "build_signal_cover",
    "build_signal_geometry",
    "check_signal_cocycle",
    "discover_signal_research_ideas",
    "glue_signal_sections",
    "group_signal_overlaps",
    "restrict_signal_sections",
    "signal_geometry_schema_version",
    "signal_geometry_summary",
    "validate_signal_geometry",
]
