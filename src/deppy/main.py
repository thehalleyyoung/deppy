"""Assemble the typed trading sites into one runnable, verified global section.

This module is the global section of the trading pipeline:

``market_data -> signal_geometry -> strategy_kernel -> risk_engine
-> execution -> portfolio -> compliance -> main``.

Its typed intent is to glue the local sites into one deterministic, auditable,
paper-trading-ready system. In the project's ideation-as-typing language, each
upstream bundle is a local section on one cover, the stage signatures are their
restriction maps, and the top-level builder discharges the final H^1-aware
gluing obligations: overlap invariants must survive restriction, alpha sections
must descend coherently into strategy and risk, only risk-approved intents may
reach execution, and the risk-critical core must remain explicitly bounded and
machine-checkable before any runnable plan is emitted.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from typing import Any, Iterable, Literal, Mapping, Sequence, TypeAlias

from deppy.compliance import (
    ComplianceBundle,
    CompliancePolicy,
    ComplianceResearchIdea,
    build_compliance,
    compliance_summary,
    validate_compliance,
)
from deppy.execution import (
    ExecutionBundle,
    ExecutionPolicy,
    ExecutionQuote,
    ExecutionResearchIdea,
    build_execution,
    execution_summary,
    validate_execution,
)
from deppy.market_data import (
    MarketDataBundle,
    NovelMarketHypothesis,
    RiskInvariantSpecification,
    build_market_data,
    market_data_summary,
    validate_market_data,
)
from deppy.portfolio import (
    PortfolioBundle,
    PortfolioPolicy,
    PortfolioResearchIdea,
    build_portfolio,
    portfolio_summary,
    validate_portfolio,
)
from deppy.risk_engine import (
    RiskEngineBundle,
    RiskPolicy,
    RiskResearchIdea,
    build_risk_engine,
    risk_engine_summary,
    validate_risk_engine,
)
from deppy.signal_geometry import (
    SignalGeometryBundle,
    SignalResearchIdea,
    build_signal_geometry,
    signal_geometry_summary,
    validate_signal_geometry,
)
from deppy.strategy_kernel import (
    StrategyKernelBundle,
    StrategyResearchIdea,
    build_strategy_kernel,
    strategy_kernel_summary,
    validate_strategy_kernel,
)

FRACTION_QUANTUM = Decimal("0.0000001")
BPS_QUANTUM = Decimal("0.0001")
CASH_QUANTUM = Decimal("0.01")
ZERO = Decimal("0")
ONE = Decimal("1")
MAIN_SCHEMA_VERSION = "main.v1"
STAGE_ORDER: tuple[str, ...] = (
    "market_data",
    "signal_geometry",
    "strategy_kernel",
    "risk_engine",
    "execution",
    "portfolio",
    "compliance",
    "main",
)
DEFAULT_REQUIRED_GLUING_OBLIGATIONS: tuple[str, ...] = (
    "restriction_invariants",
    "signature_descent",
    "alpha_strategy_coherence",
    "risk_bounds_alignment",
    "risk_approved_descent",
    "fail_safe_kill_switch",
    "formal_proof_chain",
)
DEFAULT_REQUIRED_RISK_INVARIANTS: tuple[str, ...] = (
    "max_position_size",
    "gross_leverage",
    "net_exposure",
    "drawdown_trigger",
    "order_rejection_conditions",
)
DEFAULT_REQUIRED_AUDIT_METADATA_KEYS: tuple[str, ...] = (
    "audit_log",
    "deployment_mode",
    "gluing_mode",
    "integration_mode",
    "kill_switch_policy",
    "paper_trading",
    "proof_obligation",
    "reproducibility",
    "separation",
    "stage_order",
)

MainProofMode: TypeAlias = Literal["smt_required", "machine_checked"]
DeploymentMode: TypeAlias = Literal["paper"]
KillSwitchState: TypeAlias = Literal["armed", "engaged"]
MainIdeaSide: TypeAlias = Literal["long", "short"]
MainVerificationResult: TypeAlias = Literal["proved", "failed"]


class MainError(ValueError):
    """Base error raised by global trading-system orchestration."""


class MainNormalizationError(MainError):
    """Raised when top-level orchestration data violates normalization rules."""


class MainVerificationError(MainError):
    """Raised when the top-level machine-checkable proof step cannot complete."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _quantize_fraction(value: Decimal) -> Decimal:
    return _quantize(value, FRACTION_QUANTUM)


def _quantize_bps(value: Decimal) -> Decimal:
    return _quantize(value, BPS_QUANTUM)


def _quantize_cash(value: Decimal) -> Decimal:
    return _quantize(value, CASH_QUANTUM)


def _coerce_decimal(value: Any, field_name: str) -> Decimal:
    if isinstance(value, Decimal):
        candidate = value
    else:
        try:
            candidate = Decimal(str(value).strip())
        except (AttributeError, InvalidOperation, ValueError) as exc:
            raise MainNormalizationError(
                f"Field '{field_name}' must be numeric, got {value!r}."
            ) from exc
    if not candidate.is_finite():
        raise MainNormalizationError(f"Field '{field_name}' must be finite.")
    return candidate


def _stable_digest(parts: Iterable[str]) -> str:
    digest = sha256()
    digest.update(MAIN_SCHEMA_VERSION.encode("utf-8"))
    digest.update(b"\0")
    for part in parts:
        digest.update(str(part).encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def _normalize_timestamp(value: datetime, field_name: str) -> datetime:
    if not isinstance(value, datetime):
        raise MainNormalizationError(
            f"Field '{field_name}' must be a datetime, got {value!r}."
        )
    if value.tzinfo is None or value.utcoffset() is None:
        return value.replace(tzinfo=timezone.utc)
    return value.astimezone(timezone.utc)


def _normalize_symbol(value: str) -> str:
    if not isinstance(value, str):
        raise MainNormalizationError(f"Field 'symbol' must be text, got {value!r}.")
    candidate = value.strip().upper()
    if not candidate:
        raise MainNormalizationError("Field 'symbol' cannot be empty.")
    for separator in ("/", "-", " "):
        candidate = candidate.replace(separator, "")
    if not candidate:
        raise MainNormalizationError(f"Field 'symbol' cannot normalize from {value!r}.")
    return candidate


def _validate_probability(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise MainNormalizationError(f"Field '{field_name}' must be finite.")
    if value < ZERO or value > ONE:
        raise MainNormalizationError(f"Field '{field_name}' must lie in [0, 1].")


def _validate_positive_decimal(value: Decimal, field_name: str) -> None:
    if not value.is_finite():
        raise MainNormalizationError(f"Field '{field_name}' must be finite.")
    if value <= ZERO:
        raise MainNormalizationError(f"Field '{field_name}' must be strictly positive.")


def _gap_from_bools(values: Sequence[bool]) -> Decimal:
    if not values:
        return ZERO
    passed = sum(bool(value) for value in values)
    ratio = Decimal(passed) / Decimal(len(values))
    return _quantize_fraction(ONE - ratio)


def _mean_decimal(values: Sequence[Decimal], quantum: Decimal) -> Decimal:
    if not values:
        return ZERO
    return _quantize(sum(values, ZERO) / Decimal(len(values)), quantum)


def _proof_ratio(items: Sequence[Any]) -> Decimal:
    if not items:
        return ZERO
    proved = sum(getattr(item, "result", None) == "proved" for item in items)
    return _quantize_fraction(Decimal(proved) / Decimal(len(items)))


def main_schema_version() -> str:
    return MAIN_SCHEMA_VERSION


def _mapping_signature(mapping: Mapping[str, Any]) -> str:
    return _stable_digest(f"{key}={mapping[key]!r}" for key in sorted(mapping))


def _entry_signature(entry: Mapping[str, Any]) -> str:
    return _stable_digest(f"{key}={entry[key]!r}" for key in sorted(entry))


@dataclass(frozen=True, init=False)
class MainAssemblyRequest:
    """Raw inputs and calibrated thresholds for the full end-to-end assembly."""

    historical_entries: tuple[Mapping[str, Any], ...]
    live_entries: tuple[Mapping[str, Any], ...]
    quotes_by_symbol: Mapping[str, ExecutionQuote]
    local_entries: tuple[Mapping[str, Any], ...] = ()
    local_observer: str = "local_observer"
    default_source: str = "feed"
    min_history_points: int = 6
    market_min_novelty_lift: Decimal = Decimal("0.0000500")
    market_min_edge_bps: Decimal = Decimal("2.5000")
    signal_min_idea_conviction: Decimal = Decimal("0.1500000")
    signal_min_idea_novelty: Decimal = Decimal("0.0000010")
    signal_min_edge_bps: Decimal = Decimal("1.0000")
    strategy_min_conviction: Decimal = Decimal("0.0500000")
    strategy_min_target_fraction: Decimal = Decimal("0.0050000")
    risk_min_approval_fraction: Decimal = Decimal("0.0050000")
    execution_min_order_fraction: Decimal = Decimal("0.0050000")
    starting_cash_balance: Decimal | None = None
    mark_price_by_symbol: Mapping[str, Decimal] | None = None
    risk_invariants: RiskInvariantSpecification | None = None
    risk_policy: RiskPolicy | None = None
    execution_policy: ExecutionPolicy | None = None
    portfolio_policy: PortfolioPolicy | None = None
    compliance_policy: CompliancePolicy | None = None

    def __init__(
        self,
        historical_entries: tuple[Mapping[str, Any], ...],
        live_entries: tuple[Mapping[str, Any], ...],
        quotes_by_symbol: Mapping[str, ExecutionQuote],
        local_entries: tuple[Mapping[str, Any], ...] = (),
        local_observer: str = "local_observer",
        default_source: str = "feed",
        min_history_points: int = 6,
        market_min_novelty_lift: Decimal = Decimal("0.0000500"),
        market_min_edge_bps: Decimal = Decimal("2.5000"),
        signal_min_idea_conviction: Decimal = Decimal("0.1500000"),
        signal_min_idea_novelty: Decimal = Decimal("0.0000010"),
        signal_min_edge_bps: Decimal = Decimal("1.0000"),
        strategy_min_conviction: Decimal = Decimal("0.0500000"),
        strategy_min_target_fraction: Decimal = Decimal("0.0050000"),
        risk_min_approval_fraction: Decimal = Decimal("0.0050000"),
        execution_min_order_fraction: Decimal = Decimal("0.0050000"),
        starting_cash_balance: Decimal | None = None,
        mark_price_by_symbol: Mapping[str, Decimal] | None = None,
        risk_invariants: RiskInvariantSpecification | None = None,
        risk_policy: RiskPolicy | None = None,
        execution_policy: ExecutionPolicy | None = None,
        portfolio_policy: PortfolioPolicy | None = None,
        compliance_policy: CompliancePolicy | None = None,
    ) -> None:
        object.__setattr__(self, "historical_entries", historical_entries)
        object.__setattr__(self, "live_entries", live_entries)
        object.__setattr__(self, "quotes_by_symbol", quotes_by_symbol)
        object.__setattr__(self, "local_entries", local_entries)
        object.__setattr__(self, "local_observer", local_observer)
        object.__setattr__(self, "default_source", default_source)
        object.__setattr__(self, "min_history_points", min_history_points)
        object.__setattr__(self, "market_min_novelty_lift", market_min_novelty_lift)
        object.__setattr__(self, "market_min_edge_bps", market_min_edge_bps)
        object.__setattr__(self, "signal_min_idea_conviction", signal_min_idea_conviction)
        object.__setattr__(self, "signal_min_idea_novelty", signal_min_idea_novelty)
        object.__setattr__(self, "signal_min_edge_bps", signal_min_edge_bps)
        object.__setattr__(self, "strategy_min_conviction", strategy_min_conviction)
        object.__setattr__(
            self,
            "strategy_min_target_fraction",
            strategy_min_target_fraction,
        )
        object.__setattr__(
            self,
            "risk_min_approval_fraction",
            risk_min_approval_fraction,
        )
        object.__setattr__(
            self,
            "execution_min_order_fraction",
            execution_min_order_fraction,
        )
        object.__setattr__(self, "starting_cash_balance", starting_cash_balance)
        object.__setattr__(self, "mark_price_by_symbol", mark_price_by_symbol)
        object.__setattr__(self, "risk_invariants", risk_invariants)
        object.__setattr__(self, "risk_policy", risk_policy)
        object.__setattr__(self, "execution_policy", execution_policy)
        object.__setattr__(self, "portfolio_policy", portfolio_policy)
        object.__setattr__(self, "compliance_policy", compliance_policy)
        self.__post_init__()

    def __post_init__(self) -> None:
        historical_entries = tuple(dict(entry) for entry in self.historical_entries)
        live_entries = tuple(dict(entry) for entry in self.live_entries)
        local_entries = tuple(dict(entry) for entry in self.local_entries)
        quotes_by_symbol: dict[str, ExecutionQuote] = {}
        for key, quote in self.quotes_by_symbol.items():
            if not isinstance(quote, ExecutionQuote):
                raise MainNormalizationError(
                    f"quotes_by_symbol[{key!r}] must be an ExecutionQuote."
                )
            quotes_by_symbol[_normalize_symbol(key)] = quote
        mark_price_by_symbol = (
            {_normalize_symbol(key): _coerce_decimal(value, f"mark_price_by_symbol[{key}]")
             for key, value in self.mark_price_by_symbol.items()}
            if self.mark_price_by_symbol is not None
            else None
        )
        if not historical_entries:
            raise MainNormalizationError("MainAssemblyRequest requires historical_entries.")
        if not live_entries:
            raise MainNormalizationError("MainAssemblyRequest requires live_entries.")
        if not quotes_by_symbol:
            raise MainNormalizationError("MainAssemblyRequest requires quotes_by_symbol.")
        if self.min_history_points < 1:
            raise MainNormalizationError("min_history_points must be positive.")
        market_min_novelty_lift = _quantize_fraction(
            _coerce_decimal(self.market_min_novelty_lift, "market_min_novelty_lift")
        )
        signal_min_idea_conviction = _quantize_fraction(
            _coerce_decimal(self.signal_min_idea_conviction, "signal_min_idea_conviction")
        )
        signal_min_idea_novelty = _quantize_fraction(
            _coerce_decimal(self.signal_min_idea_novelty, "signal_min_idea_novelty")
        )
        strategy_min_conviction = _quantize_fraction(
            _coerce_decimal(self.strategy_min_conviction, "strategy_min_conviction")
        )
        strategy_min_target_fraction = _quantize_fraction(
            _coerce_decimal(self.strategy_min_target_fraction, "strategy_min_target_fraction")
        )
        risk_min_approval_fraction = _quantize_fraction(
            _coerce_decimal(self.risk_min_approval_fraction, "risk_min_approval_fraction")
        )
        execution_min_order_fraction = _quantize_fraction(
            _coerce_decimal(self.execution_min_order_fraction, "execution_min_order_fraction")
        )
        market_min_edge_bps = _quantize_bps(
            _coerce_decimal(self.market_min_edge_bps, "market_min_edge_bps")
        )
        signal_min_edge_bps = _quantize_bps(
            _coerce_decimal(self.signal_min_edge_bps, "signal_min_edge_bps")
        )
        _validate_probability(market_min_novelty_lift, "market_min_novelty_lift")
        _validate_probability(signal_min_idea_conviction, "signal_min_idea_conviction")
        _validate_probability(signal_min_idea_novelty, "signal_min_idea_novelty")
        _validate_probability(strategy_min_conviction, "strategy_min_conviction")
        _validate_probability(strategy_min_target_fraction, "strategy_min_target_fraction")
        _validate_probability(risk_min_approval_fraction, "risk_min_approval_fraction")
        _validate_probability(execution_min_order_fraction, "execution_min_order_fraction")
        _validate_positive_decimal(market_min_edge_bps, "market_min_edge_bps")
        _validate_positive_decimal(signal_min_edge_bps, "signal_min_edge_bps")
        if self.starting_cash_balance is not None:
            starting_cash_balance = _quantize_cash(
                _coerce_decimal(self.starting_cash_balance, "starting_cash_balance")
            )
            _validate_positive_decimal(starting_cash_balance, "starting_cash_balance")
            object.__setattr__(self, "starting_cash_balance", starting_cash_balance)
        object.__setattr__(self, "historical_entries", historical_entries)
        object.__setattr__(self, "live_entries", live_entries)
        object.__setattr__(self, "local_entries", local_entries)
        object.__setattr__(self, "quotes_by_symbol", quotes_by_symbol)
        object.__setattr__(self, "mark_price_by_symbol", mark_price_by_symbol)
        object.__setattr__(self, "market_min_novelty_lift", market_min_novelty_lift)
        object.__setattr__(self, "market_min_edge_bps", market_min_edge_bps)
        object.__setattr__(self, "signal_min_idea_conviction", signal_min_idea_conviction)
        object.__setattr__(self, "signal_min_idea_novelty", signal_min_idea_novelty)
        object.__setattr__(self, "signal_min_edge_bps", signal_min_edge_bps)
        object.__setattr__(self, "strategy_min_conviction", strategy_min_conviction)
        object.__setattr__(self, "strategy_min_target_fraction", strategy_min_target_fraction)
        object.__setattr__(self, "risk_min_approval_fraction", risk_min_approval_fraction)
        object.__setattr__(self, "execution_min_order_fraction", execution_min_order_fraction)

    def reproducibility_signature(self) -> str:
        mark_signature = (
            _mapping_signature(self.mark_price_by_symbol)
            if self.mark_price_by_symbol is not None
            else "no-marks"
        )
        return _stable_digest(
            [
                *(_entry_signature(entry) for entry in self.historical_entries),
                *(_entry_signature(entry) for entry in self.live_entries),
                *(_entry_signature(entry) for entry in self.local_entries),
                *(
                    f"{symbol}:{quote.timestamp.isoformat()}:{quote.venue}:{quote.bid_price}:{quote.ask_price}:{quote.available_quantity}"
                    for symbol, quote in sorted(self.quotes_by_symbol.items())
                ),
                mark_signature,
                self.local_observer,
                self.default_source,
                str(self.min_history_points),
                str(self.market_min_novelty_lift),
                str(self.market_min_edge_bps),
                str(self.signal_min_idea_conviction),
                str(self.signal_min_idea_novelty),
                str(self.signal_min_edge_bps),
                str(self.strategy_min_conviction),
                str(self.strategy_min_target_fraction),
                str(self.risk_min_approval_fraction),
                str(self.execution_min_order_fraction),
                str(self.starting_cash_balance) if self.starting_cash_balance is not None else "auto-cash",
                self.risk_invariants.reproducibility_signature()
                if self.risk_invariants is not None
                else "default-risk-invariants",
                self.risk_policy.reproducibility_signature()
                if self.risk_policy is not None
                else "default-risk-policy",
                self.execution_policy.reproducibility_signature()
                if self.execution_policy is not None
                else "default-execution-policy",
                self.portfolio_policy.proof_obligation
                if self.portfolio_policy is not None
                else "default-portfolio-policy",
                self.compliance_policy.reproducibility_signature()
                if self.compliance_policy is not None
                else "default-compliance-policy",
            ]
        )


@dataclass(frozen=True, init=False)
class MainPolicy:
    """Global obligations enforced when the full system is glued."""

    required_gluing_obligations: tuple[str, ...] = DEFAULT_REQUIRED_GLUING_OBLIGATIONS
    required_risk_invariants: tuple[str, ...] = DEFAULT_REQUIRED_RISK_INVARIANTS
    required_audit_metadata_keys: tuple[str, ...] = DEFAULT_REQUIRED_AUDIT_METADATA_KEYS
    proof_obligation: MainProofMode = "smt_required"
    paper_trading_required: bool = True
    live_deployment_allowed: bool = False
    max_cross_stage_gap: Decimal = Decimal("0.2500000")

    def __init__(
        self,
        required_gluing_obligations: tuple[str, ...] = DEFAULT_REQUIRED_GLUING_OBLIGATIONS,
        required_risk_invariants: tuple[str, ...] = DEFAULT_REQUIRED_RISK_INVARIANTS,
        required_audit_metadata_keys: tuple[str, ...] = DEFAULT_REQUIRED_AUDIT_METADATA_KEYS,
        proof_obligation: MainProofMode = "smt_required",
        paper_trading_required: bool = True,
        live_deployment_allowed: bool = False,
        max_cross_stage_gap: Decimal = Decimal("0.2500000"),
    ) -> None:
        object.__setattr__(
            self,
            "required_gluing_obligations",
            tuple(required_gluing_obligations),
        )
        object.__setattr__(
            self,
            "required_risk_invariants",
            tuple(required_risk_invariants),
        )
        object.__setattr__(
            self,
            "required_audit_metadata_keys",
            tuple(required_audit_metadata_keys),
        )
        object.__setattr__(self, "proof_obligation", proof_obligation)
        object.__setattr__(self, "paper_trading_required", paper_trading_required)
        object.__setattr__(self, "live_deployment_allowed", live_deployment_allowed)
        object.__setattr__(self, "max_cross_stage_gap", max_cross_stage_gap)
        self.__post_init__()

    def __post_init__(self) -> None:
        required_gluing_obligations = tuple(sorted(set(self.required_gluing_obligations)))
        required_risk_invariants = tuple(sorted(set(self.required_risk_invariants)))
        required_audit_metadata_keys = tuple(sorted(set(self.required_audit_metadata_keys)))
        max_cross_stage_gap = _quantize_fraction(
            _coerce_decimal(self.max_cross_stage_gap, "max_cross_stage_gap")
        )
        if not required_gluing_obligations:
            raise MainNormalizationError("MainPolicy requires gluing obligations.")
        if not required_risk_invariants:
            raise MainNormalizationError("MainPolicy requires risk invariants.")
        if not required_audit_metadata_keys:
            raise MainNormalizationError("MainPolicy requires audit metadata keys.")
        _validate_probability(max_cross_stage_gap, "max_cross_stage_gap")
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise MainNormalizationError("MainPolicy proof_obligation is unsupported.")
        object.__setattr__(self, "required_gluing_obligations", required_gluing_obligations)
        object.__setattr__(self, "required_risk_invariants", required_risk_invariants)
        object.__setattr__(self, "required_audit_metadata_keys", required_audit_metadata_keys)
        object.__setattr__(self, "max_cross_stage_gap", max_cross_stage_gap)

    def reproducibility_signature(self) -> str:
        return _stable_digest(
            [
                *self.required_gluing_obligations,
                *self.required_risk_invariants,
                *self.required_audit_metadata_keys,
                self.proof_obligation,
                str(self.paper_trading_required),
                str(self.live_deployment_allowed),
                str(self.max_cross_stage_gap),
            ]
        )


@dataclass(frozen=True, init=False)
class MainGluingCertificate:
    """One global gluing witness discharged at the main boundary."""

    name: str
    source_stages: tuple[str, ...]
    observed_value: str
    expected_value: str
    h1_obstruction: Decimal
    passes: bool
    message: str
    data_signature: str

    def __init__(
        self,
        name: str,
        source_stages: tuple[str, ...],
        observed_value: str,
        expected_value: str,
        h1_obstruction: Decimal,
        passes: bool,
        message: str,
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "source_stages", tuple(source_stages))
        object.__setattr__(self, "observed_value", observed_value)
        object.__setattr__(self, "expected_value", expected_value)
        object.__setattr__(self, "h1_obstruction", h1_obstruction)
        object.__setattr__(self, "passes", passes)
        object.__setattr__(self, "message", message)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        object.__setattr__(self, "source_stages", tuple(self.source_stages))
        object.__setattr__(
            self,
            "h1_obstruction",
            _quantize_fraction(_coerce_decimal(self.h1_obstruction, "h1_obstruction")),
        )
        _validate_probability(self.h1_obstruction, "h1_obstruction")
        if not self.name.strip():
            raise MainNormalizationError("MainGluingCertificate requires a name.")
        if not self.source_stages:
            raise MainNormalizationError("MainGluingCertificate requires source stages.")
        if (
            not self.observed_value.strip()
            or not self.expected_value.strip()
            or not self.message.strip()
            or not self.data_signature
        ):
            raise MainNormalizationError(
                "MainGluingCertificate requires observed, expected, message, and signature fields."
            )


@dataclass(frozen=True, init=False)
class RuntimeDeploymentPlan:
    """Concrete paper-trading run plan descended from the verified bundle chain."""

    entrypoint: str
    deployment_mode: DeploymentMode
    stage_order: tuple[str, ...]
    symbols: tuple[str, ...]
    validated_stages: tuple[str, ...]
    orders_ready: int
    orders_may_route: bool
    kill_switch_state: KillSwitchState
    paper_trading_required: bool
    live_deployment_allowed: bool
    proof_obligation: MainProofMode
    runbook: tuple[str, ...]
    environment: tuple[tuple[str, str], ...]
    data_signature: str

    def __init__(
        self,
        entrypoint: str,
        deployment_mode: DeploymentMode,
        stage_order: tuple[str, ...],
        symbols: tuple[str, ...],
        validated_stages: tuple[str, ...],
        orders_ready: int,
        orders_may_route: bool,
        kill_switch_state: KillSwitchState,
        paper_trading_required: bool,
        live_deployment_allowed: bool,
        proof_obligation: MainProofMode,
        runbook: tuple[str, ...],
        environment: tuple[tuple[str, str], ...],
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "entrypoint", entrypoint)
        object.__setattr__(self, "deployment_mode", deployment_mode)
        object.__setattr__(self, "stage_order", tuple(stage_order))
        object.__setattr__(self, "symbols", tuple(symbols))
        object.__setattr__(self, "validated_stages", tuple(validated_stages))
        object.__setattr__(self, "orders_ready", orders_ready)
        object.__setattr__(self, "orders_may_route", orders_may_route)
        object.__setattr__(self, "kill_switch_state", kill_switch_state)
        object.__setattr__(self, "paper_trading_required", paper_trading_required)
        object.__setattr__(self, "live_deployment_allowed", live_deployment_allowed)
        object.__setattr__(self, "proof_obligation", proof_obligation)
        object.__setattr__(self, "runbook", tuple(runbook))
        object.__setattr__(self, "environment", tuple(environment))
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        stage_order = tuple(self.stage_order)
        symbols = tuple(_normalize_symbol(symbol) for symbol in self.symbols)
        validated_stages = tuple(self.validated_stages)
        runbook = tuple(self.runbook)
        environment = tuple(self.environment)
        if self.deployment_mode != "paper":
            raise MainNormalizationError("RuntimeDeploymentPlan only supports paper mode.")
        if stage_order != STAGE_ORDER:
            raise MainNormalizationError("RuntimeDeploymentPlan stage_order must match the global order.")
        if self.orders_ready < 0:
            raise MainNormalizationError("RuntimeDeploymentPlan orders_ready must be non-negative.")
        if self.kill_switch_state not in {"armed", "engaged"}:
            raise MainNormalizationError("RuntimeDeploymentPlan kill_switch_state is invalid.")
        if self.kill_switch_state == "engaged" and self.orders_may_route:
            raise MainNormalizationError(
                "RuntimeDeploymentPlan cannot route orders while the kill switch is engaged."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise MainNormalizationError("RuntimeDeploymentPlan proof_obligation is invalid.")
        if not self.entrypoint.strip() or not runbook or not environment or not self.data_signature:
            raise MainNormalizationError(
                "RuntimeDeploymentPlan requires entrypoint, runbook, environment, and data signature."
            )
        object.__setattr__(self, "stage_order", stage_order)
        object.__setattr__(self, "symbols", symbols)
        object.__setattr__(self, "validated_stages", validated_stages)
        object.__setattr__(self, "runbook", runbook)
        object.__setattr__(self, "environment", environment)


@dataclass(frozen=True, init=False)
class MainResearchIdea:
    """A top-level, testable market idea glued across every pipeline stage."""

    symbol: str
    as_of: datetime
    side: MainIdeaSide
    hypothesis: str
    validation_plan: str
    stage_lineage: tuple[str, ...]
    stage_support_count: int
    topology_alignment: Decimal
    proof_confidence: Decimal
    expected_edge_bps: Decimal
    provenance: str
    data_signature: str

    def __init__(
        self,
        symbol: str,
        as_of: datetime,
        side: MainIdeaSide,
        hypothesis: str,
        validation_plan: str,
        stage_lineage: tuple[str, ...],
        stage_support_count: int,
        topology_alignment: Decimal,
        proof_confidence: Decimal,
        expected_edge_bps: Decimal,
        provenance: str,
        data_signature: str,
    ) -> None:
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "as_of", as_of)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "hypothesis", hypothesis)
        object.__setattr__(self, "validation_plan", validation_plan)
        object.__setattr__(self, "stage_lineage", tuple(stage_lineage))
        object.__setattr__(self, "stage_support_count", stage_support_count)
        object.__setattr__(self, "topology_alignment", topology_alignment)
        object.__setattr__(self, "proof_confidence", proof_confidence)
        object.__setattr__(self, "expected_edge_bps", expected_edge_bps)
        object.__setattr__(self, "provenance", provenance)
        object.__setattr__(self, "data_signature", data_signature)
        self.__post_init__()

    def __post_init__(self) -> None:
        object.__setattr__(self, "symbol", _normalize_symbol(self.symbol))
        object.__setattr__(self, "as_of", _normalize_timestamp(self.as_of, "as_of"))
        object.__setattr__(self, "stage_lineage", tuple(self.stage_lineage))
        object.__setattr__(
            self,
            "topology_alignment",
            _quantize_fraction(_coerce_decimal(self.topology_alignment, "topology_alignment")),
        )
        object.__setattr__(
            self,
            "proof_confidence",
            _quantize_fraction(_coerce_decimal(self.proof_confidence, "proof_confidence")),
        )
        object.__setattr__(
            self,
            "expected_edge_bps",
            _quantize_bps(_coerce_decimal(self.expected_edge_bps, "expected_edge_bps")),
        )
        if self.side not in {"long", "short"}:
            raise MainNormalizationError("MainResearchIdea side must be 'long' or 'short'.")
        if self.stage_support_count < 1 or not self.stage_lineage:
            raise MainNormalizationError(
                "MainResearchIdea requires at least one supporting stage."
            )
        _validate_probability(self.topology_alignment, "topology_alignment")
        _validate_probability(self.proof_confidence, "proof_confidence")
        _validate_positive_decimal(self.expected_edge_bps, "expected_edge_bps")
        if (
            not self.hypothesis.strip()
            or not self.validation_plan.strip()
            or not self.provenance.strip()
            or not self.data_signature
        ):
            raise MainNormalizationError(
                "MainResearchIdea requires narrative fields and a reproducibility signature."
            )


@dataclass(frozen=True, init=False)
class MainFormalVerification:
    """Machine-checkable proof evidence emitted by the main boundary."""

    property_name: str
    source: str
    solver: str
    proof_obligation: MainProofMode
    result: MainVerificationResult
    message: str
    data_signature: str

    def __init__(
        self,
        property_name: str,
        source: str,
        solver: str,
        proof_obligation: MainProofMode,
        result: MainVerificationResult,
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
            raise MainNormalizationError(
                "MainFormalVerification requires property, source, and solver names."
            )
        if self.proof_obligation not in {"smt_required", "machine_checked"}:
            raise MainNormalizationError("MainFormalVerification proof_obligation is invalid.")
        if self.result not in {"proved", "failed"}:
            raise MainNormalizationError("MainFormalVerification result is invalid.")
        if not self.message.strip() or not self.data_signature:
            raise MainNormalizationError(
                "MainFormalVerification requires a message and data signature."
            )


@dataclass(frozen=True, init=False)
class MainBundle:
    """The fully glued, runnable, and verified trading platform bundle."""

    schema_version: str
    request_signature: str
    market_data_bundle: MarketDataBundle
    signal_geometry_bundle: SignalGeometryBundle
    strategy_kernel_bundle: StrategyKernelBundle
    risk_engine_bundle: RiskEngineBundle
    execution_bundle: ExecutionBundle
    portfolio_bundle: PortfolioBundle
    compliance_bundle: ComplianceBundle
    system_policy: MainPolicy
    stage_summaries: tuple[tuple[str, str], ...]
    gluing_certificates: tuple[MainGluingCertificate, ...]
    deployment_plan: RuntimeDeploymentPlan
    formal_verification: tuple[MainFormalVerification, ...]
    research_ideas: tuple[MainResearchIdea, ...]
    pipeline_cocycle_signature: str
    data_signature: str
    audit_metadata: tuple[tuple[str, str], ...]

    def __init__(
        self,
        schema_version: str,
        request_signature: str,
        market_data_bundle: MarketDataBundle,
        signal_geometry_bundle: SignalGeometryBundle,
        strategy_kernel_bundle: StrategyKernelBundle,
        risk_engine_bundle: RiskEngineBundle,
        execution_bundle: ExecutionBundle,
        portfolio_bundle: PortfolioBundle,
        compliance_bundle: ComplianceBundle,
        system_policy: MainPolicy,
        stage_summaries: tuple[tuple[str, str], ...],
        gluing_certificates: tuple[MainGluingCertificate, ...],
        deployment_plan: RuntimeDeploymentPlan,
        formal_verification: tuple[MainFormalVerification, ...],
        research_ideas: tuple[MainResearchIdea, ...],
        pipeline_cocycle_signature: str,
        data_signature: str,
        audit_metadata: tuple[tuple[str, str], ...],
    ) -> None:
        object.__setattr__(self, "schema_version", schema_version)
        object.__setattr__(self, "request_signature", request_signature)
        object.__setattr__(self, "market_data_bundle", market_data_bundle)
        object.__setattr__(self, "signal_geometry_bundle", signal_geometry_bundle)
        object.__setattr__(self, "strategy_kernel_bundle", strategy_kernel_bundle)
        object.__setattr__(self, "risk_engine_bundle", risk_engine_bundle)
        object.__setattr__(self, "execution_bundle", execution_bundle)
        object.__setattr__(self, "portfolio_bundle", portfolio_bundle)
        object.__setattr__(self, "compliance_bundle", compliance_bundle)
        object.__setattr__(self, "system_policy", system_policy)
        object.__setattr__(self, "stage_summaries", tuple(stage_summaries))
        object.__setattr__(
            self,
            "gluing_certificates",
            tuple(gluing_certificates),
        )
        object.__setattr__(self, "deployment_plan", deployment_plan)
        object.__setattr__(
            self,
            "formal_verification",
            tuple(formal_verification),
        )
        object.__setattr__(self, "research_ideas", tuple(research_ideas))
        object.__setattr__(
            self,
            "pipeline_cocycle_signature",
            pipeline_cocycle_signature,
        )
        object.__setattr__(self, "data_signature", data_signature)
        object.__setattr__(self, "audit_metadata", tuple(audit_metadata))
        self.__post_init__()

    def __post_init__(self) -> None:
        if self.schema_version != main_schema_version():
            raise MainNormalizationError("MainBundle schema_version mismatch.")
        stage_summaries = tuple(self.stage_summaries)
        gluing_certificates = tuple(self.gluing_certificates)
        formal_verification = tuple(self.formal_verification)
        research_ideas = tuple(self.research_ideas)
        audit_metadata = tuple(self.audit_metadata)
        if tuple(name for name, _ in stage_summaries) != STAGE_ORDER[:-1]:
            raise MainNormalizationError("MainBundle stage_summaries must cover the upstream stages.")
        if not self.request_signature or not self.pipeline_cocycle_signature or not self.data_signature:
            raise MainNormalizationError("MainBundle requires stable reproducibility signatures.")
        if not gluing_certificates or not formal_verification or not research_ideas:
            raise MainNormalizationError(
                "MainBundle requires gluing certificates, formal verification, and research ideas."
            )
        if not audit_metadata:
            raise MainNormalizationError("MainBundle requires audit metadata.")
        object.__setattr__(self, "stage_summaries", stage_summaries)
        object.__setattr__(self, "gluing_certificates", gluing_certificates)
        object.__setattr__(self, "formal_verification", formal_verification)
        object.__setattr__(self, "research_ideas", research_ideas)
        object.__setattr__(self, "audit_metadata", audit_metadata)

    @property
    def symbols(self) -> tuple[str, ...]:
        return self.compliance_bundle.symbols

    def summary(self) -> str:
        return main_summary(self)


@dataclass(frozen=True, init=False)
class MainValidationReport:
    """Deterministic validation report for the global system bundle."""

    passes: bool
    all_stage_reports_pass: bool
    restrictions_preserve_invariants: bool
    signature_descent_closed: bool
    alpha_sections_coherent: bool
    risk_bounds_align: bool
    only_risk_approved_descend: bool
    novel_idea_present: bool
    risk_invariants_explicit: bool
    formal_proofs_verified: bool
    proof_obligation_satisfied: bool
    paper_trading_enforced: bool
    runtime_plan_runnable: bool
    kill_switch_fail_safe: bool
    audit_metadata_complete: bool
    stage_order_complete: bool
    signature_matches: bool
    gluing_certificates_checked: int
    proofs_checked: int
    messages: tuple[str, ...]

    def __init__(
        self,
        passes: bool,
        all_stage_reports_pass: bool,
        restrictions_preserve_invariants: bool,
        signature_descent_closed: bool,
        alpha_sections_coherent: bool,
        risk_bounds_align: bool,
        only_risk_approved_descend: bool,
        novel_idea_present: bool,
        risk_invariants_explicit: bool,
        formal_proofs_verified: bool,
        proof_obligation_satisfied: bool,
        paper_trading_enforced: bool,
        runtime_plan_runnable: bool,
        kill_switch_fail_safe: bool,
        audit_metadata_complete: bool,
        stage_order_complete: bool,
        signature_matches: bool,
        gluing_certificates_checked: int,
        proofs_checked: int,
        messages: tuple[str, ...],
    ) -> None:
        object.__setattr__(self, "passes", passes)
        object.__setattr__(self, "all_stage_reports_pass", all_stage_reports_pass)
        object.__setattr__(
            self,
            "restrictions_preserve_invariants",
            restrictions_preserve_invariants,
        )
        object.__setattr__(self, "signature_descent_closed", signature_descent_closed)
        object.__setattr__(self, "alpha_sections_coherent", alpha_sections_coherent)
        object.__setattr__(self, "risk_bounds_align", risk_bounds_align)
        object.__setattr__(
            self,
            "only_risk_approved_descend",
            only_risk_approved_descend,
        )
        object.__setattr__(self, "novel_idea_present", novel_idea_present)
        object.__setattr__(
            self,
            "risk_invariants_explicit",
            risk_invariants_explicit,
        )
        object.__setattr__(self, "formal_proofs_verified", formal_proofs_verified)
        object.__setattr__(
            self,
            "proof_obligation_satisfied",
            proof_obligation_satisfied,
        )
        object.__setattr__(self, "paper_trading_enforced", paper_trading_enforced)
        object.__setattr__(self, "runtime_plan_runnable", runtime_plan_runnable)
        object.__setattr__(self, "kill_switch_fail_safe", kill_switch_fail_safe)
        object.__setattr__(self, "audit_metadata_complete", audit_metadata_complete)
        object.__setattr__(self, "stage_order_complete", stage_order_complete)
        object.__setattr__(self, "signature_matches", signature_matches)
        object.__setattr__(
            self,
            "gluing_certificates_checked",
            gluing_certificates_checked,
        )
        object.__setattr__(self, "proofs_checked", proofs_checked)
        object.__setattr__(self, "messages", tuple(messages))

    def summary(self) -> str:
        status = "pass" if self.passes else "fail"
        issues = "ok" if not self.messages else "; ".join(self.messages)
        return (
            f"validation={status} gluing={self.gluing_certificates_checked} "
            f"proofs={self.proofs_checked} issues={issues}"
        )


def _stage_reports(
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
) -> dict[str, Any]:
    return {
        "market_data": validate_market_data(market_data_bundle),
        "signal_geometry": validate_signal_geometry(signal_geometry_bundle),
        "strategy_kernel": validate_strategy_kernel(strategy_kernel_bundle),
        "risk_engine": validate_risk_engine(risk_engine_bundle),
        "execution": validate_execution(execution_bundle),
        "portfolio": validate_portfolio(portfolio_bundle),
        "compliance": validate_compliance(compliance_bundle),
    }


def _stage_summaries(
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
) -> tuple[tuple[str, str], ...]:
    return (
        ("market_data", market_data_summary(market_data_bundle)),
        ("signal_geometry", signal_geometry_summary(signal_geometry_bundle)),
        ("strategy_kernel", strategy_kernel_summary(strategy_kernel_bundle)),
        ("risk_engine", risk_engine_summary(risk_engine_bundle)),
        ("execution", execution_summary(execution_bundle)),
        ("portfolio", portfolio_summary(portfolio_bundle)),
        ("compliance", compliance_summary(compliance_bundle)),
    )


def _signature_descent_closed(bundle: MainBundle) -> bool:
    return (
        bundle.signal_geometry_bundle.upstream_data_signature == bundle.market_data_bundle.data_signature
        and bundle.strategy_kernel_bundle.upstream_data_signature
        == bundle.signal_geometry_bundle.data_signature
        and bundle.risk_engine_bundle.upstream_data_signature
        == bundle.strategy_kernel_bundle.data_signature
        and bundle.execution_bundle.upstream_data_signature
        == bundle.risk_engine_bundle.data_signature
        and bundle.portfolio_bundle.upstream_data_signature
        == bundle.execution_bundle.data_signature
        and bundle.compliance_bundle.upstream_data_signature
        == bundle.portfolio_bundle.data_signature
    )


def _proof_obligation_satisfied(bundle: MainBundle) -> bool:
    return _proof_modes_consistent(
        bundle.market_data_bundle,
        bundle.signal_geometry_bundle,
        bundle.strategy_kernel_bundle,
        bundle.risk_engine_bundle,
        bundle.execution_bundle,
        bundle.portfolio_bundle,
        bundle.compliance_bundle,
        bundle.system_policy.proof_obligation,
    )


def _proof_modes_consistent(
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
    required_mode: MainProofMode,
) -> bool:
    obligations = (
        market_data_bundle.risk_invariants.proof_obligation,
        signal_geometry_bundle.risk_invariants.proof_obligation,
        strategy_kernel_bundle.risk_policy.proof_obligation,
        risk_engine_bundle.policy.proof_obligation,
        execution_bundle.proof_obligation,
        portfolio_bundle.proof_obligation,
        compliance_bundle.witness_policy.proof_obligation,
        required_mode,
    )
    return len(set(obligations)) == 1 and obligations[0] in {"smt_required", "machine_checked"}


def _paper_trading_enforced(bundle: MainBundle) -> bool:
    return (
        bundle.market_data_bundle.risk_invariants.paper_trading_required
        and bundle.signal_geometry_bundle.risk_invariants.paper_trading_required
        and bundle.strategy_kernel_bundle.risk_policy.paper_trading_required
        and bundle.risk_engine_bundle.policy.paper_trading_required
        and bundle.execution_bundle.paper_trading_required
        and bundle.portfolio_bundle.paper_trading_required
        and bundle.compliance_bundle.witness_policy.paper_trading_required
        and bundle.deployment_plan.paper_trading_required
        and bundle.deployment_plan.deployment_mode == "paper"
    )


def _risk_invariants_explicit(bundle: MainBundle) -> bool:
    invariant_names = {item.invariant_name for item in bundle.compliance_bundle.boundary_evidence}
    portfolio_policy = bundle.portfolio_bundle.policy
    risk_policy = bundle.risk_engine_bundle.policy
    return (
        set(bundle.system_policy.required_risk_invariants).issubset(invariant_names)
        and portfolio_policy.max_symbol_exposure <= portfolio_policy.max_net_exposure
        and portfolio_policy.max_net_exposure <= portfolio_policy.max_gross_leverage
        and portfolio_policy.kill_switch_drawdown > portfolio_policy.max_drawdown
        and risk_policy.max_symbol_exposure <= risk_policy.max_net_exposure
        and risk_policy.max_net_exposure <= risk_policy.max_gross_leverage
        and risk_policy.kill_switch_drawdown > risk_policy.max_drawdown
        and bool(bundle.portfolio_bundle.order_rejection_conditions)
        and bool(bundle.risk_engine_bundle.policy.order_rejection_conditions)
    )


def _runtime_plan_runnable(bundle: MainBundle) -> bool:
    environment = dict(bundle.deployment_plan.environment)
    return (
        bundle.deployment_plan.stage_order == STAGE_ORDER
        and set(bundle.deployment_plan.validated_stages).issubset(set(STAGE_ORDER[:-1]))
        and environment.get("DEPPY_EXECUTION_MODE") == "paper"
        and environment.get("DEPPY_PROOF_MODE") == bundle.system_policy.proof_obligation
        and environment.get("DEPPY_PAPER_TRADING")
        == ("required" if bundle.system_policy.paper_trading_required else "optional")
        and (
            bundle.deployment_plan.kill_switch_state == "engaged"
            or bundle.deployment_plan.orders_ready >= 0
        )
    )


def _formal_proofs_verified(bundle: MainBundle) -> bool:
    return (
        all(item.result == "proved" for item in bundle.portfolio_bundle.formal_verification)
        and all(item.result == "proved" for item in bundle.compliance_bundle.proof_certificates)
        and all(item.result == "proved" for item in bundle.formal_verification)
    )


def _build_certificate(
    *,
    name: str,
    source_stages: Sequence[str],
    observed_value: str,
    expected_value: str,
    h1_obstruction: Decimal,
    passes: bool,
    message: str,
) -> MainGluingCertificate:
    signature = _stable_digest(
        [
            name,
            *source_stages,
            observed_value,
            expected_value,
            str(h1_obstruction),
            str(passes),
            message,
        ]
    )
    return MainGluingCertificate(
        name=name,
        source_stages=tuple(source_stages),
        observed_value=observed_value,
        expected_value=expected_value,
        h1_obstruction=h1_obstruction,
        passes=passes,
        message=message,
        data_signature=signature,
    )


def _build_gluing_certificates(
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
    reports: Mapping[str, Any],
) -> tuple[MainGluingCertificate, ...]:
    restriction_flags = [
        reports["market_data"].timestamp_symbol_invariants_preserved,
        reports["signal_geometry"].timestamp_symbol_invariants_preserved,
        reports["strategy_kernel"].timestamp_symbol_invariants_preserved,
        reports["risk_engine"].timestamp_symbol_invariants_preserved,
        reports["execution"].timestamp_symbol_invariants_preserved,
        reports["portfolio"].timestamp_symbol_invariants_preserved,
    ]
    restriction_passes = all(restriction_flags)
    restriction_certificate = _build_certificate(
        name="restriction_invariants",
        source_stages=STAGE_ORDER[:-1],
        observed_value=f"{sum(restriction_flags)}/{len(restriction_flags)} stages preserve timestamp-symbol restrictions",
        expected_value="all upstream stages preserve timestamp, symbol, and normalization invariants",
        h1_obstruction=_gap_from_bools(restriction_flags),
        passes=restriction_passes,
        message=(
            "restriction maps preserve canonical overlap invariants"
            if restriction_passes
            else "one or more stage restrictions no longer preserve timestamp-symbol normalization"
        ),
    )

    signature_flags = [
        signal_geometry_bundle.upstream_data_signature == market_data_bundle.data_signature,
        strategy_kernel_bundle.upstream_data_signature == signal_geometry_bundle.data_signature,
        risk_engine_bundle.upstream_data_signature == strategy_kernel_bundle.data_signature,
        execution_bundle.upstream_data_signature == risk_engine_bundle.data_signature,
        portfolio_bundle.upstream_data_signature == execution_bundle.data_signature,
        compliance_bundle.upstream_data_signature == portfolio_bundle.data_signature,
    ]
    signature_passes = all(signature_flags)
    signature_certificate = _build_certificate(
        name="signature_descent",
        source_stages=STAGE_ORDER[:-1],
        observed_value=f"{sum(signature_flags)}/{len(signature_flags)} signature links closed",
        expected_value="every upstream_data_signature equals its predecessor data_signature",
        h1_obstruction=_gap_from_bools(signature_flags),
        passes=signature_passes,
        message=(
            "bundle signatures descend coherently across the entire stage chain"
            if signature_passes
            else "the cross-stage signature chain leaves a descent gap"
        ),
    )

    alpha_flags = [
        reports["signal_geometry"].coherent_global_sections,
        reports["strategy_kernel"].coherent_global_sections,
        strategy_kernel_bundle.signal_sections == signal_geometry_bundle.global_sections,
        bool(signal_geometry_bundle.global_sections),
    ]
    alpha_scores = [section.gluing_score for section in signal_geometry_bundle.global_sections] + [
        section.gluing_score for section in strategy_kernel_bundle.global_sections
    ]
    alpha_certificate = _build_certificate(
        name="alpha_strategy_coherence",
        source_stages=("signal_geometry", "strategy_kernel"),
        observed_value=(
            f"signal_sections={len(signal_geometry_bundle.global_sections)} "
            f"strategy_sections={len(strategy_kernel_bundle.global_sections)}"
        ),
        expected_value="glued alpha sections descend unchanged into the strategy kernel input cover",
        h1_obstruction=_quantize_fraction(ONE - _mean_decimal(alpha_scores, FRACTION_QUANTUM)),
        passes=all(alpha_flags),
        message=(
            "alpha signals glue into one coherent strategy section"
            if all(alpha_flags)
            else "strategy input no longer matches the coherent alpha section"
        ),
    )

    risk_flags = [
        reports["strategy_kernel"].intents_align_with_risk_bounds,
        reports["risk_engine"].intents_align_with_risk_bounds,
        strategy_kernel_bundle.position_intents == risk_engine_bundle.position_intents,
        len(risk_engine_bundle.global_sections) <= len(risk_engine_bundle.local_sections),
    ]
    risk_certificate = _build_certificate(
        name="risk_bounds_alignment",
        source_stages=("strategy_kernel", "risk_engine"),
        observed_value=(
            f"strategy_intents={len(strategy_kernel_bundle.position_intents)} "
            f"risk_intents={len(risk_engine_bundle.position_intents)}"
        ),
        expected_value="position intents and risk bounds agree on every overlap",
        h1_obstruction=_gap_from_bools(risk_flags),
        passes=all(risk_flags),
        message=(
            "position intents and risk bounds agree on overlaps"
            if all(risk_flags)
            else "the risk engine no longer receives the exact strategy intent cover"
        ),
    )

    approved_symbols = {intent.symbol for intent in risk_engine_bundle.executable_intents}
    executable_symbols = {intent.symbol for intent in execution_bundle.approved_intents}
    order_symbols = {order.symbol for order in execution_bundle.executable_orders}
    descent_flags = [
        reports["risk_engine"].only_risk_approved_descend,
        reports["execution"].only_risk_approved_descend,
        reports["compliance"].only_risk_approved_descend,
        tuple(risk_engine_bundle.executable_intents) == execution_bundle.approved_intents,
        order_symbols.issubset(approved_symbols),
        executable_symbols == approved_symbols,
    ]
    descent_certificate = _build_certificate(
        name="risk_approved_descent",
        source_stages=("risk_engine", "execution", "compliance"),
        observed_value=(
            f"risk_executable={len(risk_engine_bundle.executable_intents)} "
            f"execution_approved={len(execution_bundle.approved_intents)} "
            f"orders_ready={len(execution_bundle.executable_orders)}"
        ),
        expected_value="only risk-approved intents descend to executable orders",
        h1_obstruction=_gap_from_bools(descent_flags),
        passes=all(descent_flags),
        message=(
            "only risk-approved intents descend to executable orders"
            if all(descent_flags)
            else "a non-approved intent or mismatched order escaped the risk gate"
        ),
    )

    kill_switch_flags = [
        reports["portfolio"].kill_switch_deterministic,
        reports["portfolio"].exposures_within_policy_or_killed,
        reports["portfolio"].drawdown_within_policy_or_killed,
        reports["compliance"].fail_safe_deterministic,
    ]
    kill_switch_certificate = _build_certificate(
        name="fail_safe_kill_switch",
        source_stages=("portfolio", "compliance"),
        observed_value=(
            f"portfolio_status={portfolio_bundle.state.status} "
            f"drawdown={portfolio_bundle.state.drawdown_fraction}"
        ),
        expected_value="execution fails safe with deterministic kill-switch behavior",
        h1_obstruction=_gap_from_bools(kill_switch_flags),
        passes=all(kill_switch_flags),
        message=(
            "kill-switch behavior remains deterministic and fail-safe"
            if all(kill_switch_flags)
            else "kill-switch behavior is no longer deterministic or no longer blocks unsafe exposure"
        ),
    )

    proof_flags = [
        reports["portfolio"].formal_verification_passed,
        reports["compliance"].formal_proofs_verified,
        _proof_modes_consistent(
            market_data_bundle,
            signal_geometry_bundle,
            strategy_kernel_bundle,
            risk_engine_bundle,
            execution_bundle,
            portfolio_bundle,
            compliance_bundle,
            "smt_required",
        ),
    ]
    proof_certificate = _build_certificate(
        name="formal_proof_chain",
        source_stages=("portfolio", "compliance", "main"),
        observed_value=(
            f"portfolio_proofs={len(portfolio_bundle.formal_verification)} "
            f"compliance_proofs={len(compliance_bundle.proof_certificates)}"
        ),
        expected_value="risk-critical logic remains machine-checkable before the runnable plan is emitted",
        h1_obstruction=_gap_from_bools(proof_flags),
        passes=all(proof_flags),
        message=(
            "formal proof chain remains closed at the main boundary"
            if all(proof_flags)
            else "the portfolio-compliance proof chain no longer closes"
        ),
    )

    return (
        restriction_certificate,
        signature_certificate,
        alpha_certificate,
        risk_certificate,
        descent_certificate,
        kill_switch_certificate,
        proof_certificate,
    )


def _best_market_hypothesis(
    symbol: str, hypotheses: Sequence[NovelMarketHypothesis]
) -> NovelMarketHypothesis | None:
    matches = [item for item in hypotheses if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (item.confidence, item.expected_edge_bps, item.gluing_score))


def _best_signal_idea(symbol: str, ideas: Sequence[SignalResearchIdea]) -> SignalResearchIdea | None:
    matches = [item for item in ideas if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (item.conviction, item.expected_edge_bps, item.gluing_score))


def _best_strategy_idea(
    symbol: str, ideas: Sequence[StrategyResearchIdea]
) -> StrategyResearchIdea | None:
    matches = [item for item in ideas if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (item.conviction, item.expected_edge_bps, item.target_fraction))


def _best_risk_idea(symbol: str, ideas: Sequence[RiskResearchIdea]) -> RiskResearchIdea | None:
    matches = [item for item in ideas if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (item.approved_fraction, item.expected_edge_bps))


def _best_execution_idea(
    symbol: str, ideas: Sequence[ExecutionResearchIdea]
) -> ExecutionResearchIdea | None:
    matches = [item for item in ideas if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (item.executable_fraction, item.expected_edge_bps))


def _best_portfolio_idea(
    symbol: str, ideas: Sequence[PortfolioResearchIdea]
) -> PortfolioResearchIdea | None:
    matches = [item for item in ideas if item.symbol == symbol]
    if not matches:
        return None
    return max(matches, key=lambda item: (abs(item.pnl_convexity_bps), abs(item.mark_dislocation_bps)))


def _vote_side(*values: str | None) -> MainIdeaSide:
    votes = [value for value in values if value in {"long", "short"}]
    if not votes:
        return "long"
    counts = Counter(votes)
    if counts["short"] > counts["long"]:
        return "short"
    return "long"


def _discover_main_research_ideas(
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
) -> tuple[MainResearchIdea, ...]:
    ideas: list[MainResearchIdea] = []
    proof_confidence = _mean_decimal(
        [
            _proof_ratio(portfolio_bundle.formal_verification),
            _proof_ratio(compliance_bundle.proof_certificates),
        ],
        FRACTION_QUANTUM,
    )
    for compliance_idea in compliance_bundle.research_ideas:
        symbol = compliance_idea.symbol
        market_idea = _best_market_hypothesis(symbol, market_data_bundle.hypotheses)
        signal_idea = _best_signal_idea(symbol, signal_geometry_bundle.research_ideas)
        strategy_idea = _best_strategy_idea(symbol, strategy_kernel_bundle.research_ideas)
        risk_idea = _best_risk_idea(symbol, risk_engine_bundle.research_ideas)
        execution_idea = _best_execution_idea(symbol, execution_bundle.research_ideas)
        portfolio_idea = _best_portfolio_idea(symbol, portfolio_bundle.research_ideas)
        side = _vote_side(
            compliance_idea.side,
            market_idea.direction if market_idea is not None else None,
            signal_idea.side if signal_idea is not None else None,
            strategy_idea.side if strategy_idea is not None else None,
            risk_idea.side if risk_idea is not None else None,
            execution_idea.side if execution_idea is not None else None,
            portfolio_idea.side if portfolio_idea is not None else None,
        )
        lineage = tuple(
            stage
            for stage, present in (
                ("market_data", market_idea is not None),
                ("signal_geometry", signal_idea is not None),
                ("strategy_kernel", strategy_idea is not None),
                ("risk_engine", risk_idea is not None),
                ("execution", execution_idea is not None),
                ("portfolio", portfolio_idea is not None),
                ("compliance", True),
            )
            if present
        )
        topology_inputs = [compliance_idea.overlap_stability]
        edge_inputs: list[Decimal] = []
        if market_idea is not None:
            topology_inputs.extend((market_idea.confidence, market_idea.gluing_score))
            edge_inputs.append(market_idea.expected_edge_bps)
        if signal_idea is not None:
            topology_inputs.extend((signal_idea.conviction, signal_idea.gluing_score))
            edge_inputs.append(signal_idea.expected_edge_bps)
        if strategy_idea is not None:
            topology_inputs.extend((strategy_idea.conviction, strategy_idea.target_fraction))
            edge_inputs.append(strategy_idea.expected_edge_bps)
        if risk_idea is not None:
            topology_inputs.extend((risk_idea.approved_fraction, risk_idea.residual_drawdown_capacity))
            edge_inputs.append(risk_idea.expected_edge_bps)
        if execution_idea is not None:
            topology_inputs.append(execution_idea.executable_fraction)
            edge_inputs.append(execution_idea.expected_edge_bps)
        if portfolio_idea is not None:
            edge_inputs.append(
                _quantize_bps(
                    max(abs(portfolio_idea.mark_dislocation_bps), abs(portfolio_idea.pnl_convexity_bps))
                )
            )
        topology_alignment = _mean_decimal(topology_inputs, FRACTION_QUANTUM)
        expected_edge_bps = _mean_decimal(edge_inputs, BPS_QUANTUM) if edge_inputs else Decimal("1.0000")
        market_text = market_idea.thesis if market_idea is not None else "the data-derived market baseline"
        signal_text = signal_idea.thesis if signal_idea is not None else "the glued signal section"
        strategy_text = strategy_idea.thesis if strategy_idea is not None else "the coherent strategy section"
        risk_text = risk_idea.thesis if risk_idea is not None else "the risk-approved section"
        execution_text = (
            execution_idea.hypothesis if execution_idea is not None else "the executable paper-trading route"
        )
        portfolio_text = (
            portfolio_idea.hypothesis if portfolio_idea is not None else "the reconciled portfolio identity"
        )
        hypothesis = (
            f"{side} {symbol}: the algebraic-geometry extension predicts that the market thesis "
            f"'{market_text}' survives as a topology-preserving cocycle through signal='{signal_text}', "
            f"strategy='{strategy_text}', risk='{risk_text}', execution='{execution_text}', and "
            f"portfolio='{portfolio_text}', so H^1-stable descent should preserve roughly "
            f"{expected_edge_bps} bps of testable edge."
        )
        validation_plan = (
            "Replay the full pipeline in paper trading with versioned data, configuration, and model artifacts; "
            "preserve immutable audit metadata; block lookahead bias, survivorship bias, and data leakage; "
            f"bucket outcomes by topology_alignment={topology_alignment} and proof_confidence={proof_confidence}; "
            "report risk-adjusted return, tail-risk loss, and stress-scenario loss before any deployment escalation."
        )
        signature = _stable_digest(
            [
                compliance_idea.data_signature,
                market_idea.data_signature if market_idea is not None else "no-market-idea",
                signal_idea.data_signature if signal_idea is not None else "no-signal-idea",
                strategy_idea.data_signature if strategy_idea is not None else "no-strategy-idea",
                risk_idea.data_signature if risk_idea is not None else "no-risk-idea",
                execution_idea.data_signature if execution_idea is not None else "no-execution-idea",
                portfolio_idea.data_signature if portfolio_idea is not None else "no-portfolio-idea",
                hypothesis,
                validation_plan,
            ]
        )
        ideas.append(
            MainResearchIdea(
                symbol=symbol,
                as_of=compliance_idea.as_of,
                side=side,
                hypothesis=hypothesis,
                validation_plan=validation_plan,
                stage_lineage=lineage,
                stage_support_count=len(lineage),
                topology_alignment=topology_alignment,
                proof_confidence=proof_confidence,
                expected_edge_bps=expected_edge_bps,
                provenance="algebraic_geometry_global_gluing",
                data_signature=signature,
            )
        )
    return tuple(sorted(ideas, key=lambda item: (item.as_of, item.symbol, item.side)))


def _deployment_plan_signature(plan: RuntimeDeploymentPlan) -> str:
    return _stable_digest(
        [
            plan.entrypoint,
            plan.deployment_mode,
            *plan.stage_order,
            *plan.symbols,
            *plan.validated_stages,
            str(plan.orders_ready),
            str(plan.orders_may_route),
            plan.kill_switch_state,
            str(plan.paper_trading_required),
            str(plan.live_deployment_allowed),
            plan.proof_obligation,
            *plan.runbook,
            *(f"{key}={value}" for key, value in plan.environment),
        ]
    )


def _build_runtime_plan(
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
    policy: MainPolicy,
    reports: Mapping[str, Any],
) -> RuntimeDeploymentPlan:
    validated_stages = tuple(stage for stage, report in reports.items() if report.passes)
    kill_switch_state: KillSwitchState = (
        "engaged" if portfolio_bundle.state.status == "kill_switch" else "armed"
    )
    orders_ready = len(execution_bundle.executable_orders)
    orders_may_route = kill_switch_state == "armed" and orders_ready > 0
    runbook = (
        f"validate the stage chain rooted at compliance signature {compliance_bundle.data_signature[:16]}",
        f"load versioned market data anchored by execution signature {execution_bundle.data_signature[:16]}",
        "run the strategy, risk, execution, portfolio, and compliance sites in paper-only mode",
        "submit only ready executable orders while the kill switch remains armed",
        "persist immutable audit metadata for every order and risk decision",
    )
    environment = (
        ("DEPPY_EXECUTION_MODE", "paper"),
        ("DEPPY_PAPER_TRADING", "required" if policy.paper_trading_required else "optional"),
        ("DEPPY_PROOF_MODE", policy.proof_obligation),
    )
    unsigned = RuntimeDeploymentPlan(
        entrypoint="deppy.main:build_main",
        deployment_mode="paper",
        stage_order=STAGE_ORDER,
        symbols=compliance_bundle.symbols,
        validated_stages=validated_stages,
        orders_ready=orders_ready,
        orders_may_route=orders_may_route,
        kill_switch_state=kill_switch_state,
        paper_trading_required=policy.paper_trading_required,
        live_deployment_allowed=policy.live_deployment_allowed,
        proof_obligation=policy.proof_obligation,
        runbook=runbook,
        environment=environment,
        data_signature="pending",
    )
    return RuntimeDeploymentPlan(
        entrypoint=unsigned.entrypoint,
        deployment_mode=unsigned.deployment_mode,
        stage_order=unsigned.stage_order,
        symbols=unsigned.symbols,
        validated_stages=unsigned.validated_stages,
        orders_ready=unsigned.orders_ready,
        orders_may_route=unsigned.orders_may_route,
        kill_switch_state=unsigned.kill_switch_state,
        paper_trading_required=unsigned.paper_trading_required,
        live_deployment_allowed=unsigned.live_deployment_allowed,
        proof_obligation=unsigned.proof_obligation,
        runbook=unsigned.runbook,
        environment=unsigned.environment,
        data_signature=_deployment_plan_signature(unsigned),
    )


def _main_verification_signature(
    request_signature: str,
    policy: MainPolicy,
    gluing_certificates: Sequence[MainGluingCertificate],
    deployment_plan: RuntimeDeploymentPlan,
    compliance_bundle: ComplianceBundle,
    portfolio_bundle: PortfolioBundle,
) -> str:
    return _stable_digest(
        [
            request_signature,
            policy.reproducibility_signature(),
            compliance_bundle.data_signature,
            portfolio_bundle.data_signature,
            deployment_plan.data_signature,
            *(certificate.data_signature for certificate in gluing_certificates),
        ]
    )


def _verify_main_with_z3(
    request_signature: str,
    policy: MainPolicy,
    gluing_certificates: Sequence[MainGluingCertificate],
    deployment_plan: RuntimeDeploymentPlan,
    market_data_bundle: MarketDataBundle,
    signal_geometry_bundle: SignalGeometryBundle,
    strategy_kernel_bundle: StrategyKernelBundle,
    risk_engine_bundle: RiskEngineBundle,
    execution_bundle: ExecutionBundle,
    portfolio_bundle: PortfolioBundle,
    compliance_bundle: ComplianceBundle,
    reports: Mapping[str, Any],
) -> tuple[MainFormalVerification, ...]:
    try:
        import z3  # type: ignore[import-untyped]
    except ImportError as exc:  # pragma: no cover
        raise MainVerificationError("z3-solver is required for main verification.") from exc

    verification_signature = _main_verification_signature(
        request_signature,
        policy,
        gluing_certificates,
        deployment_plan,
        compliance_bundle,
        portfolio_bundle,
    )
    certificates: list[MainFormalVerification] = []

    def prove(property_name: str, conclusion: Any, message: str) -> None:
        solver = z3.Solver()
        solver.add(z3.Not(conclusion))
        result = solver.check()
        status: MainVerificationResult = "proved" if result == z3.unsat else "failed"
        certificates.append(
            MainFormalVerification(
                property_name=property_name,
                source="main",
                solver="z3",
                proof_obligation=policy.proof_obligation,
                result=status,
                message=message,
                data_signature=verification_signature,
            )
        )

    signature_chain = (
        signal_geometry_bundle.upstream_data_signature == market_data_bundle.data_signature
        and strategy_kernel_bundle.upstream_data_signature == signal_geometry_bundle.data_signature
        and risk_engine_bundle.upstream_data_signature == strategy_kernel_bundle.data_signature
        and execution_bundle.upstream_data_signature == risk_engine_bundle.data_signature
        and portfolio_bundle.upstream_data_signature == execution_bundle.data_signature
        and compliance_bundle.upstream_data_signature == portfolio_bundle.data_signature
    )
    prove(
        "signature_descent_chain",
        z3.BoolVal(signature_chain),
        "every stage inherits the exact predecessor signature before deployment",
    )
    prove(
        "paper_only_runtime",
        z3.BoolVal(
            deployment_plan.deployment_mode == "paper"
            and (policy.live_deployment_allowed or deployment_plan.deployment_mode == "paper")
        ),
        "the runnable plan remains paper-only unless an explicit live override is allowed",
    )
    prove(
        "risk_approved_gate",
        z3.And(
            z3.IntVal(len(execution_bundle.approved_intents))
            == z3.IntVal(len(risk_engine_bundle.executable_intents)),
            z3.IntVal(len(execution_bundle.executable_orders))
            <= z3.IntVal(len(execution_bundle.approved_intents)),
            z3.BoolVal(
                any(
                    certificate.name == "risk_approved_descent" and certificate.passes
                    for certificate in gluing_certificates
                )
            ),
        ),
        "only risk-approved intents descend to the executable order set",
    )
    prove(
        "kill_switch_blocks_routing",
        z3.BoolVal(
            portfolio_bundle.state.status != "kill_switch" or not deployment_plan.orders_may_route
        ),
        "the runtime plan blocks order routing whenever the kill switch is engaged",
    )
    prove(
        "risk_core_bounds_explicit",
        z3.BoolVal(
            portfolio_bundle.policy.max_symbol_exposure <= portfolio_bundle.policy.max_net_exposure
            and portfolio_bundle.policy.max_net_exposure <= portfolio_bundle.policy.max_gross_leverage
            and portfolio_bundle.policy.kill_switch_drawdown > portfolio_bundle.policy.max_drawdown
            and reports["portfolio"].exposures_within_policy_or_killed
            and reports["portfolio"].drawdown_within_policy_or_killed
        ),
        "max position size, leverage, and drawdown trigger bounds remain explicit or kill the system",
    )
    prove(
        "formal_proof_chain_verified",
        z3.BoolVal(
            all(item.result == "proved" for item in portfolio_bundle.formal_verification)
            and all(item.result == "proved" for item in compliance_bundle.proof_certificates)
            and _proof_modes_consistent(
                market_data_bundle,
                signal_geometry_bundle,
                strategy_kernel_bundle,
                risk_engine_bundle,
                execution_bundle,
                portfolio_bundle,
                compliance_bundle,
                policy.proof_obligation,
            )
        ),
        "the portfolio-compliance proof chain remains machine-checkable at the main boundary",
    )
    return tuple(certificates)


def _build_audit_metadata(
    request_signature: str,
    policy: MainPolicy,
    deployment_plan: RuntimeDeploymentPlan,
    gluing_certificates: Sequence[MainGluingCertificate],
) -> tuple[tuple[str, str], ...]:
    return tuple(
        sorted(
            (
                ("audit_log", "immutable_required"),
                ("deployment_mode", "paper_only_verified"),
                ("gluing_mode", "h1_cocycle_checked"),
                ("integration_mode", "full_pipeline_glued"),
                ("kill_switch_policy", "deterministic_fail_safe_verified"),
                (
                    "paper_trading",
                    "required" if policy.paper_trading_required else "optional",
                ),
                ("proof_obligation", policy.proof_obligation),
                ("reproducibility", "versioned_data_configuration_model_and_signatures"),
                ("request_signature", request_signature[:16]),
                ("separation", "research_simulation_execution_risk_compliance_and_main_are_decoupled"),
                ("stage_order", " -> ".join(STAGE_ORDER)),
                ("validated_stages", ",".join(deployment_plan.validated_stages)),
                ("verified_gluing", ",".join(certificate.name for certificate in gluing_certificates)),
            )
        )
    )


def _main_bundle_signature(bundle: MainBundle) -> str:
    return _stable_digest(
        [
            bundle.schema_version,
            bundle.request_signature,
            bundle.market_data_bundle.data_signature,
            bundle.signal_geometry_bundle.data_signature,
            bundle.strategy_kernel_bundle.data_signature,
            bundle.risk_engine_bundle.data_signature,
            bundle.execution_bundle.data_signature,
            bundle.portfolio_bundle.data_signature,
            bundle.compliance_bundle.data_signature,
            bundle.system_policy.reproducibility_signature(),
            *(f"{name}={summary}" for name, summary in bundle.stage_summaries),
            *(certificate.data_signature for certificate in bundle.gluing_certificates),
            bundle.deployment_plan.data_signature,
            *(item.data_signature for item in bundle.formal_verification),
            *(idea.data_signature for idea in bundle.research_ideas),
            bundle.pipeline_cocycle_signature,
            *(f"{key}={value}" for key, value in bundle.audit_metadata),
        ]
    )


def _pipeline_cocycle_signature(
    request_signature: str,
    stage_summaries: Sequence[tuple[str, str]],
    gluing_certificates: Sequence[MainGluingCertificate],
    deployment_plan: RuntimeDeploymentPlan,
    compliance_bundle: ComplianceBundle,
) -> str:
    return _stable_digest(
        [
            request_signature,
            *(f"{name}={summary}" for name, summary in stage_summaries),
            *(certificate.data_signature for certificate in gluing_certificates),
            deployment_plan.data_signature,
            compliance_bundle.data_signature,
        ]
    )


def build_main(request: MainAssemblyRequest, *, policy: MainPolicy | None = None) -> MainBundle:
    if not isinstance(request, MainAssemblyRequest):
        raise MainNormalizationError("build_main requires a MainAssemblyRequest input.")
    resolved_policy = policy or MainPolicy()
    request_signature = request.reproducibility_signature()

    market_data_bundle = build_market_data(
        request.historical_entries,
        request.live_entries,
        local_entries=request.local_entries,
        local_observer=request.local_observer,
        default_source=request.default_source,
        min_history_points=request.min_history_points,
        min_novelty_lift=request.market_min_novelty_lift,
        min_edge_bps=request.market_min_edge_bps,
        risk_invariants=request.risk_invariants,
    )
    signal_geometry_bundle = build_signal_geometry(
        market_data_bundle,
        min_idea_conviction=request.signal_min_idea_conviction,
        min_idea_novelty=request.signal_min_idea_novelty,
        min_edge_bps=request.signal_min_edge_bps,
    )
    strategy_kernel_bundle = build_strategy_kernel(
        signal_geometry_bundle,
        min_conviction=request.strategy_min_conviction,
        min_target_fraction=request.strategy_min_target_fraction,
    )
    risk_engine_bundle = build_risk_engine(
        strategy_kernel_bundle,
        policy=request.risk_policy,
        min_approval_fraction=request.risk_min_approval_fraction,
    )
    execution_bundle = build_execution(
        risk_engine_bundle,
        quotes_by_symbol=request.quotes_by_symbol,
        policy=request.execution_policy,
        min_order_fraction=request.execution_min_order_fraction,
        starting_cash_balance=request.starting_cash_balance,
    )
    portfolio_bundle = build_portfolio(
        execution_bundle,
        policy=request.portfolio_policy,
        mark_price_by_symbol=request.mark_price_by_symbol,
    )
    compliance_bundle = build_compliance(
        portfolio_bundle,
        policy=request.compliance_policy,
    )
    reports = _stage_reports(
        market_data_bundle,
        signal_geometry_bundle,
        strategy_kernel_bundle,
        risk_engine_bundle,
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
    )
    stage_summaries = _stage_summaries(
        market_data_bundle,
        signal_geometry_bundle,
        strategy_kernel_bundle,
        risk_engine_bundle,
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
    )
    gluing_certificates = _build_gluing_certificates(
        market_data_bundle,
        signal_geometry_bundle,
        strategy_kernel_bundle,
        risk_engine_bundle,
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
        reports,
    )
    deployment_plan = _build_runtime_plan(
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
        resolved_policy,
        reports,
    )
    formal_verification = _verify_main_with_z3(
        request_signature,
        resolved_policy,
        gluing_certificates,
        deployment_plan,
        market_data_bundle,
        signal_geometry_bundle,
        strategy_kernel_bundle,
        risk_engine_bundle,
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
        reports,
    )
    research_ideas = _discover_main_research_ideas(
        market_data_bundle,
        signal_geometry_bundle,
        strategy_kernel_bundle,
        risk_engine_bundle,
        execution_bundle,
        portfolio_bundle,
        compliance_bundle,
    )
    if not research_ideas:
        raise MainNormalizationError(
            "build_main requires at least one end-to-end research idea after gluing."
        )
    audit_metadata = _build_audit_metadata(
        request_signature,
        resolved_policy,
        deployment_plan,
        gluing_certificates,
    )
    pipeline_signature = _pipeline_cocycle_signature(
        request_signature,
        stage_summaries,
        gluing_certificates,
        deployment_plan,
        compliance_bundle,
    )
    unsigned_bundle = MainBundle(
        schema_version=main_schema_version(),
        request_signature=request_signature,
        market_data_bundle=market_data_bundle,
        signal_geometry_bundle=signal_geometry_bundle,
        strategy_kernel_bundle=strategy_kernel_bundle,
        risk_engine_bundle=risk_engine_bundle,
        execution_bundle=execution_bundle,
        portfolio_bundle=portfolio_bundle,
        compliance_bundle=compliance_bundle,
        system_policy=resolved_policy,
        stage_summaries=stage_summaries,
        gluing_certificates=gluing_certificates,
        deployment_plan=deployment_plan,
        formal_verification=formal_verification,
        research_ideas=research_ideas,
        pipeline_cocycle_signature=pipeline_signature,
        data_signature="pending",
        audit_metadata=audit_metadata,
    )
    return MainBundle(
        schema_version=unsigned_bundle.schema_version,
        request_signature=unsigned_bundle.request_signature,
        market_data_bundle=unsigned_bundle.market_data_bundle,
        signal_geometry_bundle=unsigned_bundle.signal_geometry_bundle,
        strategy_kernel_bundle=unsigned_bundle.strategy_kernel_bundle,
        risk_engine_bundle=unsigned_bundle.risk_engine_bundle,
        execution_bundle=unsigned_bundle.execution_bundle,
        portfolio_bundle=unsigned_bundle.portfolio_bundle,
        compliance_bundle=unsigned_bundle.compliance_bundle,
        system_policy=unsigned_bundle.system_policy,
        stage_summaries=unsigned_bundle.stage_summaries,
        gluing_certificates=unsigned_bundle.gluing_certificates,
        deployment_plan=unsigned_bundle.deployment_plan,
        formal_verification=unsigned_bundle.formal_verification,
        research_ideas=unsigned_bundle.research_ideas,
        pipeline_cocycle_signature=unsigned_bundle.pipeline_cocycle_signature,
        data_signature=_main_bundle_signature(unsigned_bundle),
        audit_metadata=unsigned_bundle.audit_metadata,
    )


def validate_main(bundle: MainBundle) -> MainValidationReport:
    reports = _stage_reports(
        bundle.market_data_bundle,
        bundle.signal_geometry_bundle,
        bundle.strategy_kernel_bundle,
        bundle.risk_engine_bundle,
        bundle.execution_bundle,
        bundle.portfolio_bundle,
        bundle.compliance_bundle,
    )
    certificate_by_name = {certificate.name: certificate for certificate in bundle.gluing_certificates}
    required_certificates_present = all(
        name in certificate_by_name for name in bundle.system_policy.required_gluing_obligations
    )
    restrictions_preserve_invariants = (
        required_certificates_present
        and certificate_by_name["restriction_invariants"].passes
    )
    signature_descent_closed = (
        required_certificates_present
        and certificate_by_name["signature_descent"].passes
        and _signature_descent_closed(bundle)
    )
    alpha_sections_coherent = (
        required_certificates_present
        and certificate_by_name["alpha_strategy_coherence"].passes
    )
    risk_bounds_align = (
        required_certificates_present
        and certificate_by_name["risk_bounds_alignment"].passes
    )
    only_risk_approved_descend = (
        required_certificates_present
        and certificate_by_name["risk_approved_descent"].passes
    )
    kill_switch_fail_safe = (
        required_certificates_present
        and certificate_by_name["fail_safe_kill_switch"].passes
        and (
            bundle.deployment_plan.kill_switch_state != "engaged"
            or not bundle.deployment_plan.orders_may_route
        )
    )
    formal_proofs_verified = (
        required_certificates_present
        and certificate_by_name["formal_proof_chain"].passes
        and _formal_proofs_verified(bundle)
    )
    all_stage_reports_pass = all(report.passes for report in reports.values())
    novel_idea_present = bool(bundle.research_ideas)
    risk_invariants_explicit = _risk_invariants_explicit(bundle)
    proof_obligation_satisfied = _proof_obligation_satisfied(bundle)
    paper_trading_enforced = _paper_trading_enforced(bundle)
    runtime_plan_runnable = _runtime_plan_runnable(bundle)
    audit_metadata = dict(bundle.audit_metadata)
    audit_metadata_complete = all(
        key in audit_metadata for key in bundle.system_policy.required_audit_metadata_keys
    ) and audit_metadata.get("audit_log") == "immutable_required"
    stage_order_complete = (
        tuple(name for name, _ in bundle.stage_summaries) == STAGE_ORDER[:-1]
        and bundle.deployment_plan.stage_order == STAGE_ORDER
    )
    signature_matches = bundle.data_signature == _main_bundle_signature(bundle)

    messages: list[str] = []
    if not all_stage_reports_pass:
        messages.append("one or more upstream stage validations no longer pass")
    if not restrictions_preserve_invariants:
        messages.append("restriction invariants no longer close on the global cover")
    if not signature_descent_closed:
        messages.append("cross-stage signature descent no longer closes")
    if not alpha_sections_coherent:
        messages.append("alpha sections no longer glue coherently into strategy")
    if not risk_bounds_align:
        messages.append("position intents and risk bounds no longer agree on overlaps")
    if not only_risk_approved_descend:
        messages.append("a non-approved intent can now descend toward executable orders")
    if not novel_idea_present:
        messages.append("no end-to-end data-driven research idea is present")
    if not risk_invariants_explicit:
        messages.append("risk-critical invariants are not explicit enough at the main boundary")
    if not formal_proofs_verified:
        messages.append("top-level formal proof chain no longer verifies")
    if not proof_obligation_satisfied:
        messages.append("proof obligations are inconsistent across the stage chain")
    if not paper_trading_enforced:
        messages.append("paper-trading enforcement no longer holds end to end")
    if not runtime_plan_runnable:
        messages.append("runtime deployment plan is no longer internally coherent")
    if not kill_switch_fail_safe:
        messages.append("kill-switch behavior is no longer fail-safe")
    if not audit_metadata_complete:
        messages.append("audit metadata is incomplete or no longer immutable")
    if not stage_order_complete:
        messages.append("stage order or stage summaries are incomplete")
    if not signature_matches:
        messages.append("main bundle reproducibility signature mismatch")

    passes = (
        all_stage_reports_pass
        and restrictions_preserve_invariants
        and signature_descent_closed
        and alpha_sections_coherent
        and risk_bounds_align
        and only_risk_approved_descend
        and novel_idea_present
        and risk_invariants_explicit
        and formal_proofs_verified
        and proof_obligation_satisfied
        and paper_trading_enforced
        and runtime_plan_runnable
        and kill_switch_fail_safe
        and audit_metadata_complete
        and stage_order_complete
        and signature_matches
    )
    return MainValidationReport(
        passes=passes,
        all_stage_reports_pass=all_stage_reports_pass,
        restrictions_preserve_invariants=restrictions_preserve_invariants,
        signature_descent_closed=signature_descent_closed,
        alpha_sections_coherent=alpha_sections_coherent,
        risk_bounds_align=risk_bounds_align,
        only_risk_approved_descend=only_risk_approved_descend,
        novel_idea_present=novel_idea_present,
        risk_invariants_explicit=risk_invariants_explicit,
        formal_proofs_verified=formal_proofs_verified,
        proof_obligation_satisfied=proof_obligation_satisfied,
        paper_trading_enforced=paper_trading_enforced,
        runtime_plan_runnable=runtime_plan_runnable,
        kill_switch_fail_safe=kill_switch_fail_safe,
        audit_metadata_complete=audit_metadata_complete,
        stage_order_complete=stage_order_complete,
        signature_matches=signature_matches,
        gluing_certificates_checked=len(bundle.gluing_certificates),
        proofs_checked=len(bundle.formal_verification),
        messages=tuple(messages),
    )


def main_summary(bundle: MainBundle) -> str:
    report = validate_main(bundle)
    status = "pass" if report.passes else "fail"
    idea_preview = ", ".join(
        f"{idea.symbol}:{idea.side}:{idea.expected_edge_bps}"
        for idea in bundle.research_ideas[:3]
    )
    if not idea_preview:
        idea_preview = "none"
    return (
        f"main[{bundle.schema_version}] symbols={','.join(bundle.symbols) or 'none'} "
        f"stages={len(bundle.stage_summaries) + 1} "
        f"ready_orders={bundle.deployment_plan.orders_ready} "
        f"kill_switch={bundle.deployment_plan.kill_switch_state} "
        f"validation={status} proof={bundle.system_policy.proof_obligation} "
        f"paper_only={bundle.deployment_plan.deployment_mode == 'paper'} "
        f"signature={bundle.data_signature[:12]} ideas_preview={idea_preview}"
    )


__all__ = [
    "DEFAULT_REQUIRED_AUDIT_METADATA_KEYS",
    "DEFAULT_REQUIRED_GLUING_OBLIGATIONS",
    "DEFAULT_REQUIRED_RISK_INVARIANTS",
    "MAIN_SCHEMA_VERSION",
    "MainAssemblyRequest",
    "MainBundle",
    "MainError",
    "MainFormalVerification",
    "MainGluingCertificate",
    "MainIdeaSide",
    "MainNormalizationError",
    "MainPolicy",
    "MainResearchIdea",
    "MainValidationReport",
    "MainVerificationError",
    "MainVerificationResult",
    "RuntimeDeploymentPlan",
    "STAGE_ORDER",
    "build_main",
    "main_schema_version",
    "main_summary",
    "validate_main",
]
