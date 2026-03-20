"""Typed software-engineering chart for research-to-execution market descent.

This module realizes a local chart in the market-data domain model where
historical and live sections are glued into typed strategy sections, checked
against explicit risk invariants, and only then descended into executable order
intents.  The chart is deterministic and auditable: discovered hypotheses,
execution cost assumptions, parameter snapshots, overlap metadata, and order
surfaces all carry reproducibility signatures so research and live trading share
one typed interface without simulation-production drift.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from hashlib import sha256
from importlib import import_module
from typing import Any, Iterable, Literal, Mapping, Sequence

from deppy.market_data import (
    MarketDataBundle,
    RiskInvariantSpecification,
    build_market_data,
    market_data_summary,
    validate_market_data,
)

MODULE_VERSION = "market_data__domain_model_software_engineering_chart.v1"
PRICE_QUANTUM = Decimal("0.000001")
BPS_QUANTUM = Decimal("0.0001")
FRACTION_QUANTUM = Decimal("0.0000001")
ZERO = Decimal("0")
ONE = Decimal("1")
ExecutionMode = Literal["research", "paper", "live"]
_IDEATION_MODULE = "deppy.market_data__domain_model_ideation_software_engineering_section"


class DomainModelSoftwareEngineeringChartError(ValueError):
    """Base error raised by the software-engineering chart."""


class DomainModelSoftwareEngineeringChartValidationError(DomainModelSoftwareEngineeringChartError):
    """Raised when typed chart construction or validation fails."""


class DomainModelSoftwareEngineeringChartDependencyError(DomainModelSoftwareEngineeringChartError):
    """Raised when a required overlap dependency is unavailable."""


def _quantize(value: Decimal, quantum: Decimal) -> Decimal:
    return value.quantize(quantum, rounding=ROUND_HALF_EVEN)


def _stable_digest(parts: Sequence[str]) -> str:
    return sha256("\x1f".join((MODULE_VERSION, *parts)).encode("utf-8")).hexdigest()


def _coerce_decimal(value: Any, field_name: str, *, quantum: Decimal = FRACTION_QUANTUM) -> Decimal:
    try:
        candidate = value if isinstance(value, Decimal) else Decimal(str(value).strip())
    except (AttributeError, InvalidOperation, ValueError) as exc:
        raise DomainModelSoftwareEngineeringChartValidationError(
            f"Field '{field_name}' must be numeric, got {value!r}."
        ) from exc
    if not candidate.is_finite():
        raise DomainModelSoftwareEngineeringChartValidationError(f"Field '{field_name}' must be finite.")
    return _quantize(candidate, quantum)


def _clamp_probability(value: Decimal) -> Decimal:
    return _quantize(min(max(value, ZERO), ONE), FRACTION_QUANTUM)


def _stringify(value: Any) -> Any:
    if isinstance(value, Decimal):
        return format(value, "f")
    if isinstance(value, datetime):
        return value.isoformat()
    if isinstance(value, tuple):
        return [_stringify(item) for item in value]
    if isinstance(value, list):
        return [_stringify(item) for item in value]
    if isinstance(value, dict):
        return {str(key): _stringify(item) for key, item in value.items()}
    return value


# @ensure("minimum-bound obligation is computed on a shared numeric lattice")
def x_at_least_min_value(x: int | Decimal, min_value: int | Decimal) -> bool:
    return Decimal(str(x)) >= Decimal(str(min_value))


# @require("historical support and live support are present before chart construction")
def precondition_holds(
    historical_entries: Sequence[Any],
    live_entries: Sequence[Any],
    *,
    min_value: int = 1,
) -> bool:
    return x_at_least_min_value(len(historical_entries), min_value) and bool(live_entries)


@dataclass(frozen=True)
class ExperimentSnapshot:
    data_signature: str
    deterministic_seed: int
    parameter_snapshot: tuple[tuple[str, str], ...]
    dependency_state: str
    overlap_signature: str

    def reproducibility_signature(self) -> str:
        return _stable_digest(
            [
                self.data_signature,
                str(self.deterministic_seed),
                self.dependency_state,
                self.overlap_signature,
                *(f"{key}={value}" for key, value in self.parameter_snapshot),
            ]
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "data_signature": self.data_signature,
            "deterministic_seed": self.deterministic_seed,
            "parameter_snapshot": [{"name": key, "value": value} for key, value in self.parameter_snapshot],
            "dependency_state": self.dependency_state,
            "overlap_signature": self.overlap_signature,
            "reproducibility_signature": self.reproducibility_signature(),
        }


@dataclass(frozen=True)
class ExecutionCostEnvelope:
    transaction_cost_bps: Decimal
    slippage_bps: Decimal
    latency_ms: int
    partial_fill_ratio: Decimal
    total_cost_bps: Decimal

    def __post_init__(self) -> None:
        if self.latency_ms < 0:
            raise DomainModelSoftwareEngineeringChartValidationError("Latency must be non-negative.")
        for field_name, value in (
            ("transaction_cost_bps", self.transaction_cost_bps),
            ("slippage_bps", self.slippage_bps),
            ("partial_fill_ratio", self.partial_fill_ratio),
            ("total_cost_bps", self.total_cost_bps),
        ):
            if not value.is_finite() or value < ZERO:
                raise DomainModelSoftwareEngineeringChartValidationError(
                    f"Execution-cost field '{field_name}' must be finite and non-negative."
                )
        if _clamp_probability(self.partial_fill_ratio) != self.partial_fill_ratio:
            raise DomainModelSoftwareEngineeringChartValidationError("Partial-fill ratio must lie in [0, 1].")

    def to_dict(self) -> dict[str, Any]:
        return {
            "transaction_cost_bps": _stringify(self.transaction_cost_bps),
            "slippage_bps": _stringify(self.slippage_bps),
            "latency_ms": self.latency_ms,
            "partial_fill_ratio": _stringify(self.partial_fill_ratio),
            "total_cost_bps": _stringify(self.total_cost_bps),
        }


@dataclass(frozen=True)
class StrategySection:
    symbol: str
    as_of: datetime
    direction: Literal["long", "short"]
    regime: str
    thesis: str
    validation_plan: str
    expected_edge_bps: Decimal
    net_edge_bps: Decimal
    confidence: Decimal
    gluing_score: Decimal
    live_support_count: int
    historical_sample_size: int
    entry_reference_price: Decimal
    target_move_bps: Decimal
    stop_move_bps: Decimal
    execution_costs: ExecutionCostEnvelope
    audit_key: str

    def __post_init__(self) -> None:
        if self.symbol != self.symbol.upper() or not self.symbol:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy sections require canonical symbols.")
        if self.as_of.tzinfo is None or self.as_of.utcoffset() is None:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy sections require timezone-aware timestamps.")
        if self.direction not in {"long", "short"}:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy direction must be 'long' or 'short'.")
        if self.entry_reference_price <= ZERO or self.target_move_bps <= ZERO or self.stop_move_bps <= ZERO:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy pricing bounds must be strictly positive.")
        if self.live_support_count < 1 or self.historical_sample_size < 1:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy support counts must be positive.")
        for field_name, value in (("confidence", self.confidence), ("gluing_score", self.gluing_score)):
            if _clamp_probability(value) != value:
                raise DomainModelSoftwareEngineeringChartValidationError(
                    f"Strategy field '{field_name}' must lie in [0, 1]."
                )
        if not self.thesis.strip() or not self.validation_plan.strip() or not self.audit_key:
            raise DomainModelSoftwareEngineeringChartValidationError("Strategy sections require thesis, plan, and audit key.")

    @property
    def desirability_score(self) -> Decimal:
        return _quantize(max(self.net_edge_bps, ZERO) * self.confidence * self.gluing_score, BPS_QUANTUM)

    def to_dict(self) -> dict[str, Any]:
        return {
            "symbol": self.symbol,
            "as_of": _stringify(self.as_of),
            "direction": self.direction,
            "regime": self.regime,
            "thesis": self.thesis,
            "validation_plan": self.validation_plan,
            "expected_edge_bps": _stringify(self.expected_edge_bps),
            "net_edge_bps": _stringify(self.net_edge_bps),
            "confidence": _stringify(self.confidence),
            "gluing_score": _stringify(self.gluing_score),
            "live_support_count": self.live_support_count,
            "historical_sample_size": self.historical_sample_size,
            "entry_reference_price": _stringify(self.entry_reference_price),
            "target_move_bps": _stringify(self.target_move_bps),
            "stop_move_bps": _stringify(self.stop_move_bps),
            "desirability_score": _stringify(self.desirability_score),
            "execution_costs": self.execution_costs.to_dict(),
            "audit_key": self.audit_key,
        }


@dataclass(frozen=True)
class RiskInvariantCheck:
    name: str
    satisfied: bool
    actual: str
    expected: str
    rationale: str
    proof_target: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "satisfied": self.satisfied,
            "actual": self.actual,
            "expected": self.expected,
            "rationale": self.rationale,
            "proof_target": self.proof_target,
        }


@dataclass(frozen=True)
class CertifiedOrderIntent:
    symbol: str
    side: Literal["long", "short"]
    order_type: Literal["limit"]
    limit_price: Decimal
    position_fraction: Decimal
    leverage: Decimal
    stop_loss_bps: Decimal
    max_slippage_bps: Decimal
    execution_mode: ExecutionMode
    audit_key: str

    def __post_init__(self) -> None:
        if self.limit_price <= ZERO or self.position_fraction <= ZERO or self.leverage < ONE:
            raise DomainModelSoftwareEngineeringChartValidationError("Certified order intents require positive sizing and pricing.")
        if not self.audit_key:
            raise DomainModelSoftwareEngineeringChartValidationError("Certified order intents require an audit key.")

    def to_dict(self) -> dict[str, Any]:
        return {
            "symbol": self.symbol,
            "side": self.side,
            "order_type": self.order_type,
            "limit_price": _stringify(self.limit_price),
            "position_fraction": _stringify(self.position_fraction),
            "leverage": _stringify(self.leverage),
            "stop_loss_bps": _stringify(self.stop_loss_bps),
            "max_slippage_bps": _stringify(self.max_slippage_bps),
            "execution_mode": self.execution_mode,
            "audit_key": self.audit_key,
        }


# @invariant("research and live descent share one typed strategy and risk surface")
@dataclass(frozen=True)
class DomainModelSoftwareEngineeringChartState:
    module_version: str
    execution_mode: ExecutionMode
    bundle: MarketDataBundle
    experiment: ExperimentSnapshot
    strategy_sections: tuple[StrategySection, ...]
    selected_strategy: StrategySection | None
    risk_checks: tuple[RiskInvariantCheck, ...]
    order_intents: tuple[CertifiedOrderIntent, ...]
    dependency_state: str
    validation_messages: tuple[str, ...]
    reproducibility_signature: str

    def __post_init__(self) -> None:
        if self.selected_strategy is not None and self.selected_strategy not in self.strategy_sections:
            raise DomainModelSoftwareEngineeringChartValidationError("Selected strategy must come from the local chart section.")
        if self.order_intents and not all(check.satisfied for check in self.risk_checks):
            raise DomainModelSoftwareEngineeringChartValidationError(
                "Order generation is forbidden when risk invariants are violated."
            )

    @property
    def order_generation_allowed(self) -> bool:
        return bool(self.order_intents)

    def to_dict(self, *, summary: str) -> dict[str, Any]:
        return {
            "module_version": self.module_version,
            "summary": summary,
            "execution_mode": self.execution_mode,
            "market_data_summary": market_data_summary(self.bundle),
            "dependency_state": self.dependency_state,
            "experiment": self.experiment.to_dict(),
            "discovered_hypotheses": len(self.bundle.hypotheses),
            "selected_strategy": None if self.selected_strategy is None else self.selected_strategy.to_dict(),
            "strategy_sections": [section.to_dict() for section in self.strategy_sections],
            "risk_checks": [check.to_dict() for check in self.risk_checks],
            "orders": [intent.to_dict() for intent in self.order_intents],
            "order_generation_allowed": self.order_generation_allowed,
            "validation_messages": list(self.validation_messages),
            "reproducibility_signature": self.reproducibility_signature,
        }


class DomainModelSoftwareEngineeringChartService:
    """Typed orchestrator for the software-engineering chart transformations."""

    def __init__(self, *, module_version: str = MODULE_VERSION) -> None:
        self.module_version = module_version

    def _coerce_sequence_of_mappings(self, value: Any, field_name: str) -> tuple[Mapping[str, Any], ...]:
        if value is None:
            return ()
        if isinstance(value, Mapping):
            if any(key in value for key in ("timestamp", "symbol", "bid", "ask", "price")):
                return (dict(value),)
            if field_name == "local_entries" and "local_entries" in value:
                value = value["local_entries"]
        if isinstance(value, (str, bytes)):
            raise DomainModelSoftwareEngineeringChartValidationError(f"Field '{field_name}' must be a sequence of mappings.")
        try:
            materialized = tuple(dict(item) for item in value)
        except TypeError as exc:
            raise DomainModelSoftwareEngineeringChartValidationError(f"Field '{field_name}' must be iterable.") from exc
        return materialized

    def _coerce_risk_invariants(self, value: Any) -> RiskInvariantSpecification:
        if value is None:
            return RiskInvariantSpecification()
        if isinstance(value, RiskInvariantSpecification):
            return value
        if not isinstance(value, Mapping):
            raise DomainModelSoftwareEngineeringChartValidationError("Risk invariants must be a mapping or RiskInvariantSpecification.")
        default = RiskInvariantSpecification()
        conditions = value.get("order_rejection_conditions", default.order_rejection_conditions)
        if isinstance(conditions, str):
            conditions = (conditions,)
        else:
            conditions = tuple(str(condition) for condition in conditions)
        return RiskInvariantSpecification(
            max_position_fraction=_coerce_decimal(value.get("max_position_fraction", default.max_position_fraction), "max_position_fraction"),
            max_leverage=_coerce_decimal(value.get("max_leverage", default.max_leverage), "max_leverage"),
            max_drawdown_fraction=_coerce_decimal(value.get("max_drawdown_fraction", default.max_drawdown_fraction), "max_drawdown_fraction"),
            kill_switch_drawdown_fraction=_coerce_decimal(
                value.get("kill_switch_drawdown_fraction", default.kill_switch_drawdown_fraction),
                "kill_switch_drawdown_fraction",
            ),
            reject_on_stale_data_seconds=int(value.get("reject_on_stale_data_seconds", default.reject_on_stale_data_seconds)),
            order_rejection_conditions=conditions,
            proof_obligation=str(value.get("proof_obligation", default.proof_obligation)),
            paper_trading_required=bool(value.get("paper_trading_required", default.paper_trading_required)),
        )

    def _coerce_context(self, value: Any) -> Mapping[str, Any]:
        if value is None:
            return {}
        if isinstance(value, Mapping):
            return dict(value)
        return {"execution_mode": value}

    def _resolve_execution_mode(self, raw_value: Any) -> ExecutionMode:
        candidate = str(raw_value or "paper").strip().lower()
        if candidate not in {"research", "paper", "live"}:
            raise DomainModelSoftwareEngineeringChartValidationError("execution_mode must be one of: research, paper, live.")
        return candidate  # type: ignore[return-value]

    def _resolve_dependency_state(self, require_dependency: bool) -> tuple[str, str]:
        try:
            module = import_module(_IDEATION_MODULE)
        except ModuleNotFoundError:
            if require_dependency:
                raise DomainModelSoftwareEngineeringChartDependencyError(
                    f"Required overlap dependency '{_IDEATION_MODULE}' is unavailable."
                )
            return "optional_unavailable", _stable_digest([_IDEATION_MODULE, "missing"])
        export = getattr(module, "research_to_execution_trading", None)
        if export is None:
            export = getattr(module, "research-to-execution_trading", None)
        if callable(export):
            return "overlap_export_available", _stable_digest([_IDEATION_MODULE, "callable"])
        if require_dependency:
            raise DomainModelSoftwareEngineeringChartDependencyError(
                f"Required overlap dependency '{_IDEATION_MODULE}' does not expose research_to_execution_trading."
            )
        return "overlap_export_missing", _stable_digest([_IDEATION_MODULE, "missing_export"])

    def _execution_costs(self, hypothesis: Any, live_section: Any) -> ExecutionCostEnvelope:
        relative_spread_bps = _quantize(live_section.topology.relative_spread * Decimal("10000"), BPS_QUANTUM)
        flow_pressure_bps = _quantize(abs(live_section.topology.flow_pressure) * Decimal("100"), BPS_QUANTUM)
        transaction_cost_bps = _quantize(max(relative_spread_bps / Decimal("2"), Decimal("0.2500")), BPS_QUANTUM)
        slippage_bps = _quantize(max((relative_spread_bps / Decimal("4")) + flow_pressure_bps, Decimal("0.2500")), BPS_QUANTUM)
        partial_fill_ratio = _clamp_probability(
            Decimal("0.35")
            + (hypothesis.gluing_score / Decimal("2"))
            + (Decimal(min(live_section.support_count, 5)) / Decimal("20"))
            - (abs(live_section.topology.flow_pressure) / Decimal("5"))
        )
        latency_ms = int(((ONE - hypothesis.confidence) * Decimal("700")).to_integral_value(rounding=ROUND_HALF_EVEN)) + 50
        latency_cost_bps = _quantize(Decimal(latency_ms) / Decimal("1000"), BPS_QUANTUM)
        return ExecutionCostEnvelope(
            transaction_cost_bps=transaction_cost_bps,
            slippage_bps=slippage_bps,
            latency_ms=latency_ms,
            partial_fill_ratio=partial_fill_ratio,
            total_cost_bps=_quantize(transaction_cost_bps + slippage_bps + latency_cost_bps, BPS_QUANTUM),
        )

    def _strategy_sections(self, bundle: MarketDataBundle) -> tuple[StrategySection, ...]:
        live_by_symbol = {section.symbol: section for section in bundle.live_sections}
        sections: list[StrategySection] = []
        for hypothesis in bundle.hypotheses:
            live_section = live_by_symbol.get(hypothesis.symbol)
            if live_section is None:
                continue
            costs = self._execution_costs(hypothesis, live_section)
            net_edge_bps = _quantize((hypothesis.expected_edge_bps * costs.partial_fill_ratio) - costs.total_cost_bps, BPS_QUANTUM)
            audit_key = _stable_digest(
                [
                    bundle.data_signature,
                    hypothesis.data_signature,
                    live_section.reproducibility_signature(),
                    format(net_edge_bps, "f"),
                    costs.to_dict()["total_cost_bps"],
                ]
            )
            sections.append(
                StrategySection(
                    symbol=hypothesis.symbol,
                    as_of=hypothesis.as_of,
                    direction=hypothesis.direction,
                    regime=hypothesis.regime,
                    thesis=hypothesis.thesis,
                    validation_plan=hypothesis.validation_plan,
                    expected_edge_bps=hypothesis.expected_edge_bps,
                    net_edge_bps=net_edge_bps,
                    confidence=hypothesis.confidence,
                    gluing_score=hypothesis.gluing_score,
                    live_support_count=hypothesis.live_support_count,
                    historical_sample_size=hypothesis.historical_sample_size,
                    entry_reference_price=hypothesis.entry_reference_price,
                    target_move_bps=hypothesis.target_move_bps,
                    stop_move_bps=hypothesis.stop_move_bps,
                    execution_costs=costs,
                    audit_key=audit_key,
                )
            )
        return tuple(sorted(sections, key=lambda item: (-item.desirability_score, item.as_of, item.symbol)))

    def _selected_strategy(self, strategy_sections: Sequence[StrategySection]) -> StrategySection | None:
        return strategy_sections[0] if strategy_sections else None

    def _proposed_position_fraction(self, strategy: StrategySection, risk: RiskInvariantSpecification) -> Decimal:
        signal_quality = _clamp_probability((strategy.confidence + strategy.gluing_score + strategy.execution_costs.partial_fill_ratio) / Decimal("3"))
        raw_fraction = risk.max_position_fraction * (Decimal("0.30") + (signal_quality / Decimal("1.5")))
        return _quantize(min(raw_fraction, risk.max_position_fraction), FRACTION_QUANTUM)

    def _proposed_leverage(self, strategy: StrategySection, risk: RiskInvariantSpecification) -> Decimal:
        headroom = max(risk.max_leverage - ONE, ZERO)
        signal_quality = _clamp_probability((strategy.confidence + strategy.execution_costs.partial_fill_ratio) / Decimal("2"))
        return _quantize(min(ONE + (headroom * signal_quality), risk.max_leverage), FRACTION_QUANTUM)

    def _risk_checks(
        self,
        strategy: StrategySection | None,
        bundle: MarketDataBundle,
        execution_mode: ExecutionMode,
        dependency_state: str,
    ) -> tuple[RiskInvariantCheck, ...]:
        validation = validate_market_data(bundle)
        risk = bundle.risk_invariants
        if strategy is None:
            return (
                RiskInvariantCheck("hypothesis_discovery", False, "0", ">=1", "No typed strategy section could be derived.", risk.proof_obligation),
                RiskInvariantCheck("bundle_validation", validation.passes, validation.summary(), "validation=pass", "Base market-data invariants must validate.", risk.proof_obligation),
            )
        position_fraction = self._proposed_position_fraction(strategy, risk)
        leverage = self._proposed_leverage(strategy, risk)
        loss_cap_fraction = _quantize((strategy.stop_move_bps + strategy.execution_costs.total_cost_bps) / Decimal("10000"), FRACTION_QUANTUM)
        forbidden_transition = execution_mode != "live" or (
            risk.proof_obligation == "machine_checked" and not risk.paper_trading_required
        )
        rejection_coverage = all(condition.startswith("reject_") for condition in risk.order_rejection_conditions)
        return (
            RiskInvariantCheck("hypothesis_discovery", True, str(len(bundle.hypotheses)), ">=1", "Historical data discovered a non-trivial market hypothesis.", risk.proof_obligation),
            RiskInvariantCheck("bundle_validation", validation.passes, validation.summary(), "validation=pass", "Restriction, timestamp, symbol, and audit invariants must hold.", risk.proof_obligation),
            RiskInvariantCheck("dependency_overlap", not dependency_state.endswith("missing"), dependency_state, "overlap_export_available or optional_unavailable", "Overlap state must remain explicit for gluing audits.", risk.proof_obligation),
            RiskInvariantCheck("net_edge_positive", strategy.net_edge_bps > ZERO, format(strategy.net_edge_bps, "f"), ">0.0000", "Costs, slippage, latency, and partial fills must still leave positive edge.", risk.proof_obligation),
            RiskInvariantCheck("max_position_fraction", position_fraction <= risk.max_position_fraction, format(position_fraction, "f"), f"<={format(risk.max_position_fraction, 'f')}", "Proposed sizing must remain within the explicit position cap.", risk.proof_obligation),
            RiskInvariantCheck("max_leverage", leverage <= risk.max_leverage, format(leverage, "f"), f"<={format(risk.max_leverage, 'f')}", "Composed sizing and leverage must remain within the leverage cap.", risk.proof_obligation),
            RiskInvariantCheck("loss_cap_fraction", loss_cap_fraction <= risk.max_drawdown_fraction, format(loss_cap_fraction, "f"), f"<={format(risk.max_drawdown_fraction, 'f')}", "Stop distance plus execution drag must remain within the drawdown bound.", risk.proof_obligation),
            RiskInvariantCheck("kill_switch_ordering", risk.max_drawdown_fraction < risk.kill_switch_drawdown_fraction, format(risk.max_drawdown_fraction, 'f'), f"<{format(risk.kill_switch_drawdown_fraction, 'f')}", "Kill-switch threshold must exceed the standard drawdown bound.", risk.proof_obligation),
            RiskInvariantCheck("order_rejection_coverage", rejection_coverage, ",".join(risk.order_rejection_conditions), "all conditions prefixed with reject_", "Order rejection conditions must remain machine-checkable and explicit.", risk.proof_obligation),
            RiskInvariantCheck("forbidden_state_transition", forbidden_transition, f"mode={execution_mode};proof={risk.proof_obligation};paper_required={risk.paper_trading_required}", "live requires machine_checked proof and paper_trading_required=False", "Live order generation is forbidden until risk-core proof obligations discharge.", risk.proof_obligation),
        )

    def _build_order_intents(
        self,
        strategy: StrategySection | None,
        risk_checks: Sequence[RiskInvariantCheck],
        risk: RiskInvariantSpecification,
        execution_mode: ExecutionMode,
    ) -> tuple[CertifiedOrderIntent, ...]:
        if strategy is None or execution_mode == "research" or not all(check.satisfied for check in risk_checks):
            return ()
        position_fraction = self._proposed_position_fraction(strategy, risk)
        leverage = self._proposed_leverage(strategy, risk)
        sign = ONE if strategy.direction == "long" else Decimal("-1")
        limit_price = _quantize(
            strategy.entry_reference_price * (ONE + (sign * (strategy.execution_costs.slippage_bps / Decimal("10000")))),
            PRICE_QUANTUM,
        )
        stop_loss_bps = _quantize(
            min(
                strategy.stop_move_bps + strategy.execution_costs.transaction_cost_bps,
                risk.max_drawdown_fraction * Decimal("10000"),
            ),
            BPS_QUANTUM,
        )
        return (
            CertifiedOrderIntent(
                symbol=strategy.symbol,
                side=strategy.direction,
                order_type="limit",
                limit_price=limit_price,
                position_fraction=position_fraction,
                leverage=leverage,
                stop_loss_bps=stop_loss_bps,
                max_slippage_bps=strategy.execution_costs.slippage_bps,
                execution_mode=execution_mode,
                audit_key=_stable_digest([strategy.audit_key, execution_mode, format(position_fraction, "f"), format(leverage, "f")]),
            ),
        )

    def _experiment_snapshot(
        self,
        bundle: MarketDataBundle,
        risk: RiskInvariantSpecification,
        context: Mapping[str, Any],
        execution_mode: ExecutionMode,
        dependency_state: str,
        overlap_signature: str,
    ) -> ExperimentSnapshot:
        seed = int(context.get("seed", 0))
        parameters = tuple(
            sorted(
                (
                    ("execution_mode", execution_mode),
                    ("min_history_points", str(bundle.min_history_points)),
                    ("price_tolerance", format(bundle.price_tolerance, "f")),
                    ("spread_tolerance", format(bundle.spread_tolerance, "f")),
                    ("h1_tolerance", format(bundle.h1_tolerance, "f")),
                    ("proof_obligation", risk.proof_obligation),
                    ("paper_trading_required", str(risk.paper_trading_required)),
                    ("seed", str(seed)),
                )
            )
        )
        return ExperimentSnapshot(
            data_signature=bundle.data_signature,
            deterministic_seed=seed,
            parameter_snapshot=parameters,
            dependency_state=dependency_state,
            overlap_signature=overlap_signature,
        )

    def _state_signature(self, state: DomainModelSoftwareEngineeringChartState) -> str:
        return _stable_digest(
            [
                state.module_version,
                state.execution_mode,
                state.bundle.data_signature,
                state.experiment.reproducibility_signature(),
                *(section.audit_key for section in state.strategy_sections),
                *(f"{check.name}:{check.satisfied}" for check in state.risk_checks),
                *(intent.audit_key for intent in state.order_intents),
                state.dependency_state,
                *state.validation_messages,
            ]
        )

    # @require("arg1 and arg2 are raw historical/live entries; arg3-arg5 carry local, risk, and execution context")
    # @ensure("returned state shares one typed research/live strategy surface and never emits orders through failed risk checks")
    def build_state(
        self,
        arg1: Any,
        arg2: Any,
        arg3: Any,
        arg4: Any,
        arg5: Any,
    ) -> DomainModelSoftwareEngineeringChartState:
        historical_entries = self._coerce_sequence_of_mappings(arg1, "historical_entries")
        live_entries = self._coerce_sequence_of_mappings(arg2, "live_entries")
        local_entries = self._coerce_sequence_of_mappings(arg3, "local_entries")
        risk = self._coerce_risk_invariants(arg4)
        context = self._coerce_context(arg5)
        min_history_points = int(context.get("min_history_points", 12))
        if not precondition_holds(historical_entries, live_entries, min_value=min_history_points):
            raise DomainModelSoftwareEngineeringChartValidationError("precondition_holds failed for the software-engineering chart.")
        execution_mode = self._resolve_execution_mode(context.get("execution_mode", "paper"))
        dependency_state, overlap_signature = self._resolve_dependency_state(bool(context.get("require_dependency", False)))
        bundle = build_market_data(
            historical_entries,
            live_entries,
            local_entries=local_entries,
            min_history_points=min_history_points,
            price_tolerance=context.get("price_tolerance", Decimal("0.0025")),
            spread_tolerance=context.get("spread_tolerance", Decimal("0.0010")),
            h1_tolerance=context.get("h1_tolerance"),
            min_novelty_lift=context.get("min_novelty_lift", Decimal("0.0000500")),
            min_edge_bps=context.get("min_edge_bps", Decimal("2.5000")),
            risk_invariants=risk,
        )
        strategy_sections = self._strategy_sections(bundle)
        selected_strategy = self._selected_strategy(strategy_sections)
        risk_checks = self._risk_checks(selected_strategy, bundle, execution_mode, dependency_state)
        order_intents = self._build_order_intents(selected_strategy, risk_checks, bundle.risk_invariants, execution_mode)
        experiment = self._experiment_snapshot(bundle, bundle.risk_invariants, context, execution_mode, dependency_state, overlap_signature)
        provisional = DomainModelSoftwareEngineeringChartState(
            module_version=self.module_version,
            execution_mode=execution_mode,
            bundle=bundle,
            experiment=experiment,
            strategy_sections=strategy_sections,
            selected_strategy=selected_strategy,
            risk_checks=risk_checks,
            order_intents=order_intents,
            dependency_state=dependency_state,
            validation_messages=(),
            reproducibility_signature="pending",
        )
        validation_messages = self.validate_state(provisional)
        final_state = DomainModelSoftwareEngineeringChartState(
            module_version=provisional.module_version,
            execution_mode=provisional.execution_mode,
            bundle=provisional.bundle,
            experiment=provisional.experiment,
            strategy_sections=provisional.strategy_sections,
            selected_strategy=provisional.selected_strategy,
            risk_checks=provisional.risk_checks,
            order_intents=provisional.order_intents,
            dependency_state=provisional.dependency_state,
            validation_messages=validation_messages,
            reproducibility_signature="pending",
        )
        return DomainModelSoftwareEngineeringChartState(
            module_version=final_state.module_version,
            execution_mode=final_state.execution_mode,
            bundle=final_state.bundle,
            experiment=final_state.experiment,
            strategy_sections=final_state.strategy_sections,
            selected_strategy=final_state.selected_strategy,
            risk_checks=final_state.risk_checks,
            order_intents=final_state.order_intents,
            dependency_state=final_state.dependency_state,
            validation_messages=final_state.validation_messages,
            reproducibility_signature=self._state_signature(final_state),
        )

    # @require("state descends from build_state or an equivalent deterministic constructor")
    # @ensure("messages explain whether gluing, hypothesis, risk, and order surfaces still agree")
    def validate_state(self, state: DomainModelSoftwareEngineeringChartState) -> tuple[str, ...]:
        messages: list[str] = list(validate_market_data(state.bundle).messages)
        if not state.strategy_sections:
            messages.append("no strategy sections were derived from discovered hypotheses")
        if state.selected_strategy is None:
            messages.append("no selected strategy is available")
        if state.order_intents and state.execution_mode == "research":
            messages.append("research mode cannot emit executable orders")
        if state.order_intents and not all(check.satisfied for check in state.risk_checks):
            messages.append("order generation escaped failed risk checks")
        if state.bundle.data_signature != state.experiment.data_signature:
            messages.append("experiment snapshot diverges from bundle signature")
        if state.reproducibility_signature not in {"", "pending"} and state.reproducibility_signature != self._state_signature(state):
            messages.append("state reproducibility signature mismatch")
        return tuple(dict.fromkeys(messages))

    def summary(self, state: DomainModelSoftwareEngineeringChartState) -> str:
        selected = "none" if state.selected_strategy is None else f"{state.selected_strategy.symbol}:{state.selected_strategy.direction}"
        return (
            f"software_engineering_chart[{state.module_version}] mode={state.execution_mode} "
            f"hypotheses={len(state.bundle.hypotheses)} selected={selected} orders={len(state.order_intents)} "
            f"validation={'pass' if not state.validation_messages else 'fail'} signature={state.reproducibility_signature[:12]}"
        )

    # @require("state is a typed software-engineering chart state")
    # @ensure("returned dictionary is audit-ready and mirrors the typed state exactly")
    def render_report(self, state: DomainModelSoftwareEngineeringChartState) -> dict[str, Any]:
        return state.to_dict(summary=self.summary(state))


# @require("arg1..arg5 carry raw market support, risk bounds, and execution context")
# @ensure("returned dictionary contains discovered hypotheses, risk checks, and only risk-approved orders")
def research_to_execution_trading(arg1: Any, arg2: Any, arg3: Any, arg4: Any, arg5: Any) -> dict[str, Any]:
    service = DomainModelSoftwareEngineeringChartService()
    return service.render_report(service.build_state(arg1, arg2, arg3, arg4, arg5))


globals()["research-to-execution_trading"] = research_to_execution_trading

__all__ = [
    "CertifiedOrderIntent",
    "DomainModelSoftwareEngineeringChartDependencyError",
    "DomainModelSoftwareEngineeringChartError",
    "DomainModelSoftwareEngineeringChartService",
    "DomainModelSoftwareEngineeringChartState",
    "DomainModelSoftwareEngineeringChartValidationError",
    "ExecutionCostEnvelope",
    "ExperimentSnapshot",
    "RiskInvariantCheck",
    "StrategySection",
    "precondition_holds",
    "research_to_execution_trading",
    "x_at_least_min_value",
]
