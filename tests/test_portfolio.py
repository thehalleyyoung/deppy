from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

from deppy.execution import ExecutionQuote, build_execution
from deppy.market_data import glue_market_observations, normalize_feed_entry
from deppy.portfolio import (
    PortfolioPolicy,
    build_portfolio,
    portfolio_summary,
    validate_portfolio,
)
from deppy.risk_engine import (
    approve_position_intents,
    build_risk_cover,
    glue_risk_sections,
    risk_approved_intents,
)
from deppy.signal_geometry import build_signal_cover, glue_signal_sections
from deppy.strategy_kernel import (
    build_strategy_cover,
    derive_position_intents,
    glue_strategy_sections,
    pending_risk_intents,
)


def _approved_intents() -> list:
    first = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "ETH-USD",
            "source": "feed_a",
            "venue": "XNAS",
            "bid": "199.95",
            "ask": "200.05",
            "bid_size": "12",
            "ask_size": "10",
            "volume": "5",
        }
    )
    second = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00+00:00",
            "symbol": "ETHUSD",
            "source": "feed_b",
            "venue": "BATS",
            "bid": "199.96",
            "ask": "200.06",
            "bid_size": "11",
            "ask_size": "9",
            "volume": "6",
        }
    )
    market_sections = glue_market_observations([first, second])
    signal_sections = glue_signal_sections(build_signal_cover(market_sections))
    strategy_sections = glue_strategy_sections(build_strategy_cover(signal_sections))
    intents = derive_position_intents(
        strategy_sections,
        min_conviction=Decimal("0.1500000"),
        min_target_fraction=Decimal("0.0100000"),
    )
    pending = pending_risk_intents(intents)
    risk_sections = glue_risk_sections(build_risk_cover(pending))
    approved = approve_position_intents(risk_sections)
    return risk_approved_intents(approved)


def _quotes() -> dict[str, ExecutionQuote]:
    return {
        "ETHUSD": ExecutionQuote(
            timestamp=datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc),
            symbol="ETHUSD",
            venue="XNAS",
            bid_price=Decimal("199.95"),
            ask_price=Decimal("200.05"),
            available_quantity=Decimal("500.0000"),
        )
    }


def _execution_bundle():
    return build_execution(_approved_intents(), quotes_by_symbol=_quotes())


def test_build_portfolio_reconciles_fills_positions_and_pnl() -> None:
    bundle = build_portfolio(_execution_bundle())
    report = validate_portfolio(bundle)
    summary = portfolio_summary(bundle)

    assert report.passes is True
    assert report.fills_positions_cash_consistent is True
    assert report.execution_ledger_matches is True
    assert report.audit_cocycle_closed is True
    assert len(bundle.cash_records) == len(bundle.fills)
    assert len(bundle.position_records) == len(bundle.fills)
    assert len(bundle.pnl_records) == len(bundle.fills)
    assert len(bundle.positions) == 1
    assert bundle.positions[0].symbol == "ETHUSD"
    assert bundle.state.current_equity == bundle.starting_cash_balance + bundle.state.total_pnl
    assert bundle.state.status == "healthy"
    assert len(bundle.research_ideas) >= 1
    assert len(bundle.formal_verification) >= 1
    assert "portfolio[" in summary
    assert bundle.summary() == summary


def test_build_portfolio_can_trigger_deterministic_kill_switch_under_strict_policy() -> None:
    strict_policy = PortfolioPolicy(
        max_gross_leverage=Decimal("0.0500000"),
        max_net_exposure=Decimal("0.0500000"),
        max_symbol_exposure=Decimal("0.0500000"),
        max_drawdown=Decimal("0.0100000"),
        kill_switch_drawdown=Decimal("0.0200000"),
        required_rejection_conditions=(
            "reject_failed_gluing",
            "reject_kill_switch",
            "reject_max_drawdown",
            "reject_exposure_breach",
            "reject_leverage_breach",
            "reject_unverified_risk_core",
        ),
        proof_obligation="smt_required",
        paper_trading_required=True,
    )
    bundle = build_portfolio(
        _execution_bundle(),
        policy=strict_policy,
        mark_price_by_symbol={"ETHUSD": Decimal("120.00")},
    )
    report = validate_portfolio(bundle)

    assert report.passes is True
    assert report.kill_switch_deterministic is True
    assert bundle.state.status == "kill_switch"
    assert bundle.state.kill_switch_reason != ""
    assert any(event.event_type == "kill_switch_triggered" for event in bundle.audit_events)


def test_validate_portfolio_detects_signature_tampering() -> None:
    bundle = build_portfolio(_execution_bundle())
    tampered = replace(bundle, data_signature="tampered")

    report = validate_portfolio(tampered)

    assert report.passes is False
    assert report.signature_matches is False


def test_validate_portfolio_detects_broken_trace_cocycle() -> None:
    bundle = build_portfolio(_execution_bundle())
    broken_event = replace(bundle.audit_events[1], trace_parent="broken-parent")
    tampered = replace(
        bundle,
        audit_events=(bundle.audit_events[0], broken_event, *bundle.audit_events[2:]),
    )

    report = validate_portfolio(tampered)

    assert report.passes is False
    assert report.audit_cocycle_closed is False
