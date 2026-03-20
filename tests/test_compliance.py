from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

from deppy.compliance import build_compliance, compliance_summary, validate_compliance
from deppy.execution import ExecutionQuote, build_execution
from deppy.market_data import glue_market_observations, normalize_feed_entry
from deppy.portfolio import PortfolioPolicy, build_portfolio
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


def test_build_compliance_witnesses_boundary_and_ideas() -> None:
    compliance_bundle = build_compliance(build_portfolio(_execution_bundle()))
    report = validate_compliance(compliance_bundle)
    summary = compliance_summary(compliance_bundle)

    assert report.passes is True
    assert report.upstream_portfolio_valid is True
    assert report.overlap_obligations_closed is True
    assert report.boundary_trace_closed is True
    assert report.boundary_evidence_closed is True
    assert report.formal_proofs_verified is True
    assert len(compliance_bundle.overlap_witnesses) == len(compliance_bundle.portfolio_bundle.fills)
    assert len(compliance_bundle.boundary_audit_events) == len(compliance_bundle.overlap_witnesses) + 2
    assert len(compliance_bundle.research_ideas) >= 1
    assert all(item.result == "proved" for item in compliance_bundle.proof_certificates)
    assert "compliance[" in summary
    assert compliance_bundle.summary() == summary


def test_build_compliance_preserves_fail_safe_for_kill_switch_portfolio() -> None:
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
    portfolio_bundle = build_portfolio(
        _execution_bundle(),
        policy=strict_policy,
        mark_price_by_symbol={"ETHUSD": Decimal("120.00")},
    )
    compliance_bundle = build_compliance(portfolio_bundle)
    report = validate_compliance(compliance_bundle)

    assert report.passes is True
    assert report.fail_safe_deterministic is True
    assert compliance_bundle.portfolio_bundle.state.status == "kill_switch"
    assert any(
        item.invariant_name == "drawdown_trigger" for item in compliance_bundle.boundary_evidence
    )


def test_validate_compliance_detects_signature_tampering() -> None:
    compliance_bundle = build_compliance(build_portfolio(_execution_bundle()))
    tampered = replace(compliance_bundle, data_signature="tampered")

    report = validate_compliance(tampered)

    assert report.passes is False
    assert report.signature_matches is False


def test_validate_compliance_detects_boundary_trace_tampering() -> None:
    compliance_bundle = build_compliance(build_portfolio(_execution_bundle()))
    broken_event = replace(compliance_bundle.boundary_audit_events[1], trace_parent="broken-parent")
    tampered = replace(
        compliance_bundle,
        boundary_audit_events=(
            compliance_bundle.boundary_audit_events[0],
            broken_event,
            *compliance_bundle.boundary_audit_events[2:],
        ),
    )

    report = validate_compliance(tampered)

    assert report.passes is False
    assert report.boundary_trace_closed is False
