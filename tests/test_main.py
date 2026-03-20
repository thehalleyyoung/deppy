from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timedelta, timezone
from decimal import Decimal

from deppy.execution import ExecutionQuote
from deppy.main import MainAssemblyRequest, build_main, main_summary, validate_main
from deppy.portfolio import PortfolioPolicy


def _historical_eth_entries() -> list[dict[str, str]]:
    start = datetime(2026, 3, 20, 0, 0, tzinfo=timezone.utc)
    entries: list[dict[str, str]] = []
    for index in range(12):
        entries.append(
            {
                "timestamp": (start + timedelta(minutes=index)).isoformat(),
                "symbol": "ETH/USD",
                "source": "historical_feed",
                "venue": "XNAS",
                "bid": "99.95",
                "ask": "100.05",
                "bid_size": "10",
                "ask_size": "10",
                "volume": "2",
            }
        )
    return entries


def _live_eth_entries() -> list[dict[str, str]]:
    return [
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "ETHUSD",
            "source": "live_a",
            "venue": "XNAS",
            "bid": "100.00",
            "ask": "100.06",
            "bid_size": "40",
            "ask_size": "10",
            "volume": "2",
            "side": "sell",
        },
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "ETH-USD",
            "source": "live_b",
            "venue": "BATS",
            "bid": "100.01",
            "ask": "100.07",
            "bid_size": "38",
            "ask_size": "12",
            "volume": "2",
            "side": "sell",
        },
    ]


def _local_eth_entries() -> list[dict[str, str]]:
    return [
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "eth/usd",
            "price": "100.04",
            "volume": "1",
            "side": "sell",
        }
    ]


def _quotes() -> dict[str, ExecutionQuote]:
    return {
        "ETHUSD": ExecutionQuote(
            timestamp=datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc),
            symbol="ETHUSD",
            venue="XNAS",
            bid_price=Decimal("100.00"),
            ask_price=Decimal("100.06"),
            available_quantity=Decimal("500.0000"),
        )
    }


def _request(**overrides: object) -> MainAssemblyRequest:
    payload: dict[str, object] = {
        "historical_entries": tuple(_historical_eth_entries()),
        "live_entries": tuple(_live_eth_entries()),
        "local_entries": tuple(_local_eth_entries()),
        "quotes_by_symbol": _quotes(),
    }
    payload.update(overrides)
    return MainAssemblyRequest(**payload)


def test_build_main_glues_verified_system_end_to_end() -> None:
    bundle = build_main(_request())
    repeated = build_main(_request())
    report = validate_main(bundle)
    summary = main_summary(bundle)

    assert report.passes is True
    assert report.all_stage_reports_pass is True
    assert report.signature_descent_closed is True
    assert report.only_risk_approved_descend is True
    assert report.formal_proofs_verified is True
    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.gluing_certificates) >= 7
    assert len(bundle.formal_verification) >= 5
    assert len(bundle.research_ideas) >= 1
    assert bundle.deployment_plan.deployment_mode == "paper"
    assert bundle.deployment_plan.kill_switch_state == "armed"
    assert bundle.deployment_plan.orders_may_route is True
    assert bundle.compliance_bundle.upstream_data_signature == bundle.portfolio_bundle.data_signature
    assert bundle.portfolio_bundle.upstream_data_signature == bundle.execution_bundle.data_signature
    assert bundle.execution_bundle.upstream_data_signature == bundle.risk_engine_bundle.data_signature
    assert repeated.data_signature == bundle.data_signature
    assert "main[" in summary
    assert "validation=pass" in summary
    assert bundle.data_signature[:12] in summary
    assert bundle.summary() == summary


def test_build_main_preserves_fail_safe_when_kill_switch_engages() -> None:
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
    bundle = build_main(
        _request(
            portfolio_policy=strict_policy,
            mark_price_by_symbol={"ETHUSD": Decimal("120.00")},
        )
    )
    report = validate_main(bundle)

    assert report.passes is True
    assert report.kill_switch_fail_safe is True
    assert bundle.portfolio_bundle.state.status == "kill_switch"
    assert bundle.deployment_plan.kill_switch_state == "engaged"
    assert bundle.deployment_plan.orders_may_route is False


def test_validate_main_detects_signature_tampering() -> None:
    bundle = build_main(_request())
    tampered = replace(bundle, data_signature="tampered")

    report = validate_main(tampered)

    assert report.passes is False
    assert report.signature_matches is False
