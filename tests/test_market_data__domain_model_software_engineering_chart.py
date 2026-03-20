from __future__ import annotations

from datetime import datetime, timedelta, timezone

from deppy.market_data__domain_model_software_engineering_chart import (
    DomainModelSoftwareEngineeringChartService,
    research_to_execution_trading,
)
import deppy.market_data__domain_model_software_engineering_chart as software_engineering_chart


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


def test_research_to_execution_trading_returns_risk_approved_paper_order() -> None:
    report = research_to_execution_trading(
        _historical_eth_entries(),
        _live_eth_entries(),
        _local_eth_entries(),
        None,
        {"execution_mode": "paper", "min_history_points": 6, "seed": 7},
    )

    assert report["module_version"].endswith(".v1")
    assert report["discovered_hypotheses"] >= 1
    assert report["selected_strategy"]["symbol"] == "ETHUSD"
    assert report["order_generation_allowed"] is True
    assert len(report["orders"]) == 1
    assert all(check["satisfied"] for check in report["risk_checks"])
    assert report["orders"][0]["execution_mode"] == "paper"


def test_live_mode_blocks_orders_until_machine_checked_risk_core() -> None:
    service = DomainModelSoftwareEngineeringChartService()
    state = service.build_state(
        _historical_eth_entries(),
        _live_eth_entries(),
        _local_eth_entries(),
        None,
        {"execution_mode": "live", "min_history_points": 6},
    )

    forbidden = {check.name: check for check in state.risk_checks}["forbidden_state_transition"]

    assert forbidden.satisfied is False
    assert state.order_intents == ()


def test_loss_cap_violation_prevents_order_generation() -> None:
    report = research_to_execution_trading(
        _historical_eth_entries(),
        _live_eth_entries(),
        _local_eth_entries(),
        {
            "max_drawdown_fraction": "0.0001",
            "kill_switch_drawdown_fraction": "0.0002",
        },
        {"execution_mode": "paper", "min_history_points": 6},
    )

    checks = {check["name"]: check for check in report["risk_checks"]}

    assert checks["loss_cap_fraction"]["satisfied"] is False
    assert report["orders"] == []
    assert report["order_generation_allowed"] is False


def test_hyphenated_export_alias_is_available() -> None:
    assert getattr(software_engineering_chart, "research-to-execution_trading") is research_to_execution_trading
