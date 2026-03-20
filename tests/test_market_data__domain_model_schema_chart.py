from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timedelta, timezone
from decimal import Decimal

import pytest

from deppy.market_data__domain_model_schema_chart import (
    SchemaChartDependencyError,
    design_and,
    precondition_holds,
    research_to_production_trading,
    validate_schema_chart,
    x_at_least_min_value,
)


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


def test_design_and_builds_traceable_schema_chart() -> None:
    chart = design_and(
        _historical_eth_entries(),
        _live_eth_entries(),
        local_entries=_local_eth_entries(),
        regime_snapshot={"ETHUSD": "coherent_breakout"},
        min_history_points=6,
    )

    report = validate_schema_chart(chart)
    gate_map = {gate.name: gate for gate in chart.gates}

    assert chart.schema_version.endswith(".v1")
    assert chart.symbols == ("ETHUSD",)
    assert chart.sections[0].regime == "coherent_breakout"
    assert chart.sections[0].support_count >= 2
    assert chart.sections[0].effective_edge_bps > Decimal("1.0000")
    assert chart.novelty_packet.headline == "ext_machine_learning_16concepts"
    assert chart.proof_certificate.paper_ready is True
    assert chart.proof_certificate.live_ready is False
    assert len(chart.certified_intents) == 1
    assert chart.certified_intents[0].approved_for_paper is True
    assert chart.certified_intents[0].approved_for_live is False
    assert gate_map["verification"].passes is True
    assert gate_map["simulation"].passes is True
    assert gate_map["stress"].passes is True
    assert gate_map["paper_promotion"].passes is True
    assert gate_map["live_promotion"].passes is False
    assert chart.data_signature[:12] in chart.summary()
    assert report.passes is True
    assert report.signature_matches is True


def test_precondition_holds_tracks_required_raw_support() -> None:
    assert precondition_holds(_historical_eth_entries(), _live_eth_entries(), min_value=6) is True
    assert precondition_holds(_historical_eth_entries()[:5], _live_eth_entries(), min_value=6) is False
    assert precondition_holds(_historical_eth_entries(), [], min_value=6) is False


def test_x_at_least_min_value_covers_minimum_obligation() -> None:
    assert x_at_least_min_value(6, 6) is True
    assert x_at_least_min_value(7, 6) is True
    assert x_at_least_min_value(5, 6) is False


def test_validate_schema_chart_surfaces_counterexample_for_failed_minimum_bound() -> None:
    chart = design_and(
        _historical_eth_entries(),
        _live_eth_entries(),
        min_history_points=6,
    )
    bad_section = replace(chart.sections[0], effective_edge_bps=Decimal("0.5000"))
    tampered = replace(
        chart,
        sections=(bad_section,),
        invariants=tuple(
            replace(invariant, actual=Decimal("0.5000"))
            if invariant.name == "effective_edge_bps::ETHUSD"
            else invariant
            for invariant in chart.invariants
        ),
        data_signature="tampered",
    )

    report = validate_schema_chart(tampered)

    assert report.passes is False
    assert report.minimum_bounds_hold is False
    assert report.signature_matches is False
    assert any(
        counterexample.obligation == "effective_edge_bps::ETHUSD"
        for counterexample in report.counterexamples
    )


def test_design_and_requires_regime_dependency_when_requested() -> None:
    with pytest.raises(SchemaChartDependencyError):
        design_and(
            _historical_eth_entries(),
            _live_eth_entries(),
            min_history_points=6,
            require_regime_dependency=True,
        )


def test_research_to_production_trading_alias_matches_design_and() -> None:
    direct = design_and(
        _historical_eth_entries(),
        _live_eth_entries(),
        local_entries=_local_eth_entries(),
        regime_snapshot={"ETHUSD": "coherent_breakout"},
        min_history_points=6,
    )
    aliased = research_to_production_trading(
        _historical_eth_entries(),
        _live_eth_entries(),
        local_entries=_local_eth_entries(),
        regime_snapshot={"ETHUSD": "coherent_breakout"},
        min_history_points=6,
    )

    assert aliased.data_signature == direct.data_signature
    assert aliased.proof_certificate == direct.proof_certificate
    assert aliased.certified_intents == direct.certified_intents
