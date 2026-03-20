from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

import pytest

from deppy.execution import (
    ExecutionGluingError,
    build_execution,
    ExecutionQuote,
    apply_fills,
    build_execution_cover,
    check_execution_cocycle,
    empty_execution_ledger,
    execution_summary,
    executable_orders,
    glue_execution_sections,
    place_orders,
    position_quantity,
    restrict_execution_sections,
    simulate_fills,
    validate_execution,
)
from deppy.market_data import glue_market_observations, normalize_feed_entry
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


def test_build_execution_cover_creates_one_slice_per_risk_approved_intent() -> None:
    sections = build_execution_cover(_approved_intents(), quotes_by_symbol=_quotes())

    assert len(sections) == 3
    assert {section.slice_name for section in sections} == {
        "arrival",
        "impact",
        "identity",
    }
    assert all(section.symbol == "ETHUSD" for section in sections)
    assert all(
        section.timestamp == datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc)
        for section in sections
    )


def test_execution_cocycle_gluing_and_order_placement_produce_ready_order() -> None:
    sections = build_execution_cover(_approved_intents(), quotes_by_symbol=_quotes())

    certificates = check_execution_cocycle(sections)
    glued = glue_execution_sections(sections)
    orders = place_orders(glued)

    assert certificates[0].passes is True
    assert len(glued) == 1
    assert glued[0].symbol == "ETHUSD"
    assert glued[0].slices == ("arrival", "identity", "impact")
    assert glued[0].gluing_score > Decimal("0")
    assert glued[0].order_status == "ready"
    assert len(orders) == 1
    assert orders[0].order_status == "ready"
    assert executable_orders(orders) == orders


def test_restrict_execution_sections_preserves_overlap_identity() -> None:
    sections = build_execution_cover(_approved_intents(), quotes_by_symbol=_quotes())

    restricted = restrict_execution_sections(
        sections,
        symbols={"ETHUSD"},
        start=datetime(2026, 3, 20, 0, 59, tzinfo=timezone.utc),
        end=datetime(2026, 3, 20, 1, 1, tzinfo=timezone.utc),
        slices={"arrival", "impact"},
        venues={"xnas"},
    )

    assert len(restricted) == 2
    assert [section.slice_name for section in restricted] == ["arrival", "impact"]
    assert all(section.symbol == "ETHUSD" for section in restricted)


def test_glue_execution_sections_rejects_incompatible_local_slices() -> None:
    sections = build_execution_cover(_approved_intents(), quotes_by_symbol=_quotes())
    incompatible = replace(
        sections[0],
        executable_fraction=Decimal("0"),
        quantity=Decimal("0"),
        notional=Decimal("0.00"),
        estimated_fee=Decimal("0.00"),
        participation_rate=Decimal("0"),
        cash_delta=Decimal("0.00"),
        position_delta=Decimal("0"),
        identity_residual=Decimal("0.00"),
        binding=True,
        passes=False,
    )

    with pytest.raises(ExecutionGluingError):
        glue_execution_sections([incompatible, *sections[1:]])


def test_simulated_fills_update_cash_and_positions_with_exact_identities() -> None:
    sections = build_execution_cover(_approved_intents(), quotes_by_symbol=_quotes())
    orders = executable_orders(place_orders(glue_execution_sections(sections)))

    fills = simulate_fills(orders)
    ledger = apply_fills(empty_execution_ledger(), fills)

    assert len(fills) == 1
    assert fills[0].fill_status == "filled"
    assert ledger.cash_balance == Decimal("100000.00") + fills[0].cash_delta
    assert ledger.total_fees_paid == fills[0].fee
    assert position_quantity(ledger, fills[0].symbol) == fills[0].position_delta


def test_build_execution_bundle_validates_and_preserves_execution_ideas() -> None:
    bundle = build_execution(_approved_intents(), quotes_by_symbol=_quotes())
    report = validate_execution(bundle)
    summary = execution_summary(bundle)

    assert report.passes is True
    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.approved_intents) == 1
    assert len(bundle.quotes) == 1
    assert len(bundle.local_sections) == 3
    assert len(bundle.global_sections) == 1
    assert len(bundle.orders) == 1
    assert len(bundle.executable_orders) == 1
    assert len(bundle.fills) == 1
    assert bundle.ledger.cash_balance == Decimal("100000.00") + bundle.fills[0].cash_delta
    assert bundle.ledger.total_fees_paid == bundle.fills[0].fee
    assert len(bundle.research_ideas) >= 1
    assert bundle.research_ideas[0].symbol == "ETHUSD"
    assert bundle.research_ideas[0].expected_edge_bps > Decimal("0")
    assert "execution[" in summary
    assert bundle.summary() == summary


def test_validate_execution_detects_signature_tampering() -> None:
    bundle = build_execution(_approved_intents(), quotes_by_symbol=_quotes())
    tampered = replace(bundle, data_signature="tampered")

    report = validate_execution(tampered)

    assert report.passes is False
    assert report.signature_matches is False
