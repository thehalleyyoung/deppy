from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

import pytest

from deppy.market_data import glue_market_observations, normalize_feed_entry
from deppy.signal_geometry import (
    build_signal_cover,
    build_signal_geometry,
    glue_signal_sections,
)
from deppy.strategy_kernel import (
    StrategyGluingError,
    build_strategy_kernel,
    build_strategy_cover,
    check_strategy_cocycle,
    derive_position_intents,
    glue_strategy_sections,
    pending_risk_intents,
    restrict_strategy_sections,
    strategy_kernel_summary,
    validate_strategy_kernel,
)


def _glued_signal_sections() -> list:
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
    signal_sections = build_signal_cover(market_sections)
    return glue_signal_sections(signal_sections)


def _signal_geometry_bundle():
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
    return build_signal_geometry(glue_market_observations([first, second]))


def test_build_strategy_cover_creates_one_rule_per_signal() -> None:
    sections = build_strategy_cover(_glued_signal_sections())

    assert len(sections) == 3
    assert {section.rule for section in sections} == {
        "transport",
        "harmonic_reversion",
        "novelty_breakout",
    }
    assert all(section.symbol == "ETHUSD" for section in sections)
    assert all(
        section.timestamp == datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc)
        for section in sections
    )


def test_strategy_cocycle_and_gluing_produce_pending_risk_intent() -> None:
    sections = build_strategy_cover(_glued_signal_sections())

    certificates = check_strategy_cocycle(sections)
    glued = glue_strategy_sections(sections)
    intents = derive_position_intents(
        glued,
        min_conviction=Decimal("0.1500000"),
        min_target_fraction=Decimal("0.0100000"),
    )

    assert certificates[0].passes is True
    assert len(glued) == 1
    assert glued[0].symbol == "ETHUSD"
    assert glued[0].rules == (
        "harmonic_reversion",
        "novelty_breakout",
        "transport",
    )
    assert glued[0].gluing_score > Decimal("0")
    assert len(intents) == 1
    assert intents[0].approval_status == "pending_risk"
    assert pending_risk_intents(intents) == intents


def test_restrict_strategy_sections_preserves_overlap_identity() -> None:
    sections = build_strategy_cover(_glued_signal_sections())

    restricted = restrict_strategy_sections(
        sections,
        symbols={"ETHUSD"},
        start=datetime(2026, 3, 20, 0, 59, tzinfo=timezone.utc),
        end=datetime(2026, 3, 20, 1, 1, tzinfo=timezone.utc),
        rules={"transport", "novelty_breakout"},
    )

    assert len(restricted) == 2
    assert [section.rule for section in restricted] == [
        "novelty_breakout",
        "transport",
    ]
    assert all(section.symbol == "ETHUSD" for section in restricted)


def test_glue_strategy_sections_rejects_incompatible_local_rules() -> None:
    sections = build_strategy_cover(_glued_signal_sections())
    incompatible = replace(
        sections[0],
        alpha_score=Decimal("-0.9500000"),
        target_fraction=Decimal("0.2000000"),
        risk_bounds=replace(
            sections[0].risk_bounds,
            max_position_fraction=Decimal("0.2000000"),
            stop_loss_fraction=Decimal("0.1800000"),
            take_profit_fraction=Decimal("0.3000000"),
            conviction_floor=Decimal("0.1500000"),
            h1_buffer=Decimal("0.5500000"),
        ),
    )

    with pytest.raises(StrategyGluingError):
        glue_strategy_sections([incompatible, *sections[1:]])


def test_build_strategy_kernel_produces_validated_auditable_bundle() -> None:
    bundle = build_strategy_kernel(_signal_geometry_bundle())

    report = validate_strategy_kernel(bundle)
    summary = strategy_kernel_summary(bundle)

    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.signal_sections) == 1
    assert len(bundle.local_sections) == 3
    assert len(bundle.global_sections) == 1
    assert len(bundle.position_intents) == 1
    assert len(bundle.research_ideas) == 1
    assert bundle.risk_policy.proof_obligation == "smt_required"
    assert bundle.risk_policy.paper_trading_required is True
    assert report.passes is True
    assert report.signature_matches is True
    assert report.novel_idea_present is True
    assert "validation=pass" in summary
    assert "ideas=1" in summary
    assert bundle.data_signature[:12] in summary


def test_validate_strategy_kernel_detects_signature_tampering() -> None:
    bundle = build_strategy_kernel(_signal_geometry_bundle())
    tampered = replace(bundle, data_signature="0" * 64)

    report = validate_strategy_kernel(tampered)

    assert report.passes is False
    assert report.signature_matches is False
    assert "signature mismatch" in report.summary() or "mismatch" in " ".join(report.messages)
