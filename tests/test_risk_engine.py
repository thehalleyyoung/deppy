from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

import pytest

from deppy.market_data import glue_market_observations, normalize_feed_entry
from deppy.risk_engine import (
    RiskGluingError,
    approve_position_intents,
    build_risk_engine,
    build_risk_cover,
    check_risk_cocycle,
    glue_risk_sections,
    restrict_risk_sections,
    risk_approved_intents,
    risk_engine_summary,
    validate_risk_engine,
)
from deppy.signal_geometry import build_signal_cover, glue_signal_sections
from deppy.strategy_kernel import (
    build_strategy_kernel,
    build_strategy_cover,
    derive_position_intents,
    glue_strategy_sections,
    pending_risk_intents,
)


def _pending_intents() -> list:
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
    return pending_risk_intents(intents)


def _strategy_bundle():
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
    return build_strategy_kernel(
        signal_sections,
        min_conviction=Decimal("0.1500000"),
        min_target_fraction=Decimal("0.0100000"),
    )


def test_build_risk_cover_creates_one_lens_per_pending_intent() -> None:
    sections = build_risk_cover(_pending_intents())

    assert len(sections) == 3
    assert {section.lens for section in sections} == {
        "drawdown",
        "exposure",
        "leverage",
    }
    assert all(section.symbol == "ETHUSD" for section in sections)
    assert all(
        section.timestamp == datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc)
        for section in sections
    )


def test_risk_cocycle_gluing_and_approval_produce_execution_ready_intent() -> None:
    sections = build_risk_cover(_pending_intents())

    certificates = check_risk_cocycle(sections)
    glued = glue_risk_sections(sections)
    approved = approve_position_intents(glued)

    assert certificates[0].passes is True
    assert len(glued) == 1
    assert glued[0].symbol == "ETHUSD"
    assert glued[0].lenses == ("drawdown", "exposure", "leverage")
    assert glued[0].gluing_score > Decimal("0")
    assert glued[0].approval_status == "risk_approved"
    assert len(approved) == 1
    assert approved[0].approval_status == "risk_approved"
    assert risk_approved_intents(approved) == approved


def test_restrict_risk_sections_preserves_overlap_identity() -> None:
    sections = build_risk_cover(_pending_intents())

    restricted = restrict_risk_sections(
        sections,
        symbols={"ETHUSD"},
        start=datetime(2026, 3, 20, 0, 59, tzinfo=timezone.utc),
        end=datetime(2026, 3, 20, 1, 1, tzinfo=timezone.utc),
        lenses={"drawdown", "leverage"},
    )

    assert len(restricted) == 2
    assert [section.lens for section in restricted] == ["drawdown", "leverage"]
    assert all(section.symbol == "ETHUSD" for section in restricted)


def test_glue_risk_sections_rejects_incompatible_local_lenses() -> None:
    sections = build_risk_cover(_pending_intents())
    incompatible = replace(
        sections[0],
        approved_fraction=Decimal("0"),
        utilization=Decimal("1"),
        haircut_fraction=sections[0].target_fraction,
        binding=True,
        passes=False,
    )

    with pytest.raises(RiskGluingError):
        glue_risk_sections([incompatible, *sections[1:]])


def test_build_risk_engine_bundle_validates_and_preserves_research_ideas() -> None:
    bundle = build_risk_engine(_strategy_bundle())
    report = validate_risk_engine(bundle)
    summary = risk_engine_summary(bundle)

    assert report.passes is True
    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.position_intents) == 1
    assert len(bundle.local_sections) == 3
    assert len(bundle.global_sections) == 1
    assert len(bundle.approved_intents) == 1
    assert len(bundle.executable_intents) == 1
    assert len(bundle.research_ideas) >= 1
    assert bundle.research_ideas[0].symbol == "ETHUSD"
    assert bundle.research_ideas[0].expected_edge_bps > Decimal("0")
    assert "risk_engine[" in summary
    assert bundle.summary() == summary


def test_validate_risk_engine_detects_signature_tampering() -> None:
    bundle = build_risk_engine(_pending_intents())
    tampered = replace(bundle, data_signature="tampered")

    report = validate_risk_engine(tampered)

    assert report.passes is False
    assert report.signature_matches is False
