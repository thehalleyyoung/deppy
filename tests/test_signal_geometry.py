from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
from decimal import Decimal

import pytest

from deppy.market_data import glue_market_observations, normalize_feed_entry
from deppy.signal_geometry import (
    LocalSignalSection,
    SignalCoordinates,
    build_signal_geometry,
    SignalGluingError,
    signal_geometry_summary,
    validate_signal_geometry,
    build_signal_cover,
    check_signal_cocycle,
    glue_signal_sections,
    restrict_signal_sections,
)


def _glued_market_sections() -> list:
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
    return glue_market_observations([first, second])


def test_build_signal_cover_creates_one_chart_per_patch() -> None:
    sections = build_signal_cover(_glued_market_sections())

    assert len(sections) == 3
    assert {section.chart for section in sections} == {
        "persistence",
        "reversion",
        "novelty",
    }
    assert all(section.symbol == "ETHUSD" for section in sections)
    assert all(section.timestamp == datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc) for section in sections)


def test_signal_cocycle_and_gluing_produce_strategy_ready_section() -> None:
    sections = build_signal_cover(_glued_market_sections())

    certificates = check_signal_cocycle(sections)
    glued = glue_signal_sections(sections)

    assert certificates[0].passes is True
    assert len(glued) == 1
    assert glued[0].charts == ("novelty", "persistence", "reversion")
    assert glued[0].symbol == "ETHUSD"
    assert glued[0].conviction > Decimal("0")
    assert glued[0].side in {"long", "short", "flat"}


def test_restrict_signal_sections_preserves_overlap_identity() -> None:
    sections = build_signal_cover(_glued_market_sections())

    restricted = restrict_signal_sections(
        sections,
        symbols={"ETHUSD"},
        start=datetime(2026, 3, 20, 0, 59, tzinfo=timezone.utc),
        end=datetime(2026, 3, 20, 1, 1, tzinfo=timezone.utc),
        charts={"persistence", "novelty"},
    )

    assert len(restricted) == 2
    assert [section.chart for section in restricted] == ["novelty", "persistence"]
    assert all(section.symbol == "ETHUSD" for section in restricted)


def test_glue_signal_sections_rejects_incompatible_local_charts() -> None:
    timestamp = datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc)
    coordinates = SignalCoordinates(
        continuation_bias=Decimal("0.1000000"),
        mean_reversion_bias=Decimal("-0.1000000"),
        crowding_pressure=Decimal("0.0500000"),
        topology_memory=Decimal("0.1500000"),
        novelty_lift=Decimal("0.1200000"),
        regime_curvature=Decimal("0.0800000"),
    )
    sections = [
        LocalSignalSection(
            timestamp=timestamp,
            symbol="AAPL",
            chart="persistence",
            sources=("feed_a",),
            venues=("XNAS",),
            support_count=2,
            gluing_score=Decimal("0.9000000"),
            coordinates=coordinates,
            alpha_score=Decimal("0.9500000"),
            confidence=Decimal("0.9000000"),
            thesis="transport chart",
        ),
        LocalSignalSection(
            timestamp=timestamp,
            symbol="AAPL",
            chart="reversion",
            sources=("feed_a",),
            venues=("XNAS",),
            support_count=2,
            gluing_score=Decimal("0.9000000"),
            coordinates=coordinates,
            alpha_score=Decimal("-0.9500000"),
            confidence=Decimal("0.9000000"),
            thesis="reversion chart",
        ),
        LocalSignalSection(
            timestamp=timestamp,
            symbol="AAPL",
            chart="novelty",
            sources=("feed_a",),
            venues=("XNAS",),
            support_count=2,
            gluing_score=Decimal("0.9000000"),
            coordinates=coordinates,
            alpha_score=Decimal("0.8000000"),
            confidence=Decimal("0.9000000"),
            thesis="novelty chart",
        ),
    ]

    with pytest.raises(SignalGluingError):
        glue_signal_sections(sections)


def test_build_signal_geometry_produces_validated_auditable_bundle() -> None:
    bundle = build_signal_geometry(_glued_market_sections())

    report = validate_signal_geometry(bundle)
    summary = signal_geometry_summary(bundle)

    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.market_sections) == 1
    assert len(bundle.local_sections) == 3
    assert len(bundle.global_sections) == 1
    assert len(bundle.research_ideas) == 1
    assert bundle.risk_invariants.proof_obligation == "smt_required"
    assert report.passes is True
    assert report.signature_matches is True
    assert "validation=pass" in summary
    assert "ideas=1" in summary
    assert bundle.data_signature[:12] in summary


def test_validate_signal_geometry_detects_signature_tampering() -> None:
    bundle = build_signal_geometry(_glued_market_sections())
    tampered = replace(bundle, data_signature="0" * 64)

    report = validate_signal_geometry(tampered)

    assert report.passes is False
    assert report.signature_matches is False
    assert "signature mismatch" in report.summary() or "mismatch" in " ".join(report.messages)
