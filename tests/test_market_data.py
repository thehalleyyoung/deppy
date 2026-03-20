from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timedelta, timezone
from decimal import Decimal

import pytest

from deppy.market_data import (
    GluingInvariantError,
    HypothesisGenerationError,
    build_market_data,
    check_cocycle_gluing,
    discover_market_hypotheses,
    glue_market_observations,
    market_data_summary,
    normalize_feed_entry,
    restrict_observations,
    validate_market_data,
)


def test_normalize_feed_entry_canonicalizes_overlap_invariants() -> None:
    observation = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "btc/usd",
            "source": "Primary Feed",
            "venue": "XNAS",
            "bid": "99",
            "ask": "101",
            "bid_size": "60",
            "ask_size": "40",
            "volume": "12",
            "side": "buy",
        }
    )

    assert observation.symbol == "BTCUSD"
    assert observation.timestamp == datetime(2026, 3, 20, 1, 0, tzinfo=timezone.utc)
    assert observation.mid == Decimal("100.000000")
    assert observation.spread == Decimal("2.000000")
    assert observation.topology.order_imbalance == Decimal("0.2000000")
    assert observation.topology.harmonic_advantage == Decimal("-0.0020000")


def test_glue_market_observations_descends_overlap_compatible_inputs() -> None:
    first = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "ETH-USD",
            "source": "feed_a",
            "bid": "199.90",
            "ask": "200.10",
            "bid_size": "10",
            "ask_size": "10",
            "volume": "5",
        }
    )
    second = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00+00:00",
            "symbol": "ETHUSD",
            "source": "feed_b",
            "bid": "199.95",
            "ask": "200.15",
            "bid_size": "11",
            "ask_size": "9",
            "volume": "6",
        }
    )

    certificates = check_cocycle_gluing([first, second])
    glued = glue_market_observations([first, second])

    assert certificates[0].passes is True
    assert len(glued) == 1
    assert glued[0].symbol == "ETHUSD"
    assert glued[0].support_count == 2
    assert glued[0].gluing_score > Decimal("0")


def test_glue_market_observations_rejects_large_overlap_disagreement() -> None:
    first = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "AAPL",
            "source": "feed_a",
            "price": "100",
        }
    )
    second = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "AAPL",
            "source": "feed_b",
            "price": "110",
        }
    )

    with pytest.raises(GluingInvariantError):
        glue_market_observations([first, second])


def test_restrict_observations_preserves_timestamp_and_symbol() -> None:
    observation = normalize_feed_entry(
        {
            "timestamp": "2026-03-20T01:00:00Z",
            "symbol": "msft",
            "source": "feed_a",
            "price": "100",
        }
    )

    restricted = restrict_observations(
        [observation],
        symbols={"MSFT"},
        start=datetime(2026, 3, 20, 0, 59, tzinfo=timezone.utc),
        end=datetime(2026, 3, 20, 1, 1, tzinfo=timezone.utc),
    )

    assert restricted == [observation]


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


def test_discover_market_hypotheses_generates_reproducible_alpha_probe() -> None:
    historical = _historical_eth_entries()
    live = _live_eth_entries()

    hypotheses = discover_market_hypotheses(
        historical,
        live,
        min_history_points=6,
    )
    repeated = discover_market_hypotheses(
        historical,
        live,
        min_history_points=6,
    )

    assert len(hypotheses) == 1
    assert hypotheses[0].symbol == "ETHUSD"
    assert hypotheses[0].direction == "short"
    assert hypotheses[0].historical_sample_size == 12
    assert hypotheses[0].live_support_count == 2
    assert hypotheses[0].expected_edge_bps >= Decimal("2.5000")
    assert Decimal("0") <= hypotheses[0].confidence <= Decimal("1")
    assert "immutable data signature" in hypotheses[0].validation_plan
    assert repeated[0].data_signature == hypotheses[0].data_signature


def test_discover_market_hypotheses_fails_closed_when_live_data_missing() -> None:
    with pytest.raises(HypothesisGenerationError):
        discover_market_hypotheses(_historical_eth_entries(), [], min_history_points=6)


def test_build_market_data_produces_validated_auditable_bundle() -> None:
    bundle = build_market_data(
        _historical_eth_entries(),
        _live_eth_entries(),
        local_entries=_local_eth_entries(),
        min_history_points=6,
    )

    report = validate_market_data(bundle)
    summary = market_data_summary(bundle)

    assert len(bundle.live_feed_observations) == 2
    assert len(bundle.local_observations) == 1
    assert len(bundle.live_observations) == 3
    assert bundle.symbols == ("ETHUSD",)
    assert len(bundle.hypotheses) == 1
    assert report.passes is True
    assert report.signature_matches is True
    assert bundle.risk_invariants.proof_obligation == "smt_required"
    assert "reject_failed_gluing" in bundle.risk_invariants.order_rejection_conditions
    assert "validation=pass" in summary
    assert "hypotheses=1" in summary
    assert bundle.data_signature[:12] in summary


def test_build_market_data_rejects_lookahead_bias() -> None:
    historical = _historical_eth_entries()
    historical[-1]["timestamp"] = "2026-03-20T01:00:00Z"

    with pytest.raises(HypothesisGenerationError, match="lookahead bias"):
        build_market_data(
            historical,
            _live_eth_entries(),
            min_history_points=6,
        )


def test_validate_market_data_detects_signature_tampering() -> None:
    bundle = build_market_data(
        _historical_eth_entries(),
        _live_eth_entries(),
        min_history_points=6,
    )
    tampered = replace(bundle, data_signature="0" * 64)

    report = validate_market_data(tampered)

    assert report.passes is False
    assert report.signature_matches is False
    assert "signature mismatch" in report.summary()
