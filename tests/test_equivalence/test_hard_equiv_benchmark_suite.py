from __future__ import annotations

from benchmarks.hard_equiv_suite import EQUIV_PAIRS


def test_hard_equiv_suite_has_expected_shape() -> None:
    assert len(EQUIV_PAIRS) == 100
    assert sum(1 for _, _, _, expected in EQUIV_PAIRS if expected) == 50
    assert sum(1 for _, _, _, expected in EQUIV_PAIRS if not expected) == 50
    assert len({name for name, _, _, _ in EQUIV_PAIRS}) == 100
