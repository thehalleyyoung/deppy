from __future__ import annotations

from benchmarks.bug_benchmark_utils import _score_bug_labels


def test_alias_labels_count_as_true_positives() -> None:
    score = _score_bug_labels(
        ["ASSERTION_FAILURE", "RACE_CONDITION", "XSS"],
        ["ASSERT_FAIL", "DATA_RACE", "REFLECTED_XSS"],
    )

    assert score.true_positives == 3
    assert score.false_positives == 0
    assert score.false_negatives == 0
    assert score.scored_detected_labels == [
        "ASSERTION_FAILURE",
        "RACE_CONDITION",
        "XSS",
    ]


def test_non_termination_matches_only_one_expected_bug() -> None:
    score = _score_bug_labels(
        ["STACK_OVERFLOW", "INFINITE_LOOP"],
        ["NON_TERMINATION"],
    )

    assert score.true_positives == 1
    assert score.false_positives == 0
    assert score.false_negatives == 1
    assert score.scored_detected_labels in (
        ["STACK_OVERFLOW"],
        ["INFINITE_LOOP"],
    )


def test_fp_domain_scores_as_value_error_for_benchmark_suite() -> None:
    score = _score_bug_labels(["VALUE_ERROR"], ["FP_DOMAIN"])

    assert score.true_positives == 1
    assert score.false_positives == 0
    assert score.false_negatives == 0
    assert score.alias_matches == [("VALUE_ERROR", "FP_DOMAIN")]


def test_unmatched_alias_false_positives_are_canonicalized() -> None:
    score = _score_bug_labels([], ["ASSERT_FAIL", "DATA_RACE", "NON_TERMINATION"])

    assert score.true_positives == 0
    assert score.false_positives == 3
    assert score.false_negatives == 0
    assert score.scored_detected_labels == [
        "ASSERTION_FAILURE",
        "RACE_CONDITION",
        "NON_TERMINATION",
    ]
