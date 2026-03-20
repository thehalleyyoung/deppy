from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Tuple


# The benchmark suite uses a slightly coarser/public bug taxonomy than the
# detector internals. These aliases let the benchmark score implemented
# detections rather than penalizing naming drift.
_EXPECTED_LABEL_ALIASES = {
    "ASSERTION_FAILURE": ("ASSERTION_FAILURE", "ASSERT_FAIL"),
    "RACE_CONDITION": ("RACE_CONDITION", "DATA_RACE"),
    "XSS": ("XSS", "REFLECTED_XSS"),
    "INFINITE_LOOP": ("INFINITE_LOOP", "NON_TERMINATION"),
    "STACK_OVERFLOW": ("STACK_OVERFLOW", "NON_TERMINATION"),
    # The benchmark treats domain errors under Python's broader ValueError
    # umbrella, while the detector splits out FP-specific domain violations.
    "VALUE_ERROR": ("VALUE_ERROR", "FP_DOMAIN"),
}

_CANONICAL_FALSE_POSITIVE_LABELS = {
    "ASSERT_FAIL": "ASSERTION_FAILURE",
    "DATA_RACE": "RACE_CONDITION",
    "REFLECTED_XSS": "XSS",
    "FP_DOMAIN": "VALUE_ERROR",
}


@dataclass(frozen=True)
class _BugScore:
    true_positives: int
    false_positives: int
    false_negatives: int
    scored_detected_labels: List[str]
    alias_matches: List[Tuple[str, str]]


def _matches_expected_label(expected_label: str, detected_label: str) -> bool:
    aliases = _EXPECTED_LABEL_ALIASES.get(expected_label)
    if aliases is None:
        return detected_label == expected_label
    return detected_label in aliases


def _canonicalize_false_positive_label(detected_label: str) -> str:
    return _CANONICAL_FALSE_POSITIVE_LABELS.get(detected_label, detected_label)


def _score_bug_labels(
    expected_labels: Sequence[str],
    detected_labels: Sequence[str],
) -> _BugScore:
    """Score bug detections against the benchmark taxonomy.

    Uses maximum bipartite matching so an ambiguous detector label such as
    ``NON_TERMINATION`` can satisfy at most one compatible expected label.
    """
    adjacency = [
        [
            detected_idx
            for detected_idx, detected_label in enumerate(detected_labels)
            if _matches_expected_label(expected_label, detected_label)
        ]
        for expected_label in expected_labels
    ]

    match_for_detected = [-1] * len(detected_labels)

    def _augment(expected_idx: int, seen: List[bool]) -> bool:
        for detected_idx in adjacency[expected_idx]:
            if seen[detected_idx]:
                continue
            seen[detected_idx] = True
            previous = match_for_detected[detected_idx]
            if previous == -1 or _augment(previous, seen):
                match_for_detected[detected_idx] = expected_idx
                return True
        return False

    true_positives = 0
    for expected_idx in range(len(expected_labels)):
        if _augment(expected_idx, [False] * len(detected_labels)):
            true_positives += 1

    alias_matches: List[Tuple[str, str]] = []
    scored_detected_labels: List[str] = []
    for detected_idx, detected_label in enumerate(detected_labels):
        expected_idx = match_for_detected[detected_idx]
        if expected_idx == -1:
            scored_detected_labels.append(
                _canonicalize_false_positive_label(detected_label)
            )
            continue

        expected_label = expected_labels[expected_idx]
        scored_detected_labels.append(expected_label)
        if expected_label != detected_label:
            alias_matches.append((expected_label, detected_label))

    false_positives = len(detected_labels) - true_positives
    false_negatives = len(expected_labels) - true_positives
    return _BugScore(
        true_positives=true_positives,
        false_positives=false_positives,
        false_negatives=false_negatives,
        scored_detected_labels=scored_detected_labels,
        alias_matches=alias_matches,
    )
