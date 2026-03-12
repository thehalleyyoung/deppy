"""KMP string matching with failure function.

Bug: in failure function computation, when a mismatch occurs, resets
length to 0 instead of following the failure chain (len = failure[len-1]),
causing missed partial matches and wrong match positions.
"""

CORRECT = r"""
def compute_failure(pattern):
    m = len(pattern)
    failure = [0] * m
    length = 0  # length of previous longest prefix-suffix
    i = 1
    while i < m:
        if pattern[i] == pattern[length]:
            length += 1
            failure[i] = length
            i += 1
        else:
            if length != 0:
                # CORRECT: follow the failure chain
                length = failure[length - 1]
            else:
                failure[i] = 0
                i += 1
    return failure

def kmp_search(text, pattern):
    n = len(text)
    m = len(pattern)
    if m == 0:
        return []

    failure = compute_failure(pattern)
    matches = []
    j = 0  # index in pattern
    i = 0  # index in text
    while i < n:
        if text[i] == pattern[j]:
            i += 1
            j += 1
        if j == m:
            matches.append(i - j)
            j = failure[j - 1]
        elif i < n and text[i] != pattern[j]:
            if j != 0:
                j = failure[j - 1]
            else:
                i += 1
    return matches

text = TEXT
pattern = PATTERN
result = kmp_search(text, pattern)
"""

BUGGY = r"""
def compute_failure(pattern):
    m = len(pattern)
    failure = [0] * m
    length = 0
    i = 1
    while i < m:
        if pattern[i] == pattern[length]:
            length += 1
            failure[i] = length
            i += 1
        else:
            if length != 0:
                # BUG: reset to 0 instead of following failure chain
                length = 0
            else:
                failure[i] = 0
                i += 1
    return failure

def kmp_search(text, pattern):
    n = len(text)
    m = len(pattern)
    if m == 0:
        return []

    failure = compute_failure(pattern)
    matches = []
    j = 0
    i = 0
    while i < n:
        if text[i] == pattern[j]:
            i += 1
            j += 1
        if j == m:
            matches.append(i - j)
            j = failure[j - 1]
        elif i < n and text[i] != pattern[j]:
            if j != 0:
                j = failure[j - 1]
            else:
                i += 1
    return matches

text = TEXT
pattern = PATTERN
result = kmp_search(text, pattern)
"""


def SPEC(text, pattern, result):
    if not isinstance(result, list):
        return False

    # Compute ground truth with naive search
    expected = []
    m = len(pattern)
    if m == 0:
        return result == []
    for i in range(len(text) - m + 1):
        if text[i:i + m] == pattern:
            expected.append(i)

    return result == expected


BUG_DESC = (
    "In the failure function computation, when a mismatch occurs and length "
    "is nonzero, the algorithm resets length to 0 instead of following the "
    "failure chain via length = failure[length-1]. This produces an incorrect "
    "failure table for patterns with nested repeating prefixes, causing KMP "
    "to miss valid matches or report wrong positions."
)


def _gen_text():
    import random
    # The bug: in compute_failure, on mismatch when length != 0, resets
    # length = 0 instead of length = failure[length - 1].
    #
    # This matters for patterns with nested prefix-suffixes, e.g. "aabaaab":
    #   Correct failure: [0,1,0,1,2,2,3]
    #   Buggy failure:   [0,1,0,1,2,0,0]  (at i=5, length=2, mismatch 'a' vs 'b',
    #                     should follow failure[1]=1, but bug resets to 0)
    #
    # With the buggy failure table, KMP misses overlapping matches.
    # "aabaaabaaab" contains "aabaaab" at positions 0 and 4.
    # The buggy KMP only finds position 0 because failure[6]=0 instead of 3,
    # so after the first match it resets j to 0 instead of 3, missing the
    # overlap starting at position 4.
    #
    # Keep total text short to stay within size limits.
    pat = "aabaaab"
    _gen_text._pattern = pat

    # Use just the overlapping text directly - no noise that could mask the issue
    # "aabaaabaaab" has matches at 0 and 4; buggy finds only 0.
    return "aabaaabaaab"


def _gen_pattern():
    return _gen_text._pattern


INPUT_OVERRIDES = {
    "TEXT": _gen_text,
    "PATTERN": _gen_pattern,
}
