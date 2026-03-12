"""Z-algorithm for string matching. Bug: when extending from a cached match,
uses z[i - l] directly instead of min(z[i - l], r - i + 1), overshooting the Z-box boundary."""

CORRECT = r"""
# Z-algorithm: compute Z-array and find all pattern occurrences in text
# Z[i] = length of longest substring starting at i that matches a prefix of s
def z_function(s):
    n = len(s)
    if n == 0:
        return []
    z = [0] * n
    z[0] = n
    l, r = 0, 0
    for i in range(1, n):
        if i < r:
            z[i] = min(z[i - l], r - i)
        while i + z[i] < n and s[z[i]] == s[i + z[i]]:
            z[i] += 1
        if i + z[i] > r:
            l = i
            r = i + z[i]
    return z

text = TEXT
pattern = PATTERN

# Concatenate pattern + sentinel + text
sentinel = chr(0)  # character not in either string
concat = pattern + sentinel + text
z = z_function(concat)

plen = len(pattern)
occurrences = []
for i in range(plen + 1, len(concat)):
    if z[i] >= plen:
        occurrences.append(i - plen - 1)

# Also compute Z-array of just the text for verification
z_text = z_function(text)

result = {
    "occurrences": occurrences,
    "z_of_concat": z,
    "pattern_len": plen,
    "text_len": len(text),
    "z_text": z_text,
}
"""

BUGGY = r"""
# Z-algorithm with a subtle bug in the Z-box optimization
def z_function(s):
    n = len(s)
    if n == 0:
        return []
    z = [0] * n
    z[0] = n
    l, r = 0, 0
    for i in range(1, n):
        if i < r:
            # BUG: uses z[i - l] directly without clamping to r - i
            # This can overshoot the Z-box boundary
            z[i] = z[i - l]
        while i + z[i] < n and s[z[i]] == s[i + z[i]]:
            z[i] += 1
        if i + z[i] > r:
            l = i
            r = i + z[i]
    return z

text = TEXT
pattern = PATTERN

sentinel = chr(0)
concat = pattern + sentinel + text
z = z_function(concat)

plen = len(pattern)
occurrences = []
for i in range(plen + 1, len(concat)):
    if z[i] >= plen:
        occurrences.append(i - plen - 1)

z_text = z_function(text)

result = {
    "occurrences": occurrences,
    "z_of_concat": z,
    "pattern_len": plen,
    "text_len": len(text),
    "z_text": z_text,
}
"""

def SPEC(text, pattern, result):
    """Verify Z-algorithm string matching results."""
    occurrences = result["occurrences"]
    plen = result["pattern_len"]
    z_text = result["z_text"]
    z_concat = result["z_of_concat"]

    # Every reported occurrence must actually match
    for idx in occurrences:
        if idx < 0 or idx + plen > len(text):
            return False
        if text[idx:idx + plen] != pattern:
            return False

    # Must find ALL occurrences (brute force check)
    true_occ = []
    for i in range(len(text) - plen + 1):
        if text[i:i + plen] == pattern:
            true_occ.append(i)
    if occurrences != true_occ:
        return False

    # Verify Z-array of text: z_text[i] = length of longest common prefix
    # of text and text[i:]
    for i in range(1, len(text)):
        expected = 0
        while i + expected < len(text) and text[expected] == text[i + expected]:
            expected += 1
        if z_text[i] != expected:
            return False

    # Verify Z-array of concat
    concat = pattern + chr(0) + text
    for i in range(1, min(len(concat), 50)):
        expected = 0
        while i + expected < len(concat) and concat[expected] == concat[i + expected]:
            expected += 1
        if z_concat[i] != expected:
            return False

    return True

BUG_DESC = "When inside the Z-box, uses z[i-l] directly without clamping to min(z[i-l], r-i), which can overshoot the Z-box right boundary and produce incorrect Z-values."

def _gen():
    import random
    # The bug: z[i] = z[i-l] without clamping to min(z[i-l], r-i).
    # This matters when z[i-l] extends beyond the Z-box boundary (r-i).
    # Specifically, when z[i-l] > r - i, the correct code sets z[i] = r - i
    # and then tries to extend, while the bug sets z[i] = z[i-l] which may
    # skip the extension or start extending from the wrong position.
    #
    # Classic trigger: "aabxaab" or "aaabaaa" type strings where a Z-value
    # at the mirror position is larger than the remaining Z-box.
    #
    # Key pattern: s = "aabaaab"
    # z_function("aabaaab"):
    #   i=1: z[1]=1 (a vs a, then a vs b) -> l=1, r=2
    #   i=2: z[2]=0 (b vs a)
    #   i=3: i < r=2? No. extend: a==a, a==a, b==b, a!=a -> z[3]=3, l=3,r=6
    #   i=4: i=4 < r=6. mirror=2*3-4=2. z[2]=0. z[4]=0. extend: a==a,a!=b->z[4]=1. l=4,r=5? no 5<6
    #   Actually let me use well-known trigger strings.
    #
    # "aaaaaa" is perfect: z=[6,5,4,3,2,1]. At i=2, z[i-l]=z[1]=5, r-i=6-2=4.
    # Without clamping, z[2]=5 (wrong, should be 4). Then the while loop tries
    # s[5] == s[7] which is out of bounds... but the code has i+z[i]<n guard.
    # With z[2]=5, i+z[2]=7 >= n=6, so while doesn't execute. z[2]=5 is wrong (should be 4).
    #
    # Even simpler: use strings like "aaaa" as pattern with text containing them.

    cases = [
        # Repeated 'a' strings trigger the overflow reliably
        {"TEXT": "aaaaaaa", "PATTERN": "aaa"},
        {"TEXT": "aaaaabaaaa", "PATTERN": "aaaa"},
        {"TEXT": "ababababab", "PATTERN": "abab"},
        # String where Z-box overflow causes wrong Z-values
        {"TEXT": "aabaabaab", "PATTERN": "aab"},
        {"TEXT": "aaaaaa", "PATTERN": "aa"},
        {"TEXT": "abcabcabc", "PATTERN": "abcabc"},
    ]
    return random.choice(cases)

INPUT_OVERRIDES = _gen
