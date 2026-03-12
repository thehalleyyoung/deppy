"""MSD (most significant digit) radix sort for strings.
Bug: when recursing on a bucket, doesn't advance the character position
(uses same digit index d instead of d+1), causing infinite recursion."""

CORRECT = r"""
# MSD Radix Sort for variable-length strings
# Sorts strings lexicographically using recursive most-significant-digit first

def char_at(s, d):
    # Return character index at position d, or -1 if past end
    if d < len(s):
        return ord(s[d])
    return -1

def msd_sort(arr, lo, hi, d, aux):
    # Base case: subarray of size 0 or 1
    if hi <= lo:
        return
    # Use 258 buckets: one for end-of-string (-1 mapped to 0), plus 0..255 mapped to 1..256
    R = 258
    count = [0] * (R + 1)
    # Count frequencies
    for i in range(lo, hi + 1):
        c = char_at(arr[i], d)
        count[c + 2] += 1
    # Compute cumulates
    for r in range(R):
        count[r + 1] += count[r]
    # Distribute
    for i in range(lo, hi + 1):
        c = char_at(arr[i], d)
        aux[count[c + 1]] = arr[i]
        count[c + 1] += 1
    # Copy back
    for i in range(lo, hi + 1):
        arr[i] = aux[i - lo]
    # Recursively sort each bucket, advancing character position
    for r in range(R):
        # CORRECT: recurse with d + 1 to advance to next character
        new_lo = lo + count[r]
        new_hi = lo + count[r + 1] - 1
        msd_sort(arr, new_lo, new_hi, d + 1, aux)

strings = list(STRINGS)
n = len(strings)
if n > 1:
    aux = [''] * n
    msd_sort(strings, 0, n - 1, 0, aux)
result = strings
"""

BUGGY = r"""
# MSD Radix Sort for variable-length strings
# Sorts strings lexicographically using recursive most-significant-digit first

def char_at(s, d):
    # Return character index at position d, or -1 if past end
    if d < len(s):
        return ord(s[d])
    return -1

def msd_sort(arr, lo, hi, d, aux, depth=0):
    # Base case: subarray of size 0 or 1
    if hi <= lo:
        return
    # Safety limit to prevent actual infinite recursion in buggy version
    if depth > 200:
        return
    # Use 258 buckets: one for end-of-string (-1 mapped to 0), plus 0..255 mapped to 1..256
    R = 258
    count = [0] * (R + 1)
    # Count frequencies
    for i in range(lo, hi + 1):
        c = char_at(arr[i], d)
        count[c + 2] += 1
    # Compute cumulates
    for r in range(R):
        count[r + 1] += count[r]
    # Distribute
    for i in range(lo, hi + 1):
        c = char_at(arr[i], d)
        aux[count[c + 1]] = arr[i]
        count[c + 1] += 1
    # Copy back
    for i in range(lo, hi + 1):
        arr[i] = aux[i - lo]
    # BUG: recurse with d instead of d + 1, never advancing character position
    for r in range(R):
        new_lo = lo + count[r]
        new_hi = lo + count[r + 1] - 1
        msd_sort(arr, new_lo, new_hi, d, aux, depth + 1)

strings = list(STRINGS)
n = len(strings)
if n > 1:
    aux = [''] * n
    msd_sort(strings, 0, n - 1, 0, aux)
result = strings
"""


def SPEC(strings, result):
    # Result must be the sorted version of the input strings
    if not strings:
        return result == [] or result == strings
    expected = sorted(strings)
    if result != expected:
        return False
    # Must be a permutation
    if sorted(result) != sorted(strings):
        return False
    return True


BUG_DESC = (
    "When recursing on each bucket, passes d (same character position) instead "
    "of d + 1. This means the sort never advances to the next character, causing "
    "infinite recursion on any bucket with 2+ strings sharing the same character at "
    "position d. With the depth guard, the sort simply stops early and returns "
    "an unsorted result."
)


def _gen_strings():
    import random
    import string
    n = random.randint(4, 12)
    result = []
    for _ in range(n):
        length = random.randint(1, 6)
        s = ''.join(random.choices(string.ascii_lowercase[:5], k=length))
        result.append(s)
    return result


INPUT_OVERRIDES = {"STRINGS": _gen_strings}
