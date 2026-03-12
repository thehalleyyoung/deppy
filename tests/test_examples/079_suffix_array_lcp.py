"""LCP array construction from suffix array using Kasai's algorithm.
Bug: resets h to 0 at the start of each iteration instead of
decrementing by 1 (losing the key optimization and producing wrong values)."""

CORRECT = r"""
# Suffix Array + LCP Array (Kasai's Algorithm)
# Build suffix array via simple O(n log^2 n) method, then LCP via Kasai

def build_suffix_array(s):
    n = len(s)
    if n == 0:
        return []
    # Initial ranking by single character
    sa = list(range(n))
    rank = [ord(c) for c in s]
    tmp = [0] * n
    k = 1
    while k < n:
        def compare(a, b):
            if rank[a] != rank[b]:
                return rank[a] - rank[b]
            ra = rank[a + k] if a + k < n else -1
            rb = rank[b + k] if b + k < n else -1
            return ra - rb
        import functools
        sa.sort(key=functools.cmp_to_key(compare))
        tmp[sa[0]] = 0
        for i in range(1, n):
            tmp[sa[i]] = tmp[sa[i - 1]]
            if compare(sa[i - 1], sa[i]) < 0:
                tmp[sa[i]] += 1
        rank = tmp[:]
        if rank[sa[n - 1]] == n - 1:
            break
        k *= 2
    return sa

def kasai_lcp(s, sa):
    # CORRECT Kasai's algorithm
    n = len(s)
    if n == 0:
        return []
    rank = [0] * n
    for i in range(n):
        rank[sa[i]] = i
    lcp = [0] * n
    h = 0
    for i in range(n):
        if rank[i] > 0:
            j = sa[rank[i] - 1]
            # CORRECT: h carries over from previous iteration, decremented by 1
            while i + h < n and j + h < n and s[i + h] == s[j + h]:
                h += 1
            lcp[rank[i]] = h
            if h > 0:
                h -= 1
        else:
            h = 0
    return lcp

text = TEXT
sa = build_suffix_array(text)
lcp = kasai_lcp(text, sa)
result = (sa, lcp)
"""

BUGGY = r"""
# Suffix Array + LCP Array (Kasai's Algorithm)
# Build suffix array via simple O(n log^2 n) method, then LCP via Kasai

def build_suffix_array(s):
    n = len(s)
    if n == 0:
        return []
    sa = list(range(n))
    rank = [ord(c) for c in s]
    tmp = [0] * n
    k = 1
    while k < n:
        def compare(a, b):
            if rank[a] != rank[b]:
                return rank[a] - rank[b]
            ra = rank[a + k] if a + k < n else -1
            rb = rank[b + k] if b + k < n else -1
            return ra - rb
        import functools
        sa.sort(key=functools.cmp_to_key(compare))
        tmp[sa[0]] = 0
        for i in range(1, n):
            tmp[sa[i]] = tmp[sa[i - 1]]
            if compare(sa[i - 1], sa[i]) < 0:
                tmp[sa[i]] += 1
        rank = tmp[:]
        if rank[sa[n - 1]] == n - 1:
            break
        k *= 2
    return sa

def kasai_lcp(s, sa):
    # BUGGY Kasai's algorithm
    n = len(s)
    if n == 0:
        return []
    rank = [0] * n
    for i in range(n):
        rank[sa[i]] = i
    lcp = [0] * n
    for i in range(n):
        if rank[i] > 0:
            j = sa[rank[i] - 1]
            # BUG: resets h to 0 each iteration instead of carrying over
            h = 0
            while i + h < n and j + h < n and s[i + h] == s[j + h]:
                h += 1
            lcp[rank[i]] = h
            # Missing: h -= 1 (but since h is reset to 0 above, the decrement
            # would not help anyway; the real bug is re-initializing h)
    return lcp

text = TEXT
sa = build_suffix_array(text)
lcp = kasai_lcp(text, sa)
result = (sa, lcp)
"""


def SPEC(text, result):
    # Verify suffix array is correct and LCP values are correct
    sa, lcp = result
    n = len(text)
    if n == 0:
        return sa == [] and lcp == []
    # Check sa is a permutation
    if sorted(sa) != list(range(n)):
        return False
    # Check sa is sorted
    for i in range(1, n):
        if text[sa[i - 1]:] >= text[sa[i]:]:
            return False
    # Check LCP values
    if len(lcp) != n:
        return False
    for i in range(1, n):
        # Compute actual LCP between sa[i-1] and sa[i]
        a = sa[i - 1]
        b = sa[i]
        common = 0
        while a + common < n and b + common < n and text[a + common] == text[b + common]:
            common += 1
        if lcp[i] != common:
            return False
    return True


BUG_DESC = (
    "In kasai_lcp, resets h to 0 at the start of each iteration of the outer "
    "loop. Kasai's algorithm relies on h carrying over from the previous "
    "iteration (decremented by 1) to achieve O(n) total. Resetting h means "
    "some LCP values will be computed as 0 when they should be positive, "
    "because the comparison starts from offset 0 instead of h-1."
)


def _gen_text():
    import random
    import string
    n = random.randint(5, 20)
    # Use small alphabet to create repeated patterns
    return ''.join(random.choices('abc', k=n))


INPUT_OVERRIDES = {"TEXT": _gen_text}
