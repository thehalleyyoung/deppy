"""Rabin-Karp multi-pattern matching using rolling hash. Bug: on hash collision where
the string doesn't match, the window advances twice (double-advance), skipping a valid position."""

CORRECT = r"""
# Rabin-Karp multi-pattern string matching with rolling hash
# Finds all occurrences of any pattern in the text

text = TEXT
patterns = PATTERNS

BASE = 256
MOD = 1000000007

def compute_hash(s, length):
    h = 0
    for i in range(length):
        h = (h * BASE + ord(s[i])) % MOD
    return h

def rolling_hash_search(text, pattern):
    n = len(text)
    m = len(pattern)
    if m > n or m == 0:
        return []

    # Precompute BASE^(m-1) mod MOD
    h_multiplier = pow(BASE, m - 1, MOD)

    pat_hash = compute_hash(pattern, m)
    txt_hash = compute_hash(text, m)

    occurrences = []

    for i in range(n - m + 1):
        if i > 0:
            # Roll the hash: remove leading char, add trailing char
            txt_hash = (txt_hash - ord(text[i - 1]) * h_multiplier) % MOD
            txt_hash = (txt_hash * BASE + ord(text[i + m - 1])) % MOD

        if txt_hash == pat_hash:
            # Verify actual match to handle collisions
            if text[i:i + m] == pattern:
                occurrences.append(i)

    return occurrences

# Search for each pattern
all_matches = {}
for pat in patterns:
    matches = rolling_hash_search(text, pat)
    all_matches[pat] = matches

# Flatten to sorted list of (position, pattern) tuples
flat_matches = []
for pat, positions in all_matches.items():
    for pos in positions:
        flat_matches.append((pos, pat))
flat_matches.sort()

result = {
    "matches": all_matches,
    "flat_matches": flat_matches,
    "text_len": len(text),
}
"""

BUGGY = r"""
# Rabin-Karp with double-advance bug on hash collision
text = TEXT
patterns = PATTERNS

BASE = 256
MOD = 1000000007

def compute_hash(s, length):
    h = 0
    for i in range(length):
        h = (h * BASE + ord(s[i])) % MOD
    return h

def rolling_hash_search(text, pattern):
    n = len(text)
    m = len(pattern)
    if m > n or m == 0:
        return []

    h_multiplier = pow(BASE, m - 1, MOD)

    pat_hash = compute_hash(pattern, m)
    txt_hash = compute_hash(text, m)

    occurrences = []
    i = 0

    while i <= n - m:
        if i > 0:
            txt_hash = (txt_hash - ord(text[i - 1]) * h_multiplier) % MOD
            txt_hash = (txt_hash * BASE + ord(text[i + m - 1])) % MOD

        if txt_hash == pat_hash:
            if text[i:i + m] == pattern:
                occurrences.append(i)
                i += 1
            else:
                # BUG: on hash collision (hash matches but string doesn't),
                # advance by 2 instead of 1, skipping a potential match position
                i += 2
                if i <= n - m:
                    # Recompute hash from scratch since we skipped
                    txt_hash = compute_hash(text[i:], m) if i + m <= n else 0
                continue
        i += 1

    return occurrences

all_matches = {}
for pat in patterns:
    matches = rolling_hash_search(text, pat)
    all_matches[pat] = matches

flat_matches = []
for pat, positions in all_matches.items():
    for pos in positions:
        flat_matches.append((pos, pat))
flat_matches.sort()

result = {
    "matches": all_matches,
    "flat_matches": flat_matches,
    "text_len": len(text),
}
"""

def SPEC(text, patterns, result):
    """Verify Rabin-Karp multi-pattern matching."""
    all_matches = result["matches"]

    for pat in patterns:
        reported = all_matches.get(pat, [])

        # Every reported match must be correct
        for pos in reported:
            if pos < 0 or pos + len(pat) > len(text):
                return False
            if text[pos:pos + len(pat)] != pat:
                return False

        # Must find ALL occurrences (brute force)
        true_matches = []
        for i in range(len(text) - len(pat) + 1):
            if text[i:i + len(pat)] == pat:
                true_matches.append(i)

        if reported != true_matches:
            return False

    return True

BUG_DESC = "On hash collision (hash matches but string doesn't match), advances the window by 2 instead of 1, potentially skipping a valid match position."

def _gen():
    import random
    # The bug has TWO issues:
    # 1. On hash collision: advances by 2 instead of 1 (needs rare collision)
    # 2. On actual match: does i+=1 then falls through to i+=1 = advances by 2
    #    This means after finding a match, the next position is SKIPPED.
    #
    # To trigger reliably: create text where a pattern appears at adjacent
    # positions (overlapping occurrences). E.g., pattern "aa" in text "aaa"
    # appears at positions 0 and 1. Buggy code finds pos 0, advances to pos 2,
    # misses pos 1.
    #
    # Keep inputs small for max_size=8.

    cases = [
        # "aa" in "aaaa": correct matches at [0,1,2], buggy skips 1
        {"TEXT": "aaaa", "PATTERNS": ["aa"]},
        # "ab" in "ababab": matches at [0,2,4], buggy finds 0, skips to 2, finds 2, skips to 4, finds 4 - ok
        # But "aba" in "ababa": matches at [0,2], buggy finds 0, skips to 2, finds 2 - ok
        # Need truly adjacent: "aa" in "aaa" -> [0,1], buggy gets [0]
        {"TEXT": "aaa", "PATTERNS": ["aa"]},
        # Multiple overlapping patterns
        {"TEXT": "aaaaa", "PATTERNS": ["aa", "aaa"]},
        # "ab" in "aabab": matches at [1,3]. Not adjacent, so ok.
        # Better: "a" in "aaa" -> [0,1,2], buggy gets [0,2]
        {"TEXT": "aaaa", "PATTERNS": ["a"]},
        # Mixed: some patterns with adjacent matches
        {"TEXT": "aabaa", "PATTERNS": ["a", "aa"]},
        {"TEXT": "abab", "PATTERNS": ["ab"]},  # matches at [0,2], buggy gets [0] (skips to 2, finds 2?) let's check: match at 0, i=0+1=1, then i+=1=2. At i=2 hash is rolled. match at 2, i=2+1=3, i+=1=4. So buggy gets [0,2]. Correct also [0,2]. Need adjacent!
        {"TEXT": "aaab", "PATTERNS": ["aa"]},  # matches at [0,1], buggy gets [0]
    ]
    return random.choice(cases)

INPUT_OVERRIDES = _gen
