"""Manacher's algorithm for longest palindromic substring. Bug: when expanding beyond the
rightmost boundary, sets center = i + p[i] instead of center = i, corrupting future lookups."""

CORRECT = r"""
# Manacher's algorithm for all palindromic substrings
# Returns the longest palindromic substring and all palindrome radii

def manacher(s):
    # Transform: "abc" -> "^#a#b#c#$"
    t = "^#" + "#".join(s) + "#$"
    n = len(t)
    p = [0] * n  # p[i] = radius of palindrome centered at t[i]
    center = 0
    right = 0  # rightmost boundary of any palindrome found so far

    for i in range(1, n - 1):
        mirror = 2 * center - i

        if i < right:
            p[i] = min(right - i, p[mirror])

        # Expand palindrome centered at i
        while t[i + p[i] + 1] == t[i - p[i] - 1]:
            p[i] += 1

        # Update center and right boundary
        if i + p[i] > right:
            center = i
            right = i + p[i]

    # Find longest palindrome
    max_len = 0
    max_center = 0
    for i in range(1, n - 1):
        if p[i] > max_len:
            max_len = p[i]
            max_center = i

    # Convert back to original string indices
    start = (max_center - max_len) // 2
    longest = s[start:start + max_len]

    # Collect all palindrome radii in original string
    # For odd-length palindromes centered at original index i:
    #   transformed index = 2*i + 2, radius in original = p[2*i+2] // 2... not quite
    # We just return the full p array and the longest
    return longest, p, t

text = TEXT
longest, p_array, transformed = manacher(text)

# Also find all maximal palindromic substrings
palindromes = []
for i in range(1, len(transformed) - 1):
    if p_array[i] > 0:
        # Convert transformed index to original
        orig_start = (i - p_array[i]) // 2
        orig_len = p_array[i]
        if orig_len > 0:
            pal = text[orig_start:orig_start + orig_len]
            if len(pal) > 1:
                palindromes.append((orig_start, pal))

result = {
    "longest": longest,
    "text": text,
    "all_palindromes": palindromes,
}
"""

BUGGY = r"""
# Manacher's algorithm with bug in center update

def manacher(s):
    t = "^#" + "#".join(s) + "#$"
    n = len(t)
    p = [0] * n
    center = 0
    right = 0

    for i in range(1, n - 1):
        mirror = 2 * center - i

        if i < right:
            p[i] = min(right - i, p[mirror])

        while t[i + p[i] + 1] == t[i - p[i] - 1]:
            p[i] += 1

        if i + p[i] > right:
            # BUG: sets center to i + p[i] instead of i
            # This corrupts the mirror calculation for subsequent positions
            center = i + p[i]
            right = i + p[i]

    max_len = 0
    max_center = 0
    for i in range(1, n - 1):
        if p[i] > max_len:
            max_len = p[i]
            max_center = i

    start = (max_center - max_len) // 2
    longest = s[start:start + max_len]

    return longest, p, t

text = TEXT
longest, p_array, transformed = manacher(text)

palindromes = []
for i in range(1, len(transformed) - 1):
    if p_array[i] > 0:
        orig_start = (i - p_array[i]) // 2
        orig_len = p_array[i]
        if orig_len > 0:
            pal = text[orig_start:orig_start + orig_len]
            if len(pal) > 1:
                palindromes.append((orig_start, pal))

result = {
    "longest": longest,
    "text": text,
    "all_palindromes": palindromes,
}
"""

def SPEC(text, result):
    """Verify Manacher's palindrome results."""
    longest = result["longest"]

    # The longest must actually be a palindrome
    if longest != longest[::-1]:
        return False

    # The longest must appear in text
    if longest not in text:
        return False

    # Check it truly is the longest palindromic substring
    # Brute force for verification
    best = ""
    for i in range(len(text)):
        for j in range(i + 1, len(text) + 1):
            sub = text[i:j]
            if sub == sub[::-1] and len(sub) > len(best):
                best = sub
    if len(longest) != len(best):
        return False

    # Verify all reported palindromes are actual palindromes in text
    for start, pal in result["all_palindromes"]:
        if pal != pal[::-1]:
            return False
        if text[start:start + len(pal)] != pal:
            return False

    return True

BUG_DESC = "Sets center = i + p[i] instead of center = i when updating the rightmost boundary, corrupting the mirror calculation for subsequent positions."

def _gen():
    import random
    # Bug: center = i + p[i] instead of center = i when updating rightmost boundary.
    # This corrupts the mirror calculation: mirror = 2*center - i becomes
    # mirror = 2*(prev_i + p[prev_i]) - i instead of 2*prev_i - i.
    # This can cause mirror to be a huge positive number, potentially out of
    # bounds or pointing to wrong p[] values.
    #
    # The bug triggers when:
    # 1. A palindrome is found that updates right boundary (i + p[i] > right)
    # 2. The next position uses the mirror optimization (i < right)
    # 3. The corrupted mirror index gives wrong p[mirror] value
    #
    # Strings with adjacent/overlapping palindromes reliably trigger this.
    # "abacaba" has palindromes at multiple positions.
    # "abaaba" has the mirror optimization exercised.
    # Keep strings short (max_size=8).

    cases = [
        "abacaba",      # Many nested palindromes
        "abaaba",       # Overlapping palindromes
        "abcbabcba",    # Long palindrome with sub-palindromes
        "aabaab",       # Mirror optimization exercised
        "cbbd",         # Simple case
        "abacabac",     # Repeated structure
        "aabaa",        # Symmetric with inner palindrome
        "abababa",      # Alternating pattern, many palindromes
        "abbaabba",     # Double palindrome
    ]
    return random.choice(cases)

INPUT_OVERRIDES = {"TEXT": _gen}
