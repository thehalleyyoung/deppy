"""Burrows-Wheeler Transform (BWT) and its inverse.

Computes the BWT of a string by sorting all rotations and taking the last
column. The inverse reconstructs the original string using the L-F mapping
(Last-to-First column mapping).

Bug: in the inverse transform, the reconstruction follows the first column
instead of the last column when building the L-F mapping. This produces
a permuted string that is not the original.
"""

CORRECT = r"""
def bwt_transform(text):
    # Append sentinel character (lexicographically smallest)
    s = text + "\x00"
    n = len(s)
    # Build all rotations and sort
    rotations = []
    for i in range(n):
        rotations.append((s[i:] + s[:i], i))
    rotations.sort(key=lambda x: x[0])
    # BWT is the last column of sorted rotations
    bwt_str = ""
    for rot, idx in rotations:
        bwt_str += rot[-1]
    # Also record the row where the original string appears
    orig_row = 0
    for i, (rot, idx) in enumerate(rotations):
        if idx == 0:
            orig_row = i
            break
    return bwt_str, orig_row

def bwt_inverse(bwt_str, orig_row):
    # Reconstruct the original string from BWT
    n = len(bwt_str)
    if n == 0:
        return ""

    # The last column is bwt_str (L)
    last_col = list(bwt_str)
    # The first column is the sorted version of L
    first_col = sorted(last_col)

    # Build L-F mapping: for each position i in last column,
    # find the corresponding position in first column
    # We need to handle duplicate characters carefully
    # For each char, the k-th occurrence in L maps to k-th occurrence in F

    # Count occurrences for ranking
    lf_map = [0] * n

    # Rank each character in last column
    last_rank = [0] * n
    char_count_l = {}
    for i in range(n):
        c = last_col[i]
        if c not in char_count_l:
            char_count_l[c] = 0
        last_rank[i] = char_count_l[c]
        char_count_l[c] += 1

    # Rank each character in first column
    first_rank = [0] * n
    char_count_f = {}
    first_positions = {}
    for i in range(n):
        c = first_col[i]
        if c not in char_count_f:
            char_count_f[c] = 0
            first_positions[c] = []
        first_rank[i] = char_count_f[c]
        first_positions[c].append(i)
        char_count_f[c] += 1

    # CORRECT L-F mapping: position i in L maps to position in F
    # where the same-ranked occurrence of the same character appears
    for i in range(n):
        c = last_col[i]
        rank = last_rank[i]
        lf_map[i] = first_positions[c][rank]

    # Follow the mapping starting from orig_row
    # Read L[current] then advance: this reads the string backwards
    result_chars = []
    current = orig_row
    for _ in range(n):
        result_chars.append(last_col[current])
        current = lf_map[current]

    # Reverse since LF mapping traverses backwards
    result_chars.reverse()

    # Remove sentinel
    result = "".join(result_chars)
    if result and result[-1] == "\x00":
        result = result[:-1]
    elif result and result[0] == "\x00":
        result = result[1:]
    return result

def bwt_roundtrip(text):
    # Perform BWT and inverse, return both the BWT and reconstructed text
    bwt_str, orig_row = bwt_transform(text)
    reconstructed = bwt_inverse(bwt_str, orig_row)
    return {"bwt": bwt_str, "orig_row": orig_row, "reconstructed": reconstructed}

text = TEXT
result = bwt_roundtrip(text)
"""

BUGGY = r"""
def bwt_transform(text):
    s = text + "\x00"
    n = len(s)
    rotations = []
    for i in range(n):
        rotations.append((s[i:] + s[:i], i))
    rotations.sort(key=lambda x: x[0])
    bwt_str = ""
    for rot, idx in rotations:
        bwt_str += rot[-1]
    orig_row = 0
    for i, (rot, idx) in enumerate(rotations):
        if idx == 0:
            orig_row = i
            break
    return bwt_str, orig_row

def bwt_inverse(bwt_str, orig_row):
    n = len(bwt_str)
    if n == 0:
        return ""

    last_col = list(bwt_str)
    first_col = sorted(last_col)

    lf_map = [0] * n

    last_rank = [0] * n
    char_count_l = {}
    for i in range(n):
        c = last_col[i]
        if c not in char_count_l:
            char_count_l[c] = 0
        last_rank[i] = char_count_l[c]
        char_count_l[c] += 1

    first_rank = [0] * n
    char_count_f = {}
    first_positions = {}
    for i in range(n):
        c = first_col[i]
        if c not in char_count_f:
            char_count_f[c] = 0
            first_positions[c] = []
        first_rank[i] = char_count_f[c]
        first_positions[c].append(i)
        char_count_f[c] += 1

    # BUG: builds F-F mapping instead of L-F mapping
    # Uses first_col[i] (first column) instead of last_col[i] (last column)
    # This maps first column to itself rather than last to first
    for i in range(n):
        c = first_col[i]  # BUG: should be last_col[i]
        rank = first_rank[i]  # BUG: should be last_rank[i]
        lf_map[i] = first_positions[c][rank]

    result_chars = []
    current = orig_row
    for _ in range(n):
        result_chars.append(last_col[current])
        current = lf_map[current]

    result_chars.reverse()

    result = "".join(result_chars)
    if result and result[-1] == "\x00":
        result = result[:-1]
    elif result and result[0] == "\x00":
        result = result[1:]
    return result

def bwt_roundtrip(text):
    bwt_str, orig_row = bwt_transform(text)
    reconstructed = bwt_inverse(bwt_str, orig_row)
    return {"bwt": bwt_str, "orig_row": orig_row, "reconstructed": reconstructed}

text = TEXT
result = bwt_roundtrip(text)
"""


def SPEC(TEXT, result):
    text = TEXT
    # Verify BWT roundtrip: reconstructed must equal original
    if not isinstance(result, dict):
        return False
    if "bwt" not in result or "reconstructed" not in result:
        return False
    # The reconstructed text must match the original
    if result["reconstructed"] != text:
        return False
    # BWT string must be a permutation of text + sentinel
    bwt_str = result["bwt"]
    full_text = text + "\x00"
    if sorted(bwt_str) != sorted(full_text):
        return False
    return True


BUG_DESC = (
    "In the inverse BWT, the L-F mapping should map each position in the "
    "last column (L) to its corresponding position in the first column (F). "
    "The bug builds the mapping from the first column to itself (F-F mapping) "
    "by reading characters from first_col instead of last_col. This creates "
    "an identity-like mapping that fails to reconstruct the original string."
)


def _gen_text():
    import random
    alphabet = "abcde"
    length = random.randint(5, 12)
    return "".join(random.choice(alphabet) for _ in range(length))


INPUT_OVERRIDES = {
    "TEXT": _gen_text,
}
