"""Ukkonen's suffix tree construction (simplified) for substring queries.

Builds a suffix tree incrementally using Ukkonen's algorithm with the
active point mechanism and suffix links (simplified). Supports checking
whether a pattern is a substring of the text.

Bug: when a new internal node is created and the active_length falls
through (no matching edge), the 'remaining' counter is not properly
incremented. This causes suffixes to be skipped during construction,
resulting in a suffix tree that is missing some suffixes.
"""

CORRECT = r"""
def build_suffix_tree(text):
    # Simplified Ukkonen construction returning edge-label dict tree
    # Each node is a dict mapping first-char -> (start, end, child_node)
    # We use explicit end indices (not global end trick) for simplicity
    n = len(text)
    root = {}
    # Active point: (active_node, active_edge_char, active_length)
    active_node = root
    active_edge = None
    active_length = 0
    remaining = 0

    for i in range(n):
        remaining += 1
        last_new_internal = None

        while remaining > 0:
            if active_length == 0:
                active_edge = text[i]

            if active_edge not in active_node:
                # No matching edge: create a new leaf
                active_node[active_edge] = (i, n, {})
                if last_new_internal is not None:
                    # suffix link would go here in full impl
                    last_new_internal = None
                remaining -= 1
                # Rule 1: move to root (simplified suffix link)
                active_node = root
                active_length = 0
                if remaining > 0:
                    active_edge = text[i - remaining + 1]
                continue

            # There is an edge starting with active_edge
            start, end, child = active_node[active_edge]
            edge_len = end - start

            if active_length >= edge_len:
                # Walk down the edge
                active_node = child
                active_length -= edge_len
                if active_length == 0 and remaining > 0:
                    active_edge = text[i - remaining + 1 + (i - remaining + 1 < n and 0 or 0)]
                    if i - remaining + 1 + edge_len < n:
                        active_edge = text[i]
                else:
                    active_edge = text[i - remaining + 1 + edge_len] if i - remaining + 1 + edge_len < n else text[i]
                continue

            if text[start + active_length] == text[i]:
                # Character matches: extend active_length
                active_length += 1
                if last_new_internal is not None:
                    last_new_internal = None
                break

            # Split the edge
            new_internal = {}
            new_internal[text[start + active_length]] = (start + active_length, end, child)
            new_internal[text[i]] = (i, n, {})
            active_node[active_edge] = (start, start + active_length, new_internal)

            if last_new_internal is not None:
                last_new_internal = None
            last_new_internal = new_internal

            remaining -= 1
            active_node = root
            active_length = 0
            if remaining > 0:
                active_edge = text[i - remaining + 1]
            continue

    return root

def find_substring(root, text, pattern):
    # Check if pattern is a substring by walking the suffix tree
    node = root
    i = 0
    while i < len(pattern):
        ch = pattern[i]
        if ch not in node:
            return False
        start, end, child = node[ch]
        edge_len = end - start
        # Match characters along the edge
        j = 0
        while j < edge_len and i < len(pattern):
            if text[start + j] != pattern[i]:
                return False
            i += 1
            j += 1
        if i < len(pattern):
            node = child
    return True

def check_all_substrings(text, patterns):
    # Build suffix tree and check each pattern
    if not text:
        return [False] * len(patterns)
    # Append unique terminator
    full_text = text + "$"
    root = build_suffix_tree(full_text)
    results = []
    for pat in patterns:
        results.append(find_substring(root, full_text, pat))
    return results

text = TEXT
patterns = PATTERNS
result = check_all_substrings(text, patterns)
"""

BUGGY = r"""
def build_suffix_tree(text):
    n = len(text)
    root = {}
    active_node = root
    active_edge = None
    active_length = 0
    remaining = 0

    for i in range(n):
        # BUG: remaining is incremented here but when we fall through
        # the walk-down without creating anything, we lose track
        remaining += 1
        last_new_internal = None

        while remaining > 0:
            if active_length == 0:
                active_edge = text[i]

            if active_edge not in active_node:
                active_node[active_edge] = (i, n, {})
                if last_new_internal is not None:
                    last_new_internal = None
                remaining -= 1
                active_node = root
                active_length = 0
                if remaining > 0:
                    active_edge = text[i - remaining + 1]
                continue

            start, end, child = active_node[active_edge]
            edge_len = end - start

            if active_length >= edge_len:
                active_node = child
                active_length -= edge_len
                # BUG: should continue the while loop to process remaining
                # but instead breaks, failing to process this suffix
                # The remaining counter is not re-adjusted
                break

            if text[start + active_length] == text[i]:
                active_length += 1
                if last_new_internal is not None:
                    last_new_internal = None
                break

            new_internal = {}
            new_internal[text[start + active_length]] = (start + active_length, end, child)
            new_internal[text[i]] = (i, n, {})
            active_node[active_edge] = (start, start + active_length, new_internal)

            if last_new_internal is not None:
                last_new_internal = None
            last_new_internal = new_internal

            remaining -= 1
            active_node = root
            active_length = 0
            if remaining > 0:
                active_edge = text[i - remaining + 1]
            continue

    return root

def find_substring(root, text, pattern):
    node = root
    i = 0
    while i < len(pattern):
        ch = pattern[i]
        if ch not in node:
            return False
        start, end, child = node[ch]
        edge_len = end - start
        j = 0
        while j < edge_len and i < len(pattern):
            if text[start + j] != pattern[i]:
                return False
            i += 1
            j += 1
        if i < len(pattern):
            node = child
    return True

def check_all_substrings(text, patterns):
    if not text:
        return [False] * len(patterns)
    full_text = text + "$"
    root = build_suffix_tree(full_text)
    results = []
    for pat in patterns:
        results.append(find_substring(root, full_text, pat))
    return results

text = TEXT
patterns = PATTERNS
result = check_all_substrings(text, patterns)
"""


def SPEC(text, patterns, result):
    # Verify substring queries by brute-force search
    if not isinstance(result, list):
        return False
    if len(result) != len(patterns):
        return False
    for i, pat in enumerate(patterns):
        expected = pat in text
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "When the active point walks down past an edge (active_length >= edge_len), "
    "the correct version continues the inner while loop to keep processing "
    "the current suffix. The buggy version breaks out of the loop, losing "
    "track of the remaining suffixes that need insertion. This causes some "
    "suffixes to be missing from the tree, making certain valid substrings "
    "unfindable."
)


def _gen():
    import random
    # The bug: when active_length >= edge_len (walk-down case), the buggy
    # code breaks out of the inner loop instead of continuing. This loses
    # track of remaining suffixes, causing some suffixes to be missing.
    #
    # Triggers: strings over a small alphabet with repeated substrings that
    # force deep tree traversal and walk-downs. Binary strings (alphabet 'ab')
    # with length >= 8 reliably trigger this.
    #
    # We generate the text and its true substrings together so they're
    # consistent (the old code generated text/patterns independently).

    alphabet = "ab"
    length = random.randint(8, 12)
    text = "".join(random.choice(alphabet) for _ in range(length))

    patterns = []
    # Extract ALL substrings of length 2-5 as patterns (these are the ones
    # that the buggy tree is most likely to miss)
    substr_set = set()
    for i in range(len(text)):
        for j in range(i + 2, min(i + 6, len(text) + 1)):
            substr_set.add(text[i:j])
    patterns = list(substr_set)

    # Also add some patterns that should NOT match, to verify no false positives
    for _ in range(2):
        p = "".join(random.choice("abc") for _ in range(random.randint(2, 4)))
        patterns.append(p)

    return {"TEXT": text, "PATTERNS": patterns}

INPUT_OVERRIDES = _gen
