"""Counting sort preserving stability. Bug: iterates forward through input array instead
of backward when placing elements, destroying stability of equal-keyed elements."""

CORRECT = r"""
# Counting sort that preserves stability (relative order of equal elements)
# Each element is a (key, value) pair; we sort by key

items = ITEMS  # list of (key, value) pairs
max_key = MAX_KEY  # keys are in range [0, max_key]

n = len(items)

# Count occurrences of each key
count = [0] * (max_key + 1)
for key, val in items:
    count[key] += 1

# Compute cumulative count (prefix sums)
# count[k] = starting index for key k in the output
for i in range(1, max_key + 1):
    count[i] += count[i - 1]

# Build output by iterating BACKWARD through input (preserves stability)
output = [None] * n
for i in range(n - 1, -1, -1):
    key, val = items[i]
    count[key] -= 1
    output[count[key]] = (key, val)

result = {
    "sorted": output,
    "n": n,
    "max_key": max_key,
    "original": items,
}
"""

BUGGY = r"""
# Counting sort with stability bug
items = ITEMS
max_key = MAX_KEY

n = len(items)

count = [0] * (max_key + 1)
for key, val in items:
    count[key] += 1

for i in range(1, max_key + 1):
    count[i] += count[i - 1]

# BUG: iterates FORWARD instead of backward
# This destroys the stability property: equal-keyed elements
# appear in reversed order relative to their original positions
output = [None] * n
for i in range(n):
    key, val = items[i]
    count[key] -= 1
    output[count[key]] = (key, val)

result = {
    "sorted": output,
    "n": n,
    "max_key": max_key,
    "original": items,
}
"""

def SPEC(items, max_key, result):
    """Verify counting sort correctness and stability."""
    sorted_items = result["sorted"]
    n = result["n"]

    if len(sorted_items) != n:
        return False

    # Check sorted order by key
    for i in range(n - 1):
        if sorted_items[i][0] > sorted_items[i + 1][0]:
            return False

    # Check all elements are present (as a multiset)
    from collections import Counter
    orig_counts = Counter((k, v) for k, v in items)
    sort_counts = Counter((k, v) for k, v in sorted_items)
    if orig_counts != sort_counts:
        return False

    # Check STABILITY: among elements with the same key,
    # their relative order must match the original input order
    from collections import defaultdict
    orig_order = defaultdict(list)
    for i, (key, val) in enumerate(items):
        orig_order[key].append((val, i))

    sorted_order = defaultdict(list)
    for i, (key, val) in enumerate(sorted_items):
        sorted_order[key].append(val)

    for key in orig_order:
        orig_vals = [v for v, idx in orig_order[key]]
        sort_vals = sorted_order[key]
        if orig_vals != sort_vals:
            return False

    return True

BUG_DESC = "Iterates forward through the input array instead of backward when placing elements into the output, reversing the relative order of equal-keyed elements and destroying stability."

def _gen():
    import random
    # Bug: iterates forward instead of backward, reversing relative order
    # of equal-keyed elements (destroying stability).
    #
    # To trigger: need at least 2 elements with the same key but different
    # values. The forward iteration places them in reversed order.
    #
    # Use index as value to track original order. Keep small for max_size=8.
    # Use very few distinct keys to guarantee many duplicates.
    n = random.randint(4, 8)
    max_key = random.randint(1, 2)  # 1-2 distinct keys = guaranteed duplicates
    items = []
    for i in range(n):
        key = random.randint(0, max_key)
        val = i  # unique values track original order
        items.append((key, val))
    # Ensure at least one key has 2+ elements (for stability to matter)
    # Force by making first two share a key
    if n >= 2:
        shared_key = random.randint(0, max_key)
        items[0] = (shared_key, 0)
        items[1] = (shared_key, 1)
    return {"ITEMS": items, "MAX_KEY": max_key}

INPUT_OVERRIDES = _gen
