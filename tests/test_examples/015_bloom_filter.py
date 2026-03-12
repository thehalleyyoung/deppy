"""Bloom filter with k hash functions for approximate set membership.

Bug: When querying, uses `any()` instead of `all()` — returns True if
ANY of the k hash positions is set, rather than requiring ALL k to be set.
This dramatically increases the false positive rate.
"""

CORRECT = r"""
def bloom_filter(m, k, operations):
    # Initialize bit array of size m
    bits = [0] * m

    def get_hashes(item):
        # k different hash functions using different seeds
        hashes = []
        for seed in range(k):
            # Combine item with seed for different hash functions
            h = hash(str(item) + '|' + str(seed))
            hashes.append(h % m)
        return hashes

    def bf_insert(item):
        for pos in get_hashes(item):
            bits[pos] = 1

    def bf_query(item):
        positions = get_hashes(item)
        # Must have ALL k bits set for a positive result
        return all(bits[pos] == 1 for pos in positions)

    results = []
    for op in operations:
        if op[0] == 'insert':
            bf_insert(op[1])
        elif op[0] == 'query':
            found = bf_query(op[1])
            results.append((op[1], found))

    return results

m_val = M_SIZE
k_val = K_HASHES
operations = OPERATIONS
result = bloom_filter(m_val, k_val, operations)
"""

BUGGY = r"""
def bloom_filter(m, k, operations):
    # Initialize bit array of size m
    bits = [0] * m

    def get_hashes(item):
        # k different hash functions using different seeds
        hashes = []
        for seed in range(k):
            # Combine item with seed for different hash functions
            h = hash(str(item) + '|' + str(seed))
            hashes.append(h % m)
        return hashes

    def bf_insert(item):
        for pos in get_hashes(item):
            bits[pos] = 1

    def bf_query(item):
        positions = get_hashes(item)
        # BUG: uses any() instead of all()
        # Returns True if ANY bit is set, not ALL bits
        # This dramatically increases false positives since after
        # several inserts, most bit positions will be set
        return any(bits[pos] == 1 for pos in positions)

    results = []
    for op in operations:
        if op[0] == 'insert':
            bf_insert(op[1])
        elif op[0] == 'query':
            found = bf_query(op[1])
            results.append((op[1], found))

    return results

m_val = M_SIZE
k_val = K_HASHES
operations = OPERATIONS
result = bloom_filter(m_val, k_val, operations)
"""


def SPEC(M_SIZE, K_HASHES, OPERATIONS, result):
    """Verify bloom filter properties:
    (1) No false negatives — every inserted item queries True
    (2) Results match a reference implementation
    (3) At least one non-inserted item queries False (catches any-vs-all bug)
    """
    if not isinstance(result, list):
        return False

    # Build reference implementation
    bits = [0] * M_SIZE
    inserted = set()

    def get_hashes(item):
        hashes = []
        for seed in range(K_HASHES):
            h = hash(str(item) + '|' + str(seed))
            hashes.append(h % M_SIZE)
        return hashes

    expected_results = []
    for op in OPERATIONS:
        if op[0] == 'insert':
            inserted.add(op[1])
            for pos in get_hashes(op[1]):
                bits[pos] = 1
        elif op[0] == 'query':
            positions = get_hashes(op[1])
            found = all(bits[pos] == 1 for pos in positions)
            expected_results.append((op[1], found))

    # Check length matches
    if len(result) != len(expected_results):
        return False

    # (1) No false negatives: every inserted item must query True
    for item, found in result:
        if item in inserted and not found:
            return False

    # (2) Results match reference implementation exactly
    for i in range(len(result)):
        if result[i][0] != expected_results[i][0]:
            return False
        if result[i][1] != expected_results[i][1]:
            return False

    # (3) At least one non-inserted item should query False
    # (This catches the any-vs-all bug: with any(), almost everything is True)
    # Only apply this heuristic when k > 0 and the filter is large enough
    # relative to the number of inserts — otherwise the correct implementation
    # can legitimately return True for all queries (e.g. k=0 means all()
    # over an empty list, which is always True).
    if K_HASHES > 0 and M_SIZE >= 32:
        non_inserted_queries = [
            (item, found) for item, found in result if item not in inserted
        ]
        if len(non_inserted_queries) >= 5:
            has_false = any(not found for _, found in non_inserted_queries)
            if not has_false:
                return False

    return True


BUG_DESC = (
    "When querying the bloom filter, the code uses `any()` instead of `all()`. "
    "A bloom filter requires ALL k hash positions to be set for a positive "
    "result, but the bug returns True if ANY single bit is set. After several "
    "inserts, most bit positions are set, so nearly every query returns True, "
    "drastically inflating the false positive rate."
)


def _generate_inputs():
    import random
    import itertools

    m_size = 64
    k_hashes = 3

    # Generate insert items: random 3-char strings from 'abcdefgh'
    chars = 'abcdefgh'
    all_combos = [''.join(c) for c in itertools.product(chars, repeat=3)]
    random.shuffle(all_combos)

    num_inserts = random.randint(8, 12)
    insert_items = all_combos[:num_inserts]

    # Non-inserted items for queries
    remaining = all_combos[num_inserts:]
    num_non_inserted = random.randint(5, 10)
    non_inserted = remaining[:num_non_inserted]

    operations = []
    # Insert all items first
    for item in insert_items:
        operations.append(('insert', item))

    # Query all inserted items
    for item in insert_items:
        operations.append(('query', item))

    # Query non-inserted items
    for item in non_inserted:
        operations.append(('query', item))

    return m_size, k_hashes, operations


def _make_generators():
    cache = [None]

    def ensure_cache():
        if cache[0] is None:
            cache[0] = _generate_inputs()

    def get_m():
        ensure_cache()
        return cache[0][0]

    def get_k():
        ensure_cache()
        return cache[0][1]

    def get_ops():
        ensure_cache()
        val = cache[0][2]
        cache[0] = None  # Reset for next call
        return val

    return get_m, get_k, get_ops

_get_m, _get_k, _get_ops = _make_generators()

INPUT_OVERRIDES = {
    "M_SIZE": _get_m,
    "K_HASHES": _get_k,
    "OPERATIONS": _get_ops,
}
