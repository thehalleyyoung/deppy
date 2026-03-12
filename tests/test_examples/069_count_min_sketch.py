"""Count-min sketch for approximate frequency counting.

Bug: uses max instead of min when querying (should take minimum across
all hash rows, but takes maximum, consistently overestimating).
"""

CORRECT = r"""
def count_min_sketch(data):
    stream = data["stream"]
    queries = data["queries"]
    width = data["width"]
    depth = data["depth"]

    # Initialize the sketch matrix
    sketch = [[0] * width for _ in range(depth)]

    # Hash functions: use different seeds for each row
    def hash_fn(row, key):
        # Simple hash family: (a * key + b) mod prime mod width
        primes = [1000000007, 1000000009, 1000000021, 1000000033,
                  1000000087, 1000000093, 1000000097, 1000000103]
        seeds_a = [31, 37, 41, 43, 47, 53, 59, 61]
        seeds_b = [7, 13, 17, 19, 23, 29, 31, 37]
        h = (seeds_a[row % len(seeds_a)] * hash(key) + seeds_b[row % len(seeds_b)])
        return h % primes[row % len(primes)] % width

    # Process stream: increment counts
    for item in stream:
        for row in range(depth):
            col = hash_fn(row, item)
            sketch[row][col] += 1

    # Answer queries: take MINIMUM across all rows
    results = []
    for q in queries:
        estimates = []
        for row in range(depth):
            col = hash_fn(row, q)
            estimates.append(sketch[row][col])
        # CORRECT: take minimum for tightest upper bound
        results.append(min(estimates))

    # Also compute exact counts for reference
    exact = {}
    for item in stream:
        exact[item] = exact.get(item, 0) + 1

    return {"estimates": results, "exact": {q: exact.get(q, 0) for q in queries}}

data = DATA
result = count_min_sketch(data)
"""

BUGGY = r"""
def count_min_sketch(data):
    stream = data["stream"]
    queries = data["queries"]
    width = data["width"]
    depth = data["depth"]

    sketch = [[0] * width for _ in range(depth)]

    def hash_fn(row, key):
        primes = [1000000007, 1000000009, 1000000021, 1000000033,
                  1000000087, 1000000093, 1000000097, 1000000103]
        seeds_a = [31, 37, 41, 43, 47, 53, 59, 61]
        seeds_b = [7, 13, 17, 19, 23, 29, 31, 37]
        h = (seeds_a[row % len(seeds_a)] * hash(key) + seeds_b[row % len(seeds_b)])
        return h % primes[row % len(primes)] % width

    for item in stream:
        for row in range(depth):
            col = hash_fn(row, item)
            sketch[row][col] += 1

    results = []
    for q in queries:
        estimates = []
        for row in range(depth):
            col = hash_fn(row, q)
            estimates.append(sketch[row][col])
        # BUG: uses max instead of min
        # This gives the loosest upper bound, severely overestimating
        results.append(max(estimates))

    exact = {}
    for item in stream:
        exact[item] = exact.get(item, 0) + 1

    return {"estimates": results, "exact": {q: exact.get(q, 0) for q in queries}}

data = DATA
result = count_min_sketch(data)
"""


def SPEC(data, result):
    if not isinstance(result, dict):
        return False
    if "estimates" not in result or "exact" not in result:
        return False

    queries = data["queries"]
    estimates = result["estimates"]
    exact = result["exact"]

    if len(estimates) != len(queries):
        return False

    # Count-min sketch guarantees:
    # 1. estimate >= exact count (never underestimates)
    # 2. estimate <= exact count + total_stream_size / width (error bound)
    stream = data["stream"]
    total = len(stream)
    width = data["width"]
    error_bound = total / width

    # Compute actual exact counts
    true_counts = {}
    for item in stream:
        true_counts[item] = true_counts.get(item, 0) + 1

    for i, q in enumerate(queries):
        true_count = true_counts.get(q, 0)

        # Verify exact counts match
        if exact.get(q, 0) != true_count:
            return False

        # Estimate must be >= true count (no underestimation)
        if estimates[i] < true_count:
            return False

        # Estimate should be reasonably bounded
        # With depth hash functions, error is bounded by total/width
        # with probability at least 1 - (1/e)^depth
        # We use a generous bound: 3x the theoretical error
        if estimates[i] > true_count + 3 * error_bound:
            return False

    return True


BUG_DESC = (
    "When querying, takes max(estimates) across all hash rows instead of "
    "min(estimates). The count-min sketch relies on taking the minimum to "
    "get the tightest upper bound. Using max causes significant overestimation, "
    "often exceeding the theoretical error bound."
)


def _gen():
    import random
    # Create a stream with skewed frequencies
    items = list(range(1, 21))
    stream = []
    # Some items appear frequently, others rarely
    for item in items:
        freq = random.choice([1, 2, 3, 10, 20])
        stream.extend([item] * freq)
    random.shuffle(stream)
    # Use a narrow width to increase collisions and make the bug manifest
    width = 8
    depth = 4
    # Query both frequent and rare items
    queries = random.sample(items, min(8, len(items)))
    return {"stream": stream, "queries": queries, "width": width, "depth": depth}


INPUT_OVERRIDES = {"DATA": _gen}
