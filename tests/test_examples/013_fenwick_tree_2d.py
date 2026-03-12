"""2D Fenwick tree (Binary Indexed Tree) for 2D prefix sums with point updates.

Bug: In the update function, the outer loop over rows uses `r += 1`
instead of `r += r & (-r)`, so it updates every row index from r to m
instead of only the BIT-relevant rows. This causes overcounting in queries.
"""

CORRECT = r"""
def fenwick_2d(m, n, initial, operations):
    # BIT is 1-indexed, size (m+1) x (n+1)
    tree = [[0] * (n + 1) for _ in range(m + 1)]

    def update(r, c, delta):
        # Add delta to position (r, c) — 1-indexed
        i = r
        while i <= m:
            j = c
            while j <= n:
                tree[i][j] += delta
                j += j & (-j)
            i += i & (-i)

    def query(r, c):
        # Sum of rectangle (1,1) to (r, c) — 1-indexed
        s = 0
        i = r
        while i > 0:
            j = c
            while j > 0:
                s += tree[i][j]
                j -= j & (-j)
            i -= i & (-i)
        return s

    # Initialize the BIT with the initial grid values
    for i in range(m):
        for j in range(n):
            if initial[i][j] != 0:
                update(i + 1, j + 1, initial[i][j])

    # Process operations and collect query results
    results = []
    for op in operations:
        if op[0] == 'update':
            _, r, c, delta = op
            update(r + 1, c + 1, delta)  # Convert 0-indexed to 1-indexed
        elif op[0] == 'query':
            _, r, c = op
            val = query(r + 1, c + 1)  # Convert 0-indexed to 1-indexed
            results.append(val)

    return results

m = M
n = N
initial = INITIAL
operations = OPERATIONS
result = fenwick_2d(m, n, initial, operations)
"""

BUGGY = r"""
def fenwick_2d(m, n, initial, operations):
    # BIT is 1-indexed, size (m+1) x (n+1)
    tree = [[0] * (n + 1) for _ in range(m + 1)]

    def update(r, c, delta):
        # Add delta to position (r, c) — 1-indexed
        i = r
        while i <= m:
            j = c
            while j <= n:
                tree[i][j] += delta
                j += j & (-j)
            # BUG: should be i += i & (-i) but uses i += 1
            # This updates every single row from r to m instead of
            # only the BIT-relevant rows, causing overcounting
            i += 1

    def query(r, c):
        # Sum of rectangle (1,1) to (r, c) — 1-indexed
        s = 0
        i = r
        while i > 0:
            j = c
            while j > 0:
                s += tree[i][j]
                j -= j & (-j)
            i -= i & (-i)
        return s

    # Initialize the BIT with the initial grid values
    for i in range(m):
        for j in range(n):
            if initial[i][j] != 0:
                update(i + 1, j + 1, initial[i][j])

    # Process operations and collect query results
    results = []
    for op in operations:
        if op[0] == 'update':
            _, r, c, delta = op
            update(r + 1, c + 1, delta)  # Convert 0-indexed to 1-indexed
        elif op[0] == 'query':
            _, r, c = op
            val = query(r + 1, c + 1)  # Convert 0-indexed to 1-indexed
            results.append(val)

    return results

m = M
n = N
initial = INITIAL
operations = OPERATIONS
result = fenwick_2d(m, n, initial, operations)
"""


def SPEC(M, N, INITIAL, OPERATIONS, result):
    """Process same operations on a naive 2D array and compare query results."""
    # Build a naive 2D grid
    grid = [[0] * N for _ in range(M)]
    for i in range(M):
        for j in range(N):
            grid[i][j] = INITIAL[i][j]

    def naive_query(r, c):
        """Sum of rectangle (0,0) to (r, c) inclusive."""
        s = 0
        for i in range(r + 1):
            for j in range(c + 1):
                s += grid[i][j]
        return s

    expected_results = []
    for op in OPERATIONS:
        if op[0] == 'update':
            _, r, c, delta = op
            grid[r][c] += delta
        elif op[0] == 'query':
            _, r, c = op
            expected_results.append(naive_query(r, c))

    if not isinstance(result, list):
        return False
    if len(result) != len(expected_results):
        return False
    for i in range(len(result)):
        if result[i] != expected_results[i]:
            return False

    return True


BUG_DESC = (
    "In the update function, the outer loop over rows uses `i += 1` instead "
    "of `i += i & (-i)`. The BIT requires jumping by the lowest set bit to "
    "update only the relevant ancestor nodes, but incrementing by 1 updates "
    "every row from r to m, causing excess additions that corrupt prefix sums."
)


def _generate_inputs():
    import random
    m = random.randint(4, 6)
    n = random.randint(4, 6)
    initial = [[random.randint(1, 5) for _ in range(n)] for _ in range(m)]

    num_ops = random.randint(15, 20)
    operations = []
    for _ in range(num_ops):
        if random.random() < 0.4:
            r = random.randint(0, m - 1)
            c = random.randint(0, n - 1)
            delta = random.randint(-3, 5)
            operations.append(('update', r, c, delta))
        else:
            r = random.randint(0, m - 1)
            c = random.randint(0, n - 1)
            operations.append(('query', r, c))

    # Ensure at least a few queries
    for _ in range(3):
        r = random.randint(0, m - 1)
        c = random.randint(0, n - 1)
        operations.append(('query', r, c))

    return m, n, initial, operations


def _gen_m():
    vals = _generate_inputs()
    _gen_m._cache = vals
    return vals[0]

def _gen_n():
    return _gen_n._cache[1]

def _gen_initial():
    return _gen_initial._cache[2]

def _gen_operations():
    return _gen_operations._cache[3]

# Use a shared cache to keep inputs consistent
def _make_generators():
    import random

    def gen_all():
        m = random.randint(4, 6)
        n = random.randint(4, 6)
        initial = [[random.randint(1, 5) for _ in range(n)] for _ in range(m)]

        num_ops = random.randint(15, 20)
        operations = []
        for _ in range(num_ops):
            if random.random() < 0.4:
                r = random.randint(0, m - 1)
                c = random.randint(0, n - 1)
                delta = random.randint(-3, 5)
                operations.append(('update', r, c, delta))
            else:
                r = random.randint(0, m - 1)
                c = random.randint(0, n - 1)
                operations.append(('query', r, c))
        # Ensure at least a few queries
        for _ in range(3):
            r = random.randint(0, m - 1)
            c = random.randint(0, n - 1)
            operations.append(('query', r, c))

        return m, n, initial, operations

    cache = [None]

    def ensure_cache():
        if cache[0] is None:
            cache[0] = gen_all()

    def get_m():
        ensure_cache()
        return cache[0][0]

    def get_n():
        ensure_cache()
        return cache[0][1]

    def get_initial():
        ensure_cache()
        return cache[0][2]

    def get_operations():
        ensure_cache()
        val = cache[0][3]
        cache[0] = None  # Reset for next call
        return val

    return get_m, get_n, get_initial, get_operations

_get_m, _get_n, _get_initial, _get_operations = _make_generators()

INPUT_OVERRIDES = {
    "M": _get_m,
    "N": _get_n,
    "INITIAL": _get_initial,
    "OPERATIONS": _get_operations,
}
