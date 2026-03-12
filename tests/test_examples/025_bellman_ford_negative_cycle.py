"""Bellman-Ford shortest paths with negative cycle detection and reporting."""

import random

CORRECT = r"""
def solve(n, edges, source):
    # edges: list of (u, v, weight)
    # Returns: (distances, has_negative_cycle, cycle_or_none)
    # cycle_or_none: list of node ids forming a negative-weight cycle, or None

    INF = float('inf')
    dist = [INF] * n
    pred = [-1] * n
    dist[source] = 0

    # Relax all edges n-1 times
    for i in range(n - 1):
        updated = False
        for u, v, w in edges:
            if dist[u] != INF and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                pred[v] = u
                updated = True
        if not updated:
            break

    # Check for negative cycle: one more iteration
    cycle_node = -1
    for u, v, w in edges:
        if dist[u] != INF and dist[u] + w < dist[v]:
            dist[v] = dist[u] + w
            pred[v] = u
            cycle_node = v

    if cycle_node == -1:
        # No negative cycle
        # Convert INF to None for unreachable
        distances = [d if d != INF else None for d in dist]
        return (distances, False, None)

    # Trace back to find the cycle
    # Go back n steps to ensure we're in the cycle
    v = cycle_node
    for _ in range(n):
        v = pred[v]

    # Now v is guaranteed to be in the cycle; trace it
    cycle = []
    cur = v
    while True:
        cycle.append(cur)
        cur = pred[cur]
        if cur == v:
            cycle.append(v)
            break

    cycle.reverse()

    distances = [d if d != INF else None for d in dist]
    return (distances, True, cycle)

result = solve(N, EDGES, SOURCE)
"""

BUGGY = r"""
def solve(n, edges, source):
    INF = float('inf')
    dist = [INF] * n
    pred = [-1] * n
    dist[source] = 0

    # BUG: n-2 iterations instead of n-1
    for i in range(n - 2):
        updated = False
        for u, v, w in edges:
            if dist[u] != INF and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                pred[v] = u
                updated = True
        if not updated:
            break

    # Check for negative cycle
    cycle_node = -1
    for u, v, w in edges:
        if dist[u] != INF and dist[u] + w < dist[v]:
            dist[v] = dist[u] + w
            pred[v] = u
            cycle_node = v

    if cycle_node == -1:
        distances = [d if d != INF else None for d in dist]
        return (distances, False, None)

    # Trace back to find cycle
    v = cycle_node
    for _ in range(n):
        v = pred[v]

    cycle = []
    cur = v
    while True:
        cycle.append(cur)
        cur = pred[cur]
        if cur == v:
            cycle.append(v)
            break

    cycle.reverse()

    distances = [d if d != INF else None for d in dist]
    return (distances, True, cycle)

result = solve(N, EDGES, SOURCE)
"""

BUG_DESC = (
    "The main relaxation phase runs n-2 iterations instead of the required n-1. "
    "This means shortest paths requiring exactly n-1 edges are not fully relaxed, "
    "leading to incorrect distances. Additionally, the nth-iteration negative cycle "
    "check can false-positive (detecting a 'cycle' that is actually just an "
    "under-relaxed path) or false-negative (missing a real cycle whose detection "
    "depends on having correct n-1 iteration distances)."
)


def _bellman_ford_reference(n, edges, source):
    """Reference Bellman-Ford implementation (used by SPEC)."""
    INF = float('inf')
    ref_dist = [INF] * n
    ref_dist[source] = 0
    for _ in range(n - 1):
        for u, v, w in edges:
            if ref_dist[u] != INF and ref_dist[u] + w < ref_dist[v]:
                ref_dist[v] = ref_dist[u] + w
    ref_has_cycle = False
    for u, v, w in edges:
        if ref_dist[u] != INF and ref_dist[u] + w < ref_dist[v]:
            ref_has_cycle = True
            break
    return ref_dist, ref_has_cycle


def SPEC(N, EDGES, SOURCE, result):
    """Verify Bellman-Ford results."""
    n, edges, source = N, EDGES, SOURCE
    if not isinstance(result, tuple) or len(result) != 3:
        return False
    distances, has_neg_cycle, cycle = result

    ref_dist, ref_has_cycle = _bellman_ford_reference(n, edges, source)

    # Check agreement on negative cycle existence
    if has_neg_cycle != ref_has_cycle:
        return False

    if not has_neg_cycle:
        # Verify distances match reference
        INF = float('inf')
        for i in range(n):
            ref_d = ref_dist[i] if ref_dist[i] != INF else None
            if distances[i] != ref_d:
                return False
        return True
    else:
        # Negative cycle: verify the reported cycle
        if cycle is None or len(cycle) < 2:
            return False

        # cycle should be [v0, v1, ..., vk, v0] (starts and ends same node)
        if cycle[0] != cycle[-1]:
            return False

        # Verify it's an actual cycle with negative weight
        edge_set = {}
        for u, v, w in edges:
            if (u, v) not in edge_set:
                edge_set[(u, v)] = w
            else:
                edge_set[(u, v)] = min(edge_set[(u, v)], w)

        total_weight = 0
        for i in range(len(cycle) - 1):
            u, v = cycle[i], cycle[i + 1]
            if (u, v) not in edge_set:
                return False
            total_weight += edge_set[(u, v)]

        if total_weight >= 0:
            return False

        return True


def _gen_input():
    n = random.randint(5, 8)
    source = 0
    edges = []

    # Create a chain 0->1->2->...->n-1 with edges listed in REVERSE order.
    # Reverse ordering forces Bellman-Ford to need exactly n-1 iterations
    # (each iteration relaxes only one more node along the chain).
    chain_edges = []
    for i in range(n - 1):
        w = random.randint(1, 5)
        chain_edges.append((i, i + 1, w))
    chain_edges.reverse()  # critical: reverse order to force worst case
    edges.extend(chain_edges)

    # Add some random shortcut edges (listed BEFORE chain edges won't help
    # since chain edges are already reversed)
    for _ in range(random.randint(1, 4)):
        u = random.randint(0, n - 1)
        v = random.randint(0, n - 1)
        if u != v:
            w = random.randint(1, 10)
            edges.append((u, v, w))

    # Half the time, add a negative cycle (3 nodes forming a triangle
    # with total weight < 0)
    if random.random() < 0.5:
        cycle_nodes = random.sample(range(n), min(3, n))
        for i in range(len(cycle_nodes)):
            u = cycle_nodes[i]
            v = cycle_nodes[(i + 1) % len(cycle_nodes)]
            edges.append((u, v, -4))

    return {"n": n, "edges": edges, "source": source}


def _make_generators():
    cache = [None]

    def ensure_cache():
        if cache[0] is None:
            cache[0] = _gen_input()

    def get_n():
        ensure_cache()
        return cache[0]["n"]

    def get_edges():
        ensure_cache()
        return cache[0]["edges"]

    def get_source():
        ensure_cache()
        val = cache[0]["source"]
        cache[0] = None  # Reset for next call
        return val

    return get_n, get_edges, get_source

_get_n, _get_edges, _get_source = _make_generators()

INPUT_OVERRIDES = {
    "N": _get_n,
    "EDGES": _get_edges,
    "SOURCE": _get_source,
}
