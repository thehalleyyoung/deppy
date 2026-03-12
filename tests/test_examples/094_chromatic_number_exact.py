"""Exact chromatic number via inclusion-exclusion counting of independent sets.
Bug: in the independent set counting, miscounts the empty set contribution
(starts subset iteration from 1 instead of 0), giving wrong chromatic polynomial."""

CORRECT = r"""
# Exact chromatic number via inclusion-exclusion
# GRAPH: adjacency list dict {node: [neighbors]}
# Uses the deletion-contraction / inclusion-exclusion method
# Counts independent sets of each size using Moebius inversion

graph = dict(GRAPH)
nodes = sorted(graph.keys())
n = len(nodes)

if n == 0:
    result = 0
elif n == 1:
    result = 1
else:
    # Build adjacency matrix as bitmask for fast subset checks
    node_idx = {v: i for i, v in enumerate(nodes)}
    adj_mask = [0] * n
    for v in nodes:
        for u in graph.get(v, []):
            if u in node_idx:
                adj_mask[node_idx[v]] |= (1 << node_idx[u])

    # Count independent sets for each subset using DP
    # is_independent[S] = True if subset S is independent
    # We count number of independent sets of the complement graph
    # independent_sets[S] = number of independent subsets of S
    total_subsets = 1 << n
    indep_count = [0] * total_subsets

    # CORRECT: iterate from 0 (empty set is independent)
    for S in range(total_subsets):
        is_indep = True
        bits = S
        while bits:
            v_bit = bits & (-bits)
            v_idx = v_bit.bit_length() - 1
            # Check if v is adjacent to any other node in S
            if adj_mask[v_idx] & S & ~v_bit:
                is_indep = False
                break
            bits &= bits - 1
        if is_indep:
            indep_count[S] = 1

    # Count independent sets per subset size using inclusion-exclusion
    # For chromatic number: find minimum k such that chromatic poly P(k) > 0
    # P(k) = sum over S of (-1)^|V\S| * k^(number of connected components of G[S])
    # Simpler: use the fact that chi(G) = min k such that sum_{S subset V} (-1)^{|V|-|S|} * k^{c(S)} > 0
    # where c(S) = number of connected components of induced subgraph G[S]

    # Easier approach: count independent sets and use inclusion-exclusion
    # chi(G) = min k s.t. P(G, k) > 0
    # P(G, k) = sum_{i=0}^{n} a_i * k^i  where a_i comes from broken circuit theorem

    # Practical approach for small n: try coloring with k colors
    def can_color(k):
        # Try to k-color using inclusion-exclusion counting
        # Number of proper k-colorings = sum_{S} (-1)^{n-|S|} * k^{components(S)}
        total = 0
        for S in range(total_subsets):
            subset_nodes = []
            for i in range(n):
                if S & (1 << i):
                    subset_nodes.append(i)
            sz = len(subset_nodes)
            # Count connected components of induced subgraph G[S]
            if sz == 0:
                comp = 0
            else:
                visited_local = set()
                comp = 0
                for start in subset_nodes:
                    if start not in visited_local:
                        comp += 1
                        stack = [start]
                        while stack:
                            cur = stack.pop()
                            if cur in visited_local:
                                continue
                            visited_local.add(cur)
                            for j in subset_nodes:
                                if j != cur and (adj_mask[cur] & (1 << j)) and j not in visited_local:
                                    stack.append(j)
            sign = 1 if (n - sz) % 2 == 0 else -1
            total += sign * (k ** comp)
        return total > 0

    chi = 1
    while chi <= n:
        if can_color(chi):
            break
        chi += 1

    result = chi
"""

BUGGY = r"""
# Exact chromatic number via inclusion-exclusion
# GRAPH: adjacency list dict {node: [neighbors]}

graph = dict(GRAPH)
nodes = sorted(graph.keys())
n = len(nodes)

if n == 0:
    result = 0
elif n == 1:
    result = 1
else:
    node_idx = {v: i for i, v in enumerate(nodes)}
    adj_mask = [0] * n
    for v in nodes:
        for u in graph.get(v, []):
            if u in node_idx:
                adj_mask[node_idx[v]] |= (1 << node_idx[u])

    total_subsets = 1 << n

    def can_color(k):
        total = 0
        # BUG: starts from S=1, skipping the empty set (S=0)
        # The empty set contributes (-1)^n * k^0 = (-1)^n
        # Missing this term corrupts the chromatic polynomial
        for S in range(1, total_subsets):
            subset_nodes = []
            for i in range(n):
                if S & (1 << i):
                    subset_nodes.append(i)
            sz = len(subset_nodes)
            if sz == 0:
                comp = 0
            else:
                visited_local = set()
                comp = 0
                for start in subset_nodes:
                    if start not in visited_local:
                        comp += 1
                        stack = [start]
                        while stack:
                            cur = stack.pop()
                            if cur in visited_local:
                                continue
                            visited_local.add(cur)
                            for j in subset_nodes:
                                if j != cur and (adj_mask[cur] & (1 << j)) and j not in visited_local:
                                    stack.append(j)
            sign = 1 if (n - sz) % 2 == 0 else -1
            total += sign * (k ** comp)
        return total > 0

    chi = 1
    while chi <= n:
        if can_color(chi):
            break
        chi += 1

    result = chi
"""


def SPEC(graph, result):
    nodes = sorted(graph.keys())
    n = len(nodes)
    if n == 0:
        return result == 0
    if n == 1:
        return result == 1
    # Verify: result colors should suffice (greedy check is not exact)
    # Instead verify by brute-force for small graphs
    node_idx = {v: i for i, v in enumerate(nodes)}
    edges = set()
    for v in nodes:
        for u in graph.get(v, []):
            if u in node_idx:
                a, b = node_idx[v], node_idx[u]
                edges.add((min(a, b), max(a, b)))

    def try_color(k):
        # Try all k-colorings
        coloring = [0] * n
        def backtrack(idx):
            if idx == n:
                return True
            for c in range(k):
                coloring[idx] = c
                ok = True
                for j in range(idx):
                    if (min(j, idx), max(j, idx)) in edges and coloring[j] == c:
                        ok = False
                        break
                if ok:
                    if backtrack(idx + 1):
                        return True
            return False
        return backtrack(0)

    if n > 12:
        return True  # skip verification for large instances
    # chi should be the minimum k
    if not try_color(result):
        return False
    if result > 1 and try_color(result - 1):
        return False
    return True


BUG_DESC = (
    "In the inclusion-exclusion sum for the chromatic polynomial, "
    "the loop starts from subset S=1 instead of S=0, skipping the "
    "empty set. This omits the (-1)^n term, corrupting the count."
)


def _gen():
    import random
    n = random.randint(3, 6)
    graph = {i: [] for i in range(n)}
    # Random graph with moderate density
    for i in range(n):
        for j in range(i + 1, n):
            if random.random() < 0.4:
                graph[i].append(j)
                graph[j].append(i)
    return graph


INPUT_OVERRIDES = {"GRAPH": _gen}
