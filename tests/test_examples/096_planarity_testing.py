"""Left-right planarity test (simplified).
Bug: when embedding back-edges, assigns both endpoints to the same side
instead of opposite sides, accepting non-planar graphs as planar."""

CORRECT = r"""
# Simplified planarity testing using Euler's formula + Kuratowski check
# GRAPH: adjacency list dict {node: [neighbors]} (undirected)
# Returns True if graph is planar, False otherwise

graph = dict(GRAPH)
nodes = sorted(graph.keys())
n = len(nodes)

# Count edges
edge_set = set()
for v in nodes:
    for u in graph.get(v, []):
        e = (min(v, u), max(v, u))
        edge_set.add(e)
m = len(edge_set)

if n <= 4:
    result = True
elif m > 3 * n - 6:
    # Euler's formula: planar graph has at most 3n-6 edges
    result = False
else:
    # Check for K5 or K3,3 subdivision using brute force for small graphs
    # For K5: find 5 vertices that are all pairwise connected (possibly via paths)
    # Simplified: check for K5 minor and K3,3 minor

    adj_set = {}
    for v in nodes:
        adj_set[v] = set(graph.get(v, []))

    # Check K5 subgraph (complete graph on 5 vertices)
    has_k5 = False
    if n >= 5:
        from itertools import combinations
        for combo in combinations(nodes, 5):
            all_connected = True
            for i in range(5):
                for j in range(i + 1, 5):
                    if combo[j] not in adj_set.get(combo[i], set()):
                        all_connected = False
                        break
                if not all_connected:
                    break
            if all_connected:
                has_k5 = True
                break

    # Check K3,3 subgraph
    has_k33 = False
    if n >= 6:
        from itertools import combinations
        for partA in combinations(nodes, 3):
            remaining = [v for v in nodes if v not in partA]
            for partB in combinations(remaining, 3):
                all_cross = True
                for a in partA:
                    for b in partB:
                        if b not in adj_set.get(a, set()):
                            all_cross = False
                            break
                    if not all_cross:
                        break
                if all_cross:
                    has_k33 = True
                    break
            if has_k33:
                break

    if has_k5 or has_k33:
        result = False
    else:
        # Additional check: try to find a planar embedding
        # For small graphs, use the face-counting method
        # Euler: V - E + F = 2 for connected planar graphs
        # Check biconnected components
        # Simplified: if no K5/K33 subgraph and m <= 3n-6, accept
        result = True
"""

BUGGY = r"""
# Simplified planarity testing
# GRAPH: adjacency list dict {node: [neighbors]} (undirected)
# Returns True if graph is planar, False otherwise

graph = dict(GRAPH)
nodes = sorted(graph.keys())
n = len(nodes)

edge_set = set()
for v in nodes:
    for u in graph.get(v, []):
        e = (min(v, u), max(v, u))
        edge_set.add(e)
m = len(edge_set)

if n <= 4:
    result = True
elif m > 3 * n - 6:
    result = False
else:
    adj_set = {}
    for v in nodes:
        adj_set[v] = set(graph.get(v, []))

    # BUG: when checking for K3,3, assigns both partition endpoints to same side
    # This means it checks if partA nodes are connected to each OTHER in partA
    # instead of checking cross-partition edges, missing actual K3,3 subgraphs

    has_k5 = False
    if n >= 5:
        from itertools import combinations
        for combo in combinations(nodes, 5):
            all_connected = True
            for i in range(5):
                for j in range(i + 1, 5):
                    if combo[j] not in adj_set.get(combo[i], set()):
                        all_connected = False
                        break
                if not all_connected:
                    break
            if all_connected:
                has_k5 = True
                break

    has_k33 = False
    if n >= 6:
        from itertools import combinations
        for partA in combinations(nodes, 3):
            remaining = [v for v in nodes if v not in partA]
            for partB in combinations(remaining, 3):
                # BUG: checks within partA instead of between partA and partB
                all_cross = True
                for a in partA:
                    for b in partA:  # BUG: should be partB, not partA
                        if a != b and b not in adj_set.get(a, set()):
                            all_cross = False
                            break
                    if not all_cross:
                        break
                if all_cross:
                    has_k33 = True
                    break
            if has_k33:
                break

    if has_k5 or has_k33:
        result = False
    else:
        result = True
"""


def SPEC(graph, result):
    nodes = sorted(graph.keys())
    n = len(nodes)

    edge_set = set()
    for v in nodes:
        for u in graph.get(v, []):
            edge_set.add((min(v, u), max(v, u)))
    m = len(edge_set)

    # Ground truth planarity check
    if n <= 4:
        expected = True
    elif m > 3 * n - 6:
        expected = False
    else:
        adj_set = {v: set(graph.get(v, [])) for v in nodes}
        has_k5 = False
        has_k33 = False
        if n >= 5:
            from itertools import combinations
            for combo in combinations(nodes, 5):
                ok = True
                for i in range(5):
                    for j in range(i + 1, 5):
                        if combo[j] not in adj_set.get(combo[i], set()):
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    has_k5 = True
                    break
        if n >= 6:
            from itertools import combinations
            for pA in combinations(nodes, 3):
                rem = [v for v in nodes if v not in pA]
                for pB in combinations(rem, 3):
                    ok = True
                    for a in pA:
                        for b in pB:
                            if b not in adj_set.get(a, set()):
                                ok = False
                                break
                        if not ok:
                            break
                    if ok:
                        has_k33 = True
                        break
                if has_k33:
                    break
        expected = not (has_k5 or has_k33)

    return result == expected


BUG_DESC = (
    "When checking for K3,3 subgraph, the inner loop iterates over partA "
    "instead of partB, checking edges within the same partition rather than "
    "cross-partition edges. This causes real K3,3 subgraphs to be missed, "
    "so non-planar graphs are incorrectly reported as planar."
)


def _gen():
    import random
    n = random.randint(5, 8)
    graph = {i: [] for i in range(n)}
    # Sometimes generate K3,3 to trigger the bug
    if random.random() < 0.4 and n >= 6:
        # Build K3,3 on first 6 nodes
        for i in range(3):
            for j in range(3, 6):
                graph[i].append(j)
                graph[j].append(i)
        # Add remaining nodes with random edges
        for i in range(6, n):
            p = random.randint(0, i - 1)
            graph[i].append(p)
            graph[p].append(i)
    else:
        # Random sparse graph
        for i in range(1, n):
            p = random.randint(0, i - 1)
            graph[i].append(p)
            graph[p].append(i)
        for _ in range(n // 2):
            a = random.randint(0, n - 1)
            b = random.randint(0, n - 1)
            if a != b and b not in graph[a]:
                graph[a].append(b)
                graph[b].append(a)
    return graph


INPUT_OVERRIDES = {"GRAPH": _gen}
