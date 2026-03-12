"""Greedy tree decomposition via minimum degree elimination ordering.
Bug: when eliminating a vertex and creating a clique among its remaining
neighbors, uses range(len-1) instead of full pairwise iteration, missing
one edge in the clique."""

CORRECT = r"""
# Greedy tree decomposition using minimum degree elimination
# GRAPH: adjacency list dict {node: set of neighbors}
# Returns (bags, tree_edges, width) where bags[i] = set of nodes in bag i

graph_input = dict(GRAPH)
nodes = sorted(graph_input.keys())
n = len(nodes)

# Work on a copy with sets
adj = {}
for v in nodes:
    adj[v] = set(graph_input.get(v, []))

# Elimination ordering: always eliminate minimum degree vertex
eliminated = set()
bags = []
elim_order = []

for step in range(n):
    # Find vertex with minimum degree among non-eliminated
    best_v = None
    best_deg = n + 1
    for v in nodes:
        if v in eliminated:
            continue
        deg = len(adj[v] - eliminated)
        if deg < best_deg:
            best_deg = deg
            best_v = v

    if best_v is None:
        break

    v = best_v
    elim_order.append(v)

    # Neighbors of v that are not yet eliminated
    neighbors = sorted(adj[v] - eliminated)

    # Create bag: v and its live neighbors
    bag = set([v]) | set(neighbors)
    bags.append(bag)

    # CORRECT: make neighbors into a clique (all pairs)
    for i in range(len(neighbors)):
        for j in range(i + 1, len(neighbors)):
            u, w = neighbors[i], neighbors[j]
            adj[u].add(w)
            adj[w].add(u)

    eliminated.add(v)

# Build tree edges between bags
tree_edges = []
bag_of = {}
for idx, bag in enumerate(bags):
    for v in bag:
        if v not in bag_of:
            bag_of[v] = idx

for i in range(len(bags)):
    for j in range(i + 1, len(bags)):
        if bags[i] & bags[j]:
            tree_edges.append((i, j))
            break

# Compute width
width = max(len(b) - 1 for b in bags) if bags else 0

result = (bags, tree_edges, width)
"""

BUGGY = r"""
# Greedy tree decomposition using minimum degree elimination
# GRAPH: adjacency list dict {node: set of neighbors}
# Returns (bags, tree_edges, width)

graph_input = dict(GRAPH)
nodes = sorted(graph_input.keys())
n = len(nodes)

adj = {}
for v in nodes:
    adj[v] = set(graph_input.get(v, []))

eliminated = set()
bags = []
elim_order = []

for step in range(n):
    best_v = None
    best_deg = n + 1
    for v in nodes:
        if v in eliminated:
            continue
        deg = len(adj[v] - eliminated)
        if deg < best_deg:
            best_deg = deg
            best_v = v

    if best_v is None:
        break

    v = best_v
    elim_order.append(v)
    neighbors = sorted(adj[v] - eliminated)
    bag = set([v]) | set(neighbors)
    bags.append(bag)

    # BUG: range(len(neighbors) - 1) instead of range(len(neighbors))
    # This misses the last neighbor in the outer loop, so the clique
    # among neighbors is incomplete -- the last neighbor pair is never connected
    for i in range(len(neighbors) - 1):
        for j in range(i + 1, len(neighbors)):
            u, w = neighbors[i], neighbors[j]
            adj[u].add(w)
            adj[w].add(u)

    eliminated.add(v)

# Build tree edges between bags
tree_edges = []
bag_of = {}
for idx, bag in enumerate(bags):
    for v in bag:
        if v not in bag_of:
            bag_of[v] = idx

for i in range(len(bags)):
    for j in range(i + 1, len(bags)):
        if bags[i] & bags[j]:
            tree_edges.append((i, j))
            break

width = max(len(b) - 1 for b in bags) if bags else 0

result = (bags, tree_edges, width)
"""


def SPEC(graph, result):
    bags, tree_edges, width = result
    nodes = sorted(graph.keys())
    n = len(nodes)
    if n == 0:
        return width == 0

    # Property 1: every node appears in at least one bag
    all_in_bags = set()
    for b in bags:
        all_in_bags.update(b)
    for v in nodes:
        if v not in all_in_bags:
            return False

    # Property 2: every edge is covered by at least one bag
    for v in nodes:
        for u in graph.get(v, []):
            covered = False
            for b in bags:
                if v in b and u in b:
                    covered = True
                    break
            if not covered:
                return False

    # Property 3: for each node, the bags containing it form a connected subtree
    # Build bag adjacency from tree_edges
    bag_adj = {i: [] for i in range(len(bags))}
    for i, j in tree_edges:
        bag_adj[i].append(j)
        bag_adj[j].append(i)

    for v in nodes:
        containing = [i for i, b in enumerate(bags) if v in b]
        if len(containing) <= 1:
            continue
        # BFS from first containing bag, only through containing bags
        visited = {containing[0]}
        queue = [containing[0]]
        while queue:
            cur = queue.pop(0)
            for nb in bag_adj.get(cur, []):
                if nb not in visited and nb in set(containing):
                    visited.add(nb)
                    queue.append(nb)
        if visited != set(containing):
            return False

    # Width should be max bag size - 1
    expected_width = max(len(b) - 1 for b in bags) if bags else 0
    if width != expected_width:
        return False

    return True


BUG_DESC = (
    "When eliminating a vertex and forming a clique among its remaining "
    "neighbors, the outer loop uses range(len(neighbors)-1) instead of "
    "range(len(neighbors)). This means the last neighbor never appears "
    "as the first element of a pair, potentially missing edges in the "
    "fill-in clique and producing an invalid tree decomposition."
)


def _gen():
    import random
    n = random.randint(5, 9)
    graph = {i: set() for i in range(n)}
    # Build a connected graph
    for i in range(1, n):
        p = random.randint(0, i - 1)
        graph[i].add(p)
        graph[p].add(i)
    # Add extra edges
    for _ in range(n):
        a = random.randint(0, n - 1)
        b = random.randint(0, n - 1)
        if a != b:
            graph[a].add(b)
            graph[b].add(a)
    # Convert to lists for JSON compat
    return {k: list(v) for k, v in graph.items()}


INPUT_OVERRIDES = {"GRAPH": _gen}
