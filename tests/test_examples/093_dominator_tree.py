"""Dominator tree construction (simplified Lengauer-Tarjan).
Bug: in the link-eval step, uses sdom of the parent node instead
of the evaluated node's sdom, producing incorrect dominators."""

CORRECT = r"""
# Simplified dominator tree construction
# GRAPH: adjacency list dict {node: [successors]}
# ROOT: starting node
# Uses a simplified version of Lengauer-Tarjan algorithm

graph = dict(GRAPH)
root = ROOT
nodes = sorted(graph.keys())
n = len(nodes)

# Step 1: DFS numbering
dfnum = {}
vertex = []  # vertex[i] = node with dfnum i
parent_dfs = {}  # parent in DFS tree
visited = set()

def dfs(v, p):
    visited.add(v)
    dfnum[v] = len(vertex)
    vertex.append(v)
    parent_dfs[v] = p
    for w in graph.get(v, []):
        if w not in visited:
            dfs(w, v)

dfs(root, -1)
nn = len(vertex)  # number of reachable nodes

# Step 2: Compute semi-dominators and build dominator tree
sdom = {v: v for v in vertex}
idom = {v: -1 for v in vertex}
ancestor = {v: -1 for v in vertex}
best = {v: v for v in vertex}

def find(v):
    # Path compression with min sdom tracking
    if ancestor[v] == -1:
        return v
    # Iterative find with path compression
    path = []
    u = v
    while ancestor[u] != -1:
        path.append(u)
        u = ancestor[u]
    # u is now the root of the set
    # Compress path and update best
    for w in path:
        if ancestor[w] != -1 and ancestor[ancestor[w]] != -1:
            # CORRECT: compare sdom of best[w] with sdom of best[ancestor[w]]
            if dfnum[sdom[best[ancestor[w]]]] < dfnum[sdom[best[w]]]:
                best[w] = best[ancestor[w]]
            ancestor[w] = u
    return best[v]

def link(v, w):
    ancestor[w] = v

# Build predecessor lists (reverse graph)
pred = {v: [] for v in vertex}
for v in vertex:
    for w in graph.get(v, []):
        if w in dfnum:
            pred[w].append(v)

# Buckets for semi-dominator-to-node mapping
bucket = {v: [] for v in vertex}

# Process vertices in reverse DFS order
for i in range(nn - 1, 0, -1):
    w = vertex[i]
    p = parent_dfs[w]

    # Step 2a: compute sdom
    for v in pred[w]:
        u = find(v)
        if dfnum[sdom[u]] < dfnum[sdom[w]]:
            sdom[w] = sdom[u]

    bucket[sdom[w]].append(w)
    link(p, w)

    # Step 3: process bucket of parent
    for v in bucket.get(p, []):
        u = find(v)
        idom[v] = p if sdom[u] == sdom[v] else u
    bucket[p] = []

# Step 4: finalize idoms
for i in range(1, nn):
    w = vertex[i]
    if idom[w] != sdom[w]:
        idom[w] = idom[idom[w]]

# Build dominator tree as dict
dom_tree = {}
for v in vertex:
    if v == root:
        dom_tree[v] = -1
    else:
        dom_tree[v] = idom[v]

result = dom_tree
"""

BUGGY = r"""
# Simplified dominator tree construction
# GRAPH: adjacency list dict {node: [successors]}
# ROOT: starting node

graph = dict(GRAPH)
root = ROOT
nodes = sorted(graph.keys())
n = len(nodes)

# Step 1: DFS numbering
dfnum = {}
vertex = []
parent_dfs = {}
visited = set()

def dfs(v, p):
    visited.add(v)
    dfnum[v] = len(vertex)
    vertex.append(v)
    parent_dfs[v] = p
    for w in graph.get(v, []):
        if w not in visited:
            dfs(w, v)

dfs(root, -1)
nn = len(vertex)

# Step 2: Compute semi-dominators
sdom = {v: v for v in vertex}
idom = {v: -1 for v in vertex}
ancestor = {v: -1 for v in vertex}
best = {v: v for v in vertex}

def find(v):
    if ancestor[v] == -1:
        return v
    path = []
    u = v
    while ancestor[u] != -1:
        path.append(u)
        u = ancestor[u]
    for w in path:
        if ancestor[w] != -1 and ancestor[ancestor[w]] != -1:
            # BUG: uses sdom of ancestor[w] instead of sdom of best[ancestor[w]]
            # This checks the parent's sdom directly, not the best along the path
            if dfnum[sdom[ancestor[w]]] < dfnum[sdom[best[w]]]:
                best[w] = ancestor[w]  # also wrong: sets best to ancestor, not best[ancestor]
            ancestor[w] = u
    return best[v]

def link(v, w):
    ancestor[w] = v

# Build predecessor lists
pred = {v: [] for v in vertex}
for v in vertex:
    for w in graph.get(v, []):
        if w in dfnum:
            pred[w].append(v)

bucket = {v: [] for v in vertex}

for i in range(nn - 1, 0, -1):
    w = vertex[i]
    p = parent_dfs[w]

    for v in pred[w]:
        u = find(v)
        if dfnum[sdom[u]] < dfnum[sdom[w]]:
            sdom[w] = sdom[u]

    bucket[sdom[w]].append(w)
    link(p, w)

    for v in bucket.get(p, []):
        u = find(v)
        idom[v] = p if sdom[u] == sdom[v] else u
    bucket[p] = []

for i in range(1, nn):
    w = vertex[i]
    if idom[w] != sdom[w]:
        idom[w] = idom[idom[w]]

dom_tree = {}
for v in vertex:
    if v == root:
        dom_tree[v] = -1
    else:
        dom_tree[v] = idom[v]

result = dom_tree
"""


def SPEC(graph, root, result):
    # Verify dominator tree: for each node v != root, idom[v] must dominate v
    # i.e., every path from root to v must pass through idom[v]
    if not result:
        return True
    if result.get(root) != -1:
        return False

    # Find all reachable nodes from root
    reachable = set()
    stack = [root]
    while stack:
        v = stack.pop()
        if v in reachable:
            continue
        reachable.add(v)
        for w in graph.get(v, []):
            stack.append(w)

    # Every reachable node should be in result
    for v in reachable:
        if v not in result:
            return False

    # Verify domination: for each v, idom[v] dominates v
    # A dominates B if removing A disconnects root from B
    for v in reachable:
        if v == root:
            continue
        d = result[v]
        if d == -1:
            return False
        if d not in reachable:
            return False
        # Check d dominates v: remove d, check if root can reach v
        vis = set()
        q = [root]
        while q:
            u = q.pop()
            if u == d or u in vis:
                continue
            vis.add(u)
            for w in graph.get(u, []):
                q.append(w)
        # v should NOT be reachable without d
        if v in vis:
            return False
    return True


BUG_DESC = (
    "In the find/path-compression step, uses sdom of the ancestor node "
    "directly instead of sdom of best[ancestor]. This means the semi-dominator "
    "tracking along compressed paths is wrong, leading to incorrect idoms."
)


def _gen_graph():
    import random
    n = random.randint(5, 10)
    graph = {i: [] for i in range(n)}
    # Ensure connected DAG-like structure from node 0
    for i in range(1, n):
        p = random.randint(0, i - 1)
        graph[p].append(i)
    # Add some cross/back edges
    for _ in range(n):
        a = random.randint(0, n - 1)
        b = random.randint(0, n - 1)
        if a != b and b not in graph[a]:
            graph[a].append(b)
    return graph


def _gen_root():
    return 0


INPUT_OVERRIDES = {"GRAPH": _gen_graph, "ROOT": _gen_root}
