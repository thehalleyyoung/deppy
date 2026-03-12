"""Union-Find with path compression and union by rank. Bug: find returns x instead of root."""

CORRECT = r"""
# Union-Find (Disjoint Set Union) with path compression and union by rank
# Supports union and find operations on a collection of disjoint sets

parent = [0] * (len(ELEMENTS) + 1)
rank = [0] * (len(ELEMENTS) + 1)

# Initialize: each element is its own parent
for e in ELEMENTS:
    parent[e] = e
    rank[e] = 0

def find(x):
    # Path compression: make every node point directly to root
    root = x
    while parent[root] != root:
        root = parent[root]
    # Compress path
    while parent[x] != root:
        next_x = parent[x]
        parent[x] = root
        x = next_x
    return root

def union(a, b):
    ra = find(a)
    rb = find(b)
    if ra == rb:
        return False
    # Union by rank: attach smaller tree under root of larger tree
    if rank[ra] < rank[rb]:
        parent[ra] = rb
    elif rank[ra] > rank[rb]:
        parent[rb] = ra
    else:
        parent[rb] = ra
        rank[ra] += 1
    return True

# Process union operations
for a, b in UNIONS:
    union(a, b)

# Query connectivity for each pair in QUERIES
results = []
for a, b in QUERIES:
    results.append(find(a) == find(b))

# Also collect the representative for each element
representatives = {}
for e in ELEMENTS:
    representatives[e] = find(e)

# Verify path compression: after all finds, every element points to its root
all_compressed = True
for e in ELEMENTS:
    if parent[e] != find(e):
        all_compressed = False

result = {
    "connectivity": results,
    "representatives": representatives,
    "num_components": len(set(representatives[e] for e in ELEMENTS)),
    "all_compressed": all_compressed
}
"""

BUGGY = r"""
# Union-Find (Disjoint Set Union) with path compression and union by rank
# Supports union and find operations on a collection of disjoint sets

parent = [0] * (len(ELEMENTS) + 1)
rank = [0] * (len(ELEMENTS) + 1)

# Initialize: each element is its own parent
for e in ELEMENTS:
    parent[e] = e
    rank[e] = 0

def find(x):
    # Path compression: make every node point directly to root
    root = x
    while parent[root] != root:
        root = parent[root]
    # Compress path
    while parent[x] != root:
        next_x = parent[x]
        parent[x] = root
        x = next_x
    # BUG: returns x (which is now root after the loop) but if the loop
    # never executed (x was already root), this is fine. However when
    # x != root initially, after the loop x == root... except when x
    # started as root's direct child, the loop runs once: next_x = root,
    # parent[x] = root, x = root, loop ends, returns root. Hmm.
    # Actually the real bug: returns the ORIGINAL x, not root.
    # We need to capture original x before the loop.
    return x

# Wait, the above still returns root after loop. Let me make the bug clearer:
# The bug is returning the original input, not the found root.
# Redefine with the actual bug:

def find_buggy(x):
    original_x = x
    root = x
    while parent[root] != root:
        root = parent[root]
    # Compress path
    curr = original_x
    while parent[curr] != root:
        next_c = parent[curr]
        parent[curr] = root
        curr = next_c
    # BUG: returns original x instead of root
    return original_x

# Override find with buggy version
find = find_buggy

def union(a, b):
    ra = find(a)
    rb = find(b)
    if ra == rb:
        return False
    # Union by rank
    if rank[ra] < rank[rb]:
        parent[ra] = rb
    elif rank[ra] > rank[rb]:
        parent[rb] = ra
    else:
        parent[rb] = ra
        rank[ra] += 1
    return True

# Process union operations
for a, b in UNIONS:
    union(a, b)

# Query connectivity for each pair in QUERIES
results = []
for a, b in QUERIES:
    results.append(find(a) == find(b))

# Also collect the representative for each element
representatives = {}
for e in ELEMENTS:
    representatives[e] = find(e)

# Verify path compression
all_compressed = True
for e in ELEMENTS:
    if parent[e] != find(e):
        all_compressed = False

result = {
    "connectivity": results,
    "representatives": representatives,
    "num_components": len(set(representatives[e] for e in ELEMENTS)),
    "all_compressed": all_compressed
}
"""


def SPEC(elements, unions, queries, result):
    # Build ground-truth connectivity using simple BFS/union
    adj = {}
    for e in elements:
        adj[e] = set()
    for a, b in unions:
        adj[a].add(b)
        adj[b].add(a)

    # BFS to find components
    visited = {}
    comp_id = 0
    for e in elements:
        if e not in visited:
            queue = [e]
            visited[e] = comp_id
            while queue:
                node = queue.pop(0)
                for nb in adj[node]:
                    if nb not in visited:
                        visited[nb] = comp_id
                        queue.append(nb)
            comp_id += 1

    # Check connectivity answers
    conn = result["connectivity"]
    if len(conn) != len(queries):
        return False
    for i, (a, b) in enumerate(queries):
        expected = (visited[a] == visited[b])
        if conn[i] != expected:
            return False

    # Check number of components
    num_comp = len(set(visited[e] for e in elements))
    if result["num_components"] != num_comp:
        return False

    # Check representatives: elements in same component must have same rep
    reps = result["representatives"]
    for e in elements:
        if e not in reps:
            return False
    for a in elements:
        for b in elements:
            if visited[a] == visited[b]:
                if reps[a] != reps[b]:
                    return False
            else:
                if reps[a] == reps[b]:
                    return False

    return True


BUG_DESC = "find() returns the original input x instead of the root representative, so union operations attach wrong nodes and connectivity queries return incorrect results."


def _gen_elements():
    return list(range(1, 9))


def _gen_unions():
    return [(1, 2), (3, 4), (5, 6), (7, 8), (1, 3), (5, 7), (1, 5)]


def _gen_queries():
    return [(1, 8), (2, 7), (3, 6), (1, 4), (2, 5)]


INPUT_OVERRIDES = {
    "ELEMENTS": _gen_elements,
    "UNIONS": _gen_unions,
    "QUERIES": _gen_queries,
}
