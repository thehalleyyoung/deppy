"""Maximum weight closure via min-cut reduction. Bug: connects positive-weight nodes to sink instead of only negative-weight nodes."""

CORRECT = r"""
# Maximum Weight Closure via min-cut (max-flow) reduction
# A closure of a directed graph is a subset S of vertices such that
# for every edge (u,v), if u in S then v in S.
# Maximum weight closure = closure with maximum total weight.
#
# Reduction: source S connects to positive-weight nodes (capacity = weight),
# negative-weight nodes connect to sink T (capacity = |weight|),
# original edges get infinite capacity.
# Max weight closure = sum(positive weights) - max_flow(S, T)

# WEIGHTS[i] = weight of node i, DAG_EDGES = list of (u, v) directed edges
n = len(WEIGHTS)
S = n      # source
T = n + 1  # sink
total_nodes = n + 2

# Adjacency list for flow network: adj[u] = list of [v, capacity, index_of_reverse_edge]
adj = [[] for _ in range(total_nodes)]

def add_edge(u, v, cap):
    adj[u].append([v, cap, len(adj[v])])
    adj[v].append([u, 0, len(adj[u]) - 1])

# Add edges from source to positive-weight nodes
for i in range(n):
    if WEIGHTS[i] > 0:
        add_edge(S, i, WEIGHTS[i])

# Add edges from negative-weight nodes to sink
for i in range(n):
    if WEIGHTS[i] < 0:
        add_edge(i, T, -WEIGHTS[i])

# Add original DAG edges with infinite capacity
INF = 10**9
for u, v in DAG_EDGES:
    add_edge(u, v, INF)

# BFS-based max-flow (Edmonds-Karp)
def bfs(source, sink, parent):
    visited = [False] * total_nodes
    visited[source] = True
    queue = [source]
    while queue:
        u = queue.pop(0)
        for i, (v, cap, _) in enumerate(adj[u]):
            if not visited[v] and cap > 0:
                visited[v] = True
                parent[v] = (u, i)
                if v == sink:
                    return True
                queue.append(v)
    return False

def max_flow():
    flow = 0
    parent = [None] * total_nodes
    while bfs(S, T, parent):
        # Find min capacity along the path
        path_flow = float('inf')
        v = T
        while v != S:
            u, idx = parent[v]
            path_flow = min(path_flow, adj[u][idx][1])
            v = u
        # Update capacities
        v = T
        while v != S:
            u, idx = parent[v]
            adj[u][idx][1] -= path_flow
            rev_idx = adj[u][idx][2]
            adj[v][rev_idx][1] += path_flow
            v = u
        flow += path_flow
        parent = [None] * total_nodes
    return flow

mf = max_flow()
sum_positive = sum(w for w in WEIGHTS if w > 0)
max_closure_weight = sum_positive - mf

# Find the closure: BFS from source in residual graph
visited = [False] * total_nodes
queue = [S]
visited[S] = True
while queue:
    u = queue.pop(0)
    for v, cap, _ in adj[u]:
        if not visited[v] and cap > 0:
            visited[v] = True
            queue.append(v)

closure = sorted([i for i in range(n) if visited[i]])

result = {
    "max_weight": max_closure_weight,
    "closure": closure,
}
"""

BUGGY = r"""
# Maximum Weight Closure via min-cut (max-flow) reduction

n = len(WEIGHTS)
S = n
T = n + 1
total_nodes = n + 2

adj = [[] for _ in range(total_nodes)]

def add_edge(u, v, cap):
    adj[u].append([v, cap, len(adj[v])])
    adj[v].append([u, 0, len(adj[u]) - 1])

# Add edges from source to positive-weight nodes
for i in range(n):
    if WEIGHTS[i] > 0:
        add_edge(S, i, WEIGHTS[i])

# BUG: connects ALL nodes to sink with |weight| capacity, including positive-weight nodes
# Should only connect negative-weight nodes to sink
for i in range(n):
    if WEIGHTS[i] < 0:
        add_edge(i, T, -WEIGHTS[i])
    elif WEIGHTS[i] > 0:
        # BUG: positive-weight nodes should NOT connect to sink
        add_edge(i, T, WEIGHTS[i])

# Add original DAG edges with infinite capacity
INF = 10**9
for u, v in DAG_EDGES:
    add_edge(u, v, INF)

# BFS-based max-flow (Edmonds-Karp)
def bfs(source, sink, parent):
    visited = [False] * total_nodes
    visited[source] = True
    queue = [source]
    while queue:
        u = queue.pop(0)
        for i, (v, cap, _) in enumerate(adj[u]):
            if not visited[v] and cap > 0:
                visited[v] = True
                parent[v] = (u, i)
                if v == sink:
                    return True
                queue.append(v)
    return False

def max_flow():
    flow = 0
    parent = [None] * total_nodes
    while bfs(S, T, parent):
        path_flow = float('inf')
        v = T
        while v != S:
            u, idx = parent[v]
            path_flow = min(path_flow, adj[u][idx][1])
            v = u
        v = T
        while v != S:
            u, idx = parent[v]
            adj[u][idx][1] -= path_flow
            rev_idx = adj[u][idx][2]
            adj[v][rev_idx][1] += path_flow
            v = u
        flow += path_flow
        parent = [None] * total_nodes
    return flow

mf = max_flow()
sum_positive = sum(w for w in WEIGHTS if w > 0)
max_closure_weight = sum_positive - mf

# Find the closure
visited = [False] * total_nodes
queue = [S]
visited[S] = True
while queue:
    u = queue.pop(0)
    for v, cap, _ in adj[u]:
        if not visited[v] and cap > 0:
            visited[v] = True
            queue.append(v)

closure = sorted([i for i in range(n) if visited[i]])

result = {
    "max_weight": max_closure_weight,
    "closure": closure,
}
"""


def SPEC(weights, dag_edges, result):
    n = len(weights)
    closure = result["closure"]
    max_w = result["max_weight"]

    # Check closure property: for every edge (u,v), if u in closure then v in closure
    closure_set = set(closure)
    for u, v in dag_edges:
        if u in closure_set and v not in closure_set:
            return False

    # Check weight equals sum of weights of closure members
    actual_weight = sum(weights[i] for i in closure)
    if actual_weight != max_w:
        return False

    # Brute force: find the true maximum weight closure
    best = 0  # empty closure has weight 0
    for mask in range(1 << n):
        s = set()
        for i in range(n):
            if (mask >> i) & 1:
                s.add(i)
        # Check closure property
        valid = True
        for u, v in dag_edges:
            if u in s and v not in s:
                valid = False
                break
        if valid:
            w = sum(weights[i] for i in s)
            if w > best:
                best = w

    if max_w != best:
        return False

    return True


BUG_DESC = "Connects positive-weight nodes to the sink in addition to source, doubling their flow capacity and causing max-flow to over-count, yielding incorrect (lower) closure weights."


def _gen_weights():
    # Node 0: +5, Node 1: +3, Node 2: -2, Node 3: +4, Node 4: -6
    return [5, 3, -2, 4, -6]


def _gen_dag_edges():
    # 0 -> 2, 1 -> 2, 3 -> 4 (selecting 0 or 1 forces 2; selecting 3 forces 4)
    return [(0, 2), (1, 2), (3, 4)]


INPUT_OVERRIDES = {
    "WEIGHTS": _gen_weights,
    "DAG_EDGES": _gen_dag_edges,
}
