"""Edmonds/Chu-Liu algorithm for minimum spanning arborescence in directed graphs.

Bug: when contracting a cycle, doesn't adjust incoming edge weights by
subtracting the weight of the cycle edge being replaced, leading to
wrong total weight in the final arborescence.
"""

CORRECT = r"""
def min_arborescence(n, edges, root):
    # edges: list of (u, v, w) meaning directed edge u->v with weight w
    # Returns (total_weight, edge_list) of minimum spanning arborescence
    # rooted at root, or None if no arborescence exists.

    INF = float('inf')

    # Recursive Edmonds' algorithm
    def edmonds(nodes, edges, root):
        # For each non-root node, find minimum incoming edge
        min_in = {}  # node -> (weight, source, original_edge_idx)
        for i, (u, v, w) in enumerate(edges):
            if v != root and v in nodes and u in nodes:
                if v not in min_in or w < min_in[v][0]:
                    min_in[v] = (w, u, i)

        # Check if all non-root nodes are reachable
        for nd in nodes:
            if nd != root and nd not in min_in:
                return None  # no arborescence exists

        # Check for cycles among minimum edges
        visited = {}
        cycle_nodes = None
        for nd in nodes:
            if nd == root:
                continue
            path = []
            cur = nd
            while cur not in visited and cur != root and cur in min_in:
                visited[cur] = nd
                path.append(cur)
                cur = min_in[cur][1]  # follow parent
            if cur != root and cur in min_in and visited.get(cur) == nd:
                # Found a cycle
                cycle = []
                v = cur
                while True:
                    cycle.append(v)
                    v = min_in[v][1]
                    if v == cur:
                        break
                cycle_nodes = set(cycle)
                break

        if cycle_nodes is None:
            # No cycle, just return the minimum edges
            total = sum(min_in[nd][0] for nd in nodes if nd != root)
            selected = [(min_in[nd][1], nd, min_in[nd][0]) for nd in nodes if nd != root]
            return (total, selected)

        # Contract cycle into a single node
        cycle_id = min(cycle_nodes)
        cycle_weight = sum(min_in[nd][0] for nd in cycle_nodes)

        # Map old nodes to new nodes
        node_map = {}
        for nd in nodes:
            if nd in cycle_nodes:
                node_map[nd] = cycle_id
            else:
                node_map[nd] = nd

        new_nodes = set()
        for nd in nodes:
            new_nodes.add(node_map[nd])

        new_edges = []
        for u, v, w in edges:
            nu = node_map.get(u, u)
            nv = node_map.get(v, v)
            if nu == nv:
                continue  # skip intra-cycle edges
            if nv == cycle_id and v in cycle_nodes:
                # CORRECT: adjust weight by subtracting the cycle edge into v
                adjusted_w = w - min_in[v][0]
                new_edges.append((nu, nv, adjusted_w))
            else:
                new_edges.append((nu, nv, w))

        sub = edmonds(new_nodes, new_edges, root)
        if sub is None:
            return None

        # Reconstruct: total weight = cycle_weight + sub_total
        total = cycle_weight + sub[0]
        return (total, sub[1])

    node_set = set(range(n))
    result = edmonds(node_set, edges, root)
    if result is None:
        return None
    return result[0]

n = N_NODES
edges = EDGES
root = ROOT
result = min_arborescence(n, edges, root)
"""

BUGGY = r"""
def min_arborescence(n, edges, root):
    INF = float('inf')

    def edmonds(nodes, edges, root):
        min_in = {}
        for i, (u, v, w) in enumerate(edges):
            if v != root and v in nodes and u in nodes:
                if v not in min_in or w < min_in[v][0]:
                    min_in[v] = (w, u, i)

        for nd in nodes:
            if nd != root and nd not in min_in:
                return None

        visited = {}
        cycle_nodes = None
        for nd in nodes:
            if nd == root:
                continue
            path = []
            cur = nd
            while cur not in visited and cur != root and cur in min_in:
                visited[cur] = nd
                path.append(cur)
                cur = min_in[cur][1]
            if cur != root and cur in min_in and visited.get(cur) == nd:
                cycle = []
                v = cur
                while True:
                    cycle.append(v)
                    v = min_in[v][1]
                    if v == cur:
                        break
                cycle_nodes = set(cycle)
                break

        if cycle_nodes is None:
            total = sum(min_in[nd][0] for nd in nodes if nd != root)
            selected = [(min_in[nd][1], nd, min_in[nd][0]) for nd in nodes if nd != root]
            return (total, selected)

        cycle_id = min(cycle_nodes)
        cycle_weight = sum(min_in[nd][0] for nd in cycle_nodes)

        node_map = {}
        for nd in nodes:
            if nd in cycle_nodes:
                node_map[nd] = cycle_id
            else:
                node_map[nd] = nd

        new_nodes = set()
        for nd in nodes:
            new_nodes.add(node_map[nd])

        new_edges = []
        for u, v, w in edges:
            nu = node_map.get(u, u)
            nv = node_map.get(v, v)
            if nu == nv:
                continue
            if nv == cycle_id and v in cycle_nodes:
                # BUG: doesn't subtract min_in[v][0], uses raw weight
                new_edges.append((nu, nv, w))
            else:
                new_edges.append((nu, nv, w))

        sub = edmonds(new_nodes, new_edges, root)
        if sub is None:
            return None

        total = cycle_weight + sub[0]
        return (total, sub[1])

    node_set = set(range(n))
    result = edmonds(node_set, edges, root)
    if result is None:
        return None
    return result[0]

n = N_NODES
edges = EDGES
root = ROOT
result = min_arborescence(n, edges, root)
"""


def SPEC(n_nodes, edges, root, result):
    # Brute force: try all possible arborescences (select one incoming edge
    # per non-root node) and find the minimum weight one.
    # This is feasible for small n.
    from itertools import product

    n = n_nodes
    if n <= 1:
        if result is None or result == 0:
            return True
        return False

    # Group edges by target
    incoming = {}
    for u, v, w in edges:
        if v != root:
            if v not in incoming:
                incoming[v] = []
            incoming[v].append((u, w))

    non_root = [v for v in range(n) if v != root]

    # Check if arborescence is possible
    for v in non_root:
        if v not in incoming or len(incoming[v]) == 0:
            return result is None

    # Try all combinations (brute force for small inputs)
    def check_arborescence(selected_edges):
        # selected_edges: list of (parent, node)
        parent = {}
        for p, nd in selected_edges:
            parent[nd] = p

        # Check if root can reach all nodes following parent edges (reversed)
        children = {v: [] for v in range(n)}
        for nd, p in parent.items():
            children[p].append(nd)

        visited = set()
        stack = [root]
        while stack:
            u = stack.pop()
            if u in visited:
                continue
            visited.add(u)
            for c in children[u]:
                stack.append(c)

        return len(visited) == n

    best = None
    edge_choices = []
    for v in non_root:
        edge_choices.append([(u, w, v) for u, w in incoming[v]])

    for combo in product(*edge_choices):
        sel = [(u, v) for u, w, v in combo]
        total = sum(w for u, w, v in combo)
        if check_arborescence(sel):
            if best is None or total < best:
                best = total

    if best is None:
        return result is None

    if result is None:
        return False

    return abs(result - best) < 1e-9


BUG_DESC = (
    "When contracting a cycle, incoming edges to cycle nodes should have "
    "their weight reduced by the weight of the cycle edge they would replace. "
    "The bug uses the raw weight instead, so after expanding the contraction "
    "the total weight includes both the cycle edge and the replacement edge, "
    "overcounting and producing a suboptimal arborescence weight."
)


def _gen():
    import random
    # The bug: when contracting a cycle, incoming edges to cycle nodes are
    # NOT adjusted by subtracting the cycle edge weight. This means the
    # contracted graph has inflated edge weights into the cycle, leading to
    # wrong total arborescence weight.
    #
    # To trigger: need a graph where the minimum incoming edges form a cycle.
    # Then Edmonds' algorithm must contract that cycle, and the weight
    # adjustment matters for choosing the correct incoming edge to break the cycle.
    #
    # Concrete example (4 nodes, root=0):
    # Min incoming edges: 1<-2 (w=1), 2<-3 (w=1), 3<-1 (w=1) -> cycle {1,2,3}
    # Root edges into cycle: 0->1 (w=10), 0->2 (w=5), 0->3 (w=8)
    # Cycle weight = 3.
    # Correct adjustment: edge 0->2 has adjusted weight 5-1=4 (subtract min_in[2]=1)
    # Buggy: uses raw weight 5.
    # Correct total = cycle_weight + adjusted = 3 + 4 = 7 (break cycle at node 2)
    # Buggy total = 3 + 5 = 8 (wrong)
    #
    # Use carefully constructed graphs where the cycle is guaranteed.
    graphs = [
        # Graph 1: 4 nodes. Cycle among {1,2,3}, root=0.
        # Cheapest incoming: 1<-2(w=1), 2<-3(w=1), 3<-1(w=1)
        # Root edges: 0->1(10), 0->2(5), 0->3(8)
        (4, [(2,1,1), (3,2,1), (1,3,1), (0,1,10), (0,2,5), (0,3,8)]),
        # Graph 2: 4 nodes. Cycle {1,2,3} with different weights.
        (4, [(2,1,2), (3,2,3), (1,3,2), (0,1,12), (0,2,6), (0,3,9)]),
        # Graph 3: 5 nodes. Cycle {1,2,3}, node 4 reachable from root.
        (5, [(2,1,1), (3,2,1), (1,3,1), (0,1,10), (0,2,5), (0,3,8), (0,4,3)]),
        # Graph 4: 4 nodes. Cycle {1,2} (2-node cycle).
        # 1<-2(w=2), 2<-1(w=3). Root: 0->1(10), 0->2(8), 0->3(1), 1->3(4)
        (4, [(2,1,2), (1,2,3), (0,1,10), (0,2,8), (0,3,1), (1,3,4)]),
        # Graph 5: 3 nodes. Cycle {1,2}.
        # 1<-2(w=1), 2<-1(w=1). Root: 0->1(5), 0->2(7).
        (3, [(2,1,1), (1,2,1), (0,1,5), (0,2,7)]),
    ]
    n, edges = random.choice(graphs)
    _gen._n = n
    _gen._root = 0
    return edges


def _gen_n():
    return _gen._n


def _gen_root():
    return _gen._root


INPUT_OVERRIDES = {
    "EDGES": _gen,
    "N_NODES": _gen_n,
    "ROOT": _gen_root,
}
