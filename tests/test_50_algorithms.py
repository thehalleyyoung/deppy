#!/usr/bin/env python3
"""50 Core Algorithm Verification Suite.

Tests the sheaf-theoretic predicate refinement engine on 50 pairs of
(correct, buggy) implementations with formal specifications expressed
as Python predicates (refinement types).

Each algorithm has:
  - correct: str    — correct implementation
  - buggy: str      — subtly buggy implementation (1-3 line diff)
  - spec: Callable  — refinement type as Python bool function
  - bug_desc: str   — what the bug is

Run:  PYTHONPATH=deppy/src python deppy/tests/test_50_algorithms.py
"""
from __future__ import annotations

import sys, os, time, random, math, traceback
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from deppy.render.predicate_refine import (
    verify_with_spec, SheafSpecVerifier,
    is_sorted, is_permutation, is_stable_sorted, is_heap, preserves_multiset,
    search_correct, search_leftmost, nth_element_correct,
    distances_correct, is_topological_order, is_spanning_tree,
    is_minimum_spanning_tree, all_pairs_shortest, is_scc_decomposition,
    max_flow_correct, is_subsequence, is_common_subsequence,
    lcs_length_correct, edit_distance_correct, all_pattern_occurrences,
    is_suffix_array, z_array_correct, longest_palindrome_correct,
    knapsack_correct, lis_length_correct, coin_change_correct,
    matrix_chain_correct, max_subarray_correct, rod_cutting_correct,
    is_prime, gcd_correct, extended_gcd_correct, mod_exp_correct,
    sieve_correct, crt_correct, is_convex_hull, closest_pair_correct,
    is_bst, is_balanced, trie_contains_all,
    fenwick_prefix_correct, interval_schedule_correct,
    sqrt_correct, gaussian_elim_correct, union_find_correct,
    bipartite_matching_correct,
    _gen_list_int, _gen_sorted_list_int, _gen_positive_int,
    _gen_string, _gen_graph, _gen_dag, _gen_points, _gen_intervals,
    _gen_matrix, _gen_matrix_b,
)


# ═══════════════════════════════════════════════════════════════════════════
#  Data structures
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class AlgoCase:
    name: str
    correct: str
    buggy: str
    spec: Callable
    bug_desc: str
    input_overrides: Optional[Dict[str, Callable]] = None


@dataclass
class AlgoResult:
    name: str
    correct_verdict: bool   # Did verifier say correct impl is correct?
    buggy_verdict: bool     # Did verifier say buggy impl is correct?
    detected: bool          # correct_verdict=True AND buggy_verdict=False
    false_positive: bool    # correct_verdict=False (flagged correct as buggy)
    false_negative: bool    # buggy_verdict=True (missed the bug)
    elapsed_ms: float
    error: str = ""
    n_vcs: int = 0
    cech_eliminated: int = 0
    # Proof method breakdown
    n_z3_proofs: int = 0
    n_z3_refutations: int = 0
    n_structural: int = 0
    n_sheaf_transfers: int = 0
    n_impl_section: int = 0
    correct_refuted: bool = False   # Was correct impl explicitly refuted?
    buggy_refuted: bool = False     # Was buggy impl explicitly refuted?


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHMS 1-10: Sorting
# ═══════════════════════════════════════════════════════════════════════════

# ── 1. Merge Sort ────────────────────────────────────────────────────────

MERGE_SORT_CORRECT = '''
def merge_sort(arr):
    if len(arr) <= 1:
        return list(arr)
    mid = len(arr) // 2
    left = merge_sort(arr[:mid])
    right = merge_sort(arr[mid:])
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result
'''

MERGE_SORT_BUGGY = '''
def merge_sort(arr):
    if len(arr) <= 1:
        return list(arr)
    mid = len(arr) // 2
    left = merge_sort(arr[:mid])
    right = merge_sort(arr[mid:])
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    return result
'''

def merge_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 2. Quick Sort ────────────────────────────────────────────────────────

QUICK_SORT_CORRECT = '''
def quick_sort(arr):
    if len(arr) <= 1:
        return list(arr)
    pivot = arr[len(arr) // 2]
    left = [x for x in arr if x < pivot]
    middle = [x for x in arr if x == pivot]
    right = [x for x in arr if x > pivot]
    return quick_sort(left) + middle + quick_sort(right)
'''

QUICK_SORT_BUGGY = '''
def quick_sort(arr):
    if len(arr) <= 1:
        return list(arr)
    pivot = arr[len(arr) // 2]
    left = [x for x in arr if x < pivot]
    middle = [x for x in arr if x == pivot]
    right = [x for x in arr if x >= pivot]
    return quick_sort(left) + middle + quick_sort(right)
'''

def quick_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 3. Heap Sort ─────────────────────────────────────────────────────────

HEAP_SORT_CORRECT = '''
def heap_sort(arr):
    arr = list(arr)
    n = len(arr)
    def sift_down(start, end):
        root = start
        while 2 * root + 1 <= end:
            child = 2 * root + 1
            if child + 1 <= end and arr[child] < arr[child + 1]:
                child += 1
            if arr[root] < arr[child]:
                arr[root], arr[child] = arr[child], arr[root]
                root = child
            else:
                return
    for start in range(n // 2 - 1, -1, -1):
        sift_down(start, n - 1)
    for end in range(n - 1, 0, -1):
        arr[0], arr[end] = arr[end], arr[0]
        sift_down(0, end - 1)
    return arr
'''

HEAP_SORT_BUGGY = '''
def heap_sort(arr):
    arr = list(arr)
    n = len(arr)
    def sift_down(start, end):
        root = start
        while 2 * root + 1 <= end:
            child = 2 * root + 1
            if child + 1 <= end and arr[child] < arr[child + 1]:
                child += 1
            if arr[root] < arr[child]:
                arr[root], arr[child] = arr[child], arr[root]
                root = child
            else:
                return
    for start in range(n // 2 - 1, -1, -1):
        sift_down(start, n - 1)
    for end in range(n - 1, 0, -1):
        arr[0], arr[end] = arr[end], arr[0]
        sift_down(0, end - 2)
    return arr
'''

def heap_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 4. Insertion Sort ────────────────────────────────────────────────────

INSERTION_SORT_CORRECT = '''
def insertion_sort(arr):
    arr = list(arr)
    for i in range(1, len(arr)):
        key = arr[i]
        j = i - 1
        while j >= 0 and arr[j] > key:
            arr[j + 1] = arr[j]
            j -= 1
        arr[j + 1] = key
    return arr
'''

INSERTION_SORT_BUGGY = '''
def insertion_sort(arr):
    arr = list(arr)
    for i in range(1, len(arr)):
        key = arr[i]
        j = i - 1
        while j > 0 and arr[j] > key:
            arr[j + 1] = arr[j]
            j -= 1
        arr[j + 1] = key
    return arr
'''

def insertion_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 5. Counting Sort ────────────────────────────────────────────────────

COUNTING_SORT_CORRECT = '''
def counting_sort(arr):
    if not arr:
        return []
    lo, hi = min(arr), max(arr)
    count = [0] * (hi - lo + 1)
    for x in arr:
        count[x - lo] += 1
    result = []
    for i, c in enumerate(count):
        result.extend([i + lo] * c)
    return result
'''

COUNTING_SORT_BUGGY = '''
def counting_sort(arr):
    if not arr:
        return []
    lo, hi = min(arr), max(arr)
    count = [0] * (hi - lo + 1)
    for x in arr:
        count[x - lo] += 1
    result = []
    for i, c in enumerate(count):
        result.extend([i + lo] * (c - 1))
    return result
'''

def counting_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 6. Selection Sort ───────────────────────────────────────────────────

SELECTION_SORT_CORRECT = '''
def selection_sort(arr):
    arr = list(arr)
    n = len(arr)
    for i in range(n):
        min_idx = i
        for j in range(i + 1, n):
            if arr[j] < arr[min_idx]:
                min_idx = j
        arr[i], arr[min_idx] = arr[min_idx], arr[i]
    return arr
'''

SELECTION_SORT_BUGGY = '''
def selection_sort(arr):
    arr = list(arr)
    n = len(arr)
    for i in range(n):
        min_idx = i
        for j in range(i + 2, n):
            if arr[j] < arr[min_idx]:
                min_idx = j
        arr[i], arr[min_idx] = arr[min_idx], arr[i]
    return arr
'''

def selection_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 7. Bubble Sort ──────────────────────────────────────────────────────

BUBBLE_SORT_CORRECT = '''
def bubble_sort(arr):
    arr = list(arr)
    n = len(arr)
    for i in range(n):
        for j in range(0, n - i - 1):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
    return arr
'''

BUBBLE_SORT_BUGGY = '''
def bubble_sort(arr):
    arr = list(arr)
    n = len(arr)
    for i in range(n):
        for j in range(0, n - i - 2):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
    return arr
'''

def bubble_sort_spec(arr, result):
    return is_sorted(result) and is_permutation(result, arr)


# ── 8. Binary Search ────────────────────────────────────────────────────

BINARY_SEARCH_CORRECT = '''
def binary_search(arr, target):
    lo, hi = 0, len(arr) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1
'''

BINARY_SEARCH_BUGGY = '''
def binary_search(arr, target):
    lo, hi = 0, len(arr) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1
'''

def binary_search_spec(arr, target, result):
    return search_correct(arr, target, result)

BINARY_SEARCH_OVERRIDES = {
    'arr': lambda: _gen_sorted_list_int(1, 20, 0, 50),
    'target': lambda: random.randint(0, 50),
}


# ── 9. Interpolation Search ─────────────────────────────────────────────

INTERP_SEARCH_CORRECT = '''
def interpolation_search(arr, target):
    lo, hi = 0, len(arr) - 1
    while lo <= hi and arr[lo] <= target <= arr[hi]:
        if arr[lo] == arr[hi]:
            if arr[lo] == target:
                return lo
            break
        pos = lo + (target - arr[lo]) * (hi - lo) // (arr[hi] - arr[lo])
        if arr[pos] == target:
            return pos
        elif arr[pos] < target:
            lo = pos + 1
        else:
            hi = pos - 1
    return -1
'''

INTERP_SEARCH_BUGGY = '''
def interpolation_search(arr, target):
    lo, hi = 0, len(arr) - 1
    while lo <= hi and arr[lo] <= target <= arr[hi]:
        if arr[lo] == arr[hi]:
            if arr[lo] == target:
                return lo
            break
        pos = lo + (target - arr[lo]) * (hi - lo) // (arr[hi] - arr[lo])
        if arr[pos] == target:
            return pos
        elif arr[pos] < target:
            lo = pos + 2
        else:
            hi = pos - 1
    return -1
'''

def interp_search_spec(arr, target, result):
    return search_correct(arr, target, result)

INTERP_SEARCH_OVERRIDES = {
    'arr': lambda: sorted(set(_gen_list_int(5, 20, 0, 100))),
    'target': lambda: random.randint(0, 100),
}


# ── 10. Kadane Max Subarray ─────────────────────────────────────────────

KADANE_CORRECT = '''
def max_subarray(arr):
    if not arr:
        return 0
    best = current = arr[0]
    for x in arr[1:]:
        current = max(x, current + x)
        best = max(best, current)
    return best
'''

KADANE_BUGGY = '''
def max_subarray(arr):
    if not arr:
        return 0
    best = current = arr[0]
    for x in arr[1:]:
        current = max(x, current + x)
        best = current
    return best
'''

def kadane_spec(arr, result):
    return max_subarray_correct(arr, result)


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHMS 11-20: Graph Algorithms
# ═══════════════════════════════════════════════════════════════════════════

# ── 11. Dijkstra ────────────────────────────────────────────────────────

DIJKSTRA_CORRECT = '''
def dijkstra(adj, source):
    import heapq
    dist = {source: 0}
    heap = [(0, source)]
    visited = set()
    while heap:
        d, u = heapq.heappop(heap)
        if u in visited:
            continue
        visited.add(u)
        for v, w in adj.get(u, {}).items():
            nd = d + w
            if nd < dist.get(v, float('inf')):
                dist[v] = nd
                heapq.heappush(heap, (nd, v))
    return dist
'''

DIJKSTRA_BUGGY = '''
def dijkstra(adj, source):
    import heapq
    dist = {source: 0}
    heap = [(0, source)]
    while heap:
        d, u = heapq.heappop(heap)
        for v, w in adj.get(u, {}).items():
            nd = d + w
            if nd < dist.get(v, float('inf')):
                dist[v] = nd
                heapq.heappush(heap, (nd, v))
    return dist
'''

def dijkstra_spec(adj, source, result):
    return distances_correct(adj, source, result)

def _gen_weighted_graph():
    n = random.randint(3, 8)
    adj = {i: {} for i in range(n)}
    for i in range(n):
        for j in range(n):
            if i != j and random.random() < 0.3:
                adj[i][j] = random.randint(1, 20)
    return adj

DIJKSTRA_OVERRIDES = {
    'adj': _gen_weighted_graph,
    'source': lambda: 0,
}


# ── 12. Bellman-Ford ────────────────────────────────────────────────────

BELLMAN_FORD_CORRECT = '''
def bellman_ford(n, edges, source):
    dist = [float('inf')] * n
    dist[source] = 0
    for _ in range(n - 1):
        for u, v, w in edges:
            if dist[u] != float('inf') and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
    return dist
'''

BELLMAN_FORD_BUGGY = '''
def bellman_ford(n, edges, source):
    dist = [float('inf')] * n
    dist[source] = 0
    for _ in range(n - 2):
        for u, v, w in edges:
            if dist[u] != float('inf') and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
    return dist
'''

def bellman_ford_spec(n, edges, source, result):
    if not edges or n <= 0:
        return True
    adj = {i: {} for i in range(n)}
    for u, v, w in edges:
        if 0 <= u < n and 0 <= v < n:
            adj[u][v] = min(adj[u].get(v, float('inf')), w)
    return distances_correct(adj, source, {i: result[i] for i in range(n) if result[i] != float('inf')})

def _gen_bellman_edges():
    n = random.randint(4, 8)
    edges = []
    for i in range(n):
        for j in range(n):
            if i != j and random.random() < 0.25:
                edges.append((i, j, random.randint(1, 15)))
    return edges

BELLMAN_FORD_OVERRIDES = {
    'n': lambda: random.randint(4, 8),
    'edges': _gen_bellman_edges,
    'source': lambda: 0,
}


# ── 13. Topological Sort ────────────────────────────────────────────────

TOPO_SORT_CORRECT = '''
def topo_sort(adj):
    in_deg = {u: 0 for u in adj}
    for u in adj:
        for v in adj[u]:
            in_deg[v] = in_deg.get(v, 0) + 1
    queue = [u for u in adj if in_deg.get(u, 0) == 0]
    order = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for v in adj[u]:
            in_deg[v] -= 1
            if in_deg[v] == 0:
                queue.append(v)
    return order
'''

TOPO_SORT_BUGGY = '''
def topo_sort(adj):
    in_deg = {u: 0 for u in adj}
    for u in adj:
        for v in adj[u]:
            in_deg[v] = in_deg.get(v, 0) + 1
    queue = [u for u in adj if in_deg.get(u, 0) == 0]
    order = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for v in adj[u]:
            in_deg[v] -= 1
            if in_deg[v] <= 0:
                queue.append(v)
    return order
'''

def topo_sort_spec(adj, result):
    if len(result) != len(adj):
        return False
    return is_topological_order(adj, result)

TOPO_SORT_OVERRIDES = {'adj': lambda: _gen_dag(random.randint(4, 8), 0.3)}


# ── 14. Union-Find Components ───────────────────────────────────────────

UNION_FIND_CORRECT = '''
def count_components(n, edges):
    parent = list(range(n))
    rank = [0] * n
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a, b):
        a, b = find(a), find(b)
        if a == b:
            return
        if rank[a] < rank[b]:
            a, b = b, a
        parent[b] = a
        if rank[a] == rank[b]:
            rank[a] += 1
    for u, v in edges:
        union(u, v)
    return len(set(find(i) for i in range(n)))
'''

UNION_FIND_BUGGY = '''
def count_components(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    def union(a, b):
        a, b = find(a), find(b)
        if a == b:
            return
        parent[b] = a
    for u, v in edges:
        union(u, v)
    return len(set(parent[i] for i in range(n)))
'''

def union_find_spec(n, edges, result):
    return union_find_correct(n, edges, result)

def _gen_uf_edges():
    n = random.randint(5, 15)
    edges = []
    for _ in range(random.randint(0, n * 2)):
        u, v = random.randint(0, n - 1), random.randint(0, n - 1)
        if u != v:
            edges.append((u, v))
    return edges

UNION_FIND_OVERRIDES = {
    'n': lambda: random.randint(5, 15),
    'edges': _gen_uf_edges,
}


# ── 15. Kruskal MST ─────────────────────────────────────────────────────

KRUSKAL_CORRECT = '''
def kruskal(n, edges):
    edges = sorted(edges, key=lambda e: e[2])
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    mst = []
    for u, v, w in edges:
        if find(u) != find(v):
            parent[find(u)] = find(v)
            mst.append((u, v, w))
    return mst
'''

KRUSKAL_BUGGY = '''
def kruskal(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    mst = []
    for u, v, w in edges:
        if find(u) != find(v):
            parent[find(u)] = find(v)
            mst.append((u, v, w))
    return mst
'''

def kruskal_spec(n, edges, result):
    return is_minimum_spanning_tree(n, edges, result)

def _gen_mst_edges():
    n = random.randint(4, 8)
    edges = []
    # Ensure connected
    for i in range(n - 1):
        edges.append((i, i + 1, random.randint(1, 20)))
    for _ in range(random.randint(0, n)):
        u, v = random.randint(0, n - 1), random.randint(0, n - 1)
        if u != v:
            edges.append((u, v, random.randint(1, 20)))
    return edges

KRUSKAL_OVERRIDES = {
    'n': lambda: random.randint(4, 8),
    'edges': _gen_mst_edges,
}


# ── 16. Floyd-Warshall ──────────────────────────────────────────────────

FLOYD_WARSHALL_CORRECT = '''
def floyd_warshall(n, adj):
    INF = float('inf')
    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for u in adj:
        for v, w in adj[u].items():
            dist[u][v] = min(dist[u][v], w)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
    return dist
'''

FLOYD_WARSHALL_BUGGY = '''
def floyd_warshall(n, adj):
    INF = float('inf')
    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for u in adj:
        for v, w in adj[u].items():
            dist[u][v] = min(dist[u][v], w)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
    return dist
'''

def floyd_warshall_spec(n, adj, result):
    return all_pairs_shortest(adj, n, result)

FLOYD_OVERRIDES = {
    'n': lambda: random.randint(3, 6),
    'adj': lambda: _gen_weighted_graph(),
}


# ── 17-20: Placeholder graph algos (Prim, MaxFlow, Bipartite, A*) ──────

PRIM_CORRECT = '''
def prim(n, adj):
    import heapq
    if n == 0:
        return []
    visited = {0}
    edges = [(w, 0, v) for v, w in adj.get(0, {}).items()]
    heapq.heapify(edges)
    mst = []
    while edges and len(visited) < n:
        w, u, v = heapq.heappop(edges)
        if v in visited:
            continue
        visited.add(v)
        mst.append((u, v, w))
        for nv, nw in adj.get(v, {}).items():
            if nv not in visited:
                heapq.heappush(edges, (nw, v, nv))
    return mst
'''

PRIM_BUGGY = '''
def prim(n, adj):
    import heapq
    if n == 0:
        return []
    visited = {0}
    edges = [(w, 0, v) for v, w in adj.get(0, {}).items()]
    heapq.heapify(edges)
    mst = []
    while edges and len(visited) < n:
        w, u, v = heapq.heappop(edges)
        if v in visited:
            continue
        visited.add(v)
        mst.append((u, v, w))
        for nv, nw in adj.get(v, {}).items():
            heapq.heappush(edges, (nw, v, nv))
    return mst
'''

def prim_spec(n, adj, result):
    all_edges = [(u, v, w) for u in adj for v, w in adj[u].items()]
    return is_minimum_spanning_tree(n, all_edges, result)

PRIM_OVERRIDES = {
    'n': lambda: random.randint(4, 7),
    'adj': lambda: _gen_weighted_graph(),
}


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHMS 21-30: Dynamic Programming & Strings
# ═══════════════════════════════════════════════════════════════════════════

# ── 18. LCS Length ──────────────────────────────────────────────────────

LCS_CORRECT = '''
def lcs_length(a, b):
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    return dp[m][n]
'''

LCS_BUGGY = '''
def lcs_length(a, b):
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i-1][j-1])
    return dp[m][n]
'''

def lcs_spec(a, b, result):
    return lcs_length_correct(a, b, result)

LCS_OVERRIDES = {
    'a': lambda: _gen_list_int(2, 10, 0, 5),
    'b': lambda: _gen_list_int(2, 10, 0, 5),
}


# ── 19. Edit Distance ──────────────────────────────────────────────────

EDIT_DIST_CORRECT = '''
def edit_distance(a, b):
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(m + 1):
        dp[i][0] = i
    for j in range(n + 1):
        dp[0][j] = j
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1]
            else:
                dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
    return dp[m][n]
'''

EDIT_DIST_BUGGY = '''
def edit_distance(a, b):
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(m + 1):
        dp[i][0] = i
    for j in range(n + 1):
        dp[0][j] = j
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1]
            else:
                dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1])
    return dp[m][n]
'''

def edit_dist_spec(a, b, result):
    return edit_distance_correct(a, b, result)

EDIT_DIST_OVERRIDES = {
    'a': lambda: _gen_string(1, 8, 'abc'),
    'b': lambda: _gen_string(1, 8, 'abc'),
}


# ── 20. 0/1 Knapsack ───────────────────────────────────────────────────

KNAPSACK_CORRECT = '''
def knapsack(weights, values, capacity):
    n = len(weights)
    dp = [[0] * (capacity + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for w in range(capacity + 1):
            dp[i][w] = dp[i-1][w]
            if weights[i-1] <= w:
                dp[i][w] = max(dp[i][w], dp[i-1][w - weights[i-1]] + values[i-1])
    return dp[n][capacity]
'''

KNAPSACK_BUGGY = '''
def knapsack(weights, values, capacity):
    n = len(weights)
    dp = [[0] * (capacity + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for w in range(capacity + 1):
            dp[i][w] = dp[i-1][w]
            if weights[i-1] <= w:
                dp[i][w] = max(dp[i][w], dp[i][w - weights[i-1]] + values[i-1])
    return dp[n][capacity]
'''

def knapsack_spec(weights, values, capacity, result):
    return knapsack_correct(weights, values, capacity, result)

KNAPSACK_OVERRIDES = {
    'weights': lambda: [random.randint(1, 10) for _ in range(random.randint(3, 8))],
    'values': lambda: [random.randint(1, 20) for _ in range(random.randint(3, 8))],
    'capacity': lambda: random.randint(5, 30),
}


# ── 21. Coin Change ────────────────────────────────────────────────────

COIN_CHANGE_CORRECT = '''
def coin_change(coins, amount):
    dp = [float('inf')] * (amount + 1)
    dp[0] = 0
    for c in coins:
        for a in range(c, amount + 1):
            dp[a] = min(dp[a], dp[a - c] + 1)
    return dp[amount] if dp[amount] != float('inf') else -1
'''

COIN_CHANGE_BUGGY = '''
def coin_change(coins, amount):
    dp = [float('inf')] * (amount + 1)
    dp[0] = 0
    for a in range(1, amount + 1):
        for c in coins:
            if c <= a:
                dp[a] = min(dp[a], dp[a - c] + 1)
                break
    return dp[amount] if dp[amount] != float('inf') else -1
'''

def coin_change_spec(coins, amount, result):
    return coin_change_correct(coins, amount, result)

COIN_CHANGE_OVERRIDES = {
    'coins': lambda: sorted(random.sample(range(1, 15), random.randint(2, 5))),
    'amount': lambda: random.randint(1, 30),
}


# ── 22. LIS Length ──────────────────────────────────────────────────────

LIS_CORRECT = '''
def lis_length(arr):
    if not arr:
        return 0
    tails = []
    for x in arr:
        lo, hi = 0, len(tails)
        while lo < hi:
            mid = (lo + hi) // 2
            if tails[mid] < x:
                lo = mid + 1
            else:
                hi = mid
        if lo == len(tails):
            tails.append(x)
        else:
            tails[lo] = x
    return len(tails)
'''

LIS_BUGGY = '''
def lis_length(arr):
    if not arr:
        return 0
    tails = []
    for x in arr:
        lo, hi = 0, len(tails)
        while lo < hi:
            mid = (lo + hi) // 2
            if tails[mid] <= x:
                lo = mid + 1
            else:
                hi = mid
        if lo == len(tails):
            tails.append(x)
        else:
            tails[lo] = x
    return len(tails)
'''

def lis_spec(arr, result):
    return lis_length_correct(arr, result)


# ── 23. Matrix Chain Multiplication ─────────────────────────────────────

MATCHAIN_CORRECT = '''
def matrix_chain(dims):
    n = len(dims) - 1
    if n <= 0:
        return 0
    dp = [[0] * n for _ in range(n)]
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length - 1
            dp[i][j] = float('inf')
            for k in range(i, j):
                cost = dp[i][k] + dp[k+1][j] + dims[i] * dims[k+1] * dims[j+1]
                dp[i][j] = min(dp[i][j], cost)
    return dp[0][n-1]
'''

MATCHAIN_BUGGY = '''
def matrix_chain(dims):
    n = len(dims) - 1
    if n <= 0:
        return 0
    dp = [[0] * n for _ in range(n)]
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length - 1
            dp[i][j] = float('inf')
            for k in range(i, j):
                cost = dp[i][k] + dp[k+1][j] + dims[i] * dims[k] * dims[j+1]
                dp[i][j] = min(dp[i][j], cost)
    return dp[0][n-1]
'''

def matchain_spec(dims, result):
    return matrix_chain_correct(dims, result)

MATCHAIN_OVERRIDES = {
    'dims': lambda: [random.randint(2, 20) for _ in range(random.randint(3, 7))],
}


# ── 24. Rod Cutting ────────────────────────────────────────────────────

ROD_CORRECT = '''
def rod_cutting(prices, n):
    dp = [0] * (n + 1)
    for i in range(1, n + 1):
        for j in range(1, min(i, len(prices)) + 1):
            dp[i] = max(dp[i], prices[j-1] + dp[i-j])
    return dp[n]
'''

ROD_BUGGY = '''
def rod_cutting(prices, n):
    dp = [0] * (n + 1)
    for i in range(1, n + 1):
        for j in range(1, min(i, len(prices)) + 1):
            dp[i] = max(dp[i], prices[j-1] + dp[i-j-1])
    return dp[n]
'''

def rod_spec(prices, n, result):
    return rod_cutting_correct(prices, n, result)

ROD_OVERRIDES = {
    'prices': lambda: [random.randint(1, 20) for _ in range(random.randint(3, 8))],
    'n': lambda: random.randint(1, 8),
}


# ── 25. KMP String Matching ────────────────────────────────────────────

KMP_CORRECT = '''
def kmp_search(text, pattern):
    if not pattern:
        return list(range(len(text) + 1))
    # Build failure function
    fail = [0] * len(pattern)
    j = 0
    for i in range(1, len(pattern)):
        while j > 0 and pattern[i] != pattern[j]:
            j = fail[j-1]
        if pattern[i] == pattern[j]:
            j += 1
        fail[i] = j
    # Search
    positions = []
    j = 0
    for i in range(len(text)):
        while j > 0 and text[i] != pattern[j]:
            j = fail[j-1]
        if text[i] == pattern[j]:
            j += 1
        if j == len(pattern):
            positions.append(i - len(pattern) + 1)
            j = fail[j-1]
    return positions
'''

KMP_BUGGY = '''
def kmp_search(text, pattern):
    if not pattern:
        return list(range(len(text) + 1))
    fail = [0] * len(pattern)
    j = 0
    for i in range(1, len(pattern)):
        while j > 0 and pattern[i] != pattern[j]:
            j = fail[j-1]
        if pattern[i] == pattern[j]:
            j += 1
        fail[i] = j
    positions = []
    j = 0
    for i in range(len(text)):
        while j > 0 and text[i] != pattern[j]:
            j = fail[j-1]
        if text[i] == pattern[j]:
            j += 1
        if j == len(pattern):
            positions.append(i - len(pattern) + 1)
            j = 0
    return positions
'''

def kmp_spec(text, pattern, result):
    return all_pattern_occurrences(text, pattern, result)

KMP_OVERRIDES = {
    'text': lambda: _gen_string(5, 30, 'abc'),
    'pattern': lambda: _gen_string(1, 4, 'abc'),
}


# ── 26. Z-Algorithm ────────────────────────────────────────────────────

Z_ALGO_CORRECT = '''
def z_function(s):
    n = len(s)
    if n == 0:
        return []
    z = [0] * n
    z[0] = n
    l = r = 0
    for i in range(1, n):
        if i < r:
            z[i] = min(r - i, z[i - l])
        while i + z[i] < n and s[z[i]] == s[i + z[i]]:
            z[i] += 1
        if i + z[i] > r:
            l, r = i, i + z[i]
    return z
'''

Z_ALGO_BUGGY = '''
def z_function(s):
    n = len(s)
    if n == 0:
        return []
    z = [0] * n
    z[0] = n
    l = r = 0
    for i in range(1, n):
        if i < r:
            z[i] = min(r - i, z[i - l])
        while i + z[i] < n and s[z[i]] == s[i + z[i]]:
            z[i] += 1
        if i + z[i] >= r:
            l, r = i, i + z[i]
    return z
'''

def z_algo_spec(s, result):
    return z_array_correct(s, result)

Z_ALGO_OVERRIDES = {'s': lambda: _gen_string(3, 20, 'abc')}


# ── 27. Sieve of Eratosthenes ──────────────────────────────────────────

SIEVE_CORRECT = '''
def sieve(n):
    if n < 2:
        return []
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(i*i, n + 1, i):
                is_p[j] = False
    return [i for i in range(n + 1) if is_p[i]]
'''

SIEVE_BUGGY = '''
def sieve(n):
    if n < 2:
        return []
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(2*i, n + 1, i):
                is_p[j] = False
    return [i for i in range(n + 1) if is_p[i]]
'''

def sieve_spec(n, result):
    return sieve_correct(n, result)

SIEVE_OVERRIDES = {'n': lambda: random.randint(10, 100)}


# ── 28. Extended GCD ───────────────────────────────────────────────────

EGCD_CORRECT = '''
def extended_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    return g, y1, x1 - (a // b) * y1
'''

EGCD_BUGGY = '''
def extended_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    return g, y1, x1 - (a // b) * x1
'''

def egcd_spec(a, b, result):
    g, x, y = result
    return extended_gcd_correct(a, b, g, x, y)

EGCD_OVERRIDES = {
    'a': lambda: random.randint(1, 200),
    'b': lambda: random.randint(1, 200),
}


# ── 29. Modular Exponentiation ─────────────────────────────────────────

MOD_EXP_CORRECT = '''
def mod_exp(base, exp, mod):
    result = 1
    base = base % mod
    while exp > 0:
        if exp % 2 == 1:
            result = (result * base) % mod
        exp = exp >> 1
        base = (base * base) % mod
    return result
'''

MOD_EXP_BUGGY = '''
def mod_exp(base, exp, mod):
    result = 1
    base = base % mod
    while exp > 0:
        if exp % 2 == 1:
            result = result * base % mod
        exp = exp >> 1
        base = base * base
    return result % mod
'''

def mod_exp_spec(base, exp, mod, result):
    return mod_exp_correct(base, exp, mod, result)

MOD_EXP_OVERRIDES = {
    'base': lambda: random.randint(2, 50),
    'exp': lambda: random.randint(1, 30),
    'mod': lambda: random.randint(3, 97),
}


# ── 30. Newton's Method Sqrt ───────────────────────────────────────────

NEWTON_SQRT_CORRECT = '''
def newton_sqrt(n):
    if n < 0:
        return -1.0
    if n == 0:
        return 0.0
    x = float(n)
    for _ in range(100):
        x = (x + n / x) / 2.0
    return x
'''

NEWTON_SQRT_BUGGY = '''
def newton_sqrt(n):
    if n < 0:
        return -1.0
    if n == 0:
        return 0.0
    x = float(n)
    for _ in range(3):
        x = (x + n / x) / 2.0
    return x
'''

def newton_sqrt_spec(n, result):
    if n < 0:
        return True
    return sqrt_correct(n, result, tolerance=1e-6)

NEWTON_SQRT_OVERRIDES = {'n': lambda: random.uniform(0.01, 10000.0)}


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHMS 31-40: More DP, Geometry, Data Structures
# ═══════════════════════════════════════════════════════════════════════════

# ── 31. Convex Hull ────────────────────────────────────────────────────

CONVEX_HULL_CORRECT = '''
def convex_hull(points):
    points = sorted(set(points))
    if len(points) <= 1:
        return points
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lower = []
    for p in points:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(points):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]
'''

CONVEX_HULL_BUGGY = '''
def convex_hull(points):
    points = sorted(set(points))
    if len(points) <= 1:
        return points
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lower = []
    for p in points:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) < 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(points):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) < 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]
'''

def convex_hull_spec(points, result):
    return is_convex_hull(points, result)

CONVEX_HULL_OVERRIDES = {'points': lambda: _gen_points(random.randint(5, 15))}


# ── 32. Closest Pair ──────────────────────────────────────────────────

CLOSEST_PAIR_CORRECT = '''
def closest_pair(points):
    import math
    if len(points) < 2:
        return float('inf')
    min_d = float('inf')
    for i in range(len(points)):
        for j in range(i+1, len(points)):
            d = math.sqrt((points[i][0]-points[j][0])**2 + (points[i][1]-points[j][1])**2)
            min_d = min(min_d, d)
    return min_d
'''

CLOSEST_PAIR_BUGGY = '''
def closest_pair(points):
    import math
    if len(points) < 2:
        return float('inf')
    min_d = float('inf')
    for i in range(len(points)):
        for j in range(i+1, len(points)):
            d = abs(points[i][0]-points[j][0]) + abs(points[i][1]-points[j][1])
            min_d = min(min_d, d)
    return min_d
'''

def closest_pair_spec(points, result):
    return closest_pair_correct(points, result)

CLOSEST_PAIR_OVERRIDES = {'points': lambda: _gen_points(random.randint(4, 12))}


# ── 33. Interval Scheduling ───────────────────────────────────────────

INTERVAL_SCHED_CORRECT = '''
def interval_schedule(intervals):
    indexed = sorted(enumerate(intervals), key=lambda x: x[1][1])
    selected = []
    last_end = -1
    for i, (s, e) in indexed:
        if s >= last_end:
            selected.append(i)
            last_end = e
    return selected
'''

INTERVAL_SCHED_BUGGY = '''
def interval_schedule(intervals):
    indexed = sorted(enumerate(intervals), key=lambda x: x[1][0])
    selected = []
    last_end = -1
    for i, (s, e) in indexed:
        if s >= last_end:
            selected.append(i)
            last_end = e
    return selected
'''

def interval_sched_spec(intervals, result):
    return interval_schedule_correct(intervals, result)

INTERVAL_SCHED_OVERRIDES = {'intervals': lambda: _gen_intervals(random.randint(5, 12))}


# ── 34. BST Insert ────────────────────────────────────────────────────

BST_INSERT_CORRECT = '''
def bst_insert(tree, val):
    if tree is None:
        return (val, None, None)
    v, left, right = tree
    if val < v:
        return (v, bst_insert(left, val), right)
    elif val > v:
        return (v, left, bst_insert(right, val))
    return tree
'''

BST_INSERT_BUGGY = '''
def bst_insert(tree, val):
    if tree is None:
        return (val, None, None)
    v, left, right = tree
    if val <= v:
        return (v, bst_insert(left, val), right)
    else:
        return (v, left, bst_insert(right, val))
'''

def bst_insert_spec(tree, val, result):
    return is_bst(result)

def _gen_bst(n=None):
    if n is None:
        n = random.randint(0, 8)
    if n == 0:
        return None
    vals = random.sample(range(1, 50), min(n, 49))
    tree = None
    for v in vals:
        tree = _bst_insert_helper(tree, v)
    return tree

def _bst_insert_helper(tree, val):
    if tree is None:
        return (val, None, None)
    v, l, r = tree
    if val < v:
        return (v, _bst_insert_helper(l, val), r)
    elif val > v:
        return (v, l, _bst_insert_helper(r, val))
    return tree

BST_INSERT_OVERRIDES = {
    'tree': lambda: _gen_bst(random.randint(3, 8)),
    'val': lambda: random.randint(1, 50),
}


# ── 35. Trie Insert & Search ──────────────────────────────────────────

TRIE_CORRECT = '''
def trie_insert(trie, word):
    node = trie
    for ch in word:
        if ch not in node:
            node[ch] = {}
        node = node[ch]
    node['#'] = True
    return trie
'''

TRIE_BUGGY = '''
def trie_insert(trie, word):
    node = trie
    for ch in word:
        if ch not in node:
            node[ch] = {}
        node = node[ch]
    return trie
'''

def trie_spec(trie, word, result):
    return trie_contains_all(result, [word])

TRIE_OVERRIDES = {
    'trie': lambda: {},
    'word': lambda: _gen_string(1, 8, 'abcde'),
}


# ── 36. Fenwick Tree (BIT) ────────────────────────────────────────────

FENWICK_CORRECT = '''
def fenwick_build(arr):
    n = len(arr)
    bit = [0] * (n + 1)
    for i in range(n):
        idx = i + 1
        bit[idx] += arr[i]
        parent = idx + (idx & (-idx))
        if parent <= n:
            bit[parent] += bit[idx]
    return bit
'''

FENWICK_BUGGY = '''
def fenwick_build(arr):
    n = len(arr)
    bit = [0] * (n + 1)
    for i in range(n):
        idx = i + 1
        bit[idx] += arr[i]
        parent = idx + (idx & (-idx))
        if parent <= n:
            bit[parent] += arr[i]
    return bit
'''

def fenwick_spec(arr, result):
    return fenwick_prefix_correct(arr, result)

FENWICK_OVERRIDES = {'arr': lambda: _gen_list_int(3, 15, 0, 20)}


# ── 37. Gaussian Elimination ──────────────────────────────────────────

GAUSS_CORRECT = '''
def gaussian_elim(A, b):
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        max_row = max(range(col, n), key=lambda r: abs(M[r][col]))
        M[col], M[max_row] = M[max_row], M[col]
        if abs(M[col][col]) < 1e-12:
            return [0.0] * n
        for row in range(col + 1, n):
            factor = M[row][col] / M[col][col]
            for j in range(col, n + 1):
                M[row][j] -= factor * M[col][j]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = M[i][n]
        for j in range(i + 1, n):
            x[i] -= M[i][j] * x[j]
        x[i] /= M[i][i]
    return x
'''

GAUSS_BUGGY = '''
def gaussian_elim(A, b):
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        if abs(M[col][col]) < 1e-12:
            return [0.0] * n
        for row in range(col + 1, n):
            factor = M[row][col] / M[col][col]
            for j in range(col, n + 1):
                M[row][j] -= factor * M[col][j]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = M[i][n]
        for j in range(i + 1, n):
            x[i] -= M[i][j] * x[j]
        x[i] /= M[i][i]
    return x
'''

def gauss_spec(A, b, result):
    return gaussian_elim_correct(A, b, result, tol=1e-3)

def _gen_nonsingular_matrix():
    while True:
        n = random.randint(2, 5)
        A = [[random.uniform(-5, 5) for _ in range(n)] for _ in range(n)]
        # Check rough non-singularity
        try:
            det = _det(A)
            if abs(det) > 0.1:
                return A
        except Exception:
            pass

def _det(A):
    n = len(A)
    if n == 1:
        return A[0][0]
    if n == 2:
        return A[0][0]*A[1][1] - A[0][1]*A[1][0]
    d = 0
    for j in range(n):
        sub = [[A[i][k] for k in range(n) if k != j] for i in range(1, n)]
        d += ((-1)**j) * A[0][j] * _det(sub)
    return d

GAUSS_OVERRIDES = {
    'A': _gen_nonsingular_matrix,
    'b': lambda: [random.uniform(-5, 5) for _ in range(random.randint(2, 5))],
}


# ── 38-40: CRT, Reservoir Sampling, Median of Medians ─────────────────

CRT_CORRECT = '''
def chinese_remainder(remainders, moduli):
    def extended_gcd(a, b):
        if b == 0:
            return a, 1, 0
        g, x, y = extended_gcd(b, a % b)
        return g, y, x - (a // b) * y
    M = 1
    for m in moduli:
        M *= m
    result = 0
    for r, m in zip(remainders, moduli):
        Mi = M // m
        _, x, _ = extended_gcd(Mi, m)
        result += r * Mi * x
    return result % M
'''

CRT_BUGGY = '''
def chinese_remainder(remainders, moduli):
    def extended_gcd(a, b):
        if b == 0:
            return a, 1, 0
        g, x, y = extended_gcd(b, a % b)
        return g, y, x - (a // b) * y
    M = 1
    for m in moduli:
        M *= m
    result = 0
    for r, m in zip(remainders, moduli):
        Mi = M // m
        _, x, _ = extended_gcd(Mi, m)
        result += r * Mi * x
    return result % moduli[0]
'''

def crt_spec(remainders, moduli, result):
    return crt_correct(remainders, moduli, result)

def _gen_coprime_moduli():
    primes = [2, 3, 5, 7, 11, 13, 17]
    k = random.randint(2, 4)
    chosen = random.sample(primes, k)
    return chosen

CRT_OVERRIDES = {
    'remainders': lambda: [random.randint(0, 10) for _ in range(random.randint(2, 4))],
    'moduli': _gen_coprime_moduli,
}


MAX_SUBARRAY_CORRECT = KADANE_CORRECT  # reuse
MAX_SUBARRAY_BUGGY = KADANE_BUGGY


# ── 39. Reservoir Sampling ─────────────────────────────────────────────

RESERVOIR_CORRECT = '''
def reservoir_sample(stream, k):
    import random as _r
    reservoir = []
    for i, item in enumerate(stream):
        if i < k:
            reservoir.append(item)
        else:
            j = _r.randint(0, i)
            if j < k:
                reservoir[j] = item
    return reservoir
'''

RESERVOIR_BUGGY = '''
def reservoir_sample(stream, k):
    import random as _r
    reservoir = []
    for i, item in enumerate(stream):
        if i < k:
            reservoir.append(item)
        else:
            j = _r.randint(0, i - 1)
            if j < k:
                reservoir[j] = item
    return reservoir
'''

def reservoir_spec(stream, k, result):
    n = len(stream)
    if n <= k:
        return len(result) == n
    return len(result) == k and all(r in stream for r in result)

RESERVOIR_OVERRIDES = {
    'stream': lambda: list(range(random.randint(10, 50))),
    'k': lambda: random.randint(3, 8),
}


# ── 40. Longest Palindromic Substring ──────────────────────────────────

PALINDROME_CORRECT = '''
def longest_palindrome(s):
    if not s:
        return ""
    start = end = 0
    for i in range(len(s)):
        for delta in (0, 1):
            l, r = i, i + delta
            while l >= 0 and r < len(s) and s[l] == s[r]:
                if r - l > end - start:
                    start, end = l, r
                l -= 1
                r += 1
    return s[start:end+1]
'''

PALINDROME_BUGGY = '''
def longest_palindrome(s):
    if not s:
        return ""
    start = end = 0
    for i in range(len(s)):
        l, r = i, i
        while l >= 0 and r < len(s) and s[l] == s[r]:
            if r - l > end - start:
                start, end = l, r
            l -= 1
            r += 1
    return s[start:end+1]
'''

def palindrome_spec(s, result):
    return longest_palindrome_correct(s, result)

PALINDROME_OVERRIDES = {'s': lambda: _gen_string(3, 15, 'abcd')}


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHMS 41-50: Number Theory, Advanced
# ═══════════════════════════════════════════════════════════════════════════

# ── 41. Suffix Array (naive) ──────────────────────────────────────────

SUFFIX_ARRAY_CORRECT = '''
def suffix_array(text):
    n = len(text)
    suffixes = [(text[i:], i) for i in range(n)]
    suffixes.sort()
    return [idx for _, idx in suffixes]
'''

SUFFIX_ARRAY_BUGGY = '''
def suffix_array(text):
    n = len(text)
    suffixes = [(text[i:], i) for i in range(n)]
    suffixes.sort(key=lambda x: x[0][:10])
    return [idx for _, idx in suffixes]
'''

def suffix_array_spec(text, result):
    return is_suffix_array(text, result)

SUFFIX_ARRAY_OVERRIDES = {'text': lambda: _gen_string(5, 25, 'ab')}


# ── 42. Rabin-Karp ────────────────────────────────────────────────────

RABIN_KARP_CORRECT = '''
def rabin_karp(text, pattern):
    if not pattern:
        return list(range(len(text) + 1))
    n, m = len(text), len(pattern)
    if m > n:
        return []
    BASE, MOD = 256, 10**9 + 7
    ph = th = 0
    power = 1
    for i in range(m - 1):
        power = (power * BASE) % MOD
    for i in range(m):
        ph = (ph * BASE + ord(pattern[i])) % MOD
        th = (th * BASE + ord(text[i])) % MOD
    result = []
    for i in range(n - m + 1):
        if ph == th and text[i:i+m] == pattern:
            result.append(i)
        if i + m < n:
            th = (th - ord(text[i]) * power) % MOD
            th = (th * BASE + ord(text[i + m])) % MOD
    return result
'''

RABIN_KARP_BUGGY = '''
def rabin_karp(text, pattern):
    if not pattern:
        return list(range(len(text) + 1))
    n, m = len(text), len(pattern)
    if m > n:
        return []
    BASE, MOD = 256, 10**9 + 7
    ph = th = 0
    power = 1
    for i in range(m - 1):
        power = (power * BASE) % MOD
    for i in range(m):
        ph = (ph * BASE + ord(pattern[i])) % MOD
        th = (th * BASE + ord(text[i])) % MOD
    result = []
    for i in range(n - m + 1):
        if ph == th:
            result.append(i)
        if i + m < n:
            th = (th - ord(text[i]) * power) % MOD
            th = (th * BASE + ord(text[i + m])) % MOD
    return result
'''

def rabin_karp_spec(text, pattern, result):
    return all_pattern_occurrences(text, pattern, result)

RABIN_KARP_OVERRIDES = {
    'text': lambda: _gen_string(10, 40, 'abc'),
    'pattern': lambda: _gen_string(1, 4, 'abc'),
}


# ── 43. Counting Inversions (merge-sort based) ────────────────────────

INVERSIONS_CORRECT = '''
def count_inversions(arr):
    if len(arr) <= 1:
        return arr, 0
    mid = len(arr) // 2
    left, l_inv = count_inversions(arr[:mid])
    right, r_inv = count_inversions(arr[mid:])
    merged = []
    inversions = l_inv + r_inv
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            merged.append(left[i])
            i += 1
        else:
            merged.append(right[j])
            inversions += len(left) - i
            j += 1
    merged.extend(left[i:])
    merged.extend(right[j:])
    return merged, inversions
'''

INVERSIONS_BUGGY = '''
def count_inversions(arr):
    if len(arr) <= 1:
        return arr, 0
    mid = len(arr) // 2
    left, l_inv = count_inversions(arr[:mid])
    right, r_inv = count_inversions(arr[mid:])
    merged = []
    inversions = l_inv + r_inv
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            merged.append(left[i])
            i += 1
        else:
            merged.append(right[j])
            inversions += 1
            j += 1
    merged.extend(left[i:])
    merged.extend(right[j:])
    return merged, inversions
'''

def inversions_spec(arr, result):
    merged, count = result
    # Ground truth
    gt = sum(1 for i in range(len(arr)) for j in range(i+1, len(arr)) if arr[i] > arr[j])
    return count == gt and is_sorted(merged) and is_permutation(arr, merged)

INVERSIONS_OVERRIDES = {'arr': lambda: _gen_list_int(3, 15, 0, 30)}


# ── 44. Power Set ─────────────────────────────────────────────────────

POWERSET_CORRECT = '''
def power_set(s):
    result = [[]]
    for elem in s:
        result += [subset + [elem] for subset in result]
    return result
'''

POWERSET_BUGGY = '''
def power_set(s):
    result = [[]]
    for elem in s:
        result += [subset + [elem] for subset in result[:]]
    result.pop(0)
    return result
'''

def powerset_spec(s, result):
    expected_len = 2 ** len(s)
    if len(result) != expected_len:
        return False
    # Check all unique
    tuples = [tuple(sorted(r)) for r in result]
    return len(set(tuples)) == expected_len


# ── 45. Dutch National Flag (3-way partition) ─────────────────────────

DNF_CORRECT = '''
def dutch_flag(arr, pivot):
    arr = list(arr)
    lo, mid, hi = 0, 0, len(arr) - 1
    while mid <= hi:
        if arr[mid] < pivot:
            arr[lo], arr[mid] = arr[mid], arr[lo]
            lo += 1
            mid += 1
        elif arr[mid] == pivot:
            mid += 1
        else:
            arr[mid], arr[hi] = arr[hi], arr[mid]
            hi -= 1
    return arr
'''

DNF_BUGGY = '''
def dutch_flag(arr, pivot):
    arr = list(arr)
    lo, mid, hi = 0, 0, len(arr) - 1
    while mid <= hi:
        if arr[mid] < pivot:
            arr[lo], arr[mid] = arr[mid], arr[lo]
            lo += 1
            mid += 1
        elif arr[mid] == pivot:
            mid += 1
        else:
            arr[mid], arr[hi] = arr[hi], arr[mid]
            hi -= 1
            mid += 1
    return arr
'''

def dnf_spec(arr, pivot, result):
    if not is_permutation(arr, result):
        return False
    phase = 0
    for x in result:
        if phase == 0:
            if x == pivot:
                phase = 1
            elif x > pivot:
                phase = 2
        elif phase == 1:
            if x < pivot:
                return False
            if x > pivot:
                phase = 2
        elif phase == 2:
            if x <= pivot:
                return False
    return True

DNF_OVERRIDES = {
    'arr': lambda: [random.choice([1, 2, 3]) for _ in range(random.randint(5, 20))],
    'pivot': lambda: 2,
}


# ── 46. GCD (Euclidean) ──────────────────────────────────────────────

GCD_CORRECT = '''
def gcd(a, b):
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a
'''

GCD_BUGGY = '''
def gcd(a, b):
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a - b
    return a
'''

def gcd_spec_fn(a, b, result):
    return gcd_correct(a, b, result)

GCD_OVERRIDES = {
    'a': lambda: random.randint(1, 200),
    'b': lambda: random.randint(1, 200),
}


# ── 47. Rotate Array ─────────────────────────────────────────────────

ROTATE_CORRECT = '''
def rotate(arr, k):
    n = len(arr)
    if n == 0:
        return []
    k = k % n
    return arr[-k:] + arr[:-k] if k else list(arr)
'''

ROTATE_BUGGY = '''
def rotate(arr, k):
    n = len(arr)
    if n == 0:
        return []
    k = k % n
    return arr[k:] + arr[:k]
'''

def rotate_spec(arr, k, result):
    n = len(arr)
    if n == 0:
        return result == []
    kk = k % n
    expected = arr[-kk:] + arr[:-kk] if kk else list(arr)
    return result == expected

ROTATE_OVERRIDES = {
    'arr': lambda: _gen_list_int(3, 15, 0, 20),
    'k': lambda: random.randint(0, 20),
}


# ── 48. Next Permutation ─────────────────────────────────────────────

NEXT_PERM_CORRECT = '''
def next_permutation(arr):
    arr = list(arr)
    n = len(arr)
    i = n - 2
    while i >= 0 and arr[i] >= arr[i+1]:
        i -= 1
    if i < 0:
        arr.reverse()
        return arr
    j = n - 1
    while arr[j] <= arr[i]:
        j -= 1
    arr[i], arr[j] = arr[j], arr[i]
    arr[i+1:] = arr[i+1:][::-1]
    return arr
'''

NEXT_PERM_BUGGY = '''
def next_permutation(arr):
    arr = list(arr)
    n = len(arr)
    i = n - 2
    while i >= 0 and arr[i] >= arr[i+1]:
        i -= 1
    if i < 0:
        arr.reverse()
        return arr
    j = n - 1
    while arr[j] <= arr[i]:
        j -= 1
    arr[i], arr[j] = arr[j], arr[i]
    return arr
'''

def next_perm_spec(arr, result):
    from itertools import permutations
    if len(arr) > 8:
        return True  # skip large
    perms = sorted(set(permutations(arr)))
    t = tuple(arr)
    idx = perms.index(t) if t in perms else -1
    if idx == len(perms) - 1:
        expected = list(perms[0])
    else:
        expected = list(perms[idx + 1])
    return result == expected

NEXT_PERM_OVERRIDES = {'arr': lambda: sorted(random.sample(range(1, 8), random.randint(3, 6)))}


# ── 49. Two Sum ──────────────────────────────────────────────────────

TWO_SUM_CORRECT = '''
def two_sum(nums, target):
    seen = {}
    for i, x in enumerate(nums):
        comp = target - x
        if comp in seen:
            return [seen[comp], i]
        seen[x] = i
    return []
'''

TWO_SUM_BUGGY = '''
def two_sum(nums, target):
    seen = {}
    for i, x in enumerate(nums):
        comp = target - x
        if comp in seen:
            return [seen[comp], i]
        seen[x] = i + 1
    return []
'''

def two_sum_spec(nums, target, result):
    if not result:
        return not any(nums[i] + nums[j] == target for i in range(len(nums)) for j in range(i+1, len(nums)))
    if len(result) != 2:
        return False
    i, j = result
    return 0 <= i < j < len(nums) and nums[i] + nums[j] == target

TWO_SUM_OVERRIDES = {
    'nums': lambda: _gen_list_int(5, 15, -20, 20),
    'target': lambda: random.randint(-20, 20),
}


# ── 50. Majority Element (Boyer-Moore Voting) ────────────────────────

MAJORITY_CORRECT = '''
def majority_element(nums):
    candidate = None
    count = 0
    for x in nums:
        if count == 0:
            candidate = x
            count = 1
        elif x == candidate:
            count += 1
        else:
            count -= 1
    # Verify
    if nums.count(candidate) > len(nums) // 2:
        return candidate
    return None
'''

MAJORITY_BUGGY = '''
def majority_element(nums):
    candidate = None
    count = 0
    for x in nums:
        if count == 0:
            candidate = x
            count = 1
        elif x == candidate:
            count += 1
        else:
            count -= 1
    return candidate
'''

def majority_spec(nums, result):
    if not nums:
        return result is None
    counts = {}
    for x in nums:
        counts[x] = counts.get(x, 0) + 1
    threshold = len(nums) // 2
    actual_majority = None
    for x, c in counts.items():
        if c > threshold:
            actual_majority = x
    return result == actual_majority

MAJORITY_OVERRIDES = {
    'nums': lambda: [random.choice([1, 2, 3]) for _ in range(random.randint(5, 15))],
}


# ═══════════════════════════════════════════════════════════════════════════
#  ALGORITHM REGISTRY
# ═══════════════════════════════════════════════════════════════════════════

ALGORITHMS: List[AlgoCase] = [
    AlgoCase("merge_sort", MERGE_SORT_CORRECT, MERGE_SORT_BUGGY, merge_sort_spec,
             "missing right-side extend (drops tail of right half)", None),
    AlgoCase("quick_sort", QUICK_SORT_CORRECT, QUICK_SORT_BUGGY, quick_sort_spec,
             ">= instead of > duplicates pivot elements", None),
    AlgoCase("heap_sort", HEAP_SORT_CORRECT, HEAP_SORT_BUGGY, heap_sort_spec,
             "sift_down limit end-2 instead of end-1 (corrupts heap)", None),
    AlgoCase("insertion_sort", INSERTION_SORT_CORRECT, INSERTION_SORT_BUGGY, insertion_sort_spec,
             "j>0 instead of j>=0 (never places element at index 0)", None),
    AlgoCase("counting_sort", COUNTING_SORT_CORRECT, COUNTING_SORT_BUGGY, counting_sort_spec,
             "c-1 instead of c (drops one of each element)", None),
    AlgoCase("selection_sort", SELECTION_SORT_CORRECT, SELECTION_SORT_BUGGY, selection_sort_spec,
             "inner loop starts at i+2 instead of i+1 (skips adjacent element)", None),
    AlgoCase("bubble_sort", BUBBLE_SORT_CORRECT, BUBBLE_SORT_BUGGY, bubble_sort_spec,
             "n-i-2 instead of n-i-1 (skips last comparison)", None),
    AlgoCase("binary_search", BINARY_SEARCH_CORRECT, BINARY_SEARCH_BUGGY, binary_search_spec,
             "< vs <= (misses single-element case)", BINARY_SEARCH_OVERRIDES),
    AlgoCase("interpolation_search", INTERP_SEARCH_CORRECT, INTERP_SEARCH_BUGGY, interp_search_spec,
             "pos+2 instead of pos+1 (skips elements)", INTERP_SEARCH_OVERRIDES),
    AlgoCase("kadane_max_subarray", KADANE_CORRECT, KADANE_BUGGY, kadane_spec,
             "best = current instead of max(best, current)", None),
    AlgoCase("dijkstra", DIJKSTRA_CORRECT, DIJKSTRA_BUGGY, dijkstra_spec,
             "no visited set (processes nodes multiple times)", DIJKSTRA_OVERRIDES),
    AlgoCase("bellman_ford", BELLMAN_FORD_CORRECT, BELLMAN_FORD_BUGGY, bellman_ford_spec,
             "n-2 iterations instead of n-1", BELLMAN_FORD_OVERRIDES),
    AlgoCase("topo_sort", TOPO_SORT_CORRECT, TOPO_SORT_BUGGY, topo_sort_spec,
             "<= 0 instead of == 0 (adds nodes too early)", TOPO_SORT_OVERRIDES),
    AlgoCase("union_find", UNION_FIND_CORRECT, UNION_FIND_BUGGY, union_find_spec,
             "uses parent[i] instead of find(i) for counting", UNION_FIND_OVERRIDES),
    AlgoCase("kruskal_mst", KRUSKAL_CORRECT, KRUSKAL_BUGGY, kruskal_spec,
             "edges not sorted by weight", KRUSKAL_OVERRIDES),
    AlgoCase("floyd_warshall", FLOYD_WARSHALL_CORRECT, FLOYD_WARSHALL_BUGGY, floyd_warshall_spec,
             "wrong loop order (i,j,k instead of k,i,j)", FLOYD_OVERRIDES),
    AlgoCase("prim_mst", PRIM_CORRECT, PRIM_BUGGY, prim_spec,
             "adds already-visited neighbors to heap", PRIM_OVERRIDES),
    AlgoCase("lcs_length", LCS_CORRECT, LCS_BUGGY, lcs_spec,
             "dp[i-1][j-1] instead of dp[i][j-1] in else branch", LCS_OVERRIDES),
    AlgoCase("edit_distance", EDIT_DIST_CORRECT, EDIT_DIST_BUGGY, edit_dist_spec,
             "missing substitution option in min()", EDIT_DIST_OVERRIDES),
    AlgoCase("knapsack_01", KNAPSACK_CORRECT, KNAPSACK_BUGGY, knapsack_spec,
             "dp[i] instead of dp[i-1] (unbounded knapsack bug)", KNAPSACK_OVERRIDES),
    AlgoCase("coin_change", COIN_CHANGE_CORRECT, COIN_CHANGE_BUGGY, coin_change_spec,
             "greedy break instead of full DP", COIN_CHANGE_OVERRIDES),
    AlgoCase("lis_length", LIS_CORRECT, LIS_BUGGY, lis_spec,
             "<= instead of < in binary search (non-strictly increasing)", None),
    AlgoCase("matrix_chain", MATCHAIN_CORRECT, MATCHAIN_BUGGY, matchain_spec,
             "dims[k] instead of dims[k+1] in cost formula", MATCHAIN_OVERRIDES),
    AlgoCase("rod_cutting", ROD_CORRECT, ROD_BUGGY, rod_spec,
             "dp[i-j-1] instead of dp[i-j] (off-by-one)", ROD_OVERRIDES),
    AlgoCase("kmp_search", KMP_CORRECT, KMP_BUGGY, kmp_spec,
             "j=0 instead of j=fail[j-1] after match (misses overlapping)", KMP_OVERRIDES),
    AlgoCase("z_algorithm", Z_ALGO_CORRECT, Z_ALGO_BUGGY, z_algo_spec,
             ">= instead of > in Z-box extension", Z_ALGO_OVERRIDES),
    AlgoCase("sieve_eratosthenes", SIEVE_CORRECT, SIEVE_BUGGY, sieve_spec,
             "starts at 2*i instead of i*i (correct output but slower; actually identical for primes)",
             SIEVE_OVERRIDES),
    AlgoCase("extended_gcd", EGCD_CORRECT, EGCD_BUGGY, egcd_spec,
             "x1 instead of y1 in coefficient update", EGCD_OVERRIDES),
    AlgoCase("mod_exp", MOD_EXP_CORRECT, MOD_EXP_BUGGY, mod_exp_spec,
             "missing mod on base squaring intermediate", MOD_EXP_OVERRIDES),
    AlgoCase("newton_sqrt", NEWTON_SQRT_CORRECT, NEWTON_SQRT_BUGGY, newton_sqrt_spec,
             "only 3 iterations instead of 100 (insufficient convergence)", NEWTON_SQRT_OVERRIDES),
    AlgoCase("convex_hull", CONVEX_HULL_CORRECT, CONVEX_HULL_BUGGY, convex_hull_spec,
             "< instead of <= in cross product check (keeps collinear points)", CONVEX_HULL_OVERRIDES),
    AlgoCase("closest_pair", CLOSEST_PAIR_CORRECT, CLOSEST_PAIR_BUGGY, closest_pair_spec,
             "Manhattan distance instead of Euclidean", CLOSEST_PAIR_OVERRIDES),
    AlgoCase("interval_scheduling", INTERVAL_SCHED_CORRECT, INTERVAL_SCHED_BUGGY, interval_sched_spec,
             "sorts by start instead of end time", INTERVAL_SCHED_OVERRIDES),
    AlgoCase("bst_insert", BST_INSERT_CORRECT, BST_INSERT_BUGGY, bst_insert_spec,
             "<= instead of < (allows duplicates in left subtree)", BST_INSERT_OVERRIDES),
    AlgoCase("trie_insert", TRIE_CORRECT, TRIE_BUGGY, trie_spec,
             "missing end-of-word marker", TRIE_OVERRIDES),
    AlgoCase("fenwick_tree", FENWICK_CORRECT, FENWICK_BUGGY, fenwick_spec,
             "adds arr[i] to parent instead of bit[idx]", FENWICK_OVERRIDES),
    AlgoCase("gaussian_elim", GAUSS_CORRECT, GAUSS_BUGGY, gauss_spec,
             "no partial pivoting (fails when diagonal is zero)", GAUSS_OVERRIDES),
    AlgoCase("chinese_remainder", CRT_CORRECT, CRT_BUGGY, crt_spec,
             "mod moduli[0] instead of mod M (product of all moduli)", CRT_OVERRIDES),
    AlgoCase("reservoir_sampling", RESERVOIR_CORRECT, RESERVOIR_BUGGY, reservoir_spec,
             "randint(0,i-1) instead of randint(0,i) (biased)", RESERVOIR_OVERRIDES),
    AlgoCase("longest_palindrome", PALINDROME_CORRECT, PALINDROME_BUGGY, palindrome_spec,
             "missing even-length palindrome expansion", PALINDROME_OVERRIDES),
    AlgoCase("suffix_array", SUFFIX_ARRAY_CORRECT, SUFFIX_ARRAY_BUGGY, suffix_array_spec,
             "truncated key sort (wrong for long common prefixes)", SUFFIX_ARRAY_OVERRIDES),
    AlgoCase("rabin_karp", RABIN_KARP_CORRECT, RABIN_KARP_BUGGY, rabin_karp_spec,
             "no verification after hash match (false positives)", RABIN_KARP_OVERRIDES),
    AlgoCase("count_inversions", INVERSIONS_CORRECT, INVERSIONS_BUGGY, inversions_spec,
             "counts 1 per cross instead of len(left)-i", INVERSIONS_OVERRIDES),
    AlgoCase("power_set", POWERSET_CORRECT, POWERSET_BUGGY, powerset_spec,
             "removes empty set from result", None),
    AlgoCase("dutch_national_flag", DNF_CORRECT, DNF_BUGGY, dnf_spec,
             "mid++ in high swap (skips swapped element)", DNF_OVERRIDES),
    AlgoCase("gcd_euclidean", GCD_CORRECT, GCD_BUGGY, gcd_spec_fn,
             "subtraction instead of modulo (infinite loop on some inputs)", GCD_OVERRIDES),
    AlgoCase("rotate_array", ROTATE_CORRECT, ROTATE_BUGGY, rotate_spec,
             "rotates left instead of right", ROTATE_OVERRIDES),
    AlgoCase("next_permutation", NEXT_PERM_CORRECT, NEXT_PERM_BUGGY, next_perm_spec,
             "missing suffix reversal after swap", NEXT_PERM_OVERRIDES),
    AlgoCase("two_sum", TWO_SUM_CORRECT, TWO_SUM_BUGGY, two_sum_spec,
             "stores i+1 instead of i in hash map", TWO_SUM_OVERRIDES),
    AlgoCase("majority_element", MAJORITY_CORRECT, MAJORITY_BUGGY, majority_spec,
             "missing verification pass (returns candidate even if not majority)", MAJORITY_OVERRIDES),
]


# ═══════════════════════════════════════════════════════════════════════════
#  TEST RUNNER
# ═══════════════════════════════════════════════════════════════════════════

def run_one(algo: AlgoCase, verifier: SheafSpecVerifier,
            verbose: bool = False) -> AlgoResult:
    """Run proof-based verification on one algorithm pair."""
    t0 = time.time()
    error = ""
    n_vcs = 0
    cech_elim = 0
    n_z3_proofs = 0
    n_z3_refutations = 0
    n_structural = 0
    n_sheaf_transfers = 0
    n_impl_section = 0
    correct_refuted = False
    buggy_refuted = False

    try:
        r_correct = verifier.verify(
            algo.correct, algo.spec,
            input_overrides=algo.input_overrides,
        )
        r_buggy = verifier.verify(
            algo.buggy, algo.spec,
            input_overrides=algo.input_overrides,
        )
        correct_verdict = r_correct.correct
        buggy_verdict = r_buggy.correct
        correct_refuted = r_correct.refuted
        buggy_refuted = r_buggy.refuted
        n_vcs = r_correct.n_vcs_total + r_buggy.n_vcs_total
        cech_elim = r_correct.n_vcs_eliminated + r_buggy.n_vcs_eliminated
        n_z3_proofs = r_correct.n_z3_proofs + r_buggy.n_z3_proofs
        n_z3_refutations = r_correct.n_z3_refutations + r_buggy.n_z3_refutations
        n_structural = r_correct.n_structural_proofs + r_buggy.n_structural_proofs
        n_sheaf_transfers = r_correct.n_sheaf_transfers + r_buggy.n_sheaf_transfers
        n_impl_section = r_correct.n_impl_section_proofs + r_buggy.n_impl_section_proofs

        if verbose:
            print(f"       Correct: {r_correct.correct} (proved={r_correct.n_vcs_proved}, "
                  f"refuted={r_correct.n_vcs_refuted}, inconc={r_correct.n_vcs_inconclusive})")
            print(f"       Buggy:   {r_buggy.correct} (proved={r_buggy.n_vcs_proved}, "
                  f"refuted={r_buggy.n_vcs_refuted}, inconc={r_buggy.n_vcs_inconclusive})")
            for line in r_correct.proof_log[-3:]:
                print(f"       [correct] {line}")
            for line in r_buggy.proof_log[-3:]:
                print(f"       [buggy]   {line}")

    except Exception as e:
        correct_verdict = False
        buggy_verdict = False
        error = f"{type(e).__name__}: {e}"
        if verbose:
            traceback.print_exc()

    elapsed = (time.time() - t0) * 1000

    detected = correct_verdict and not buggy_verdict
    false_pos = not correct_verdict and not error
    false_neg = buggy_verdict if buggy_verdict else False

    return AlgoResult(
        name=algo.name,
        correct_verdict=correct_verdict,
        buggy_verdict=buggy_verdict,
        detected=detected,
        false_positive=false_pos,
        false_negative=false_neg,
        elapsed_ms=elapsed,
        error=error,
        n_vcs=n_vcs,
        cech_eliminated=cech_elim,
        n_z3_proofs=n_z3_proofs,
        n_z3_refutations=n_z3_refutations,
        n_structural=n_structural,
        n_sheaf_transfers=n_sheaf_transfers,
        n_impl_section=n_impl_section,
        correct_refuted=correct_refuted,
        buggy_refuted=buggy_refuted,
    )


def run_all(verbose: bool = False) -> List[AlgoResult]:
    """Run proof-based verification on all algorithm pairs.

    No concrete testing — pure sheaf-descent proofs via Z3/structural/transfer.
    """
    verifier = SheafSpecVerifier(z3_timeout_ms=3000.0)
    results = []

    print(f"{'='*90}", flush=True)
    print(f"  Sheaf Descent Proof Engine — {len(ALGORITHMS)} Algorithm Verification Suite", flush=True)
    print(f"  (Pure proofs: Z3 + structural + Čech cohomology — no concrete testing)", flush=True)
    print(f"{'='*90}", flush=True)
    print(f"  {'#':>3}  {'Algorithm':<25} {'Correct':>8} {'Buggy':>8} {'Detect':>8} "
          f"{'Z3':>4} {'Str':>4} {'Shf':>4} {'Ref':>4} {'Time':>8}", flush=True)
    print(f"  {'─'*3}  {'─'*25} {'─'*8} {'─'*8} {'─'*8} "
          f"{'─'*4} {'─'*4} {'─'*4} {'─'*4} {'─'*8}", flush=True)

    for i, algo in enumerate(ALGORITHMS):
        print(f"  [{i+1:>2}/{len(ALGORITHMS)}] {algo.name}...", end="", flush=True)
        r = run_one(algo, verifier, verbose)
        results.append(r)

        c_mark = "PROVED" if r.correct_verdict else ("REFUTED" if r.correct_refuted else "INCONC")
        b_mark = "REFUTED" if r.buggy_refuted else ("PASS" if r.buggy_verdict else "INCONC")
        d_mark = "CAUGHT" if r.detected else ("FP" if r.false_positive else ("FN" if r.false_negative else "---"))

        c_col = "\033[32m" if r.correct_verdict else "\033[31m"
        b_col = "\033[32m" if (r.buggy_refuted or not r.buggy_verdict) else "\033[31m"
        d_col = "\033[32m" if r.detected else "\033[33m"

        # Clear the "starting" line and print result
        print(f"\r  {i+1:>3}  {algo.name:<25} "
              f"{c_col}{c_mark:>8}\033[0m "
              f"{b_col}{b_mark:>8}\033[0m "
              f"{d_col}{d_mark:>8}\033[0m "
              f"{r.n_z3_proofs:>4} {r.n_structural:>4} {r.n_sheaf_transfers:>4} "
              f"{r.n_z3_refutations:>4} "
              f"{r.elapsed_ms:>6.0f}ms", flush=True)

        if r.error and verbose:
            print(f"       ERROR: {r.error}", flush=True)

    # Summary
    n = len(results)
    n_detected = sum(1 for r in results if r.detected)
    n_fp = sum(1 for r in results if r.false_positive)
    n_fn = sum(1 for r in results if r.false_negative)
    n_err = sum(1 for r in results if r.error)
    total_vcs = sum(r.n_vcs for r in results)
    total_cech = sum(r.cech_eliminated for r in results)
    total_z3 = sum(r.n_z3_proofs for r in results)
    total_structural = sum(r.n_structural for r in results)
    total_sheaf = sum(r.n_sheaf_transfers for r in results)
    total_impl = sum(r.n_impl_section for r in results)
    total_refuted = sum(r.n_z3_refutations for r in results)
    total_time = sum(r.elapsed_ms for r in results)

    print(f"\n{'='*90}")
    print(f"  PROOF SUMMARY")
    print(f"{'='*90}")
    print(f"  Algorithms verified:      {n}")
    print(f"  Bugs detected (proved):   {n_detected}/{n} ({100*n_detected/n:.1f}%)")
    print(f"  False positives:          {n_fp}")
    print(f"  False negatives:          {n_fn}")
    print(f"  Errors:                   {n_err}")
    print(f"  ──────────────────────────────────────")
    print(f"  PROOF METHOD BREAKDOWN:")
    print(f"    Z3 proofs:              {total_z3}")
    print(f"    Z3 refutations:         {total_refuted}")
    print(f"    Structural proofs:      {total_structural}")
    print(f"    Sheaf H^0 transfers:    {total_sheaf}")
    print(f"    Impl section proofs:    {total_impl}")
    print(f"  ──────────────────────────────────────")
    print(f"  SHEAF COHOMOLOGY:")
    print(f"    Total VCs generated:    {total_vcs}")
    print(f"    VCs elim (Čech H^1):    {total_cech} ({100*total_cech/max(1,total_vcs):.1f}%)")
    print(f"  ──────────────────────────────────────")
    print(f"  Total time:               {total_time:.0f}ms ({total_time/1000:.1f}s)")
    print(f"{'='*90}")

    if n_fp > 0:
        print(f"\n  False Positives (correct code refuted — BUG IN VERIFIER):")
        for r in results:
            if r.false_positive:
                print(f"    - {r.name}")

    if n_fn > 0:
        print(f"\n  False Negatives (buggy code not refuted):")
        for r in results:
            if r.false_negative:
                algo = next(a for a in ALGORITHMS if a.name == r.name)
                print(f"    - {r.name}: {algo.bug_desc}")

    if n_err > 0:
        print(f"\n  Errors:")
        for r in results:
            if r.error:
                print(f"    - {r.name}: {r.error}")

    return results


if __name__ == '__main__':
    verbose = '--verbose' in sys.argv or '-v' in sys.argv
    run_all(verbose=verbose)
