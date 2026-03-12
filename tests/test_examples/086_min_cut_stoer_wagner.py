"""Stoer-Wagner algorithm for global minimum cut. Bug: merges with wrong vertex's weight, producing incorrect cut values."""

CORRECT = r"""
# Stoer-Wagner algorithm for finding the global minimum cut in an undirected weighted graph
# Input: EDGES is a list of (u, v, weight) tuples, NUM_VERTICES is the vertex count

import sys

n = NUM_VERTICES
# Build adjacency matrix
w = [[0] * n for _ in range(n)]
for u, v, wt in EDGES:
    w[u][v] += wt
    w[v][u] += wt

# Track which original vertices are merged into each supernode
merged = [[i] for i in range(n)]
active = [True] * n

best_cut = float('inf')
best_partition = None

def minimum_cut_phase():
    global best_cut, best_partition
    # Maximum adjacency search
    in_A = [False] * n
    # Weight of edges from node to set A
    wa = [0] * n

    # Start with the first active vertex
    start = -1
    for i in range(n):
        if active[i]:
            start = i
            break

    last = start
    second_last = start

    # We need to add n_active vertices to A
    n_active = sum(1 for i in range(n) if active[i])

    for step in range(n_active):
        # Find the most tightly connected vertex not in A
        in_A[last if step > 0 else start] = True
        if step == 0:
            # Update weights from start
            for j in range(n):
                if active[j] and not in_A[j]:
                    wa[j] += w[start][j]
        else:
            for j in range(n):
                if active[j] and not in_A[j]:
                    wa[j] += w[last][j]

        if step == n_active - 1:
            break

        # Pick next vertex with max wa
        next_v = -1
        max_w = -1
        for j in range(n):
            if active[j] and not in_A[j] and wa[j] > max_w:
                max_w = wa[j]
                next_v = j
        second_last = last
        last = next_v

    # The cut of the phase is wa[last] (weight of last added vertex)
    cut_of_phase = wa[last]
    if cut_of_phase < best_cut:
        best_cut = cut_of_phase
        best_partition = list(merged[last])

    # Merge last into second_last
    for i in range(n):
        w[second_last][i] += w[last][i]
        w[i][second_last] += w[i][last]
    merged[second_last].extend(merged[last])
    active[last] = False

n_active = sum(1 for i in range(n) if active[i])
while n_active > 1:
    minimum_cut_phase()
    n_active = sum(1 for i in range(n) if active[i])

result = {
    "min_cut_value": best_cut,
    "partition_side": sorted(best_partition),
}
"""

BUGGY = r"""
# Stoer-Wagner algorithm for finding the global minimum cut

import sys

n = NUM_VERTICES
w = [[0] * n for _ in range(n)]
for u, v, wt in EDGES:
    w[u][v] += wt
    w[v][u] += wt

merged = [[i] for i in range(n)]
active = [True] * n

best_cut = float('inf')
best_partition = None

def minimum_cut_phase():
    global best_cut, best_partition
    in_A = [False] * n
    wa = [0] * n

    start = -1
    for i in range(n):
        if active[i]:
            start = i
            break

    last = start
    second_last = start

    n_active = sum(1 for i in range(n) if active[i])

    for step in range(n_active):
        in_A[last if step > 0 else start] = True
        if step == 0:
            for j in range(n):
                if active[j] and not in_A[j]:
                    wa[j] += w[start][j]
        else:
            for j in range(n):
                if active[j] and not in_A[j]:
                    wa[j] += w[last][j]

        if step == n_active - 1:
            break

        next_v = -1
        max_w = -1
        for j in range(n):
            if active[j] and not in_A[j] and wa[j] > max_w:
                max_w = wa[j]
                next_v = j
        second_last = last
        last = next_v

    # BUG: uses wa[second_last] instead of wa[last]
    # This uses the wrong vertex's accumulated weight as the cut value
    cut_of_phase = wa[second_last]
    if cut_of_phase < best_cut:
        best_cut = cut_of_phase
        best_partition = list(merged[last])

    # Merge last into second_last
    for i in range(n):
        w[second_last][i] += w[last][i]
        w[i][second_last] += w[i][last]
    merged[second_last].extend(merged[last])
    active[last] = False

n_active = sum(1 for i in range(n) if active[i])
while n_active > 1:
    minimum_cut_phase()
    n_active = sum(1 for i in range(n) if active[i])

result = {
    "min_cut_value": best_cut,
    "partition_side": sorted(best_partition),
}
"""


def SPEC(edges, num_vertices, result):
    # Verify by checking all possible 2-partitions for small graphs
    # or at least verify the returned cut value is correct
    n = num_vertices
    if n <= 1:
        return result["min_cut_value"] == 0

    # Build adjacency for brute force
    adj = [[0] * n for _ in range(n)]
    for u, v, wt in edges:
        adj[u][v] += wt
        adj[v][u] += wt

    # Brute force: try all non-empty subsets of size 1..n-1
    min_cut = float('inf')
    for mask in range(1, (1 << n) - 1):
        cut_val = 0
        for i in range(n):
            for j in range(i + 1, n):
                if ((mask >> i) & 1) != ((mask >> j) & 1):
                    cut_val += adj[i][j]
        if cut_val < min_cut:
            min_cut = cut_val

    if result["min_cut_value"] != min_cut:
        return False

    # Verify partition_side is a valid non-empty proper subset
    part = result["partition_side"]
    if not part or len(part) >= n:
        return False
    if any(v < 0 or v >= n for v in part):
        return False

    # Verify the partition actually achieves the claimed cut value
    part_set = set(part)
    actual_cut = 0
    for u, v, wt in edges:
        if (u in part_set) != (v in part_set):
            actual_cut += wt
    if actual_cut != min_cut:
        return False

    return True


BUG_DESC = "Uses wa[second_last] instead of wa[last] as the cut-of-phase value, reading the wrong vertex's accumulated weight and producing incorrect minimum cut values."


def _gen_edges():
    # Small graph where the bug triggers
    return [
        (0, 1, 2), (0, 2, 3), (1, 2, 3),
        (1, 3, 2), (2, 3, 2), (2, 4, 4),
        (3, 4, 1), (3, 5, 3), (4, 5, 2),
    ]


def _gen_num_vertices():
    return 6


INPUT_OVERRIDES = {
    "EDGES": _gen_edges,
    "NUM_VERTICES": _gen_num_vertices,
}
