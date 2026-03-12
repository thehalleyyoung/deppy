"""Hungarian algorithm for minimum-cost bipartite matching.

Bug: When updating the min_to[] array for unvisited columns after computing
delta, the correct code subtracts delta (min_to[j] -= delta). The buggy
version adds delta instead (min_to[j] += delta), which causes the reduced
costs to grow rather than shrink, leading to selection of suboptimal
augmenting paths and a non-minimum-cost matching.
"""

CORRECT = r"""
def hungarian(cost_matrix):
    n = len(cost_matrix)
    INF = float('inf')

    # u[i] = potential for row i, v[j] = potential for column j
    u = [0] * (n + 1)
    v = [0] * (n + 1)
    # match_col[j] = row matched to column j (0 = unmatched sentinel)
    match_col = [0] * (n + 1)
    # match_row[i] = column matched to row i
    match_row = [0] * (n + 1)

    for i in range(1, n + 1):
        # Start augmenting from row i
        match_col[0] = i
        j0 = 0  # virtual column 0

        min_to = [INF] * (n + 1)    # min reduced cost to reach col j
        visited = [False] * (n + 1) # visited columns
        prev_col = [0] * (n + 1)    # previous column in augmenting path

        while True:
            visited[j0] = True
            row_of_j0 = match_col[j0]
            delta = INF
            j1 = -1

            for j in range(1, n + 1):
                if not visited[j]:
                    reduced = cost_matrix[row_of_j0 - 1][j - 1] - u[row_of_j0] - v[j]
                    if reduced < min_to[j]:
                        min_to[j] = reduced
                        prev_col[j] = j0
                    if min_to[j] < delta:
                        delta = min_to[j]
                        j1 = j

            # Update potentials
            for j in range(0, n + 1):
                if visited[j]:
                    u[match_col[j]] += delta
                    v[j] -= delta
                else:
                    min_to[j] -= delta  # CORRECT: subtract delta

            j0 = j1

            if match_col[j0] == 0:
                break

        # Recover augmenting path
        while j0 != 0:
            j_prev = prev_col[j0]
            match_col[j0] = match_col[j_prev]
            match_row[match_col[j0]] = j0
            j0 = j_prev

    # Build result: assignment[i] = j for row i (0-indexed)
    assignment = [0] * n
    total_cost = 0
    for i in range(1, n + 1):
        assignment[i - 1] = match_row[i] - 1
        total_cost += cost_matrix[i - 1][match_row[i] - 1]

    return assignment, total_cost

cost = COST_MATRIX
result = hungarian(cost)
"""

BUGGY = r"""
def hungarian(cost_matrix):
    n = len(cost_matrix)
    INF = float('inf')

    # u[i] = potential for row i, v[j] = potential for column j
    u = [0] * (n + 1)
    v = [0] * (n + 1)
    # match_col[j] = row matched to column j (0 = unmatched sentinel)
    match_col = [0] * (n + 1)
    # match_row[i] = column matched to row i
    match_row = [0] * (n + 1)

    for i in range(1, n + 1):
        # Start augmenting from row i
        match_col[0] = i
        j0 = 0  # virtual column 0

        min_to = [INF] * (n + 1)    # min reduced cost to reach col j
        visited = [False] * (n + 1) # visited columns
        prev_col = [0] * (n + 1)    # previous column in augmenting path

        # Limit iterations to prevent infinite loops from the bug
        max_iters = n * n + 10
        iteration = 0

        while iteration < max_iters:
            iteration += 1
            visited[j0] = True
            row_of_j0 = match_col[j0]
            delta = INF
            j1 = -1

            for j in range(1, n + 1):
                if not visited[j]:
                    reduced = cost_matrix[row_of_j0 - 1][j - 1] - u[row_of_j0] - v[j]
                    if reduced < min_to[j]:
                        min_to[j] = reduced
                        prev_col[j] = j0
                    if min_to[j] < delta:
                        delta = min_to[j]
                        j1 = j

            if j1 == -1:
                # Fallback: pick first unmatched column (greedy, suboptimal)
                for j in range(1, n + 1):
                    if match_col[j] == 0:
                        j1 = j
                        break
                if j1 == -1:
                    break

            # Update potentials
            for j in range(0, n + 1):
                if visited[j]:
                    u[match_col[j]] += delta
                    v[j] -= delta
                else:
                    min_to[j] += delta  # BUG: should be -= delta, not += delta

            j0 = j1

            if match_col[j0] == 0:
                break

        # Recover augmenting path
        while j0 != 0:
            j_prev = prev_col[j0]
            match_col[j0] = match_col[j_prev]
            match_row[match_col[j0]] = j0
            j0 = j_prev

    # Build result: assignment[i] = j for row i (0-indexed)
    assignment = [0] * n
    total_cost = 0
    for i in range(1, n + 1):
        assignment[i - 1] = match_row[i] - 1
        total_cost += cost_matrix[i - 1][match_row[i] - 1]

    return assignment, total_cost

cost = COST_MATRIX
result = hungarian(cost)
"""


def SPEC(cost_matrix, result):
    """Verify Hungarian algorithm result:
    1) Assignment is a valid permutation.
    2) Total cost matches the assignment.
    3) Total cost is optimal (brute-force for small n).
    """
    import itertools

    if not isinstance(result, (list, tuple)) or len(result) != 2:
        return False

    assignment, total_cost = result
    n = len(cost_matrix)

    if len(assignment) != n:
        return False

    # Check valid permutation
    if sorted(assignment) != list(range(n)):
        return False

    # Check total cost matches assignment
    computed_cost = sum(cost_matrix[i][assignment[i]] for i in range(n))
    if computed_cost != total_cost:
        return False

    # Brute-force optimality check (feasible for n <= 8)
    min_cost = float('inf')
    for perm in itertools.permutations(range(n)):
        c = sum(cost_matrix[i][perm[i]] for i in range(n))
        if c < min_cost:
            min_cost = c

    if total_cost != min_cost:
        return False

    return True


BUG_DESC = (
    "When updating the min_to[] array for unvisited columns after finding "
    "delta, the buggy version ADDS delta (min_to[j] += delta) instead of "
    "SUBTRACTING it (min_to[j] -= delta). This causes the reduced costs "
    "to increase rather than decrease, so the algorithm selects wrong "
    "augmenting paths and produces a suboptimal (non-minimum-cost) matching."
)


def _generate_cost_matrix():
    import random
    n = random.randint(4, 6)
    return [[random.randint(1, 20) for _ in range(n)] for _ in range(n)]


INPUT_OVERRIDES = {
    "COST_MATRIX": _generate_cost_matrix,
}
