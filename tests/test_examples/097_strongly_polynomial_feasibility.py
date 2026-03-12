"""Checking feasibility of a system of difference constraints via Bellman-Ford.
Bug: runs only n-2 relaxation iterations instead of n-1, missing negative
cycles that require the full n-1 passes to detect."""

CORRECT = r"""
# Difference constraints feasibility via Bellman-Ford
# CONSTRAINTS: list of (u, v, w) meaning x_v - x_u <= w
# NUM_VARS: number of variables (0 to NUM_VARS-1)
# We add a source node s connected to all variables with weight 0
# Returns (feasible, distances) where distances is a feasible assignment if feasible

constraints = list(CONSTRAINTS)
num_vars = NUM_VARS

# Build graph: nodes 0..num_vars, where num_vars is the source
n = num_vars + 1
source = num_vars

# Edges: source to each var with weight 0, plus constraint edges
edges = []
for i in range(num_vars):
    edges.append((source, i, 0))
for u, v, w in constraints:
    edges.append((u, v, w))

# Bellman-Ford
INF = float('inf')
dist = [INF] * n
dist[source] = 0

# CORRECT: n-1 relaxation iterations
for iteration in range(n - 1):
    updated = False
    for u, v, w in edges:
        if dist[u] != INF and dist[u] + w < dist[v]:
            dist[v] = dist[u] + w
            updated = True
    if not updated:
        break

# Check for negative cycle
has_neg_cycle = False
for u, v, w in edges:
    if dist[u] != INF and dist[u] + w < dist[v]:
        has_neg_cycle = True
        break

if has_neg_cycle:
    result = (False, [])
else:
    # Extract feasible assignment for variables 0..num_vars-1
    assignment = dist[:num_vars]
    result = (True, assignment)
"""

BUGGY = r"""
# Difference constraints feasibility via Bellman-Ford
# CONSTRAINTS: list of (u, v, w) meaning x_v - x_u <= w
# NUM_VARS: number of variables (0 to NUM_VARS-1)

constraints = list(CONSTRAINTS)
num_vars = NUM_VARS

n = num_vars + 1
source = num_vars

edges = []
for i in range(num_vars):
    edges.append((source, i, 0))
for u, v, w in constraints:
    edges.append((u, v, w))

INF = float('inf')
dist = [INF] * n
dist[source] = 0

# BUG: runs n-2 iterations instead of n-1
# This means negative cycles requiring exactly n-1 passes to propagate
# through the full chain will not be detected
for iteration in range(n - 2):
    updated = False
    for u, v, w in edges:
        if dist[u] != INF and dist[u] + w < dist[v]:
            dist[v] = dist[u] + w
            updated = True
    if not updated:
        break

# Check for negative cycle
has_neg_cycle = False
for u, v, w in edges:
    if dist[u] != INF and dist[u] + w < dist[v]:
        has_neg_cycle = True
        break

if has_neg_cycle:
    result = (False, [])
else:
    assignment = dist[:num_vars]
    result = (True, assignment)
"""


def SPEC(constraints, num_vars, result):
    feasible, assignment = result

    # Verify independently: check for negative cycles using full Bellman-Ford
    n = num_vars + 1
    source = num_vars
    edges = []
    for i in range(num_vars):
        edges.append((source, i, 0))
    for u, v, w in constraints:
        edges.append((u, v, w))

    INF = float('inf')
    dist = [INF] * n
    dist[source] = 0
    for _ in range(n - 1):
        for u, v, w in edges:
            if dist[u] != INF and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w

    has_neg = False
    for u, v, w in edges:
        if dist[u] != INF and dist[u] + w < dist[v]:
            has_neg = True
            break

    expected_feasible = not has_neg

    if feasible != expected_feasible:
        return False

    if feasible:
        # Verify the assignment satisfies all constraints
        if len(assignment) != num_vars:
            return False
        for u, v, w in constraints:
            if assignment[v] - assignment[u] > w + 1e-9:
                return False

    return True


BUG_DESC = (
    "Bellman-Ford runs n-2 relaxation iterations instead of the required n-1. "
    "Negative cycles that need the full n-1 passes to propagate are not "
    "detected, so infeasible systems are incorrectly reported as feasible."
)


def _gen_constraints():
    import random
    num_vars = random.randint(4, 7)
    constraints = []
    # Generate some normal constraints
    for _ in range(num_vars + 2):
        u = random.randint(0, num_vars - 1)
        v = random.randint(0, num_vars - 1)
        if u != v:
            w = random.randint(-5, 10)
            constraints.append((u, v, w))
    # Sometimes add a long negative cycle to trigger the bug
    if random.random() < 0.5:
        # Create chain 0 -> 1 -> 2 -> ... -> k -> 0 with total weight < 0
        k = num_vars - 1
        for i in range(k):
            constraints.append((i, i + 1, 1))
        # Close the cycle with negative weight making total negative
        constraints.append((k, 0, -(k + 2)))
    return constraints


def _gen_num_vars():
    import random
    return random.randint(4, 7)


INPUT_OVERRIDES = {"CONSTRAINTS": _gen_constraints, "NUM_VARS": _gen_num_vars}
