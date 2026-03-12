"""Matrix chain multiplication ordering via dynamic programming.

Given a sequence of matrices with dimensions p[0]xp[1], p[1]xp[2], ...,
p[n-1]xp[n], finds the optimal parenthesization that minimizes the total
number of scalar multiplications using the classic O(n^3) DP.

Bug: in the DP recurrence, the right subproblem uses m[k+1][j] instead
of m[k][j] (with the correct split at k meaning left=m[i][k], right=m[k+1][j],
but the bug shifts the split by using k+1 for both the cost lookup and
the dimension index). This produces wrong costs and suboptimal orderings.
"""

CORRECT = r"""
def solve_chain(dimensions):
    n = len(dimensions) - 1
    if n <= 0:
        return {"min_cost": 0, "parenthesization": "", "num_matrices": 0}
    if n == 1:
        return {"min_cost": 0, "parenthesization": "A0", "num_matrices": 1}

    m = [[0] * n for _ in range(n)]
    s = [[0] * n for _ in range(n)]

    for chain_len in range(2, n + 1):
        for i in range(n - chain_len + 1):
            j = i + chain_len - 1
            m[i][j] = float("inf")
            for k in range(i, j):
                cost = m[i][k] + m[k + 1][j] + dimensions[i] * dimensions[k + 1] * dimensions[j + 1]
                if cost < m[i][j]:
                    m[i][j] = cost
                    s[i][j] = k

    def build_parens(i, j):
        if i == j:
            return "A" + str(i)
        k = s[i][j]
        left = build_parens(i, k)
        right = build_parens(k + 1, j)
        return "(" + left + " x " + right + ")"

    parens = build_parens(0, n - 1)
    return {"min_cost": m[0][n - 1], "parenthesization": parens, "num_matrices": n}

dimensions = DIMENSIONS
result = solve_chain(dimensions)
"""

BUGGY = r"""
def solve_chain(dimensions):
    n = len(dimensions) - 1
    if n <= 0:
        return {"min_cost": 0, "parenthesization": "", "num_matrices": 0}
    if n == 1:
        return {"min_cost": 0, "parenthesization": "A0", "num_matrices": 1}

    m = [[0] * n for _ in range(n)]
    s = [[0] * n for _ in range(n)]

    for chain_len in range(2, n + 1):
        for i in range(n - chain_len + 1):
            j = i + chain_len - 1
            m[i][j] = float("inf")
            for k in range(i, j):
                # BUG: uses k+2 instead of k+1 for dimension index
                k2 = min(k + 2, len(dimensions) - 1)
                cost = m[i][k] + m[k + 1][j] + dimensions[i] * dimensions[k2] * dimensions[j + 1]
                if cost < m[i][j]:
                    m[i][j] = cost
                    s[i][j] = k

    def build_parens(i, j):
        if i == j:
            return "A" + str(i)
        k = s[i][j]
        left = build_parens(i, k)
        right = build_parens(k + 1, j)
        return "(" + left + " x " + right + ")"

    parens = build_parens(0, n - 1)
    return {"min_cost": m[0][n - 1], "parenthesization": parens, "num_matrices": n}

dimensions = DIMENSIONS
result = solve_chain(dimensions)
"""


def SPEC(dimensions, result):
    if not isinstance(result, dict):
        return False
    if "min_cost" not in result or "num_matrices" not in result:
        return False

    n = len(dimensions) - 1
    if n != result["num_matrices"]:
        return False

    if n <= 1:
        return result["min_cost"] == 0

    # Compute correct min cost via reference DP
    m_ref = [[0] * n for _ in range(n)]
    for cl in range(2, n + 1):
        for i in range(n - cl + 1):
            j = i + cl - 1
            m_ref[i][j] = float("inf")
            for k in range(i, j):
                cost = m_ref[i][k] + m_ref[k + 1][j] + dimensions[i] * dimensions[k + 1] * dimensions[j + 1]
                if cost < m_ref[i][j]:
                    m_ref[i][j] = cost

    expected_cost = m_ref[0][n - 1]
    if result["min_cost"] != expected_cost:
        return False

    # Verify the parenthesization string contains all matrix names
    parens = result.get("parenthesization", "")
    for i in range(n):
        if ("A" + str(i)) not in parens:
            return False

    return True


BUG_DESC = (
    "In the matrix chain DP recurrence, the cost of splitting at position k "
    "should be m[i][k] + m[k+1][j] + p[i]*p[k+1]*p[j+1]. The bug uses "
    "p[k+2] instead of p[k+1] for the shared dimension, effectively using "
    "the wrong inner dimension for the multiplication cost. This produces "
    "incorrect cost values and therefore a suboptimal parenthesization."
)


def _gen_dimensions():
    import random
    # Generate n+1 dimensions for n matrices (n between 4 and 7)
    n = random.randint(4, 7)
    dims = []
    for _ in range(n + 1):
        dims.append(random.choice([5, 10, 15, 20, 25, 30, 35, 40]))
    return dims


INPUT_OVERRIDES = {
    "DIMENSIONS": _gen_dimensions,
}
