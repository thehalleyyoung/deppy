"""Gaussian elimination over GF(2) (binary field). Bug: uses OR instead of XOR for row elimination."""

CORRECT = r"""
# Gaussian Elimination over GF(2) (binary field)
# Solves a system of linear equations over GF(2): MATRIX * x = TARGET
# MATRIX is a list of lists of 0/1 values, TARGET is a list of 0/1 values

import copy

m = len(MATRIX)       # number of equations
n = len(MATRIX[0])    # number of variables

# Build augmented matrix [MATRIX | TARGET]
aug = []
for i in range(m):
    row = list(MATRIX[i]) + [TARGET[i]]
    aug.append(row)

# Forward elimination
pivot_col = [0] * m
num_pivots = 0

for col in range(n):
    # Find a row with 1 in this column at or below num_pivots
    pivot_row = -1
    for row in range(num_pivots, m):
        if aug[row][col] == 1:
            pivot_row = row
            break

    if pivot_row == -1:
        continue

    # Swap pivot row to position num_pivots
    aug[num_pivots], aug[pivot_row] = aug[pivot_row], aug[num_pivots]
    pivot_col[num_pivots] = col

    # Eliminate all other rows (both above and below for reduced row echelon)
    for row in range(m):
        if row != num_pivots and aug[row][col] == 1:
            # XOR the pivot row into this row (GF(2) addition = XOR)
            for j in range(n + 1):
                aug[row][j] ^= aug[num_pivots][j]

    num_pivots += 1

# Check for inconsistency: a row with all-zero left side but 1 on right
solvable = True
for row in range(num_pivots, m):
    if aug[row][n] == 1:
        solvable = False
        break

# Extract solution (if solvable, set free variables to 0)
solution = [0] * n
if solvable:
    for i in range(num_pivots):
        solution[pivot_col[i]] = aug[i][n]

# Verify solution
if solvable:
    verified = True
    for i in range(m):
        s = 0
        for j in range(n):
            s ^= (MATRIX[i][j] & solution[j])
        if s != TARGET[i]:
            verified = False
            break
else:
    verified = False

result = {
    "solvable": solvable,
    "solution": solution if solvable else [],
    "rank": num_pivots,
    "verified": verified if solvable else False,
}
"""

BUGGY = r"""
# Gaussian Elimination over GF(2) (binary field)

import copy

m = len(MATRIX)
n = len(MATRIX[0])

aug = []
for i in range(m):
    row = list(MATRIX[i]) + [TARGET[i]]
    aug.append(row)

# Forward elimination
pivot_col = [0] * m
num_pivots = 0

for col in range(n):
    pivot_row = -1
    for row in range(num_pivots, m):
        if aug[row][col] == 1:
            pivot_row = row
            break

    if pivot_row == -1:
        continue

    aug[num_pivots], aug[pivot_row] = aug[pivot_row], aug[num_pivots]
    pivot_col[num_pivots] = col

    for row in range(m):
        if row != num_pivots and aug[row][col] == 1:
            # BUG: uses OR instead of XOR for elimination
            # Over GF(2), addition is XOR, not OR
            # OR does not properly cancel 1+1=0 in GF(2)
            for j in range(n + 1):
                aug[row][j] = aug[row][j] | aug[num_pivots][j]

    num_pivots += 1

# Check for inconsistency
solvable = True
for row in range(num_pivots, m):
    if aug[row][n] == 1:
        solvable = False
        break

# Extract solution
solution = [0] * n
if solvable:
    for i in range(num_pivots):
        solution[pivot_col[i]] = aug[i][n]

# Verify solution
if solvable:
    verified = True
    for i in range(m):
        s = 0
        for j in range(n):
            s ^= (MATRIX[i][j] & solution[j])
        if s != TARGET[i]:
            verified = False
            break
else:
    verified = False

result = {
    "solvable": solvable,
    "solution": solution if solvable else [],
    "rank": num_pivots,
    "verified": verified if solvable else False,
}
"""


def SPEC(matrix, target, result):
    m = len(matrix)
    n = len(matrix[0])

    if result["solvable"]:
        sol = result["solution"]
        if len(sol) != n:
            return False
        # All values must be 0 or 1
        if any(v not in (0, 1) for v in sol):
            return False
        # Verify: MATRIX * solution = TARGET (over GF(2))
        for i in range(m):
            s = 0
            for j in range(n):
                s ^= (matrix[i][j] & sol[j])
            if s != target[i]:
                return False
        # verified flag must be True
        if not result["verified"]:
            return False
        return True
    else:
        # Verify unsolvable: brute-force check no solution exists (small n)
        for mask in range(1 << n):
            sol = [(mask >> j) & 1 for j in range(n)]
            ok = True
            for i in range(m):
                s = 0
                for j in range(n):
                    s ^= (matrix[i][j] & sol[j])
                if s != target[i]:
                    ok = False
                    break
            if ok:
                return False  # Found solution but solver said unsolvable
        return True


BUG_DESC = "Uses bitwise OR instead of XOR when eliminating rows during Gaussian elimination, which is incorrect over GF(2) because 1+1 should be 0 (XOR) not 1 (OR)."


def _gen_matrix():
    # 4 equations, 4 unknowns over GF(2)
    return [
        [1, 1, 0, 0],
        [0, 1, 1, 0],
        [0, 0, 1, 1],
        [1, 0, 0, 1],
    ]


def _gen_target():
    # Solution should be [1, 0, 1, 0]: check
    # eq1: 1^0 = 1, eq2: 0^1 = 1, eq3: 1^0 = 1, eq4: 1^0 = 1
    return [1, 1, 1, 1]


INPUT_OVERRIDES = {
    "MATRIX": _gen_matrix,
    "TARGET": _gen_target,
}
