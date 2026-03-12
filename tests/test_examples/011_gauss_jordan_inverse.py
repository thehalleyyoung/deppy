"""Gauss-Jordan elimination for matrix inverse.

Bug: During back-substitution (eliminating entries above the pivot),
uses the un-scaled original row instead of the already-scaled pivot row.
This corrupts the elimination and produces a wrong inverse.
"""

CORRECT = r"""
def gauss_jordan_inverse(matrix):
    n = len(matrix)
    # Augment with identity
    aug = []
    for i in range(n):
        row = [float(matrix[i][j]) for j in range(n)]
        for j in range(n):
            row.append(1.0 if i == j else 0.0)
        aug.append(row)

    for col in range(n):
        # Partial pivoting: find row with largest absolute value in column
        max_row = col
        max_val = abs(aug[col][col])
        for row in range(col + 1, n):
            if abs(aug[row][col]) > max_val:
                max_val = abs(aug[row][col])
                max_row = row
        if max_val < 1e-12:
            return None  # Singular matrix

        # Swap rows
        aug[col], aug[max_row] = aug[max_row], aug[col]

        # Scale pivot row so diagonal entry becomes 1
        pivot = aug[col][col]
        for j in range(2 * n):
            aug[col][j] /= pivot

        # Eliminate all other entries in this column
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            for j in range(2 * n):
                aug[row][j] -= factor * aug[col][j]

    # Extract right half as inverse
    inverse = []
    for i in range(n):
        inverse.append([aug[i][j] for j in range(n, 2 * n)])
    return inverse

matrix = MATRIX
result = gauss_jordan_inverse(matrix)
"""

BUGGY = r"""
def gauss_jordan_inverse(matrix):
    n = len(matrix)
    # Augment with identity
    aug = []
    for i in range(n):
        row = [float(matrix[i][j]) for j in range(n)]
        for j in range(n):
            row.append(1.0 if i == j else 0.0)
        aug.append(row)

    for col in range(n):
        # Partial pivoting: find row with largest absolute value in column
        max_row = col
        max_val = abs(aug[col][col])
        for row in range(col + 1, n):
            if abs(aug[row][col]) > max_val:
                max_val = abs(aug[row][col])
                max_row = row
        if max_val < 1e-12:
            return None  # Singular matrix

        # Swap rows
        aug[col], aug[max_row] = aug[max_row], aug[col]

        # Save the original row BEFORE scaling (this is the bug setup)
        original_pivot_row = aug[col][:]

        # Scale pivot row so diagonal entry becomes 1
        pivot = aug[col][col]
        for j in range(2 * n):
            aug[col][j] /= pivot

        # Eliminate entries BELOW the pivot (forward elimination) - correct
        for row in range(col + 1, n):
            factor = aug[row][col]
            for j in range(2 * n):
                aug[row][j] -= factor * aug[col][j]

        # BUG: Eliminate entries ABOVE the pivot (back-substitution)
        # Uses original_pivot_row (un-scaled) instead of aug[col] (scaled)
        for row in range(col):
            factor = aug[row][col]
            for j in range(2 * n):
                aug[row][j] -= factor * original_pivot_row[j]

    # Extract right half as inverse
    inverse = []
    for i in range(n):
        inverse.append([aug[i][j] for j in range(n, 2 * n)])
    return inverse

matrix = MATRIX
result = gauss_jordan_inverse(matrix)
"""


def SPEC(MATRIX, result):
    """Verify A @ result ≈ I (within tolerance), or if None, verify A is singular."""
    n = len(MATRIX)

    if result is None:
        # Check that matrix is actually singular (det ≈ 0)
        # Compute determinant via row reduction
        aug = [[float(MATRIX[i][j]) for j in range(n)] for i in range(n)]
        det = 1.0
        for col in range(n):
            max_row = col
            for row in range(col + 1, n):
                if abs(aug[row][col]) > abs(aug[max_row][col]):
                    max_row = row
            if abs(aug[max_row][col]) < 1e-12:
                return True  # Singular, returning None is correct
            if max_row != col:
                aug[col], aug[max_row] = aug[max_row], aug[col]
                det *= -1
            det *= aug[col][col]
            for row in range(col + 1, n):
                factor = aug[row][col] / aug[col][col]
                for j in range(col + 1, n):
                    aug[row][j] -= factor * aug[col][j]
        return abs(det) < 0.1

    if not isinstance(result, list) or len(result) != n:
        return False

    # Verify A @ result ≈ I
    for i in range(n):
        if not isinstance(result[i], list) or len(result[i]) != n:
            return False
        for j in range(n):
            dot = 0.0
            for k in range(n):
                dot += float(MATRIX[i][k]) * float(result[k][j])
            expected = 1.0 if i == j else 0.0
            if abs(dot - expected) > 1e-6:
                return False
    return True


BUG_DESC = (
    "During back-substitution (eliminating entries above the pivot), "
    "the bug uses the un-scaled original pivot row instead of the already-scaled "
    "pivot row. This means the elimination factors are computed against the scaled "
    "row but subtraction uses unscaled values, corrupting the augmented matrix "
    "and producing an incorrect inverse."
)


def _generate_matrix():
    import random
    n = random.randint(3, 4)
    while True:
        matrix = [[random.randint(-5, 5) for _ in range(n)] for _ in range(n)]
        # Check determinant is large enough (non-singular)
        aug = [[float(matrix[i][j]) for j in range(n)] for i in range(n)]
        det = 1.0
        singular = False
        for col in range(n):
            max_row = col
            for row in range(col + 1, n):
                if abs(aug[row][col]) > abs(aug[max_row][col]):
                    max_row = row
            if abs(aug[max_row][col]) < 1e-12:
                singular = True
                break
            if max_row != col:
                aug[col], aug[max_row] = aug[max_row], aug[col]
                det *= -1
            det *= aug[col][col]
            for row in range(col + 1, n):
                factor = aug[row][col] / aug[col][col]
                for j in range(col + 1, n):
                    aug[row][j] -= factor * aug[col][j]
        if not singular and abs(det) > 0.1:
            return matrix


INPUT_OVERRIDES = {
    "MATRIX": _generate_matrix,
}
