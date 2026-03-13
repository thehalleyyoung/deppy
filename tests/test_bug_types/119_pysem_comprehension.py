"""Python semantics: comprehension scoping — DIV_ZERO, INDEX_OOB, KEY_ERROR."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Division by zero in comprehension expressions"

EXAMPLES = [
    (
        "listcomp_div_zero",
        # buggy: division in list comprehension with zero
        '''\
def normalize(values):
    total = sum(values)
    return [v / total for v in values]
''',
        # safe: guard zero
        '''\
def normalize(values):
    total = sum(values)
    if total == 0:
        return [0.0 for _ in values]
    return [v / total for v in values]
''',
        "total may be 0; division in listcomp",
    ),
    (
        "dictcomp_div_zero",
        # buggy: dict comprehension with division
        '''\
def ratio_map(keys, counts, base):
    return {k: c / base for k, c in zip(keys, counts)}
''',
        # safe: guard base
        '''\
def ratio_map(keys, counts, base):
    if base == 0:
        return {k: 0 for k, c in zip(keys, counts)}
    return {k: c / base for k, c in zip(keys, counts)}
''',
        "base may be 0; division in dictcomp",
    ),
    (
        "nested_comp_div",
        # buggy: nested comprehension with division
        '''\
def matrix_normalize(matrix):
    row_sums = [sum(row) for row in matrix]
    return [[x / row_sums[i] for x in row]
            for i, row in enumerate(matrix)]
''',
        # safe: guard each row sum
        '''\
def matrix_normalize(matrix):
    row_sums = [sum(row) for row in matrix]
    return [[x / row_sums[i] if row_sums[i] != 0 else 0.0
             for x in row]
            for i, row in enumerate(matrix)]
''',
        "row_sums[i] may be 0 in nested comprehension",
    ),
]
