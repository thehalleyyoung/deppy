"""Python semantics: walrus operator in complex contexts — DIV_ZERO, NULL_PTR, INDEX_OOB."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Walrus operator in while loops and conditions with division"

EXAMPLES = [
    (
        "walrus_while_div",
        # buggy: walrus in while condition, divide by decremented value
        '''\
def sum_until_zero(values):
    total = 0
    idx = 0
    while (val := values[idx]) != 0:
        total += 100 / val
        idx += 1
    remaining = total / val
    return remaining
''',
        # safe: guard the post-loop division
        '''\
def sum_until_zero(values):
    total = 0
    idx = 0
    while (val := values[idx]) != 0:
        total += 100 / val
        idx += 1
    if val != 0:
        remaining = total / val
    else:
        remaining = total
    return remaining
''',
        "Loop exits when val == 0; total / val is div-by-zero",
    ),
    (
        "walrus_filter_div",
        # buggy: walrus in list comp, then divide by filtered value
        '''\
def process_scores(scores):
    passed = [s for s in scores if (n := s - 50) > 0]
    return 100 / n
''',
        # safe: check n
        '''\
def process_scores(scores):
    passed = [s for s in scores if (n := s - 50) > 0]
    if n > 0:
        return 100 / n
    return 0
''',
        "n retains last value from comp; if last element has s <= 50, n <= 0",
    ),
    (
        "walrus_match_div",
        # buggy: walrus assigns 0 on no-match path
        '''\
def safe_ratio(a, b):
    if (denom := b) > 0:
        return a / denom
    return a / denom
''',
        # safe: don't divide on else branch
        '''\
def safe_ratio(a, b):
    if (denom := b) > 0:
        return a / denom
    return 0
''',
        "else branch: denom <= 0; a / denom may be div-by-zero",
    ),
]
