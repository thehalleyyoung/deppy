"""Hard UNBOUND_VAR examples — try blocks, loops that might not execute, deeper paths."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Unbound variable in harder patterns"

EXAMPLES = [
    (
        "try_only_assign",
        # buggy: variable assigned only in try, used after — exception skips assignment
        '''\
def load_config(path):
    try:
        data = open(path).read()
    except IOError:
        pass
    return data
''',
        # safe: provide default
        '''\
def load_config(path):
    data = ""
    try:
        data = open(path).read()
    except IOError:
        pass
    return data
''',
        "Variable only assigned in try block, exception path leaves it unbound",
    ),
    (
        "empty_loop_var",
        # buggy: variable only assigned inside a loop that may never execute
        '''\
def last_positive(numbers):
    for n in numbers:
        if n > 0:
            last = n
    return last
''',
        # safe: initialize before loop
        '''\
def last_positive(numbers):
    last = None
    for n in numbers:
        if n > 0:
            last = n
    return last
''',
        "Variable assigned inside loop body that may never execute",
    ),
    (
        "switch_gap",
        # buggy: elif chain misses a case, variable not assigned on that path
        '''\
def classify(score):
    if score >= 90:
        grade = "A"
    elif score >= 80:
        grade = "B"
    elif score >= 70:
        grade = "C"
    return grade
''',
        # safe: add else default
        '''\
def classify(score):
    if score >= 90:
        grade = "A"
    elif score >= 80:
        grade = "B"
    elif score >= 70:
        grade = "C"
    else:
        grade = "F"
    return grade
''',
        "elif chain without else leaves variable unbound for low scores",
    ),
]
