"""Guard stress: truthiness as emptiness/nullity section.

In Python, `if x:` when x is a collection implies len(x) > 0.
When x is an optional, it implies x is not None (and truthy).
Sheaf-theoretically, truthiness refines the covering sieve to the
sub-presheaf of non-empty / non-None values — the local section
carries a cardinality lower bound or a non-None guarantee.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Truthiness guards for collection access"

EXAMPLES = [
    (
        "truthiness_list_index",
        # buggy: index without length check
        '''\
def first_item(data):
    items = data
    return items[0]
''',
        # safe: truthiness implies non-empty
        '''\
def first_item(data):
    items = data
    if items:
        return items[0]
    return None
''',
        "Truthiness check before indexing",
    ),
    (
        "truthiness_last",
        # buggy: index -1 on possibly-empty
        '''\
def last_item(lst):
    items = lst
    return items[-1]
''',
        # safe: truthiness guard
        '''\
def last_item(lst):
    items = lst
    if items:
        return items[-1]
    return None
''',
        "Truthiness before negative index",
    ),
    (
        "truthiness_not_empty",
        # buggy: access without guard
        '''\
def peek(queue):
    q = queue
    return q[0]
''',
        # safe: `not` truthiness as early return
        '''\
def peek(queue):
    q = queue
    if not q:
        return None
    return q[0]
''',
        "Not-truthiness early return before access",
    ),
]
