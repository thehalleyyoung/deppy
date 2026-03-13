"""Python semantics: functools and higher-order functions — NULL_PTR, TYPE_ERROR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Higher-order function patterns that produce None"

EXAMPLES = [
    (
        "map_filter_none",
        # buggy: filter returns empty, next gets StopIteration-like None
        '''\
def first_positive(numbers):
    gen = filter(lambda x: x > 0, numbers)
    result = next(gen, None)
    return result.bit_length()
''',
        # safe: guard None
        '''\
def first_positive(numbers):
    gen = filter(lambda x: x > 0, numbers)
    result = next(gen, None)
    if result is not None:
        return result.bit_length()
    return 0
''',
        "If no positive number, result is None; .bit_length() on None",
    ),
    (
        "reduce_empty_no_init",
        # buggy: reduce on potentially empty iterable without initial
        '''\
from functools import reduce

def product(numbers):
    result = reduce(lambda a, b: a * b, numbers)
    return result.bit_length()
''',
        # safe: provide initial value
        '''\
from functools import reduce

def product(numbers):
    if not numbers:
        return 0
    result = reduce(lambda a, b: a * b, numbers)
    return result.bit_length()
''',
        "reduce on empty raises TypeError; but with None chain it's NULL_PTR context",
    ),
    (
        "sorted_key_none",
        # buggy: sorted with key that returns None for some items
        '''\
def sort_by_name(items):
    ordered = sorted(items, key=lambda x: x.get("name"))
    first = ordered[0] if ordered else None
    return first["name"].upper()
''',
        # safe: guard None
        '''\
def sort_by_name(items):
    ordered = sorted(items, key=lambda x: x.get("name", ""))
    first = ordered[0] if ordered else None
    if first is not None and "name" in first:
        return first["name"].upper()
    return ""
''',
        "first may be None; first['name'] on None",
    ),
]
