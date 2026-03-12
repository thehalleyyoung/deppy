"""PANIC: Unhandled runtime error — exception escapement.

Required section: {op : T | ¬raises(RuntimeError/ValueError)}
"""

BUG_TYPE = "VALUE_ERROR"

BUGGY_A = r"""
def parse_int(s):
    return int(s)
"""

SAFE_A = r"""
def parse_int(s):
    try:
        return int(s)
    except ValueError:
        return None
"""

BUGGY_B = r"""
def remove_item(lst, item):
    lst.remove(item)
    return lst
"""

SAFE_B = r"""
def remove_item(lst, item):
    if item in lst:
        lst.remove(item)
    return lst
"""

BUGGY_C = r"""
def unpack_pair(data):
    a, b = data
    return a + b
"""

SAFE_C = r"""
def unpack_pair(data):
    if len(data) != 2:
        raise ValueError("expected exactly 2 elements")
    a, b = data
    return a + b
"""

EXAMPLES = [
    ("int_parse", BUGGY_A, SAFE_A, "int() on non-numeric string raises ValueError"),
    ("list_remove", BUGGY_B, SAFE_B, "list.remove() raises ValueError if item not found"),
    ("unpack_wrong_len", BUGGY_C, SAFE_C, "unpacking wrong-length sequence raises ValueError"),
]

BUG_DESC = "Operation that raises ValueError/RuntimeError without handling."
