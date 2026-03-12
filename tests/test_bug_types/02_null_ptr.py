"""NULL_PTR: None dereference — refinement gap.

Required section: {obj : T | obj is not None}
"""

BUG_TYPE = "NULL_PTR"

BUGGY_A = r"""
def get_username(user_map, user_id):
    user = user_map.get(user_id)
    return user.name
"""

SAFE_A = r"""
def get_username(user_map, user_id):
    user = user_map.get(user_id)
    if user is None:
        return "unknown"
    return user.name
"""

BUGGY_B = r"""
def first_match(items, predicate):
    result = None
    for item in items:
        if predicate(item):
            result = item
            break
    return result.value
"""

SAFE_B = r"""
def first_match(items, predicate):
    result = None
    for item in items:
        if predicate(item):
            result = item
            break
    if result is None:
        return None
    return result.value
"""

BUGGY_C = r"""
def get_parent_name(node):
    parent = node.parent
    return parent.name
"""

SAFE_C = r"""
def get_parent_name(node):
    parent = node.parent
    if parent is None:
        return ""
    return parent.name
"""

EXAMPLES = [
    ("dict_get", BUGGY_A, SAFE_A, "dict.get() may return None"),
    ("search_miss", BUGGY_B, SAFE_B, "result stays None when no match found"),
    ("parent_none", BUGGY_C, SAFE_C, "node.parent may be None for root nodes"),
]

BUG_DESC = "Attribute access on a value that may be None."
