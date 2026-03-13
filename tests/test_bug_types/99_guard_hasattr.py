"""Guard stress: hasattr-based attribute-existence sections.

`hasattr(obj, 'x')` tests whether the attribute fiber at 'x' carries
a total section over obj's stalk.  Inside the body of
`if hasattr(obj, 'x'):`, the access `obj.x` lives on the open set
where the section is guaranteed total — no NULL_PTR obstruction.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "hasattr guards for attribute access"

EXAMPLES = [
    (
        "hasattr_simple",
        # buggy: attribute access without checking existence
        '''\
def get_label(widget):
    obj = widget
    return obj.label
''',
        # safe: hasattr guards the attribute fiber
        '''\
def get_label(widget):
    obj = widget
    if hasattr(obj, 'label'):
        return obj.label
    return "default"
''',
        "hasattr before attribute access",
    ),
    (
        "hasattr_method",
        # buggy: method call without check
        '''\
def try_close(resource):
    obj = resource
    obj.close()
''',
        # safe: hasattr guards the method fiber
        '''\
def try_close(resource):
    obj = resource
    if hasattr(obj, 'close'):
        obj.close()
''',
        "hasattr before method call",
    ),
    (
        "hasattr_nested",
        # buggy: nested attribute without guard
        '''\
def get_address(person):
    obj = person
    return obj.address.street
''',
        # safe: hasattr with nested check
        '''\
def get_address(person):
    obj = person
    if hasattr(obj, 'address') and obj.address is not None:
        return obj.address.street
    return None
''',
        "hasattr with compound None check",
    ),
]
