"""Guard stress: assert-based refinements.

Sheaf-theoretically, `assert P` introduces a restriction morphism that
narrows the ambient section to the sub-presheaf where P holds.  The
continuation lives on the open set {P = true} of the covering sieve.
Code after the assert should carry the refined section.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Assert-based null guards"

EXAMPLES = [
    (
        "assert_not_none_attr",
        # buggy: no guard before attribute access
        '''\
def process(user):
    result = user
    return result.name
''',
        # safe: assert refines the section to non-None fiber
        '''\
def process(user):
    result = user
    assert result is not None
    return result.name
''',
        "Assert is not None before attribute access",
    ),
    (
        "assert_not_none_method",
        # buggy: call method on possibly-None
        '''\
def invoke(handler):
    cb = handler
    return cb.execute()
''',
        # safe: assert introduces non-None section
        '''\
def invoke(handler):
    cb = handler
    assert cb is not None, "handler must not be None"
    return cb.execute()
''',
        "Assert with message before method call",
    ),
    (
        "assert_not_none_chained",
        # buggy: chained attribute on possibly-None
        '''\
def get_city(record):
    addr = record
    return addr.address.city
''',
        # safe: double assert for chained access
        '''\
def get_city(record):
    addr = record
    assert addr is not None
    assert addr.address is not None
    return addr.address.city
''',
        "Chained asserts refine nested sections",
    ),
]
