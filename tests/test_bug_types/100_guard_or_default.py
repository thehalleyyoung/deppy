"""Guard stress: or-default and fallback patterns.

`x = val or default` creates a section where x is guaranteed non-None
and truthy (either val was truthy, or default is used).
Sheaf-theoretically, the BoolOp(Or) morphism maps the ambient presheaf
to a sub-presheaf where the result carries a total non-None section.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Or-default patterns as null guards"

EXAMPLES = [
    (
        "or_default_attr",
        # buggy: attribute access on unchecked variable
        '''\
def greet(config):
    name = config
    return name.upper()
''',
        # safe: or-default ensures non-None section
        '''\
def greet(config):
    name = config or "world"
    return name.upper()
''',
        "Or-default before attribute access",
    ),
    (
        "or_default_method",
        # buggy: method on possibly-None
        '''\
def process(handler):
    h = handler
    return h.run()
''',
        # safe: or-default with fallback object
        '''\
class _DefaultHandler:
    def run(self):
        return None

def process(handler):
    h = handler or _DefaultHandler()
    return h.run()
''',
        "Or-default with fallback object",
    ),
    (
        "or_default_index",
        # buggy: chained attribute on possibly-None
        '''\
def first(items):
    data = items
    return data.pop()
''',
        # safe: or-default provides non-None fallback
        '''\
def first(items):
    data = items or []
    return data.pop() if data else None
''',
        "Or-default provides non-None section",
    ),
]
