"""Guard stress: getattr/dict.get safe-access patterns.

`d.get(key, default)` is a morphism that NEVER raises KeyError —
it maps to the union of the key-present fiber (returning d[key])
and the key-absent fiber (returning default).
`getattr(obj, name, default)` similarly provides a total section
over the attribute existence presheaf.
"""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Safe accessor patterns (.get, getattr, setdefault)"

EXAMPLES = [
    (
        "dict_get_default",
        # buggy: direct subscript on dict
        '''\
def lookup(config, key):
    d = config
    return d[key]
''',
        # safe: .get() returns default on missing key
        '''\
def lookup(config, key):
    d = config
    return d.get(key, "missing")
''',
        "dict.get() is a total morphism",
    ),
    (
        "dict_setdefault",
        # buggy: access possibly-missing key
        '''\
def get_list(registry, name):
    d = registry
    return d[name]
''',
        # safe: setdefault ensures key exists then access
        '''\
def get_list(registry, name):
    d = registry
    d.setdefault(name, [])
    return d[name]
''',
        "setdefault creates total section before access",
    ),
    (
        "dict_pop_default",
        # buggy: pop without default can raise KeyError
        '''\
def remove_key(data, key):
    d = data
    return d[key]
''',
        # safe: pop with default is total
        '''\
def remove_key(data, key):
    d = data
    return d.pop(key, None)
''',
        "dict.pop with default is a total morphism",
    ),
]
