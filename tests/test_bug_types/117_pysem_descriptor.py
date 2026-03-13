"""Python semantics: descriptor protocol — NULL_PTR, TYPE_ERROR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Descriptor __get__ may return None or raise"

EXAMPLES = [
    (
        "descriptor_returns_none",
        # buggy: descriptor returns None, caller dereferences
        '''\
class CachedProp:
    def __init__(self, func):
        self.func = func
    def __get__(self, obj, objtype=None):
        if obj is None:
            return None
        return self.func(obj)

class Data:
    @CachedProp
    def value(self):
        return {"key": 42}

def use_descriptor():
    d = Data()
    result = Data.value
    return result.upper()
''',
        # safe: use instance, check None
        '''\
class CachedProp:
    def __init__(self, func):
        self.func = func
    def __get__(self, obj, objtype=None):
        if obj is None:
            return self
        return self.func(obj)

class Data:
    @CachedProp
    def value(self):
        return {"key": 42}

def use_descriptor():
    d = Data()
    result = d.value
    if result is not None:
        return result.get("key")
    return 0
''',
        "Data.value on class returns None; .upper() on None",
    ),
    (
        "property_none_deref",
        # buggy: property returns None, caller chains method
        '''\
class Config:
    def __init__(self):
        self._data = None

    @property
    def data(self):
        return self._data

def process(cfg):
    result = cfg.data
    return result.strip()
''',
        # safe: guard None
        '''\
class Config:
    def __init__(self):
        self._data = None

    @property
    def data(self):
        return self._data

def process(cfg):
    result = cfg.data
    if result is not None:
        return result.strip()
    return ""
''',
        "cfg.data is None; .strip() on None is NULL_PTR",
    ),
]
