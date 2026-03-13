"""Python semantics: decorator patterns — NULL_PTR, TYPE_ERROR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Decorator that drops return value or returns None"

EXAMPLES = [
    (
        "decorator_drops_return",
        # buggy: decorator forgets to return wrapper result
        '''\
def log_calls(func):
    def wrapper(*args, **kwargs):
        func(*args, **kwargs)
    return wrapper

@log_calls
def compute(x):
    return x * 2

def use():
    result = compute(5)
    return result.bit_length()
''',
        # safe: decorator returns result
        '''\
def log_calls(func):
    def wrapper(*args, **kwargs):
        return func(*args, **kwargs)
    return wrapper

@log_calls
def compute(x):
    return x * 2

def use():
    result = compute(5)
    return result.bit_length()
''',
        "wrapper returns None implicitly; .bit_length() on None",
    ),
    (
        "decorator_wrong_type",
        # buggy: decorator wraps in string
        '''\
def stringify(func):
    def wrapper(*args, **kwargs):
        result = func(*args, **kwargs)
        return str(result)
    return wrapper

@stringify
def add(a, b):
    return a + b

def use():
    total = add(3, 4)
    return total / 2
''',
        # safe: return int
        '''\
def stringify(func):
    def wrapper(*args, **kwargs):
        result = func(*args, **kwargs)
        return result
    return wrapper

@stringify
def add(a, b):
    return a + b

def use():
    total = add(3, 4)
    return total / 2
''',
        "str / 2 is type error but declared NULL_PTR for the None path",
    ),
    (
        "cached_none",
        # buggy: cache returns None first time for missing key
        '''\
_cache = {}

def cached_lookup(key, fetch_fn):
    if key not in _cache:
        _cache[key] = fetch_fn(key)
    result = _cache[key]
    return result.decode()
''',
        # safe: guard None
        '''\
_cache = {}

def cached_lookup(key, fetch_fn):
    if key not in _cache:
        _cache[key] = fetch_fn(key)
    result = _cache[key]
    if result is not None:
        return result.decode()
    return ""
''',
        "fetch_fn may return None; .decode() on None",
    ),
]
