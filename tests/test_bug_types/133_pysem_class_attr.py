"""Python semantics: class attribute vs instance attribute — NULL_PTR, KEY_ERROR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Class vs instance attribute confusion leading to None dereference"

EXAMPLES = [
    (
        "class_attr_none",
        # buggy: class attribute is None, instance never overrides
        '''\
class Service:
    client = None

    def __init__(self, name):
        self.name = name

def call_service(svc):
    return svc.client.send("hello")
''',
        # safe: guard None
        '''\
class Service:
    client = None

    def __init__(self, name):
        self.name = name

def call_service(svc):
    if svc.client is not None:
        return svc.client.send("hello")
    return None
''',
        "svc.client is None (class default); .send() on None",
    ),
    (
        "init_conditional_attr",
        # buggy: attribute only set in one branch of __init__
        '''\
class Parser:
    def __init__(self, strict=False):
        if strict:
            self.validator = build_validator()

    def parse(self, text):
        return self.validator.validate(text)
''',
        # safe: default attribute
        '''\
class Parser:
    def __init__(self, strict=False):
        self.validator = None
        if strict:
            self.validator = build_validator()

    def parse(self, text):
        if self.validator is not None:
            return self.validator.validate(text)
        return text
''',
        "self.validator may not exist if strict=False; AttributeError",
    ),
    (
        "slots_missing_attr",
        # buggy: __slots__ prevents dynamic attribute, code assumes it exists
        '''\
class Point:
    __slots__ = ('x', 'y')
    def __init__(self, x, y):
        self.x = x
        self.y = y

def use_point(p):
    result = p.z
    return result.real
''',
        # safe: use existing attrs
        '''\
class Point:
    __slots__ = ('x', 'y')
    def __init__(self, x, y):
        self.x = x
        self.y = y

def use_point(p):
    result = p.x
    return result
''',
        "p.z does not exist on slotted class; AttributeError → NULL_PTR",
    ),
]
