"""Python semantics: MRO / super() — TYPE_ERROR, NULL_PTR."""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "MRO-related type errors from cooperative multiple inheritance"

EXAMPLES = [
    (
        "super_wrong_signature",
        # buggy: child passes wrong type to super().__init__
        '''\
class Base:
    def __init__(self, value):
        self.value = value

class Mixin:
    def __init__(self, **kwargs):
        super().__init__(**kwargs)

class Child(Mixin, Base):
    def __init__(self, x):
        super().__init__(value=x)

def use():
    c = Child(42)
    return c.value + "string"
''',
        # safe: same type operations
        '''\
class Base:
    def __init__(self, value):
        self.value = value

class Mixin:
    def __init__(self, **kwargs):
        super().__init__(**kwargs)

class Child(Mixin, Base):
    def __init__(self, x):
        super().__init__(value=x)

def use():
    c = Child(42)
    return c.value + 1
''',
        "int + str is a type error",
    ),
    (
        "diamond_method_type",
        # buggy: diamond inheritance, method returns incompatible type
        '''\
class A:
    def compute(self):
        return 10

class B(A):
    def compute(self):
        return super().compute()

class C(A):
    def compute(self):
        return str(super().compute())

class D(B, C):
    pass

def run():
    d = D()
    result = d.compute()
    return result / 2
''',
        # safe: ensure int
        '''\
class A:
    def compute(self):
        return 10

class B(A):
    def compute(self):
        return super().compute()

class C(A):
    def compute(self):
        return str(super().compute())

class D(B, C):
    pass

def run():
    d = D()
    result = d.compute()
    return int(result) / 2
''',
        "MRO resolves D.compute → B.compute → C.compute → str; str / 2 is TYPE_ERROR",
    ),
]
