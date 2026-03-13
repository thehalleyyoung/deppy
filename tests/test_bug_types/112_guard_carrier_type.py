"""Guard stress: TYPE_ERROR with diverse carrier patterns.

The carrier presheaf assigns type sections to expressions via
constructor morphisms.  Patterns like string formatting, list
concatenation, and numeric coercion should carry compatible
carrier sections that resolve the TYPE_ERROR gluing condition.
"""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Carrier presheaf resolution for TYPE_ERROR"

EXAMPLES = [
    (
        "str_format_concat",
        # buggy: concatenate string and int
        '''\
def label(name, count):
    s = name
    n = count
    return s + n
''',
        # safe: str() constructor creates string carrier section
        '''\
def label(name, count):
    s = name
    n = count
    return s + str(n)
''',
        "str() constructor produces string carrier",
    ),
    (
        "int_arithmetic",
        # buggy: add string and int
        '''\
def offset_label(text, delta):
    t = text
    d = delta
    return t + d
''',
        # safe: int() constructor produces numeric carrier
        '''\
def offset_label(text, delta):
    t = text
    d = delta
    return int(t) + d
''',
        "int() constructor produces numeric carrier",
    ),
    (
        "float_multiply",
        # buggy: multiply incompatible types
        '''\
def scale(value, factor):
    v = value
    f = factor
    return v * f
''',
        # safe: float() coercion ensures numeric carrier
        '''\
def scale(value, factor):
    v = value
    f = factor
    return float(v) * float(f)
''',
        "float() coercion on both operands",
    ),
]
