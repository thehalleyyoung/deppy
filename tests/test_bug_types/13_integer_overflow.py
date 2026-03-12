"""INTEGER_OVERFLOW: struct.pack with bounded integer format — value must
lie within the representable range of the format specifier.
"""

BUG_TYPE = "INTEGER_OVERFLOW"
BUG_DESC = "Integer overflow in struct packing"

EXAMPLES = [
    (
        "pack_int32",
        # buggy: no bounds check before struct.pack('i', v)
        '''\
import struct
def serialize(v):
    return struct.pack('i', v)
''',
        # safe: clamp to 32-bit range before packing
        '''\
import struct
def serialize(v):
    v = max(-2147483648, min(2147483647, v))
    return struct.pack('i', v)
''',
        "struct.pack('i'): value must be in [-2^31, 2^31-1]",
    ),
    (
        "pack_int16",
        # buggy: no bounds check before struct.pack('h', v)
        '''\
import struct
def to_short(v):
    return struct.pack('h', v)
''',
        # safe: clamp to 16-bit range
        '''\
import struct
def to_short(v):
    v = max(-32768, min(32767, v))
    return struct.pack('h', v)
''',
        "struct.pack('h'): value must be in [-2^15, 2^15-1]",
    ),
    (
        "pack_byte",
        # buggy: no bounds check before struct.pack('b', v)
        '''\
import struct
def to_byte(v):
    return struct.pack('b', v)
''',
        # safe: clamp to 8-bit signed range
        '''\
import struct
def to_byte(v):
    v = max(-128, min(127, v))
    return struct.pack('b', v)
''',
        "struct.pack('b'): value must be in [-128, 127]",
    ),
]
