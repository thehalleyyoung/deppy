"""Edge-case INTEGER_OVERFLOW: struct.pack with various formats."""

BUG_TYPE = "INTEGER_OVERFLOW"
BUG_DESC = "Integer overflow in struct pack edge cases"

EXAMPLES = [
    (
        "pack_byte",
        # buggy: packing arbitrary value as byte
        '''\
import struct
def encode_byte(value):
    return struct.pack("b", value)
''',
        # safe: clamp value to byte range
        '''\
import struct
def encode_byte(value):
    value = max(-128, min(value, 127))
    return struct.pack("b", value)
''',
        "struct.pack byte with possibly out-of-range value",
    ),
    (
        "pack_short",
        # buggy: packing arbitrary value as short
        '''\
import struct
def encode_short(value):
    return struct.pack("h", value)
''',
        # safe: clamp value
        '''\
import struct
def encode_short(value):
    value = max(-32768, min(value, 32767))
    return struct.pack("h", value)
''',
        "struct.pack short with possibly out-of-range value",
    ),
    (
        "pack_int32",
        # buggy: packing arbitrary value as 32-bit int
        '''\
import struct
def encode_int(value):
    return struct.pack("i", value)
''',
        # safe: clamp value
        '''\
import struct
def encode_int(value):
    value = max(-2147483648, min(value, 2147483647))
    return struct.pack("i", value)
''',
        "struct.pack int with possibly out-of-range value",
    ),
]
