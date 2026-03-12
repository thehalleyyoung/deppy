"""OVERFLOW: struct.pack with 64-bit format — value must lie within
the representable range of the format specifier.
"""

BUG_TYPE = "OVERFLOW"
BUG_DESC = "Overflow in struct packing (64-bit)"

EXAMPLES = [
    (
        "pack_int64",
        # buggy: no bounds check before struct.pack('q', v)
        '''\
import struct
def serialize_big(v):
    return struct.pack('q', v)
''',
        # safe: clamp to 64-bit range
        '''\
import struct
def serialize_big(v):
    v = max(-9223372036854775808, min(9223372036854775807, v))
    return struct.pack('q', v)
''',
        "struct.pack('q'): value must be in [-2^63, 2^63-1]",
    ),
    (
        "pack_multi_format",
        # buggy: pack two 64-bit values unchecked
        '''\
import struct
def pack_pair(a, b):
    return struct.pack('qq', a, b)
''',
        # safe: validated before packing
        '''\
import struct
def pack_pair(a, b):
    lo, hi = -9223372036854775808, 9223372036854775807
    a = max(lo, min(hi, a))
    b = max(lo, min(hi, b))
    return struct.pack('qq', a, b)
''',
        "Multiple 64-bit values need bounds checks",
    ),
    (
        "pack_with_header",
        # buggy: long-long value unchecked
        '''\
import struct
def pack_message(msg_type, payload_size):
    return struct.pack('iq', msg_type, payload_size)
''',
        # safe: bounds checked
        '''\
import struct
def pack_message(msg_type, payload_size):
    msg_type = max(-2147483648, min(2147483647, msg_type))
    payload_size = max(-9223372036854775808, min(9223372036854775807, payload_size))
    return struct.pack('iq', msg_type, payload_size)
''',
        "Mixed format with 64-bit value",
    ),
]
