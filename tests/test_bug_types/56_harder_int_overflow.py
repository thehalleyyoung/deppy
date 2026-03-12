"""Harder INTEGER_OVERFLOW: struct.pack with computed values."""

BUG_TYPE = "INTEGER_OVERFLOW"
BUG_DESC = "Integer overflow in complex struct packing patterns"

EXAMPLES = [
    (
        "pack_computed_offset",
        # buggy: computed offset packed as signed short
        '''\
import struct
def write_offset(base, delta):
    offset = base + delta
    return struct.pack(">h", offset)
''',
        # safe: clamp to signed short range
        '''\
import struct
def write_offset(base, delta):
    offset = base + delta
    clamped = max(-32768, min(offset, 32767))
    return struct.pack(">h", clamped)
''',
        "Computed offset packed as signed short may overflow",
    ),
    (
        "pack_product",
        # buggy: product of two values packed as signed int
        '''\
import struct
def encode_area(width, height):
    area = width * height
    return struct.pack("<i", area)
''',
        # safe: clamp product
        '''\
import struct
def encode_area(width, height):
    area = width * height
    area = max(-2147483648, min(area, 2147483647))
    return struct.pack("<i", area)
''',
        "Product of two values packed as signed int may overflow",
    ),
    (
        "pack_timestamp_delta",
        # buggy: time delta packed as signed byte
        '''\
import struct
def pack_delta(t1, t2):
    delta = t2 - t1
    return struct.pack("b", delta)
''',
        # safe: clamp to byte range
        '''\
import struct
def pack_delta(t1, t2):
    delta = t2 - t1
    delta = max(-128, min(delta, 127))
    return struct.pack("b", delta)
''',
        "Time delta packed as signed byte may overflow",
    ),
]
