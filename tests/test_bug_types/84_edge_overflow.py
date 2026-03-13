"""Edge-case OVERFLOW: struct.pack with 64-bit format."""

BUG_TYPE = "OVERFLOW"
BUG_DESC = "Overflow in 64-bit struct pack edge cases"

EXAMPLES = [
    (
        "pack_int64",
        # buggy: packing arbitrary value as 64-bit
        '''\
import struct
def encode_long(value):
    return struct.pack("q", value)
''',
        # safe: clamp to 64-bit range
        '''\
import struct
def encode_long(value):
    value = max(-9223372036854775808, min(value, 9223372036854775807))
    return struct.pack("q", value)
''',
        "struct.pack 64-bit int with possibly out-of-range value",
    ),
    (
        "pack_timestamp64",
        # buggy: timestamp as 64-bit int
        '''\
import struct
def pack_timestamp(ts):
    return struct.pack("q", ts)
''',
        # safe: try/except
        '''\
import struct
def pack_timestamp(ts):
    try:
        return struct.pack("q", ts)
    except OverflowError:
        return b"\\x00" * 8
''',
        "64-bit timestamp pack with possible overflow",
    ),
    (
        "pack_file_size",
        # buggy: file size as 64-bit int
        '''\
import struct
def encode_size(nbytes):
    return struct.pack("q", nbytes)
''',
        # safe: range check before pack
        '''\
import struct
def encode_size(nbytes):
    if nbytes < -9223372036854775808:
        return b"\\x00" * 8
    if nbytes > 9223372036854775807:
        return b"\\x00" * 8
    return struct.pack("q", nbytes)
''',
        "File size pack as 64-bit with possible overflow",
    ),
]
