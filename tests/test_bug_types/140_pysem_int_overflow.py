"""Python semantics: integer overflow and precision — INTEGER_OVERFLOW, FP_DOMAIN."""

BUG_TYPE = "INTEGER_OVERFLOW"
BUG_DESC = "Integer overflow in struct packing and bit operations"

EXAMPLES = [
    (
        "struct_pack_overflow",
        # buggy: value too large for struct format
        '''\
import struct

def pack_short(value):
    return struct.pack("h", value * 1000)
''',
        # safe: clamp to range
        '''\
import struct

def pack_short(value):
    clamped = max(-32768, min(32767, value * 1000))
    return struct.pack("h", clamped)
''',
        "value * 1000 may exceed short range [-32768, 32767]",
    ),
    (
        "ctypes_overflow",
        # buggy: ctypes c_int32 overflow
        '''\
import ctypes

def to_int32(value):
    return ctypes.c_int32(value * 2147483647).value
''',
        # safe: range check
        '''\
import ctypes

def to_int32(value):
    result = value * 2147483647
    if -2147483648 <= result <= 2147483647:
        return ctypes.c_int32(result).value
    return 0
''',
        "value * MAX_INT32 overflows c_int32",
    ),
    (
        "bit_shift_overflow",
        # buggy: left shift creates huge number then pack
        '''\
import struct

def encode_flags(flags):
    combined = 0
    for i, f in enumerate(flags):
        combined |= (f << (i * 8))
    return struct.pack("I", combined)
''',
        # safe: mask to 32 bits
        '''\
import struct

def encode_flags(flags):
    combined = 0
    for i, f in enumerate(flags):
        if i < 4:
            combined |= (f << (i * 8))
    combined &= 0xFFFFFFFF
    return struct.pack("I", combined)
''',
        "flags with >4 elements shift past 32-bit boundary",
    ),
]
