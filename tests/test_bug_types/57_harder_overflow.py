"""Harder OVERFLOW: struct.pack with 'q' format on large computed values."""

BUG_TYPE = "OVERFLOW"
BUG_DESC = "Overflow in complex struct packing patterns"

EXAMPLES = [
    (
        "pack_large_product",
        # buggy: product of large values packed as signed long long
        '''\
import struct
def encode_volume(x, y, z):
    vol = x * y * z
    return struct.pack(">q", vol)
''',
        # safe: clamp to int64 range
        '''\
import struct
def encode_volume(x, y, z):
    vol = x * y * z
    lo = -(2**63)
    hi = 2**63 - 1
    vol = max(lo, min(vol, hi))
    return struct.pack(">q", vol)
''',
        "Product of three values packed as int64 may overflow",
    ),
    (
        "pack_running_total",
        # buggy: accumulated total packed as long long
        '''\
import struct
def pack_total(amounts):
    total = 0
    for a in amounts:
        total += a
    return struct.pack("<q", total)
''',
        # safe: clamp before packing
        '''\
import struct
def pack_total(amounts):
    total = 0
    for a in amounts:
        total += a
    clamped = max(-(2**63), min(total, 2**63 - 1))
    return struct.pack("<q", clamped)
''',
        "Accumulated sum packed as int64 may overflow",
    ),
    (
        "pack_bit_shift",
        # buggy: shifted value may exceed int64
        '''\
import struct
def pack_shifted(value, bits):
    result = value << bits
    return struct.pack("q", result)
''',
        # safe: mask to int64 range
        '''\
import struct
def pack_shifted(value, bits):
    result = value << bits
    mask = (1 << 63) - 1
    clamped = max(-(2**63), min(result, mask))
    return struct.pack("q", clamped)
''',
        "Bit-shifted value packed as int64 may overflow",
    ),
]
