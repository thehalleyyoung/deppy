"""BOUNDS: slice upper bound may exceed sequence length — the index
presheaf requires upper <= len(seq), but no such section is available.
"""

BUG_TYPE = "BOUNDS"
BUG_DESC = "Bounds violation on slice access"

EXAMPLES = [
    (
        "slice_upper_unchecked",
        # buggy: slice with unchecked upper bound
        '''\
def get_chunk(buf, start, end):
    return buf[start:end]
''',
        # safe: clamp upper to len
        '''\
def get_chunk(buf, start, end):
    end = min(end, len(buf))
    return buf[start:end]
''',
        "Slice upper bound may exceed len(buf)",
    ),
    (
        "prefix_slice",
        # buggy: take first n elements without checking length
        '''\
def first_n(items, n):
    return items[0:n]
''',
        # safe: clamp n
        '''\
def first_n(items, n):
    n = min(n, len(items))
    return items[0:n]
''',
        "Slice [0:n] with unchecked n",
    ),
    (
        "window_slice",
        # buggy: sliding window with unchecked offset
        '''\
def window(data, offset, size):
    return data[offset:offset + size]
''',
        # safe: clamp end
        '''\
def window(data, offset, size):
    end = min(offset + size, len(data))
    return data[offset:end]
''',
        "Window slice may exceed buffer length",
    ),
]
