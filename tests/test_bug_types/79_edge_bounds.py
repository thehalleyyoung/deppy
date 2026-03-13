"""Edge-case BOUNDS: upper slice, computed upper bound, nested slice."""

BUG_TYPE = "BOUNDS"
BUG_DESC = "Bounds violation in edge-case slice patterns"

EXAMPLES = [
    (
        "slice_with_offset",
        # buggy: slice upper bound not checked
        '''\
def get_chunk(data, start, size):
    end = start + size
    return data[:end]
''',
        # safe: clamp upper bound
        '''\
def get_chunk(data, start, size):
    end = min(start + size, len(data))
    return data[:end]
''',
        "Slice upper bound may exceed sequence length",
    ),
    (
        "prefix_slice",
        # buggy: prefix slice with arbitrary length
        '''\
def get_prefix(text, n):
    return text[:n]
''',
        # safe: clamp to len
        '''\
def get_prefix(text, n):
    n = min(n, len(text))
    return text[:n]
''',
        "Prefix slice with unchecked length parameter",
    ),
    (
        "window_slice",
        # buggy: sliding window slice unchecked
        '''\
def window(data, pos, width):
    return data[:width]
''',
        # safe: clamp width
        '''\
def window(data, pos, width):
    width = min(width, len(data))
    return data[:width]
''',
        "Window slice with unchecked width",
    ),
    (
        "batch_slice",
        # buggy: batch slice upper bound
        '''\
def get_batch(items, batch_num, batch_size):
    end = batch_num * batch_size
    return items[:end]
''',
        # safe: clamp to length
        '''\
def get_batch(items, batch_num, batch_size):
    end = min(batch_num * batch_size, len(items))
    return items[:end]
''',
        "Batch slice upper bound may exceed list length",
    ),
]
