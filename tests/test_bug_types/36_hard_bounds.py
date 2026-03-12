"""Hard BOUNDS examples — computed slice bounds, off-by-one patterns."""

BUG_TYPE = "BOUNDS"
BUG_DESC = "Bounds violation in harder slice patterns"

EXAMPLES = [
    (
        "chunk_slice",
        # buggy: chunk slicing without clamping end to length
        '''\
def get_chunk(data, offset, size):
    return data[offset:offset + size]
''',
        # safe: clamp the end
        '''\
def get_chunk(data, offset, size):
    end = min(offset + size, len(data))
    return data[offset:end]
''',
        "Slice end offset+size may exceed data length",
    ),
    (
        "page_slice",
        # buggy: page * page_size may go past end
        '''\
def get_page(items, page, page_size):
    start = page * page_size
    return items[start:start + page_size]
''',
        # safe: clamp
        '''\
def get_page(items, page, page_size):
    start = min(page * page_size, len(items))
    end = min(start + page_size, len(items))
    return items[start:end]
''',
        "Pagination slice with unchecked page number",
    ),
    (
        "tail_slice",
        # buggy: take last N items but uses index access with computed start
        '''\
def last_n(items, n):
    start = len(items) - n
    return items[start:start + n]
''',
        # safe: clamp start
        '''\
def last_n(items, n):
    start = max(len(items) - n, 0)
    return items[start:start + n]
''',
        "Unclamped start in slice when n > len(items)",
    ),
]
