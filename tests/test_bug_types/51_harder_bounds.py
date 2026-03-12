"""Harder BOUNDS: complex slice patterns, computed upper bounds."""

BUG_TYPE = "BOUNDS"
BUG_DESC = "Buffer bounds violation in complex slice patterns"

EXAMPLES = [
    (
        "sliding_window",
        # buggy: window end may exceed buffer length
        '''\
def sliding_windows(buf, size):
    results = []
    for i in range(len(buf)):
        window = buf[i:i + size]
        results.append(window)
    return results
''',
        # safe: clamp upper bound
        '''\
def sliding_windows(buf, size):
    results = []
    for i in range(len(buf)):
        end = min(i + size, len(buf))
        window = buf[i:end]
        results.append(window)
    return results
''',
        "Slice upper bound i+size may exceed buffer length",
    ),
    (
        "batch_extract",
        # buggy: batch_size offset may go past end
        '''\
def extract_batches(data, batch_size):
    batches = []
    offset = 0
    while offset < len(data):
        batch = data[offset:offset + batch_size]
        batches.append(batch)
        offset += batch_size
    return batches
''',
        # safe: clamp slice end
        '''\
def extract_batches(data, batch_size):
    batches = []
    offset = 0
    while offset < len(data):
        end = min(offset + batch_size, len(data))
        batch = data[offset:end]
        batches.append(batch)
        offset += batch_size
    return batches
''',
        "Batch slice end may exceed data length",
    ),
    (
        "prefix_copy",
        # buggy: n may be larger than buffer
        '''\
def copy_prefix(buf, n):
    return buf[:n]
''',
        # safe: clamp n to buffer length
        '''\
def copy_prefix(buf, n):
    safe_n = min(n, len(buf))
    return buf[:safe_n]
''',
        "Slice upper bound from parameter may exceed buffer length",
    ),
]
