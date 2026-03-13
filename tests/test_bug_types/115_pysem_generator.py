"""Python semantics: generator/iterator protocol — INDEX_OOB, NULL_PTR."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Bugs via generator exhaustion and next() without default"

EXAMPLES = [
    (
        "next_exhausted_generator",
        # buggy: generator exhaustion then index
        '''\
def first_match(items, pred):
    gen = (x for x in items if pred(x))
    first = next(gen)
    second = next(gen)
    pair = [first, second]
    return pair[2]
''',
        # safe: bounded access
        '''\
def first_match(items, pred):
    gen = (x for x in items if pred(x))
    first = next(gen, None)
    second = next(gen, None)
    pair = [first, second]
    return pair[1]
''',
        "Index 2 on a 2-element list built from generator",
    ),
    (
        "yield_accumulate_oob",
        # buggy: accumulate into list, access past end
        '''\
def yield_first_n(stream, n):
    collected = []
    for item in stream:
        collected.append(item)
        if len(collected) >= n:
            break
    return collected[n]
''',
        # safe: guard non-empty + access last valid index
        '''\
def yield_first_n(stream, n):
    collected = []
    for item in stream:
        collected.append(item)
        if len(collected) >= n:
            break
    if collected:
        return collected[n - 1]
    return None
''',
        "collected has n items; collected[n] is OOB",
    ),
    (
        "send_to_generator_oob",
        # buggy: send values, index result
        '''\
def coroutine_collect(data):
    results = []
    def gen():
        val = yield
        while val is not None:
            results.append(val * 2)
            val = yield
    g = gen()
    next(g)
    for d in data:
        g.send(d)
    return results[len(data)]
''',
        # safe: guard non-empty + last valid index
        '''\
def coroutine_collect(data):
    results = []
    def gen():
        val = yield
        while val is not None:
            results.append(val * 2)
            val = yield
    g = gen()
    next(g)
    for d in data:
        g.send(d)
    if results:
        return results[len(data) - 1]
    return 0
''',
        "results has len(data) items; index len(data) is OOB",
    ),
]
