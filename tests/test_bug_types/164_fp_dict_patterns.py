"""FP stress: real-world safe patterns that combine guards subtly.

These mirror patterns from popular Python libraries and frameworks
where bugs are prevented through non-obvious mechanisms.
"""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Real-world dict safety patterns"

EXAMPLES = [
    (
        "defaultdict_no_keyerror",
        '''\
def count_words(words):
    counts = {}
    for w in words:
        counts[w] += 1
    return counts
''',
        '''\
from collections import defaultdict

def count_words(words):
    counts = defaultdict(int)
    for w in words:
        counts[w] += 1
    return counts
''',
        "defaultdict(int) never raises KeyError",
    ),
    (
        "counter_safe",
        '''\
def top_item(items):
    freq = {}
    for item in items:
        freq[item] += 1
    return max(freq, key=freq.__getitem__)
''',
        '''\
from collections import Counter

def top_item(items):
    if not items:
        return None
    freq = Counter(items)
    return freq.most_common(1)[0][0]
''',
        "Counter handles counting; emptiness checked",
    ),
    (
        "dict_comprehension_safe_keys",
        '''\
def invert(d):
    return {v: d[v] for v in d.values()}
''',
        '''\
def invert(d):
    return {v: k for k, v in d.items()}
''',
        "dict.items() iteration never causes KeyError",
    ),
    (
        "environ_get_with_default",
        '''\
import os
def get_port():
    return int(os.environ["PORT"])
''',
        '''\
import os
def get_port():
    return int(os.environ.get("PORT", "8080"))
''',
        "os.environ.get with default prevents KeyError",
    ),
    (
        "update_then_access",
        '''\
def merge_and_read(base, extra, key):
    return base[key]
''',
        '''\
def merge_and_read(base, extra, key):
    merged = {**base, **extra}
    return merged.get(key)
''',
        "dict.get on merged dict returns None instead of KeyError",
    ),
]
