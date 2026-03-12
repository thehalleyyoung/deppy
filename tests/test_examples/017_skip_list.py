"""Skip list with search, insert, and range query.

Bug: During insert, when splicing the new node into each level, the correct
order is: (1) new_node.forward[i] = update[i].forward[i], then
(2) update[i].forward[i] = new_node. The bug reverses this order, first
setting update[i].forward[i] = new_node and then setting
new_node.forward[i] = update[i].forward[i] (which is now new_node itself).
This makes new_node point to itself at each level, creating cycles. At level 0,
this causes range queries to loop, so the bug variant caps range query
traversal, losing elements beyond the cycle. For search, the cycle means
any key after the self-pointing node is unreachable.
"""

CORRECT = r"""
import random as _rand

MAX_LEVEL = 4
_rand.seed(42)

class SkipNode:
    def __init__(self, key, value, level):
        self.key = key
        self.value = value
        self.forward = [None] * (level + 1)

def random_level():
    lvl = 0
    while _rand.random() < 0.5 and lvl < MAX_LEVEL:
        lvl += 1
    return lvl

def make_skip_list():
    header = SkipNode(float('-inf'), None, MAX_LEVEL)
    return header

def skip_insert(header, key, value):
    update = [None] * (MAX_LEVEL + 1)
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        while current.forward[i] is not None and current.forward[i].key < key:
            current = current.forward[i]
        update[i] = current

    nxt = current.forward[0]
    if nxt is not None and nxt.key == key:
        nxt.value = value
        return

    new_lvl = random_level()
    new_node = SkipNode(key, value, new_lvl)
    for i in range(new_lvl + 1):
        # CORRECT ORDER: set new_node's forward first, then update predecessor
        new_node.forward[i] = update[i].forward[i]
        update[i].forward[i] = new_node

def skip_search(header, key):
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        while current.forward[i] is not None and current.forward[i].key < key:
            current = current.forward[i]
    current = current.forward[0]
    if current is not None and current.key == key:
        return current.value
    return None

def skip_range_query(header, lo, hi):
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        while current.forward[i] is not None and current.forward[i].key < lo:
            current = current.forward[i]
    current = current.forward[0]
    results = []
    while current is not None and current.key <= hi:
        results.append((current.key, current.value))
        current = current.forward[0]
    return results

def process_operations(operations):
    header = make_skip_list()
    search_results = []
    range_results = []

    for op in operations:
        if op[0] == 'insert':
            skip_insert(header, op[1], op[2])
        elif op[0] == 'search':
            val = skip_search(header, op[1])
            search_results.append((op[1], val))
        elif op[0] == 'range':
            rng = skip_range_query(header, op[1], op[2])
            range_results.append((op[1], op[2], rng))

    return search_results, range_results

ops = OPERATIONS
result = process_operations(ops)
"""

BUGGY = r"""
import random as _rand

MAX_LEVEL = 4
_rand.seed(42)

_STEP_CAP = 500

class SkipNode:
    def __init__(self, key, value, level):
        self.key = key
        self.value = value
        self.forward = [None] * (level + 1)

def random_level():
    lvl = 0
    while _rand.random() < 0.5 and lvl < MAX_LEVEL:
        lvl += 1
    return lvl

def make_skip_list():
    header = SkipNode(float('-inf'), None, MAX_LEVEL)
    return header

def skip_insert(header, key, value):
    update = [None] * (MAX_LEVEL + 1)
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        s = 0
        while current.forward[i] is not None and current.forward[i].key < key and s < _STEP_CAP:
            current = current.forward[i]
            s += 1
        update[i] = current

    nxt = current.forward[0]
    if nxt is not None and nxt.key == key:
        nxt.value = value
        return

    new_lvl = random_level()
    new_node = SkipNode(key, value, new_lvl)
    for i in range(new_lvl + 1):
        # BUG: reversed splice order - update predecessor first, then set forward
        # After line 1: update[i].forward[i] now points to new_node
        # After line 2: new_node.forward[i] = update[i].forward[i] = new_node (self!)
        update[i].forward[i] = new_node
        new_node.forward[i] = update[i].forward[i]

def skip_search(header, key):
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        s = 0
        while current.forward[i] is not None and current.forward[i].key < key and s < _STEP_CAP:
            current = current.forward[i]
            s += 1
    current = current.forward[0]
    if current is not None and current.key == key:
        return current.value
    return None

def skip_range_query(header, lo, hi):
    current = header
    for i in range(MAX_LEVEL, -1, -1):
        s = 0
        while current.forward[i] is not None and current.forward[i].key < lo and s < _STEP_CAP:
            current = current.forward[i]
            s += 1
    current = current.forward[0]
    results = []
    seen_keys = set()
    s = 0
    while current is not None and current.key <= hi and s < _STEP_CAP:
        if current.key in seen_keys:
            break  # cycle detected
        seen_keys.add(current.key)
        results.append((current.key, current.value))
        current = current.forward[0]
        s += 1
    return results

def process_operations(operations):
    header = make_skip_list()
    search_results = []
    range_results = []

    for op in operations:
        if op[0] == 'insert':
            skip_insert(header, op[1], op[2])
        elif op[0] == 'search':
            val = skip_search(header, op[1])
            search_results.append((op[1], val))
        elif op[0] == 'range':
            rng = skip_range_query(header, op[1], op[2])
            range_results.append((op[1], op[2], rng))

    return search_results, range_results

ops = OPERATIONS
result = process_operations(ops)
"""


def SPEC(OPERATIONS, result):
    """Verify skip list correctness:
    1) All inserted keys are found by search.
    2) Range queries return exactly the inserted keys in [lo, hi].
    3) Range results are sorted.
    """
    if not isinstance(result, tuple) or len(result) != 2:
        return False

    search_results, range_results = result

    inserted = {}
    search_idx = 0
    range_idx = 0
    for op in OPERATIONS:
        if op[0] == 'insert':
            inserted[op[1]] = op[2]
        elif op[0] == 'search':
            if search_idx >= len(search_results):
                return False
            key, val = search_results[search_idx]
            if key != op[1]:
                return False
            expected = inserted.get(op[1], None)
            if val != expected:
                return False
            search_idx += 1
        elif op[0] == 'range':
            if range_idx >= len(range_results):
                return False
            lo_ret, hi_ret, rng = range_results[range_idx]
            if lo_ret != op[1] or hi_ret != op[2]:
                return False
            expected_keys = sorted(
                [(k, v) for k, v in inserted.items() if op[1] <= k <= op[2]]
            )
            if rng != expected_keys:
                return False
            for i in range(len(rng) - 1):
                if rng[i][0] > rng[i + 1][0]:
                    return False
            range_idx += 1

    return True


BUG_DESC = (
    "During insert, the splice order is reversed: update[i].forward[i] is set "
    "to new_node before new_node.forward[i] is assigned. This means "
    "new_node.forward[i] reads back new_node itself (since update[i].forward[i] "
    "was just set to new_node), creating a self-loop. Nodes after the insertion "
    "point become unreachable, causing search to miss keys and range queries to "
    "return incomplete or repeated results."
)


def _generate_operations():
    import random
    ops = []
    keys = random.sample(range(1, 101), random.randint(15, 20))
    for k in keys:
        ops.append(('insert', k, k * 10))
    # Search for inserted keys and some non-inserted
    search_keys = random.sample(keys, min(5, len(keys)))
    search_keys += [random.randint(1, 100) for _ in range(3)]
    for k in search_keys:
        ops.append(('search', k))
    # Range queries
    for _ in range(3):
        lo = random.randint(1, 50)
        hi = random.randint(lo + 5, min(lo + 40, 100))
        ops.append(('range', lo, hi))
    return ops


INPUT_OVERRIDES = {
    "OPERATIONS": _generate_operations,
}
