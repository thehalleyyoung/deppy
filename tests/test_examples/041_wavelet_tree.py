"""Wavelet tree for rank/select queries on integer sequences.

Builds a wavelet tree over an alphabet and supports rank(value, position)
which counts occurrences of value in the sequence up to a given position,
and select(value, k) which finds the position of the k-th occurrence.

Bug: when recursing into the right child, the position offset is not
adjusted by subtracting the count of elements routed to the left child.
This causes right-child queries to use the wrong position, producing
incorrect rank counts.
"""

CORRECT = r"""
# Wavelet tree node stores a bitvector indicating left(0) vs right(1)
# for each element at this level of recursion.

def build_wavelet_tree(seq, lo, hi):
    # Returns a tree node dict with bitvector and children
    if lo >= hi - 1 or len(seq) == 0:
        return {"leaf": True, "val": lo, "count": len(seq)}
    mid = (lo + hi) // 2
    # bitvector: 0 if element goes left (<= mid), 1 if right (> mid)
    bv = []
    left_seq = []
    right_seq = []
    for x in seq:
        if x < mid:
            bv.append(0)
            left_seq.append(x)
        else:
            bv.append(1)
            right_seq.append(x)
    node = {"leaf": False, "bv": bv, "lo": lo, "hi": hi, "mid": mid}
    node["left"] = build_wavelet_tree(left_seq, lo, mid)
    node["right"] = build_wavelet_tree(right_seq, mid, hi)
    return node

def rank_query(node, value, pos):
    # Count occurrences of value in seq[0..pos) using wavelet tree
    if pos <= 0:
        return 0
    if node.get("leaf"):
        return pos
    mid = node["mid"]
    bv = node["bv"]
    # Count zeros (left) and ones (right) in bv[0..pos)
    left_count = 0
    right_count = 0
    for i in range(pos):
        if bv[i] == 0:
            left_count += 1
        else:
            right_count += 1
    if value < mid:
        # Recurse into left child with left_count as new position
        return rank_query(node["left"], value, left_count)
    else:
        # CORRECT: recurse into right child with right_count as position
        return rank_query(node["right"], value, right_count)

def select_query(node, value, k):
    # Find position of k-th occurrence (1-indexed) of value
    if k <= 0:
        return -1
    if node.get("leaf"):
        if k <= node["count"]:
            return k - 1
        return -1
    mid = node["mid"]
    bv = node["bv"]
    if value < mid:
        # Find position in left child, then map back
        child_pos = select_query(node["left"], value, k)
        if child_pos < 0:
            return -1
        # Map child_pos back: find the (child_pos+1)-th zero in bv
        count = 0
        for i in range(len(bv)):
            if bv[i] == 0:
                if count == child_pos:
                    return i
                count += 1
        return -1
    else:
        child_pos = select_query(node["right"], value, k)
        if child_pos < 0:
            return -1
        # Map child_pos back: find the (child_pos+1)-th one in bv
        count = 0
        for i in range(len(bv)):
            if bv[i] == 1:
                if count == child_pos:
                    return i
                count += 1
        return -1

def process_queries(seq, queries):
    # queries is a list of (type, value, param) tuples
    # type "rank": count of value in seq[0..param)
    # type "select": position of param-th occurrence of value
    if not seq:
        return []
    lo = min(seq)
    hi = max(seq) + 1
    root = build_wavelet_tree(seq, lo, hi)
    results = []
    for qtype, val, param in queries:
        if qtype == "rank":
            results.append(rank_query(root, val, param))
        elif qtype == "select":
            results.append(select_query(root, val, param))
        else:
            results.append(-1)
    return results

seq = SEQUENCE
queries = QUERIES
result = process_queries(seq, queries)
"""

BUGGY = r"""
def build_wavelet_tree(seq, lo, hi):
    # Returns a tree node dict with bitvector and children
    if lo >= hi - 1 or len(seq) == 0:
        return {"leaf": True, "val": lo, "count": len(seq)}
    mid = (lo + hi) // 2
    bv = []
    left_seq = []
    right_seq = []
    for x in seq:
        if x < mid:
            bv.append(0)
            left_seq.append(x)
        else:
            bv.append(1)
            right_seq.append(x)
    node = {"leaf": False, "bv": bv, "lo": lo, "hi": hi, "mid": mid}
    node["left"] = build_wavelet_tree(left_seq, lo, mid)
    node["right"] = build_wavelet_tree(right_seq, mid, hi)
    return node

def rank_query(node, value, pos):
    # Count occurrences of value in seq[0..pos) using wavelet tree
    if pos <= 0:
        return 0
    if node.get("leaf"):
        return pos
    mid = node["mid"]
    bv = node["bv"]
    left_count = 0
    right_count = 0
    for i in range(pos):
        if bv[i] == 0:
            left_count += 1
        else:
            right_count += 1
    if value < mid:
        return rank_query(node["left"], value, left_count)
    else:
        # BUG: should pass right_count, but passes pos (unadjusted)
        # This fails to subtract the count of left-going elements
        return rank_query(node["right"], value, pos)

def select_query(node, value, k):
    # Find position of k-th occurrence (1-indexed) of value
    if k <= 0:
        return -1
    if node.get("leaf"):
        if k <= node["count"]:
            return k - 1
        return -1
    mid = node["mid"]
    bv = node["bv"]
    if value < mid:
        child_pos = select_query(node["left"], value, k)
        if child_pos < 0:
            return -1
        count = 0
        for i in range(len(bv)):
            if bv[i] == 0:
                if count == child_pos:
                    return i
                count += 1
        return -1
    else:
        child_pos = select_query(node["right"], value, k)
        if child_pos < 0:
            return -1
        count = 0
        for i in range(len(bv)):
            if bv[i] == 1:
                if count == child_pos:
                    return i
                count += 1
        return -1

def process_queries(seq, queries):
    if not seq:
        return []
    lo = min(seq)
    hi = max(seq) + 1
    root = build_wavelet_tree(seq, lo, hi)
    results = []
    for qtype, val, param in queries:
        if qtype == "rank":
            results.append(rank_query(root, val, param))
        elif qtype == "select":
            results.append(select_query(root, val, param))
        else:
            results.append(-1)
    return results

seq = SEQUENCE
queries = QUERIES
result = process_queries(seq, queries)
"""


def SPEC(SEQUENCE, QUERIES, result):
    sequence, queries = SEQUENCE, QUERIES
    # Verify rank/select queries by brute force
    if not isinstance(result, list):
        return False
    if len(result) != len(queries):
        return False
    for i, (qtype, val, param) in enumerate(queries):
        if qtype == "rank":
            # Count occurrences of val in sequence[0..param)
            expected = sum(1 for x in sequence[:param] if x == val)
            if result[i] != expected:
                return False
        elif qtype == "select":
            # Find position of param-th occurrence (1-indexed)
            positions = [j for j, x in enumerate(sequence) if x == val]
            if param <= 0 or param > len(positions):
                if result[i] != -1:
                    return False
            else:
                if result[i] != positions[param - 1]:
                    return False
    return True


BUG_DESC = (
    "When recursing into the right child during a rank query, the position "
    "should be adjusted to right_count (number of elements routed right in "
    "the bitvector up to the query position). The bug passes the original "
    "unadjusted position, which includes elements that went to the left "
    "child, producing inflated rank counts for right-side values."
)


def _gen_inputs():
    import random
    n = random.randint(8, 15)
    alphabet_size = random.randint(3, 6)
    seq = [random.randint(0, alphabet_size - 1) for _ in range(n)]
    queries = []
    vals_in_seq = list(set(seq))
    for _ in range(random.randint(4, 8)):
        qtype = random.choice(["rank", "select"])
        val = random.choice(vals_in_seq)
        if qtype == "rank":
            pos = random.randint(1, len(seq))
            queries.append(("rank", val, pos))
        else:
            count = sum(1 for x in seq if x == val)
            k = random.randint(1, max(1, count))
            queries.append(("select", val, k))
    return seq, queries


def _make_generators():
    cache = [None]

    def ensure_cache():
        if cache[0] is None:
            cache[0] = _gen_inputs()

    def get_seq():
        ensure_cache()
        return cache[0][0]

    def get_queries():
        ensure_cache()
        val = cache[0][1]
        cache[0] = None
        return val

    return get_seq, get_queries

_get_seq, _get_queries = _make_generators()

INPUT_OVERRIDES = {
    "SEQUENCE": _get_seq,
    "QUERIES": _get_queries,
}
