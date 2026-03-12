"""van Emde Boas tree supporting insert, delete, predecessor, and successor.

Implements a simplified vEB tree over a fixed universe [0, u) supporting
O(log log u) predecessor/successor queries. The tree uses a summary
structure and clusters to recursively decompose the universe.

Bug: in the delete operation, when a cluster becomes empty after removal,
the algorithm fails to delete that cluster index from the summary structure.
This causes predecessor/successor to visit empty clusters and return wrong
results or miss valid predecessors.
"""

CORRECT = r"""
import math

def veb_new(u):
    # Create a vEB tree for universe size u
    # u should be a power of 2 and >= 2
    node = {"u": u, "min": None, "max": None}
    if u <= 2:
        return node
    upper_sqrt = 1 << ((int(math.log2(u)) + 1) // 2)
    lower_sqrt = u // upper_sqrt
    node["upper_sqrt"] = upper_sqrt
    node["lower_sqrt"] = lower_sqrt
    node["summary"] = veb_new(upper_sqrt)
    node["clusters"] = {}
    return node

def veb_high(node, x):
    return x // node["lower_sqrt"]

def veb_low(node, x):
    return x % node["lower_sqrt"]

def veb_index(node, hi, lo):
    return hi * node["lower_sqrt"] + lo

def veb_member(node, x):
    if node["min"] is None:
        return False
    if x == node["min"] or x == node["max"]:
        return True
    if node["u"] <= 2:
        return False
    c = veb_high(node, x)
    if c not in node["clusters"]:
        return False
    return veb_member(node["clusters"][c], veb_low(node, x))

def veb_insert(node, x):
    if node["min"] is None:
        node["min"] = x
        node["max"] = x
        return
    if x == node["min"] or x == node["max"]:
        return
    if x < node["min"]:
        x, node["min"] = node["min"], x
    if x > node["max"]:
        node["max"] = x
    if node["u"] <= 2:
        return
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c not in node["clusters"]:
        node["clusters"][c] = veb_new(node["lower_sqrt"])
    if node["clusters"][c]["min"] is None:
        veb_insert(node["summary"], c)
    veb_insert(node["clusters"][c], lo)

def veb_delete(node, x):
    if node["min"] is None:
        return
    if node["min"] == node["max"]:
        if node["min"] == x:
            node["min"] = None
            node["max"] = None
        return
    if node["u"] <= 2:
        if x == 0:
            node["min"] = 1
        else:
            node["min"] = 0
        node["max"] = node["min"]
        return
    if x == node["min"]:
        first_cluster = node["summary"]["min"]
        if first_cluster is None:
            node["min"] = node["max"]
            return
        x = veb_index(node, first_cluster, node["clusters"][first_cluster]["min"])
        node["min"] = x
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c in node["clusters"]:
        veb_delete(node["clusters"][c], lo)
        # CORRECT: if cluster becomes empty, remove from summary
        if node["clusters"][c]["min"] is None:
            veb_delete(node["summary"], c)
            del node["clusters"][c]
    if x == node["max"]:
        if node["summary"]["min"] is None:
            node["max"] = node["min"]
        else:
            last_cluster = node["summary"]["max"]
            node["max"] = veb_index(node, last_cluster, node["clusters"][last_cluster]["max"])

def veb_predecessor(node, x):
    if node["min"] is None or x <= node["min"]:
        return None
    if node["u"] <= 2:
        if x > node["min"]:
            return node["min"]
        return None
    c = veb_high(node, x)
    lo = veb_low(node, x)
    # Check within the same cluster first
    if c in node["clusters"] and node["clusters"][c]["min"] is not None and lo > node["clusters"][c]["min"]:
        offset = veb_predecessor(node["clusters"][c], lo)
        if offset is not None:
            return veb_index(node, c, offset)
    # Check previous cluster via summary
    prev_cluster = veb_predecessor(node["summary"], c)
    if prev_cluster is not None and prev_cluster in node["clusters"]:
        offset = node["clusters"][prev_cluster]["max"]
        return veb_index(node, prev_cluster, offset)
    # Check tree min
    if node["min"] is not None and node["min"] < x:
        return node["min"]
    return None

def veb_successor(node, x):
    if node["min"] is None or x >= node["max"]:
        return None
    if x < node["min"]:
        return node["min"]
    if node["u"] <= 2:
        if x < node["max"]:
            return node["max"]
        return None
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c in node["clusters"] and node["clusters"][c]["max"] is not None and lo < node["clusters"][c]["max"]:
        offset = veb_successor(node["clusters"][c], lo)
        if offset is not None:
            return veb_index(node, c, offset)
    next_cluster = veb_successor(node["summary"], c)
    if next_cluster is not None and next_cluster in node["clusters"]:
        offset = node["clusters"][next_cluster]["min"]
        return veb_index(node, next_cluster, offset)
    return None

def run_operations(universe_bits, ops):
    u = 1 << universe_bits
    tree = veb_new(u)
    results = []
    for op, val in ops:
        if op == "insert":
            veb_insert(tree, val)
            results.append(None)
        elif op == "delete":
            veb_delete(tree, val)
            results.append(None)
        elif op == "pred":
            results.append(veb_predecessor(tree, val))
        elif op == "succ":
            results.append(veb_successor(tree, val))
        elif op == "member":
            results.append(veb_member(tree, val))
    return results

universe_bits = UNIVERSE_BITS
ops = OPS
result = run_operations(universe_bits, ops)
"""

BUGGY = r"""
import math

def veb_new(u):
    node = {"u": u, "min": None, "max": None}
    if u <= 2:
        return node
    upper_sqrt = 1 << ((int(math.log2(u)) + 1) // 2)
    lower_sqrt = u // upper_sqrt
    node["upper_sqrt"] = upper_sqrt
    node["lower_sqrt"] = lower_sqrt
    node["summary"] = veb_new(upper_sqrt)
    node["clusters"] = {}
    return node

def veb_high(node, x):
    return x // node["lower_sqrt"]

def veb_low(node, x):
    return x % node["lower_sqrt"]

def veb_index(node, hi, lo):
    return hi * node["lower_sqrt"] + lo

def veb_member(node, x):
    if node["min"] is None:
        return False
    if x == node["min"] or x == node["max"]:
        return True
    if node["u"] <= 2:
        return False
    c = veb_high(node, x)
    if c not in node["clusters"]:
        return False
    return veb_member(node["clusters"][c], veb_low(node, x))

def veb_insert(node, x):
    if node["min"] is None:
        node["min"] = x
        node["max"] = x
        return
    if x == node["min"] or x == node["max"]:
        return
    if x < node["min"]:
        x, node["min"] = node["min"], x
    if x > node["max"]:
        node["max"] = x
    if node["u"] <= 2:
        return
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c not in node["clusters"]:
        node["clusters"][c] = veb_new(node["lower_sqrt"])
    if node["clusters"][c]["min"] is None:
        veb_insert(node["summary"], c)
    veb_insert(node["clusters"][c], lo)

def veb_delete(node, x):
    if node["min"] is None:
        return
    if node["min"] == node["max"]:
        if node["min"] == x:
            node["min"] = None
            node["max"] = None
        return
    if node["u"] <= 2:
        if x == 0:
            node["min"] = 1
        else:
            node["min"] = 0
        node["max"] = node["min"]
        return
    if x == node["min"]:
        first_cluster = node["summary"]["min"]
        if first_cluster is None:
            node["min"] = node["max"]
            return
        x = veb_index(node, first_cluster, node["clusters"][first_cluster]["min"])
        node["min"] = x
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c in node["clusters"]:
        veb_delete(node["clusters"][c], lo)
        # BUG: does NOT update summary when cluster becomes empty
        # Should delete c from summary, but just removes the cluster dict entry
        if node["clusters"][c]["min"] is None:
            del node["clusters"][c]
            # Missing: veb_delete(node["summary"], c)
    if x == node["max"]:
        if node["summary"]["min"] is None:
            node["max"] = node["min"]
        else:
            last_cluster = node["summary"]["max"]
            if last_cluster in node["clusters"]:
                node["max"] = veb_index(node, last_cluster, node["clusters"][last_cluster]["max"])
            else:
                node["max"] = node["min"]

def veb_predecessor(node, x):
    if node["min"] is None or x <= node["min"]:
        return None
    if node["u"] <= 2:
        if x > node["min"]:
            return node["min"]
        return None
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c in node["clusters"] and node["clusters"][c]["min"] is not None and lo > node["clusters"][c]["min"]:
        offset = veb_predecessor(node["clusters"][c], lo)
        if offset is not None:
            return veb_index(node, c, offset)
    prev_cluster = veb_predecessor(node["summary"], c)
    if prev_cluster is not None and prev_cluster in node["clusters"]:
        offset = node["clusters"][prev_cluster]["max"]
        return veb_index(node, prev_cluster, offset)
    if node["min"] is not None and node["min"] < x:
        return node["min"]
    return None

def veb_successor(node, x):
    if node["min"] is None or x >= node["max"]:
        return None
    if x < node["min"]:
        return node["min"]
    if node["u"] <= 2:
        if x < node["max"]:
            return node["max"]
        return None
    c = veb_high(node, x)
    lo = veb_low(node, x)
    if c in node["clusters"] and node["clusters"][c]["max"] is not None and lo < node["clusters"][c]["max"]:
        offset = veb_successor(node["clusters"][c], lo)
        if offset is not None:
            return veb_index(node, c, offset)
    next_cluster = veb_successor(node["summary"], c)
    if next_cluster is not None and next_cluster in node["clusters"]:
        offset = node["clusters"][next_cluster]["min"]
        return veb_index(node, next_cluster, offset)
    return None

def run_operations(universe_bits, ops):
    u = 1 << universe_bits
    tree = veb_new(u)
    results = []
    for op, val in ops:
        if op == "insert":
            veb_insert(tree, val)
            results.append(None)
        elif op == "delete":
            veb_delete(tree, val)
            results.append(None)
        elif op == "pred":
            results.append(veb_predecessor(tree, val))
        elif op == "succ":
            results.append(veb_successor(tree, val))
        elif op == "member":
            results.append(veb_member(tree, val))
    return results

universe_bits = UNIVERSE_BITS
ops = OPS
result = run_operations(universe_bits, ops)
"""


def SPEC(universe_bits, ops, result):
    # Simulate with a simple sorted set and compare
    if not isinstance(result, list):
        return False
    if len(result) != len(ops):
        return False
    elements = set()
    u = 1 << universe_bits
    for i, (op, val) in enumerate(ops):
        if val < 0 or val >= u:
            return False
        if op == "insert":
            elements.add(val)
            if result[i] is not None:
                return False
        elif op == "delete":
            elements.discard(val)
            if result[i] is not None:
                return False
        elif op == "pred":
            candidates = [e for e in elements if e < val]
            expected = max(candidates) if candidates else None
            if result[i] != expected:
                return False
        elif op == "succ":
            candidates = [e for e in elements if e > val]
            expected = min(candidates) if candidates else None
            if result[i] != expected:
                return False
        elif op == "member":
            if result[i] != (val in elements):
                return False
    return True


BUG_DESC = (
    "In the delete operation, when a cluster becomes empty after removing "
    "an element, the algorithm deletes the cluster dict entry but does NOT "
    "remove that cluster's index from the summary vEB tree. This causes "
    "predecessor and successor queries to follow stale summary pointers "
    "to clusters that no longer exist, returning incorrect results."
)


def _gen_universe_bits():
    return 4  # universe of 16


def _gen_ops():
    import random
    # The bug: after deleting an element that empties a cluster, the cluster
    # index is NOT removed from the summary. This causes predecessor/successor
    # queries to follow stale summary pointers.
    #
    # Key trigger pattern (universe=16, clusters of size 4):
    #   Cluster 0=[0..3], 1=[4..7], 2=[8..11], 3=[12..15]
    #
    # 1. Insert elements in clusters 0, 1, and 2
    # 2. Delete ALL from cluster 1 (the middle cluster) -- must NOT delete
    #    the overall tree min, which would crash on stale summary access
    # 3. Query pred(x) where x is in cluster 2's range
    #    Correct: returns max of cluster 0
    #    Buggy: summary.pred(2)=1 (stale!), cluster 1 not found, falls to
    #           tree min instead of cluster 0's max
    #
    # IMPORTANT: the tree min is stored separately (not in any cluster),
    # so we put min in cluster 0 and never delete it. We only delete
    # from cluster 1 (the middle one).

    u = 16
    ops = []

    # Insert in cluster 0: elements 0, 1 (0 becomes tree min)
    ops.append(("insert", 0))
    ops.append(("insert", 1))

    # Insert in cluster 1: elements 4, 5
    cluster1_vals = random.sample(range(4, 8), 2)
    for v in cluster1_vals:
        ops.append(("insert", v))

    # Insert in cluster 2: elements 8, 9
    cluster2_vals = random.sample(range(8, 12), 2)
    for v in cluster2_vals:
        ops.append(("insert", v))

    # Delete ALL from cluster 1 (4 and 5). Since tree min=0 is in cluster 0,
    # deleting from cluster 1 won't hit the dangerous min-replacement path.
    for v in cluster1_vals:
        ops.append(("delete", v))

    # Now summary still thinks cluster 1 exists (stale).
    # Query pred of first element in cluster 2's range.
    # Correct: max of cluster 0 = 1
    # Buggy: summary.pred(cluster_2_idx=2) returns 1 (stale cluster 1),
    #        cluster 1 not in clusters dict, falls back to tree min = 0
    first_c2 = min(cluster2_vals)
    ops.append(("pred", first_c2))

    # More queries that exercise the stale summary
    ops.append(("pred", first_c2 + 1))
    ops.append(("succ", 2))
    ops.append(("succ", 3))

    # Additional pred/succ queries
    for _ in range(3):
        v = random.randint(0, u - 1)
        ops.append((random.choice(["pred", "succ"]), v))

    return ops


INPUT_OVERRIDES = {
    "UNIVERSE_BITS": _gen_universe_bits,
    "OPS": _gen_ops,
}
