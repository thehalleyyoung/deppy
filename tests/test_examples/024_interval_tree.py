"""Interval tree for stabbing queries (find all intervals containing a point)."""

import random

CORRECT = """
def solve(intervals, queries):
    # intervals: list of (lo, hi, id)
    # queries: list of int (query points)
    # Returns: dict mapping query point -> sorted list of interval ids

    class Node:
        __slots__ = ('center', 'by_lo', 'by_hi', 'left', 'right')
        def __init__(self):
            self.center = 0
            self.by_lo = []
            self.by_hi = []
            self.left = None
            self.right = None

    def build(ivals):
        if not ivals:
            return None
        # Choose median endpoint as center
        endpoints = []
        for lo, hi, iid in ivals:
            endpoints.append(lo)
            endpoints.append(hi)
        endpoints.sort()
        center = endpoints[len(endpoints) // 2]

        node = Node()
        node.center = center

        left_intervals = []
        right_intervals = []
        center_intervals = []

        for lo, hi, iid in ivals:
            if hi < center:
                left_intervals.append((lo, hi, iid))
            elif lo > center:
                right_intervals.append((lo, hi, iid))
            else:
                center_intervals.append((lo, hi, iid))

        # Store center intervals sorted by lo and by hi
        node.by_lo = sorted(center_intervals, key=lambda x: x[0])
        node.by_hi = sorted(center_intervals, key=lambda x: x[1], reverse=True)

        node.left = build(left_intervals)
        node.right = build(right_intervals)
        return node

    def query_point(node, x):
        if node is None:
            return []
        result = []
        if x < node.center:
            # Scan by_lo from left: all with lo <= x overlap
            for lo, hi, iid in node.by_lo:
                if lo <= x:
                    result.append(iid)
                else:
                    break
            # Recurse left
            result.extend(query_point(node.left, x))
        elif x > node.center:
            # Scan by_hi from left (highest hi first): all with hi >= x overlap
            for lo, hi, iid in node.by_hi:
                if hi >= x:
                    result.append(iid)
                else:
                    break
            # Recurse right
            result.extend(query_point(node.right, x))
        else:
            # x == center: all center intervals match
            for lo, hi, iid in node.by_lo:
                result.append(iid)
        return result

    root = build(intervals)

    results = {}
    for x in queries:
        ids = query_point(root, x)
        results[x] = sorted(ids)
    return results
"""

BUGGY = """
def solve(intervals, queries):
    class Node:
        __slots__ = ('center', 'by_lo', 'by_hi', 'left', 'right')
        def __init__(self):
            self.center = 0
            self.by_lo = []
            self.by_hi = []
            self.left = None
            self.right = None

    def build(ivals):
        if not ivals:
            return None
        endpoints = []
        for lo, hi, iid in ivals:
            endpoints.append(lo)
            endpoints.append(hi)
        endpoints.sort()
        center = endpoints[len(endpoints) // 2]

        node = Node()
        node.center = center

        left_intervals = []
        right_intervals = []
        center_intervals = []

        for lo, hi, iid in ivals:
            if hi < center:
                left_intervals.append((lo, hi, iid))
            elif lo > center:
                right_intervals.append((lo, hi, iid))
            else:
                center_intervals.append((lo, hi, iid))

        node.by_lo = sorted(center_intervals, key=lambda x: x[0])
        node.by_hi = sorted(center_intervals, key=lambda x: x[1], reverse=True)

        node.left = build(left_intervals)
        node.right = build(right_intervals)
        return node

    def query_point(node, x):
        if node is None:
            return []
        result = []
        if x < node.center:
            # BUG: scans by_hi (sorted by hi desc) checking hi >= x
            # instead of scanning by_lo checking lo <= x.
            # This uses the wrong sorted list, so we miss intervals
            # whose lo <= x but whose hi is not among the largest.
            for lo, hi, iid in node.by_hi:
                if hi >= x:
                    result.append(iid)
                else:
                    break
            result.extend(query_point(node.left, x))
        elif x > node.center:
            # BUG: scans by_lo (sorted by lo asc) checking lo <= x
            # instead of scanning by_hi checking hi >= x.
            for lo, hi, iid in node.by_lo:
                if lo <= x:
                    result.append(iid)
                else:
                    break
            result.extend(query_point(node.right, x))
        else:
            for lo, hi, iid in node.by_lo:
                result.append(iid)
        return result

    root = build(intervals)

    results = {}
    for x in queries:
        ids = query_point(root, x)
        results[x] = sorted(ids)
    return results
"""

BUG_DESC = (
    "When querying for x < center, the bug scans the by_hi list instead of "
    "by_lo, and when x > center, it scans by_lo instead of by_hi. This swaps "
    "the scanning logic: the early-termination condition works on the wrong "
    "sort order, causing intervals to be missed or spuriously included."
)


def SPEC(intervals, queries, result):
    """Compare to brute force: for each query x, find all intervals with lo <= x <= hi."""
    for x in queries:
        if x not in result:
            return False
        # Brute force
        expected = sorted(
            iid for lo, hi, iid in intervals if lo <= x <= hi
        )
        if result[x] != expected:
            return False
    return True


def _gen_input():
    # The bug swaps by_lo and by_hi scanning:
    # - When x < center, it scans by_hi (sorted by hi DESC) with hi >= x
    #   instead of by_lo (sorted by lo ASC) with lo <= x
    # - When x > center, it scans by_lo (sorted by lo ASC) with lo <= x
    #   instead of by_hi (sorted by hi DESC) with hi >= x
    #
    # To trigger: we need center intervals where scanning the wrong sorted
    # list with early termination misses some intervals.
    # Example: intervals crossing center where some have lo <= x but hi is small
    # (so they appear late in by_hi and get cut off by early termination).

    # Use small fixed values to keep within max_size=8
    # Center will be median of endpoints
    # Create intervals that all cross a center point but have varied lo/hi
    center = 5
    intervals = [
        (1, 5, 0),   # lo=1, hi=5: crosses center, low hi
        (3, 5, 1),   # lo=3, hi=5: crosses center, low hi
        (1, 9, 2),   # lo=1, hi=9: crosses center, high hi
        (4, 8, 3),   # lo=4, hi=8: crosses center, high hi
        (2, 6, 4),   # lo=2, hi=6: crosses center, medium hi
    ]
    # Query x=3, which is < center=5
    # CORRECT: scans by_lo (sorted by lo ASC): (1,5,0),(1,9,2),(2,6,4),(3,5,1),(4,8,3)
    #   lo <= 3: ids 0,2,4,1 -> stops at (4,8,3) since lo=4 > 3
    # BUGGY: scans by_hi (sorted by hi DESC): (1,9,2),(4,8,3),(2,6,4),(1,5,0),(3,5,1)
    #   hi >= 3: ids 2,3,4,0,1 -> all pass! Returns too many OR
    # Actually buggy scans by_hi with hi >= x. Let me check...
    # For x=3 < center=5, buggy scans by_hi checking hi >= 3:
    # by_hi desc: (1,9,2),(4,8,3),(2,6,4),(1,5,0),(3,5,1) -> all have hi >= 3
    # So buggy returns all 5, but correct returns only those with lo <= 3: 0,2,4,1 (not 3)
    # Interval 3 has lo=4 > 3, so correct excludes it. Buggy includes it. -> different!

    # Query x=7, which is > center=5
    # CORRECT: scans by_hi (sorted by hi DESC): (1,9,2),(4,8,3),(2,6,4),(1,5,0),(3,5,1)
    #   hi >= 7: ids 2,3 -> stops at (2,6,4) since hi=6 < 7
    # BUGGY: scans by_lo (sorted by lo ASC): (1,5,0),(1,9,2),(2,6,4),(3,5,1),(4,8,3)
    #   lo <= 7: ids 0,2,4,1,3 -> all pass! But 0 has hi=5 < 7. -> wrong

    queries = [3, 7]
    return {"intervals": intervals, "queries": queries}


INPUT_OVERRIDES = {"_gen": _gen_input}
