"""Cuckoo hashing with two hash functions.

Bug: when displacing an element, inserts into the same table it came
from instead of the alternate table, causing infinite eviction loops
on some inputs.
"""

CORRECT = r"""
def cuckoo_hash(data):
    keys = data["keys"]
    capacity = data["capacity"]
    max_evictions = capacity * 6

    table1 = [None] * capacity
    table2 = [None] * capacity

    def h1(key):
        x = key * 2654435761
        x = ((x >> 16) ^ x) * 45684174 + 54321
        return x % capacity

    def h2(key):
        x = key * 2246822519
        x = ((x >> 13) ^ x) * 15073261 + 98765
        return x % capacity

    inserted = []
    failed = []

    for key in keys:
        if table1[h1(key)] == key or table2[h2(key)] == key:
            inserted.append(key)
            continue

        current = key
        evictions = 0
        success = True
        use_table1 = True

        while evictions < max_evictions:
            if use_table1:
                pos = h1(current)
                if table1[pos] is None:
                    table1[pos] = current
                    break
                current, table1[pos] = table1[pos], current
                use_table1 = False
            else:
                pos = h2(current)
                if table2[pos] is None:
                    table2[pos] = current
                    break
                current, table2[pos] = table2[pos], current
                use_table1 = True
            evictions += 1
        else:
            success = False

        if success:
            inserted.append(key)
        else:
            failed.append(key)

    lookups = data.get("lookups", [])
    lookup_results = []
    for key in lookups:
        found = (table1[h1(key)] == key) or (table2[h2(key)] == key)
        lookup_results.append(found)

    return {"inserted": sorted(inserted), "failed": sorted(failed),
            "lookups": lookup_results,
            "table1_count": sum(1 for x in table1 if x is not None),
            "table2_count": sum(1 for x in table2 if x is not None)}

data = DATA
result = cuckoo_hash(data)
"""

BUGGY = r"""
def cuckoo_hash(data):
    keys = data["keys"]
    capacity = data["capacity"]
    max_evictions = capacity * 6

    table1 = [None] * capacity
    table2 = [None] * capacity

    def h1(key):
        x = key * 2654435761
        x = ((x >> 16) ^ x) * 45684174 + 54321
        return x % capacity

    def h2(key):
        x = key * 2246822519
        x = ((x >> 13) ^ x) * 15073261 + 98765
        return x % capacity

    inserted = []
    failed = []

    for key in keys:
        if table1[h1(key)] == key or table2[h2(key)] == key:
            inserted.append(key)
            continue

        current = key
        evictions = 0
        success = True
        use_table1 = True

        while evictions < max_evictions:
            if use_table1:
                pos = h1(current)
                if table1[pos] is None:
                    table1[pos] = current
                    break
                current, table1[pos] = table1[pos], current
                # BUG: stays on table1 instead of switching to table2
                use_table1 = True
            else:
                pos = h2(current)
                if table2[pos] is None:
                    table2[pos] = current
                    break
                current, table2[pos] = table2[pos], current
                use_table1 = True
            evictions += 1
        else:
            success = False

        if success:
            inserted.append(key)
        else:
            failed.append(key)

    lookups = data.get("lookups", [])
    lookup_results = []
    for key in lookups:
        found = (table1[h1(key)] == key) or (table2[h2(key)] == key)
        lookup_results.append(found)

    return {"inserted": sorted(inserted), "failed": sorted(failed),
            "lookups": lookup_results,
            "table1_count": sum(1 for x in table1 if x is not None),
            "table2_count": sum(1 for x in table2 if x is not None)}

data = DATA
result = cuckoo_hash(data)
"""


def SPEC(data, result):
    if not isinstance(result, dict):
        return False

    keys = data["keys"]
    capacity = data["capacity"]
    lookups = data.get("lookups", [])

    if "inserted" not in result or "failed" not in result:
        return False
    if "lookups" not in result:
        return False

    inserted = result["inserted"]
    failed = result["failed"]

    # Every key should be in exactly one of inserted or failed
    all_keys = sorted(set(keys))
    accounted = sorted(set(inserted) | set(failed))
    if accounted != all_keys:
        return False

    # No key in both
    if set(inserted) & set(failed):
        return False

    # For a well-sized table, most keys should be inserted
    # With capacity >= 2 * num_keys, all should succeed
    unique_keys = len(set(keys))
    if capacity >= 2 * unique_keys:
        if len(failed) > 0:
            return False

    # table counts should be consistent
    t1 = result.get("table1_count", 0)
    t2 = result.get("table2_count", 0)
    if t1 + t2 != len(set(inserted)):
        return False

    # Lookup results
    if len(result["lookups"]) != len(lookups):
        return False
    for i, key in enumerate(lookups):
        expected = key in set(inserted)
        if result["lookups"][i] != expected:
            return False

    return True


BUG_DESC = (
    "When displacing an element from table1, the code keeps use_table1=True "
    "instead of setting it to False. The displaced element gets reinserted "
    "into the same table, causing a ping-pong loop at the same position "
    "until max_evictions is reached, failing to insert keys that should fit."
)


def _gen():
    import random
    n = random.randint(8, 14)
    capacity = n * 5  # Generous capacity so correct version always succeeds
    keys = random.sample(range(1, 200), n)
    lookups = random.sample(keys, min(5, n)) + [random.randint(201, 300)]
    return {"keys": keys, "capacity": capacity, "lookups": lookups}


INPUT_OVERRIDES = {"DATA": _gen}
