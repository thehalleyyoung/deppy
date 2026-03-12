"""Suffix automaton (DAWG) construction with distinct substring count and query."""

import random

CORRECT = """
def solve(s, queries):
    # State: len, link, transitions
    # We use dicts for states
    INIT = 0
    states = [{"len": 0, "link": -1, "trans": {}}]  # initial state
    last = INIT
    size = 1

    def sa_extend(c):
        nonlocal last, size
        cur = size
        states.append({"len": states[last]["len"] + 1, "link": -1, "trans": {}})
        size += 1
        p = last
        while p != -1 and c not in states[p]["trans"]:
            states[p]["trans"][c] = cur
            p = states[p]["link"]
        if p == -1:
            states[cur]["link"] = INIT
        else:
            q = states[p]["trans"][c]
            if states[p]["len"] + 1 == states[q]["len"]:
                states[cur]["link"] = q
            else:
                # Clone q
                clone = size
                states.append({
                    "len": states[p]["len"] + 1,
                    "link": states[q]["link"],
                    "trans": dict(states[q]["trans"]),
                })
                size += 1
                while p != -1 and states[p]["trans"].get(c) == q:
                    states[p]["trans"][c] = clone
                    p = states[p]["link"]
                states[q]["link"] = clone
                states[cur]["link"] = clone
        last = cur

    for c in s:
        sa_extend(c)

    # Count distinct substrings: sum of (len - link.len) for all non-initial
    num_distinct = 0
    for i in range(1, size):
        link = states[i]["link"]
        parent_len = states[link]["len"] if link >= 0 else 0
        num_distinct += states[i]["len"] - parent_len

    # Answer substring queries
    def is_substring(pattern):
        cur = INIT
        for c in pattern:
            if c not in states[cur]["trans"]:
                return False
            cur = states[cur]["trans"][c]
        return True

    query_results = [is_substring(q) for q in queries]
    return (num_distinct, query_results)
"""

BUGGY = """
def solve(s, queries):
    INIT = 0
    states = [{"len": 0, "link": -1, "trans": {}}]
    last = INIT
    size = 1

    def sa_extend(c):
        nonlocal last, size
        cur = size
        states.append({"len": states[last]["len"] + 1, "link": -1, "trans": {}})
        size += 1
        p = last
        while p != -1 and c not in states[p]["trans"]:
            states[p]["trans"][c] = cur
            p = states[p]["link"]
        if p == -1:
            states[cur]["link"] = INIT
        else:
            q = states[p]["trans"][c]
            if states[p]["len"] + 1 == states[q]["len"]:
                states[cur]["link"] = q
            else:
                # Clone q — BUG: clone's suffix link set to INIT
                # instead of states[q]["link"]
                clone = size
                states.append({
                    "len": states[p]["len"] + 1,
                    "link": INIT,  # BUG: should be states[q]["link"]
                    "trans": dict(states[q]["trans"]),
                })
                size += 1
                while p != -1 and states[p]["trans"].get(c) == q:
                    states[p]["trans"][c] = clone
                    p = states[p]["link"]
                states[q]["link"] = clone
                states[cur]["link"] = clone
        last = cur

    for c in s:
        sa_extend(c)

    # Count distinct substrings
    num_distinct = 0
    for i in range(1, size):
        link = states[i]["link"]
        parent_len = states[link]["len"] if link >= 0 else 0
        num_distinct += states[i]["len"] - parent_len

    def is_substring(pattern):
        cur = INIT
        for c in pattern:
            if c not in states[cur]["trans"]:
                return False
            cur = states[cur]["trans"][c]
        return True

    query_results = [is_substring(q) for q in queries]
    return (num_distinct, query_results)
"""

BUG_DESC = (
    "When cloning a state during suffix automaton construction, the clone's "
    "suffix link is set to the initial state (INIT) instead of the original "
    "state's suffix link. This breaks the suffix link tree, causing the "
    "distinct substring count (computed via len - link.len) to be incorrect."
)


def SPEC(s, queries, result):
    """Verify suffix automaton results."""
    num_distinct, query_results = result
    n = len(s)

    # (1) Brute force distinct substring count
    all_subs = set()
    for i in range(n):
        for j in range(i + 1, n + 1):
            all_subs.add(s[i:j])
    if num_distinct != len(all_subs):
        return False

    # (2) All true substrings return True
    for q, res in zip(queries, query_results):
        is_sub = q in all_subs or q == ""
        # Actually check membership more directly
        actually_sub = any(
            s[i:i + len(q)] == q
            for i in range(len(s) - len(q) + 1)
        ) if len(q) <= len(s) and len(q) > 0 else (len(q) == 0)
        if res != actually_sub:
            return False

    return True


def _gen_input():
    alphabet = "abc"
    length = random.randint(8, 15)
    s = "".join(random.choice(alphabet) for _ in range(length))

    queries = []
    n = len(s)
    # Add some true substrings
    for _ in range(random.randint(3, 5)):
        i = random.randint(0, n - 1)
        j = random.randint(i + 1, min(i + 5, n))
        queries.append(s[i:j])
    # Add some non-substrings
    for _ in range(random.randint(2, 3)):
        fake = "".join(random.choice("abcxyz") for _ in range(random.randint(2, 5)))
        queries.append(fake)

    return {"s": s, "queries": queries}


INPUT_OVERRIDES = {"_gen": _gen_input}
