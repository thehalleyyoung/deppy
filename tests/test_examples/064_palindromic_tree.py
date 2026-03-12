"""Eertree (palindromic tree) construction.

Bug: when extending by character c, follows suffix links but checks
the wrong character position (i - len - 1 instead of i - len(current) - 1),
causing incorrect palindrome detection and wrong tree structure.
"""

CORRECT = r"""
def solve(s):
    class PalNode:
        def __init__(self, length, suffix_link=None):
            self.length = length
            self.suffix_link = suffix_link
            self.edges = {}
            self.count = 0

    odd_root = PalNode(-1)
    even_root = PalNode(0)
    odd_root.suffix_link = odd_root
    even_root.suffix_link = odd_root

    nodes = [odd_root, even_root]
    current = even_root

    for i in range(len(s)):
        c = s[i]
        cur = current
        while True:
            pos = i - cur.length - 1
            if pos >= 0 and s[pos] == c:
                break
            cur = cur.suffix_link

        if c in cur.edges:
            current = cur.edges[c]
            current.count += 1
            continue

        new_len = cur.length + 2
        new_node = PalNode(new_len)
        new_node.count = 1

        link = cur.suffix_link
        while True:
            pos = i - link.length - 1
            if pos >= 0 and s[pos] == c:
                break
            link = link.suffix_link

        if c in link.edges:
            new_node.suffix_link = link.edges[c]
        else:
            new_node.suffix_link = even_root

        cur.edges[c] = new_node
        nodes.append(new_node)
        current = new_node

    for node in reversed(nodes[2:]):
        if node.suffix_link is not None and node.suffix_link is not odd_root:
            node.suffix_link.count += node.count

    palindromes = {}
    for node in nodes[2:]:
        length = node.length
        palindromes[length] = palindromes.get(length, 0) + node.count

    distinct_count = len(nodes) - 2
    total_occurrences = sum(node.count for node in nodes[2:])
    return {"distinct": distinct_count, "total": total_occurrences, "by_length": palindromes}

s = TEXT
result = solve(s)
"""

BUGGY = r"""
def solve(s):
    class PalNode:
        def __init__(self, length, suffix_link=None):
            self.length = length
            self.suffix_link = suffix_link
            self.edges = {}
            self.count = 0

    odd_root = PalNode(-1)
    even_root = PalNode(0)
    odd_root.suffix_link = odd_root
    even_root.suffix_link = odd_root

    nodes = [odd_root, even_root]
    current = even_root

    for i in range(len(s)):
        c = s[i]
        cur = current
        while True:
            # BUG: uses i - cur.length instead of i - cur.length - 1
            pos = i - cur.length
            if pos >= 0 and pos < len(s) and s[pos] == c:
                break
            cur = cur.suffix_link

        if c in cur.edges:
            current = cur.edges[c]
            current.count += 1
            continue

        new_len = cur.length + 2
        new_node = PalNode(new_len)
        new_node.count = 1

        link = cur.suffix_link
        while True:
            # Same bug in suffix link search
            pos = i - link.length
            if pos >= 0 and pos < len(s) and s[pos] == c:
                break
            link = link.suffix_link

        if c in link.edges:
            new_node.suffix_link = link.edges[c]
        else:
            new_node.suffix_link = even_root

        cur.edges[c] = new_node
        nodes.append(new_node)
        current = new_node

    for node in reversed(nodes[2:]):
        if node.suffix_link is not None and node.suffix_link is not odd_root:
            node.suffix_link.count += node.count

    palindromes = {}
    for node in nodes[2:]:
        length = node.length
        palindromes[length] = palindromes.get(length, 0) + node.count

    distinct_count = len(nodes) - 2
    total_occurrences = sum(node.count for node in nodes[2:])
    return {"distinct": distinct_count, "total": total_occurrences, "by_length": palindromes}

s = TEXT
result = solve(s)
"""


def SPEC(text, result):
    # Brute-force: find all palindromic substrings
    if not isinstance(result, dict):
        return False
    if "distinct" not in result or "total" not in result:
        return False

    s = text
    n = len(s)
    palindrome_set = set()
    total_count = 0

    for i in range(n):
        for j in range(i + 1, n + 1):
            sub = s[i:j]
            if sub == sub[::-1]:
                palindrome_set.add(sub)
                total_count += 1

    expected_distinct = len(palindrome_set)
    expected_total = total_count

    if result["distinct"] != expected_distinct:
        return False
    if result["total"] != expected_total:
        return False

    # Verify by_length breakdown
    by_length = {}
    for i in range(n):
        for j in range(i + 1, n + 1):
            sub = s[i:j]
            if sub == sub[::-1]:
                length = len(sub)
                by_length[length] = by_length.get(length, 0) + 1

    if result.get("by_length") != by_length:
        return False

    return True


BUG_DESC = (
    "When checking whether a palindrome can be extended, uses position "
    "i - cur.length instead of i - cur.length - 1. This off-by-one error "
    "checks the wrong character, causing palindromes to be misidentified "
    "and the tree to have incorrect structure and counts."
)


def _gen():
    import random
    # Generate strings with repeated characters to ensure palindromes
    alphabet = "abc"
    length = random.randint(8, 16)
    s = "".join(random.choice(alphabet) for _ in range(length))
    return s


INPUT_OVERRIDES = {"TEXT": _gen}
