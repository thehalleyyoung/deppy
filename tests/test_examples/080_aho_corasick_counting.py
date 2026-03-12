"""Aho-Corasick automaton for counting total occurrences of all patterns.
Bug: when traversing failure links to count matches, stops at the first
failure link match instead of following the entire suffix link chain."""

CORRECT = r"""
# Aho-Corasick algorithm for multi-pattern string matching
# Counts total occurrences of all patterns in the text

class AhoCorasickNode:
    def __init__(self):
        self.children = {}
        self.fail = 0
        self.output = []  # list of pattern indices that end here
        self.dict_suffix = -1  # suffix link to nearest node with output

def build_automaton(patterns):
    # Build trie
    root = AhoCorasickNode()
    nodes = [root]

    for pi, pattern in enumerate(patterns):
        cur = 0
        for ch in pattern:
            if ch not in nodes[cur].children:
                nodes[cur].children[ch] = len(nodes)
                nodes.append(AhoCorasickNode())
            cur = nodes[cur].children[ch]
        nodes[cur].output.append(pi)

    # Build failure links via BFS
    queue = []
    for ch, nid in nodes[0].children.items():
        nodes[nid].fail = 0
        queue.append(nid)

    head = 0
    while head < len(queue):
        u = queue[head]
        head += 1
        for ch, v in nodes[u].children.items():
            queue.append(v)
            f = nodes[u].fail
            while f != 0 and ch not in nodes[f].children:
                f = nodes[f].fail
            nodes[v].fail = nodes[f].children.get(ch, 0)
            if nodes[v].fail == v:
                nodes[v].fail = 0
            # Set dict suffix link
            if nodes[nodes[v].fail].output:
                nodes[v].dict_suffix = nodes[v].fail
            else:
                nodes[v].dict_suffix = nodes[nodes[v].fail].dict_suffix

    return nodes

def count_matches(text, nodes):
    # CORRECT: follows entire dict suffix chain to count all matches
    total = 0
    cur = 0
    for ch in text:
        while cur != 0 and ch not in nodes[cur].children:
            cur = nodes[cur].fail
        cur = nodes[cur].children.get(ch, 0)
        # Count outputs at current node
        total += len(nodes[cur].output)
        # Follow dict suffix links to count all pattern matches
        temp = nodes[cur].dict_suffix
        while temp != -1:
            total += len(nodes[temp].output)
            temp = nodes[temp].dict_suffix
    return total

patterns = list(PATTERNS)
text = TEXT
nodes = build_automaton(patterns)
result = count_matches(text, nodes)
"""

BUGGY = r"""
# Aho-Corasick algorithm for multi-pattern string matching
# Counts total occurrences of all patterns in the text

class AhoCorasickNode:
    def __init__(self):
        self.children = {}
        self.fail = 0
        self.output = []
        self.dict_suffix = -1

def build_automaton(patterns):
    root = AhoCorasickNode()
    nodes = [root]

    for pi, pattern in enumerate(patterns):
        cur = 0
        for ch in pattern:
            if ch not in nodes[cur].children:
                nodes[cur].children[ch] = len(nodes)
                nodes.append(AhoCorasickNode())
            cur = nodes[cur].children[ch]
        nodes[cur].output.append(pi)

    queue = []
    for ch, nid in nodes[0].children.items():
        nodes[nid].fail = 0
        queue.append(nid)

    head = 0
    while head < len(queue):
        u = queue[head]
        head += 1
        for ch, v in nodes[u].children.items():
            queue.append(v)
            f = nodes[u].fail
            while f != 0 and ch not in nodes[f].children:
                f = nodes[f].fail
            nodes[v].fail = nodes[f].children.get(ch, 0)
            if nodes[v].fail == v:
                nodes[v].fail = 0
            if nodes[nodes[v].fail].output:
                nodes[v].dict_suffix = nodes[v].fail
            else:
                nodes[v].dict_suffix = nodes[nodes[v].fail].dict_suffix

    return nodes

def count_matches(text, nodes):
    # BUG: only follows dict_suffix once instead of the full chain
    total = 0
    cur = 0
    for ch in text:
        while cur != 0 and ch not in nodes[cur].children:
            cur = nodes[cur].fail
        cur = nodes[cur].children.get(ch, 0)
        total += len(nodes[cur].output)
        # BUG: only checks one level of dict suffix, not the full chain
        temp = nodes[cur].dict_suffix
        if temp != -1:
            total += len(nodes[temp].output)
            # Missing: should continue following temp = nodes[temp].dict_suffix
    return total

patterns = list(PATTERNS)
text = TEXT
nodes = build_automaton(patterns)
result = count_matches(text, nodes)
"""


def SPEC(patterns, text, result):
    # Naive: count all occurrences of all patterns in text
    total = 0
    for pattern in patterns:
        if not pattern:
            continue
        start = 0
        while True:
            idx = text.find(pattern, start)
            if idx == -1:
                break
            total += 1
            start = idx + 1
    return result == total


BUG_DESC = (
    "In count_matches, when following dictionary suffix links to find all "
    "pattern matches at a position, only follows one level (if temp != -1, "
    "count and stop) instead of following the entire chain with a while loop. "
    "This misses patterns that are suffixes of suffixes, undercounting when "
    "three or more patterns form a nested suffix chain (e.g., 'c', 'bc', 'abc')."
)


def _gen_patterns():
    import random
    # Create patterns with suffix relationships to trigger the bug
    base_patterns = ['a', 'ba', 'cba', 'ab', 'b']
    n = random.randint(3, 5)
    return random.sample(base_patterns, min(n, len(base_patterns)))


def _gen_text():
    import random
    # Include substrings that match nested patterns
    segments = ['cba', 'abba', 'ba', 'cba', 'abc']
    n = random.randint(3, 6)
    return ''.join(random.choices(segments, k=n))


INPUT_OVERRIDES = {"PATTERNS": _gen_patterns, "TEXT": _gen_text}
