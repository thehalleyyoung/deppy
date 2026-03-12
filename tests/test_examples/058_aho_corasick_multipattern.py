"""Aho-Corasick automaton for multiple pattern search.

Bug: when building failure links, skips the immediate children of root,
leaving their failure links as None instead of root, so traversal crashes
or misses matches when falling back from depth-1 nodes.
"""

CORRECT = r"""
from collections import deque

class AhoCorasickNode:
    def __init__(self):
        self.children = {}
        self.fail = None
        self.output = []  # list of pattern indices that end here

def build_automaton(patterns):
    root = AhoCorasickNode()

    # Build trie
    for idx, pat in enumerate(patterns):
        node = root
        for ch in pat:
            if ch not in node.children:
                node.children[ch] = AhoCorasickNode()
            node = node.children[ch]
        node.output.append(idx)

    # Build failure links via BFS
    queue = deque()
    # CORRECT: initialize fail links of root's children to root
    for ch, child in root.children.items():
        child.fail = root
        queue.append(child)

    while queue:
        curr = queue.popleft()
        for ch, child in curr.children.items():
            queue.append(child)
            # Follow failure links to find longest proper suffix
            fail = curr.fail
            while fail is not None and ch not in fail.children:
                fail = fail.fail
            child.fail = fail.children[ch] if fail is not None else root
            if child.fail == child:
                child.fail = root
            # Merge output from failure link
            child.output = child.output + child.fail.output

    return root

def search(text, patterns):
    if not patterns:
        return []
    root = build_automaton(patterns)
    results = []  # list of (position, pattern_index)
    node = root
    for i, ch in enumerate(text):
        while node is not None and ch not in node.children:
            node = node.fail
        if node is None:
            node = root
            continue
        node = node.children[ch]
        for pat_idx in node.output:
            start = i - len(patterns[pat_idx]) + 1
            results.append((start, pat_idx))
    # Sort by position, then pattern index
    results.sort()
    return results

text = TEXT
patterns = PATTERNS
result = search(text, patterns)
"""

BUGGY = r"""
from collections import deque

class AhoCorasickNode:
    def __init__(self):
        self.children = {}
        self.fail = None
        self.output = []

def build_automaton(patterns):
    root = AhoCorasickNode()

    for idx, pat in enumerate(patterns):
        node = root
        for ch in pat:
            if ch not in node.children:
                node.children[ch] = AhoCorasickNode()
            node = node.children[ch]
        node.output.append(idx)

    # Build failure links via BFS
    queue = deque()
    # BUG: skip root's children, their fail links remain None
    for ch, child in root.children.items():
        # Missing: child.fail = root
        queue.append(child)

    while queue:
        curr = queue.popleft()
        for ch, child in curr.children.items():
            queue.append(child)
            fail = curr.fail
            while fail is not None and ch not in fail.children:
                fail = fail.fail
            child.fail = fail.children[ch] if fail is not None else root
            if child.fail == child:
                child.fail = root
            child.output = child.output + child.fail.output

    return root

def search(text, patterns):
    if not patterns:
        return []
    root = build_automaton(patterns)
    results = []
    node = root
    for i, ch in enumerate(text):
        while node is not None and ch not in node.children:
            node = node.fail
        if node is None:
            node = root
            continue
        node = node.children[ch]
        for pat_idx in node.output:
            start = i - len(patterns[pat_idx]) + 1
            results.append((start, pat_idx))
    results.sort()
    return results

text = TEXT
patterns = PATTERNS
result = search(text, patterns)
"""


def SPEC(text, patterns, result):
    if not isinstance(result, list):
        return False

    # Compute ground truth with naive search
    expected = []
    for idx, pat in enumerate(patterns):
        m = len(pat)
        for i in range(len(text) - m + 1):
            if text[i:i + m] == pat:
                expected.append((i, idx))
    expected.sort()

    return result == expected


BUG_DESC = (
    "When building failure links, the immediate children of root are added "
    "to the BFS queue without setting their fail link to root. Their fail "
    "links remain None. When the search traverses up the failure chain from "
    "a depth-1 node on mismatch, it hits None and jumps back to root, "
    "potentially missing matches that overlap with the first character or "
    "crashing if deeper nodes rely on these failure links for output merging."
)


def _gen_text():
    import random
    _gen_text._patterns = None
    # The bug: root's children have fail = None instead of root.
    #
    # This causes two problems:
    # 1. When at a depth-1 node and we see a char not in its children,
    #    we follow fail=None, hit None, and reset to root, skipping the
    #    current character entirely. In correct code, fail=root would check
    #    root's children for that character.
    # 2. For depth-2 nodes, their fail link computation uses curr.fail (the
    #    depth-1 parent's fail). Since that's None, the depth-2 node's fail
    #    is set to root instead of potentially a depth-1 node. This means
    #    output from shorter patterns at depth-1 isn't merged into depth-2 nodes.
    #
    # Concrete trigger: patterns ["a", "ba"] with text "ba".
    # Correct: finds "b" -> no pattern, then "a" at depth-1 of 'a' -> output [0],
    #   also "ba" matched -> output [1]. Results: [(0,1), (1,0)].
    # Buggy: when processing "ba", after matching 'b' we're at depth-1 node for 'b',
    #   then we see 'a'. Node 'b' doesn't have child 'a', so follow fail=None,
    #   which goes to None, resets to root, SKIPS 'a'. Miss the single-char match "a".
    #
    # Even simpler: patterns ["a", "b"] with text "ab".
    # After matching 'a' at root->a (depth 1), we see 'b'. Node 'a' has no child 'b'.
    # Correct: fail=root, root has child 'b', go there, find match for "b" at pos 1.
    # Buggy: fail=None, reset to root, skip 'b'. Miss "b" at position 1.
    #
    # Use patterns that have single-char patterns alongside multi-char ones
    # to maximize the chance of the depth-1 fail link bug being exposed.
    pattern_sets = [
        (["a", "b"], "ab"),           # misses "b" at pos 1
        (["a", "ba"], "ba"),          # misses "a" at pos 1
        (["b", "ab"], "ab"),          # misses "b" at pos 1
        (["a", "b", "ab"], "abab"),   # misses many
        (["he", "she", "his", "hers"], "ahishers"),  # classic; misses overlapping matches
        (["a", "bc", "b"], "abc"),    # misses "b" at pos 1
    ]
    pats, text = random.choice(pattern_sets)
    _gen_text._patterns = pats
    return text


def _gen_patterns():
    return _gen_text._patterns


INPUT_OVERRIDES = {
    "TEXT": _gen_text,
    "PATTERNS": _gen_patterns,
}
