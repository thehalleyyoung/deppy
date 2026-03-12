"""Persistent trie for versioned string set membership. Bug: mutates shared nodes in-place instead of copying on write."""

CORRECT = r"""
# Persistent Trie: each insert creates a new version (root)
# Supports membership queries on any past version

# Node structure: each node is a dict with 'children' and 'is_end'
# We represent nodes as list of dicts for mutability
nodes = []

def new_node():
    idx = len(nodes)
    nodes.append({"children": {}, "is_end": False})
    return idx

def copy_node(src):
    idx = len(nodes)
    # Deep copy children dict (shallow copy of the mapping, not the subtrees)
    nodes.append({"children": dict(nodes[src]["children"]), "is_end": nodes[src]["is_end"]})
    return idx

def insert(root, word):
    # Create new root by copying the old root
    new_root = copy_node(root)
    curr = new_root
    for ch in word:
        if ch in nodes[curr]["children"]:
            # Copy the existing child node to avoid mutating shared structure
            old_child = nodes[curr]["children"][ch]
            new_child = copy_node(old_child)
            nodes[curr]["children"][ch] = new_child
            curr = new_child
        else:
            # Create a brand new node
            child = new_node()
            nodes[curr]["children"][ch] = child
            curr = child
    nodes[curr]["is_end"] = True
    return new_root

def search(root, word):
    curr = root
    for ch in word:
        if ch not in nodes[curr]["children"]:
            return False
        curr = nodes[curr]["children"][ch]
    return nodes[curr]["is_end"]

# Initialize version 0 with empty trie
initial_root = new_node()
versions = [initial_root]

# Process insertions: each creates a new version
for word in WORDS:
    new_root = insert(versions[-1], word)
    versions.append(new_root)

# Process queries: (version_index, word) -> bool
answers = []
for ver, word in QUERIES:
    answers.append(search(versions[ver], word))

result = answers
"""

BUGGY = r"""
# Persistent Trie: each insert creates a new version (root)
# Supports membership queries on any past version

nodes = []

def new_node():
    idx = len(nodes)
    nodes.append({"children": {}, "is_end": False})
    return idx

def copy_node(src):
    idx = len(nodes)
    nodes.append({"children": dict(nodes[src]["children"]), "is_end": nodes[src]["is_end"]})
    return idx

def insert(root, word):
    # Create new root by copying the old root
    new_root = copy_node(root)
    curr = new_root
    for ch in word:
        if ch in nodes[curr]["children"]:
            # BUG: does NOT copy the child node -- just follows the pointer
            # This mutates the shared node in place, corrupting old versions
            curr = nodes[curr]["children"][ch]
        else:
            child = new_node()
            nodes[curr]["children"][ch] = child
            curr = child
    nodes[curr]["is_end"] = True
    return new_root

def search(root, word):
    curr = root
    for ch in word:
        if ch not in nodes[curr]["children"]:
            return False
        curr = nodes[curr]["children"][ch]
    return nodes[curr]["is_end"]

# Initialize version 0 with empty trie
initial_root = new_node()
versions = [initial_root]

# Process insertions: each creates a new version
for word in WORDS:
    new_root = insert(versions[-1], word)
    versions.append(new_root)

# Process queries: (version_index, word) -> bool
answers = []
for ver, word in QUERIES:
    answers.append(search(versions[ver], word))

result = answers
"""


def SPEC(words, queries, result):
    # Simulate: version 0 is empty, version i contains words[0..i-1]
    if len(result) != len(queries):
        return False

    for i, (ver, word) in enumerate(queries):
        # Words in version ver are words[0:ver]
        expected = word in words[:ver]
        if result[i] != expected:
            return False
    return True


BUG_DESC = "When inserting along an existing path, the buggy version follows the shared child pointer without copying, mutating the node in-place and corrupting all earlier versions that share that node."


def _gen_words():
    # Insert words that share prefixes to trigger the bug
    return ["abc", "abd", "xyz", "abf"]


def _gen_queries():
    # Query old versions for words that share prefixes
    # Version 0: empty
    # Version 1: {abc}
    # Version 2: {abc, abd}
    # Version 3: {abc, abd, xyz}
    # Version 4: {abc, abd, xyz, abf}
    return [
        (0, "abc"),   # False: empty
        (1, "abc"),   # True
        (1, "abd"),   # False: not yet inserted
        (2, "abd"),   # True
        (2, "abf"),   # False: not yet inserted
        (1, "abf"),   # False: not yet inserted
        (1, "abd"),   # False: this is the key test -- buggy version corrupts version 1
        (4, "abf"),   # True
        (3, "abf"),   # False: not yet in version 3
        (0, "xyz"),   # False
    ]


INPUT_OVERRIDES = {
    "WORDS": _gen_words,
    "QUERIES": _gen_queries,
}
