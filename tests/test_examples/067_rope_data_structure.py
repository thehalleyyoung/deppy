"""Rope (balanced binary tree of strings) for efficient string concatenation and indexing.

Bug: in the index operation, when going right, subtracts left.length but
should subtract left.length + 1 (off-by-one in rank calculation), causing
character lookups to be shifted by one position in the right subtree.
"""

CORRECT = r"""
class RopeNode:
    def __init__(self, text=None, left=None, right=None):
        if text is not None:
            self.text = text
            self.left = None
            self.right = None
            self.length = len(text)
            self.depth = 0
        else:
            self.text = None
            self.left = left
            self.right = right
            self.length = (left.length if left else 0) + (right.length if right else 0)
            self.depth = 1 + max(
                left.depth if left else 0,
                right.depth if right else 0
            )

def rope_from_string(s):
    if len(s) <= 8:
        return RopeNode(text=s)
    mid = len(s) // 2
    left = rope_from_string(s[:mid])
    right = rope_from_string(s[mid:])
    return RopeNode(left=left, right=right)

def rope_concat(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return RopeNode(left=a, right=b)

def rope_index(node, idx):
    # CORRECT: standard rope indexing
    if node.text is not None:
        return node.text[idx]
    left_len = node.left.length if node.left else 0
    if idx < left_len:
        return rope_index(node.left, idx)
    else:
        # CORRECT: subtract left_len (0-indexed)
        return rope_index(node.right, idx - left_len)

def rope_split(node, idx):
    # Split rope into [0..idx) and [idx..length)
    if node is None:
        return None, None
    if node.text is not None:
        if idx <= 0:
            return None, node
        if idx >= len(node.text):
            return node, None
        return RopeNode(text=node.text[:idx]), RopeNode(text=node.text[idx:])
    left_len = node.left.length if node.left else 0
    if idx <= left_len:
        ll, lr = rope_split(node.left, idx)
        return ll, RopeNode(left=lr, right=node.right)
    else:
        rl, rr = rope_split(node.right, idx - left_len)
        return RopeNode(left=node.left, right=rl), rr

def rope_insert(node, idx, text):
    new_rope = rope_from_string(text)
    left, right = rope_split(node, idx)
    return rope_concat(rope_concat(left, new_rope), right)

def rope_delete(node, start, end):
    left, temp = rope_split(node, start)
    _, right = rope_split(temp, end - start)
    return rope_concat(left, right)

def rope_to_string(node):
    if node is None:
        return ""
    if node.text is not None:
        return node.text
    return rope_to_string(node.left) + rope_to_string(node.right)

def rope_substring(node, start, end):
    chars = []
    for i in range(start, end):
        chars.append(rope_index(node, i))
    return "".join(chars)

data = DATA
rope = rope_from_string(data["initial"])
results = []

for op in data["ops"]:
    if op[0] == "index":
        idx = op[1]
        results.append(rope_index(rope, idx))
    elif op[0] == "insert":
        idx, text = op[1], op[2]
        rope = rope_insert(rope, idx, text)
        results.append("ok")
    elif op[0] == "delete":
        start, end = op[1], op[2]
        rope = rope_delete(rope, start, end)
        results.append("ok")
    elif op[0] == "substring":
        start, end = op[1], op[2]
        results.append(rope_substring(rope, start, end))
    elif op[0] == "to_string":
        results.append(rope_to_string(rope))

result = results
"""

BUGGY = r"""
class RopeNode:
    def __init__(self, text=None, left=None, right=None):
        if text is not None:
            self.text = text
            self.left = None
            self.right = None
            self.length = len(text)
            self.depth = 0
        else:
            self.text = None
            self.left = left
            self.right = right
            self.length = (left.length if left else 0) + (right.length if right else 0)
            self.depth = 1 + max(
                left.depth if left else 0,
                right.depth if right else 0
            )

def rope_from_string(s):
    if len(s) <= 8:
        return RopeNode(text=s)
    mid = len(s) // 2
    left = rope_from_string(s[:mid])
    right = rope_from_string(s[mid:])
    return RopeNode(left=left, right=right)

def rope_concat(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return RopeNode(left=a, right=b)

def rope_index(node, idx):
    if node.text is not None:
        return node.text[idx]
    left_len = node.left.length if node.left else 0
    if idx < left_len:
        return rope_index(node.left, idx)
    else:
        # BUG: subtracts left_len + 1 instead of left_len
        # Off-by-one: shifts all right-subtree lookups by 1
        return rope_index(node.right, idx - left_len - 1)

def rope_split(node, idx):
    if node is None:
        return None, None
    if node.text is not None:
        if idx <= 0:
            return None, node
        if idx >= len(node.text):
            return node, None
        return RopeNode(text=node.text[:idx]), RopeNode(text=node.text[idx:])
    left_len = node.left.length if node.left else 0
    if idx <= left_len:
        ll, lr = rope_split(node.left, idx)
        return ll, RopeNode(left=lr, right=node.right)
    else:
        rl, rr = rope_split(node.right, idx - left_len)
        return RopeNode(left=node.left, right=rl), rr

def rope_insert(node, idx, text):
    new_rope = rope_from_string(text)
    left, right = rope_split(node, idx)
    return rope_concat(rope_concat(left, new_rope), right)

def rope_delete(node, start, end):
    left, temp = rope_split(node, start)
    _, right = rope_split(temp, end - start)
    return rope_concat(left, right)

def rope_to_string(node):
    if node is None:
        return ""
    if node.text is not None:
        return node.text
    return rope_to_string(node.left) + rope_to_string(node.right)

def rope_substring(node, start, end):
    chars = []
    for i in range(start, end):
        chars.append(rope_index(node, i))
    return "".join(chars)

data = DATA
rope = rope_from_string(data["initial"])
results = []

for op in data["ops"]:
    if op[0] == "index":
        idx = op[1]
        results.append(rope_index(rope, idx))
    elif op[0] == "insert":
        idx, text = op[1], op[2]
        rope = rope_insert(rope, idx, text)
        results.append("ok")
    elif op[0] == "delete":
        start, end = op[1], op[2]
        rope = rope_delete(rope, start, end)
        results.append("ok")
    elif op[0] == "substring":
        start, end = op[1], op[2]
        results.append(rope_substring(rope, start, end))
    elif op[0] == "to_string":
        results.append(rope_to_string(rope))

result = results
"""


def SPEC(data, result):
    # Simulate with a plain string
    s = data["initial"]
    ops = data["ops"]

    if not isinstance(result, list):
        return False
    if len(result) != len(ops):
        return False

    for i, op in enumerate(ops):
        if op[0] == "index":
            idx = op[1]
            if idx < 0 or idx >= len(s):
                return False
            if result[i] != s[idx]:
                return False
        elif op[0] == "insert":
            idx, text = op[1], op[2]
            s = s[:idx] + text + s[idx:]
            if result[i] != "ok":
                return False
        elif op[0] == "delete":
            start, end = op[1], op[2]
            s = s[:start] + s[end:]
            if result[i] != "ok":
                return False
        elif op[0] == "substring":
            start, end = op[1], op[2]
            expected = s[start:end]
            if result[i] != expected:
                return False
        elif op[0] == "to_string":
            if result[i] != s:
                return False
    return True


BUG_DESC = (
    "In rope_index, when traversing to the right subtree, subtracts "
    "left_len + 1 instead of left_len. This off-by-one shifts all "
    "right-subtree character lookups, causing index and substring "
    "operations to return wrong characters."
)


def _gen():
    # The bug: rope_index subtracts left_len + 1 instead of left_len when
    # going to the right subtree. This shifts all right-subtree lookups by 1.
    #
    # rope_from_string splits at len/2 when len > 8, creating internal nodes.
    # For a 16-char string "abcdefghijklmnop":
    #   root.left = leaf "abcdefgh" (length 8)
    #   root.right = leaf "ijklmnop" (length 8)
    #
    # rope_index(root, 8) should return 'i' (the 9th char, 0-indexed).
    # Correct: idx=8 >= left_len=8, so recurse right with idx - 8 = 0 -> 'i'
    # Buggy: idx=8 >= left_len=8, so recurse right with idx - 8 - 1 = -1 -> crash or wrong
    #
    # rope_index(root, 9) should return 'j'.
    # Buggy: recurse right with 9 - 8 - 1 = 0 -> returns 'i' instead of 'j'
    #
    # Use distinct chars so wrong lookups are always detectable.
    # String must be >8 chars to have internal nodes.
    initial = "abcdefghijklmnop"  # 16 chars, will split into two 8-char leaves
    ops = [
        # These indices are in the right subtree (>= 8), bug shifts them
        ["index", 8],       # should be 'i', buggy gives wrong char or crashes
        ["index", 9],       # should be 'j', buggy gives 'i'
        ["index", 12],      # should be 'm', buggy gives 'l'
        ["index", 15],      # should be 'p', buggy gives 'o'
        # Also test substring spanning left and right subtrees
        ["substring", 6, 12],  # should be "ghijkl", buggy will be wrong
        # Full dump to verify everything
        ["to_string"],
    ]
    return {"initial": initial, "ops": ops}


INPUT_OVERRIDES = {"DATA": _gen}
