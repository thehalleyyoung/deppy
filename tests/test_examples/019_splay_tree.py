"""Splay tree with splay, insert, search, and inorder traversal.

Bug: In the zig-zag case of the splay operation, the correct algorithm performs
a double rotation (rotate child, then rotate target). The bug instead performs
two rotations in the zig-zig pattern (rotate parent, then rotate target), which
does not correctly bring the target to the root and can violate the BST property
after the malformed rotation sequence.
"""

CORRECT = r"""
class SplayNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.parent = None

def left_rotate(x):
    y = x.right
    x.right = y.left
    if y.left is not None:
        y.left.parent = x
    y.parent = x.parent
    if x.parent is None:
        pass
    elif x == x.parent.left:
        x.parent.left = y
    else:
        x.parent.right = y
    y.left = x
    x.parent = y
    return y

def right_rotate(x):
    y = x.left
    x.left = y.right
    if y.right is not None:
        y.right.parent = x
    y.parent = x.parent
    if x.parent is None:
        pass
    elif x == x.parent.right:
        x.parent.right = y
    else:
        x.parent.left = y
    y.right = x
    x.parent = y
    return y

def splay(root, node):
    while node.parent is not None:
        parent = node.parent
        grandparent = parent.parent
        if grandparent is None:
            # Zig step
            if node == parent.left:
                right_rotate(parent)
            else:
                left_rotate(parent)
        elif node == parent.left and parent == grandparent.left:
            # Zig-zig (left-left)
            right_rotate(grandparent)
            right_rotate(parent)
        elif node == parent.right and parent == grandparent.right:
            # Zig-zig (right-right)
            left_rotate(grandparent)
            left_rotate(parent)
        elif node == parent.right and parent == grandparent.left:
            # CORRECT zig-zag: rotate parent left, then grandparent right
            left_rotate(parent)
            right_rotate(grandparent)
        else:
            # CORRECT zig-zag: rotate parent right, then grandparent left
            right_rotate(parent)
            left_rotate(grandparent)
    return node

def splay_insert(root, key):
    if root is None:
        return SplayNode(key)
    current = root
    parent = None
    while current is not None:
        parent = current
        if key < current.key:
            current = current.left
        elif key > current.key:
            current = current.right
        else:
            return splay(root, current)
    new_node = SplayNode(key)
    new_node.parent = parent
    if key < parent.key:
        parent.left = new_node
    else:
        parent.right = new_node
    return splay(root, new_node)

def splay_search(root, key):
    current = root
    last = None
    while current is not None:
        last = current
        if key < current.key:
            current = current.left
        elif key > current.key:
            current = current.right
        else:
            new_root = splay(root, current)
            return new_root, True
    if last is not None:
        new_root = splay(root, last)
        return new_root, False
    return root, False

def inorder(node):
    result = []
    stack = []
    current = node
    while current is not None or stack:
        while current is not None:
            stack.append(current)
            current = current.left
        current = stack.pop()
        result.append(current.key)
        current = current.right
    return result

def process_operations(operations):
    root = None
    search_results = []
    for op in operations:
        if op[0] == 'insert':
            root = splay_insert(root, op[1])
        elif op[0] == 'search':
            root, found = splay_search(root, op[1])
            search_results.append((op[1], found))
    traversal = inorder(root)
    return search_results, traversal

ops = OPERATIONS
result = process_operations(ops)
"""

BUGGY = r"""
class SplayNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.parent = None

def left_rotate(x):
    y = x.right
    x.right = y.left
    if y.left is not None:
        y.left.parent = x
    y.parent = x.parent
    if x.parent is None:
        pass
    elif x == x.parent.left:
        x.parent.left = y
    else:
        x.parent.right = y
    y.left = x
    x.parent = y
    return y

def right_rotate(x):
    y = x.left
    x.left = y.right
    if y.right is not None:
        y.right.parent = x
    y.parent = x.parent
    if x.parent is None:
        pass
    elif x == x.parent.right:
        x.parent.right = y
    else:
        x.parent.left = y
    y.right = x
    x.parent = y
    return y

def splay(root, node):
    steps = 0
    while node.parent is not None and steps < 200:
        steps += 1
        parent = node.parent
        grandparent = parent.parent
        if grandparent is None:
            # Zig step
            if node == parent.left:
                right_rotate(parent)
            else:
                left_rotate(parent)
        elif node == parent.left and parent == grandparent.left:
            # Zig-zig (left-left)
            right_rotate(grandparent)
            right_rotate(parent)
        elif node == parent.right and parent == grandparent.right:
            # Zig-zig (right-right)
            left_rotate(grandparent)
            left_rotate(parent)
        elif node == parent.right and parent == grandparent.left:
            # BUG: applies zig-zig pattern instead of zig-zag
            # Should be: left_rotate(parent), right_rotate(grandparent)
            # Instead does: right_rotate(grandparent), left_rotate(parent)
            right_rotate(grandparent)
            left_rotate(parent)
        else:
            # BUG: applies zig-zig pattern instead of zig-zag
            # Should be: right_rotate(parent), left_rotate(grandparent)
            # Instead does: left_rotate(grandparent), right_rotate(parent)
            left_rotate(grandparent)
            right_rotate(parent)
    return node

def splay_insert(root, key):
    if root is None:
        return SplayNode(key)
    current = root
    parent = None
    while current is not None:
        parent = current
        if key < current.key:
            current = current.left
        elif key > current.key:
            current = current.right
        else:
            return splay(root, current)
    new_node = SplayNode(key)
    new_node.parent = parent
    if key < parent.key:
        parent.left = new_node
    else:
        parent.right = new_node
    return splay(root, new_node)

def splay_search(root, key):
    current = root
    last = None
    while current is not None:
        last = current
        if key < current.key:
            current = current.left
        elif key > current.key:
            current = current.right
        else:
            new_root = splay(root, current)
            return new_root, True
    if last is not None:
        new_root = splay(root, last)
        return new_root, False
    return root, False

def inorder(node):
    result = []
    stack = []
    current = node
    while current is not None or stack:
        while current is not None:
            stack.append(current)
            current = current.left
        current = stack.pop()
        result.append(current.key)
        current = current.right
    return result

def process_operations(operations):
    root = None
    search_results = []
    for op in operations:
        if op[0] == 'insert':
            root = splay_insert(root, op[1])
        elif op[0] == 'search':
            root, found = splay_search(root, op[1])
            search_results.append((op[1], found))
    traversal = inorder(root)
    return search_results, traversal

ops = OPERATIONS
result = process_operations(ops)
"""


def SPEC(OPERATIONS, result):
    """Verify splay tree correctness:
    1) Inorder traversal is sorted (BST property maintained).
    2) All inserted keys appear in the traversal.
    3) Search results are correct (found iff key was previously inserted).
    """
    if not isinstance(result, tuple) or len(result) != 2:
        return False

    search_results, traversal = result

    # Check inorder traversal is sorted
    if not isinstance(traversal, list):
        return False
    for i in range(len(traversal) - 1):
        if traversal[i] >= traversal[i + 1]:
            return False

    # Track which keys have been inserted
    inserted = set()
    search_idx = 0
    for op in OPERATIONS:
        if op[0] == 'insert':
            inserted.add(op[1])
        elif op[0] == 'search':
            if search_idx >= len(search_results):
                return False
            key, found = search_results[search_idx]
            if key != op[1]:
                return False
            expected = op[1] in inserted
            if found != expected:
                return False
            search_idx += 1

    # All inserted keys must appear in traversal
    traversal_set = set(traversal)
    if inserted != traversal_set:
        return False

    return True


BUG_DESC = (
    "In the zig-zag cases of the splay operation, the bug applies rotations in "
    "the zig-zig order (rotate grandparent first, then parent) instead of the "
    "correct zig-zag order (rotate parent first, then grandparent). This performs "
    "the wrong structural transformation, potentially violating the BST property "
    "and producing incorrect inorder traversals and search results."
)


def _generate_operations():
    import random
    ops = []
    n_inserts = random.randint(10, 15)
    keys = random.sample(range(1, 31), n_inserts)
    for k in keys:
        ops.append(('insert', k))
    # Search for some inserted and some non-inserted keys
    for _ in range(random.randint(5, 8)):
        if random.random() < 0.6:
            ops.append(('search', random.choice(keys)))
        else:
            ops.append(('search', random.randint(1, 40)))
    return ops


INPUT_OVERRIDES = {
    "OPERATIONS": _generate_operations,
}
