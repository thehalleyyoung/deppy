"""AVL tree insertion with rotations.

Bug: after rotation, doesn't update the height of the rotated node's
old parent, causing future balance factor calculations to be wrong.
"""

CORRECT = r"""
class AVLNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.height = 1

def height(node):
    if node is None:
        return 0
    return node.height

def update_height(node):
    if node is not None:
        node.height = 1 + max(height(node.left), height(node.right))

def balance_factor(node):
    if node is None:
        return 0
    return height(node.left) - height(node.right)

def right_rotate(y):
    x = y.left
    t2 = x.right
    x.right = y
    y.left = t2
    # CORRECT: update both heights
    update_height(y)
    update_height(x)
    return x

def left_rotate(x):
    y = x.right
    t2 = y.left
    y.left = x
    x.right = t2
    # CORRECT: update both heights
    update_height(x)
    update_height(y)
    return y

def insert(node, key):
    if node is None:
        return AVLNode(key)

    if key < node.key:
        node.left = insert(node.left, key)
    elif key > node.key:
        node.right = insert(node.right, key)
    else:
        return node  # no duplicates

    update_height(node)
    bf = balance_factor(node)

    # Left Left
    if bf > 1 and key < node.left.key:
        return right_rotate(node)
    # Right Right
    if bf < -1 and key > node.right.key:
        return left_rotate(node)
    # Left Right
    if bf > 1 and key > node.left.key:
        node.left = left_rotate(node.left)
        return right_rotate(node)
    # Right Left
    if bf < -1 and key < node.right.key:
        node.right = right_rotate(node.right)
        return left_rotate(node)

    return node

def inorder(node):
    if node is None:
        return []
    return inorder(node.left) + [node.key] + inorder(node.right)

def collect_balance_factors(node):
    if node is None:
        return []
    result = [(node.key, balance_factor(node))]
    result.extend(collect_balance_factors(node.left))
    result.extend(collect_balance_factors(node.right))
    return result

def verify_heights(node):
    # Recompute heights from scratch and compare
    if node is None:
        return True
    lh = 0 if node.left is None else node.left.height
    rh = 0 if node.right is None else node.right.height
    expected = 1 + max(lh, rh)
    if node.height != expected:
        return False
    return verify_heights(node.left) and verify_heights(node.right)

root = None
for k in KEYS:
    root = insert(root, k)

sorted_keys = inorder(root)
bfs = collect_balance_factors(root)
all_balanced = all(abs(bf) <= 1 for _, bf in bfs)
heights_ok = verify_heights(root)
result = (sorted_keys, all_balanced, heights_ok)
"""

BUGGY = r"""
class AVLNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.height = 1

def height(node):
    if node is None:
        return 0
    return node.height

def update_height(node):
    if node is not None:
        node.height = 1 + max(height(node.left), height(node.right))

def balance_factor(node):
    if node is None:
        return 0
    return height(node.left) - height(node.right)

def right_rotate(y):
    x = y.left
    t2 = x.right
    x.right = y
    y.left = t2
    # BUG: only update y's height, not x's (the new parent)
    update_height(y)
    # Missing: update_height(x)
    return x

def left_rotate(x):
    y = x.right
    t2 = y.left
    y.left = x
    x.right = t2
    # BUG: only update x's height, not y's (the new parent)
    update_height(x)
    # Missing: update_height(y)
    return y

def insert(node, key):
    if node is None:
        return AVLNode(key)

    if key < node.key:
        node.left = insert(node.left, key)
    elif key > node.key:
        node.right = insert(node.right, key)
    else:
        return node

    update_height(node)
    bf = balance_factor(node)

    if bf > 1 and key < node.left.key:
        return right_rotate(node)
    if bf < -1 and key > node.right.key:
        return left_rotate(node)
    if bf > 1 and key > node.left.key:
        node.left = left_rotate(node.left)
        return right_rotate(node)
    if bf < -1 and key < node.right.key:
        node.right = right_rotate(node.right)
        return left_rotate(node)

    return node

def inorder(node):
    if node is None:
        return []
    return inorder(node.left) + [node.key] + inorder(node.right)

def collect_balance_factors(node):
    if node is None:
        return []
    result = [(node.key, balance_factor(node))]
    result.extend(collect_balance_factors(node.left))
    result.extend(collect_balance_factors(node.right))
    return result

def verify_heights(node):
    if node is None:
        return True
    lh = 0 if node.left is None else node.left.height
    rh = 0 if node.right is None else node.right.height
    expected = 1 + max(lh, rh)
    if node.height != expected:
        return False
    return verify_heights(node.left) and verify_heights(node.right)

root = None
for k in KEYS:
    root = insert(root, k)

sorted_keys = inorder(root)
bfs = collect_balance_factors(root)
all_balanced = all(abs(bf) <= 1 for _, bf in bfs)
heights_ok = verify_heights(root)
result = (sorted_keys, all_balanced, heights_ok)
"""


def SPEC(keys, result):
    if not isinstance(result, (list, tuple)) or len(result) != 3:
        return False
    sorted_keys, all_balanced, heights_ok = result

    # Inorder traversal must give sorted unique keys
    expected = sorted(set(keys))
    if list(sorted_keys) != expected:
        return False

    # All balance factors must be in {-1, 0, 1}
    if not all_balanced:
        return False

    # All stored heights must be consistent
    if not heights_ok:
        return False

    return True


BUG_DESC = (
    "After a rotation, only the child node's height is updated but the "
    "new parent's height is not. This causes the stored height of the "
    "rotation's new root to be stale, leading to incorrect balance factor "
    "calculations in subsequent insertions. The verify_heights check "
    "catches the inconsistency."
)


def _gen_keys():
    import random
    # The bug: after rotation, the new parent's height is NOT updated.
    # In right_rotate, x's height is stale (still the old value before rotation).
    # In left_rotate, y's height is stale.
    #
    # verify_heights checks that every node's stored height equals
    # 1 + max(left.height, right.height). After a rotation, the new root
    # of the rotated subtree will have a wrong stored height.
    #
    # To trigger rotations with small inputs (max 8 keys):
    # - Ascending sequence triggers left-left case (right rotations)
    # - Descending triggers right-right case (left rotations)
    # - Mixed triggers double rotations
    #
    # After just 3 ascending keys [1,2,3], a right rotation occurs at node 2,
    # and x (new root) doesn't get its height updated. But then insert calls
    # update_height on the way back up, which might fix it.
    #
    # The key insight: the rotation returns x whose height is stale. But the
    # insert function does NOT call update_height after the rotation return
    # (the rotation IS the return). So x's height stays wrong.
    #
    # Actually looking more carefully: insert does update_height(node) before
    # checking balance, then rotates. The rotation returns x, and that goes
    # back to the caller's insert which does update_height on its own node.
    # So the stale height of x propagates.
    #
    # Use sequences that cause multiple rotations and subsequent operations
    # that depend on the stale heights.
    # These sequences all produce stale heights in the buggy code,
    # causing verify_heights to return False. They involve double rotations
    # (LR or RL cases) where the inner rotation's new root has a stale
    # height that propagates through the outer rotation.
    known_bad = [
        [4, 11, 6, 16, 15],
        [9, 16, 7, 10, 11],
        [16, 21, 6, 13, 12],
        [17, 23, 15, 2, 3],
        [5, 3, 29, 8, 15],
        [14, 2, 15, 25, 24],
        [25, 23, 14, 12, 13],
        [24, 3, 26, 10, 8],
        [16, 14, 15, 5, 10],
        [3, 17, 25, 18, 19],
        [8, 25, 16, 12, 11],
        [22, 8, 3, 10, 20],
        [5, 17, 28, 22, 23],
        [28, 5, 3, 7, 14],
    ]
    return random.choice(known_bad)


INPUT_OVERRIDES = {
    "KEYS": _gen_keys,
}
