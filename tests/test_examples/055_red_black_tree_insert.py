"""Red-black tree insertion with fixup.

Bug: in the fixup, when uncle is black and node is a left child (zig-zag case),
rotates the wrong direction (left-rotates instead of right-rotates the parent),
corrupting the tree structure.
"""

CORRECT = r"""
BLACK = 0
RED = 1

class Node:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.parent = None
        self.color = RED

class RBTree:
    def __init__(self):
        self.NIL = Node(None)
        self.NIL.color = BLACK
        self.root = self.NIL

    def left_rotate(self, x):
        y = x.right
        x.right = y.left
        if y.left != self.NIL:
            y.left.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x == x.parent.left:
            x.parent.left = y
        else:
            x.parent.right = y
        y.left = x
        x.parent = y

    def right_rotate(self, x):
        y = x.left
        x.left = y.right
        if y.right != self.NIL:
            y.right.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x == x.parent.right:
            x.parent.right = y
        else:
            x.parent.left = y
        y.right = x
        x.parent = y

    def insert_fixup(self, z):
        while z.parent is not None and z.parent.color == RED:
            if z.parent == z.parent.parent.left:
                uncle = z.parent.parent.right
                if uncle.color == RED:
                    z.parent.color = BLACK
                    uncle.color = BLACK
                    z.parent.parent.color = RED
                    z = z.parent.parent
                else:
                    if z == z.parent.right:
                        z = z.parent
                        self.left_rotate(z)
                    z.parent.color = BLACK
                    z.parent.parent.color = RED
                    # CORRECT: right-rotate grandparent
                    self.right_rotate(z.parent.parent)
            else:
                uncle = z.parent.parent.left
                if uncle.color == RED:
                    z.parent.color = BLACK
                    uncle.color = BLACK
                    z.parent.parent.color = RED
                    z = z.parent.parent
                else:
                    if z == z.parent.left:
                        z = z.parent
                        # CORRECT: right-rotate to align
                        self.right_rotate(z)
                    z.parent.color = BLACK
                    z.parent.parent.color = RED
                    self.left_rotate(z.parent.parent)
        self.root.color = BLACK

    def insert(self, key):
        z = Node(key)
        z.left = self.NIL
        z.right = self.NIL
        y = None
        x = self.root
        while x != self.NIL:
            y = x
            if z.key < x.key:
                x = x.left
            else:
                x = x.right
        z.parent = y
        if y is None:
            self.root = z
        elif z.key < y.key:
            y.left = z
        else:
            y.right = z
        self.insert_fixup(z)

    def inorder(self):
        result = []
        def walk(node):
            if node != self.NIL:
                walk(node.left)
                result.append(node.key)
                walk(node.right)
        walk(self.root)
        return result

    def check_properties(self):
        # Returns (is_valid, black_height)
        def check(node):
            if node == self.NIL:
                return (True, 1)
            # Red node cannot have red child
            if node.color == RED:
                if node.left.color == RED or node.right.color == RED:
                    return (False, 0)
            # BST property
            if node.left != self.NIL and node.left.key >= node.key:
                return (False, 0)
            if node.right != self.NIL and node.right.key <= node.key:
                return (False, 0)
            lv, lh = check(node.left)
            rv, rh = check(node.right)
            if not lv or not rv:
                return (False, 0)
            if lh != rh:
                return (False, 0)
            return (True, lh + (1 if node.color == BLACK else 0))
        if self.root.color != BLACK:
            return False
        valid, _ = check(self.root)
        return valid

tree = RBTree()
for k in KEYS:
    tree.insert(k)
result = (tree.inorder(), tree.check_properties())
"""

BUGGY = r"""
BLACK = 0
RED = 1

class Node:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.parent = None
        self.color = RED

class RBTree:
    def __init__(self):
        self.NIL = Node(None)
        self.NIL.color = BLACK
        self.root = self.NIL

    def left_rotate(self, x):
        y = x.right
        x.right = y.left
        if y.left != self.NIL:
            y.left.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x == x.parent.left:
            x.parent.left = y
        else:
            x.parent.right = y
        y.left = x
        x.parent = y

    def right_rotate(self, x):
        y = x.left
        x.left = y.right
        if y.right != self.NIL:
            y.right.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x == x.parent.right:
            x.parent.right = y
        else:
            x.parent.left = y
        y.right = x
        x.parent = y

    def insert_fixup(self, z):
        while z.parent is not None and z.parent.color == RED:
            if z.parent == z.parent.parent.left:
                uncle = z.parent.parent.right
                if uncle.color == RED:
                    z.parent.color = BLACK
                    uncle.color = BLACK
                    z.parent.parent.color = RED
                    z = z.parent.parent
                else:
                    if z == z.parent.right:
                        z = z.parent
                        self.left_rotate(z)
                    z.parent.color = BLACK
                    z.parent.parent.color = RED
                    self.right_rotate(z.parent.parent)
            else:
                uncle = z.parent.parent.left
                if uncle.color == RED:
                    z.parent.color = BLACK
                    uncle.color = BLACK
                    z.parent.parent.color = RED
                    z = z.parent.parent
                else:
                    if z == z.parent.left:
                        z = z.parent
                        # BUG: left-rotate instead of right-rotate
                        self.left_rotate(z)
                    z.parent.color = BLACK
                    z.parent.parent.color = RED
                    self.left_rotate(z.parent.parent)
        self.root.color = BLACK

    def insert(self, key):
        z = Node(key)
        z.left = self.NIL
        z.right = self.NIL
        y = None
        x = self.root
        while x != self.NIL:
            y = x
            if z.key < x.key:
                x = x.left
            else:
                x = x.right
        z.parent = y
        if y is None:
            self.root = z
        elif z.key < y.key:
            y.left = z
        else:
            y.right = z
        self.insert_fixup(z)

    def inorder(self):
        result = []
        def walk(node):
            if node != self.NIL:
                walk(node.left)
                result.append(node.key)
                walk(node.right)
        walk(self.root)
        return result

    def check_properties(self):
        def check(node):
            if node == self.NIL:
                return (True, 1)
            if node.color == RED:
                if node.left.color == RED or node.right.color == RED:
                    return (False, 0)
            if node.left != self.NIL and node.left.key >= node.key:
                return (False, 0)
            if node.right != self.NIL and node.right.key <= node.key:
                return (False, 0)
            lv, lh = check(node.left)
            rv, rh = check(node.right)
            if not lv or not rv:
                return (False, 0)
            if lh != rh:
                return (False, 0)
            return (True, lh + (1 if node.color == BLACK else 0))
        if self.root.color != BLACK:
            return False
        valid, _ = check(self.root)
        return valid

tree = RBTree()
for k in KEYS:
    tree.insert(k)
result = (tree.inorder(), tree.check_properties())
"""


def SPEC(keys, result):
    if not isinstance(result, (list, tuple)) or len(result) != 2:
        return False
    inorder, props_valid = result

    # Inorder must be sorted version of unique keys
    expected = sorted(set(keys))
    if list(inorder) != expected:
        return False

    # All RB-tree properties must hold
    if not props_valid:
        return False

    return True


BUG_DESC = (
    "In the fixup when the parent is a right child and the node is a left "
    "child (zig-zag case), the algorithm left-rotates the parent instead of "
    "right-rotating it. This corrupts the BST ordering or violates red-black "
    "properties, causing check_properties to return False."
)


def _gen_keys():
    import random
    # The bug is in the else branch of insert_fixup: when parent is a RIGHT
    # child of grandparent, and node is a LEFT child of parent (zig-zag case),
    # the code does left_rotate instead of right_rotate.
    #
    # To trigger this reliably with small inputs:
    # - Insert keys that create a right-child chain, then insert a key that
    #   goes left from a right-child parent with a black uncle.
    #
    # Concrete example: inserting [3, 1, 5, 7, 6] triggers the bug.
    #  After [3,1,5]: root=3(B), left=1(R), right=5(R)
    #  Insert 7: recolor -> root=3(B), 1(B), 5(B), 7(R)
    #  Insert 6: parent=7(R) is right child of 5(B), node 6 is left child of 7
    #  Uncle of 7 is NIL (black) -> zig-zag case triggers the bug.
    #
    # We use several known-bad sequences and also small random ones.
    # All of these trigger the right-child zig-zag case, causing a crash
    # or BST violation in the buggy code. Pattern: a, b>a, c between a&b, d>b
    # creates the right-child left-child configuration.
    known_bad = [
        [3, 1, 5, 7, 6],
        [2, 1, 4, 6, 5],
        [10, 5, 15, 20, 17],
        [5, 3, 8, 12, 10],
        [4, 2, 6, 8, 7],
        [3, 1, 5, 7, 6, 8, 4],
        [6, 32, 10, 40],
        [9, 30, 20, 31],
        [7, 44, 41, 25],
        [17, 33, 20, 40],
    ]
    return random.choice(known_bad)


INPUT_OVERRIDES = {
    "KEYS": _gen_keys,
}
