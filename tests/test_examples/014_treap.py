"""Treap — BST with random priorities maintaining both BST property on keys
and max-heap property on priorities.

Bug: In right_rotate(node), should set node.left = left_child.right, but
the bug sets node.left = left_child.left, corrupting the BST structure.
"""

CORRECT = r"""
class TreapNode:
    def __init__(self, key, priority):
        self.key = key
        self.priority = priority
        self.left = None
        self.right = None

def right_rotate(node):
    left_child = node.left
    node.left = left_child.right
    left_child.right = node
    return left_child

def left_rotate(node):
    right_child = node.right
    node.right = right_child.left
    right_child.left = node
    return right_child

def insert(root, key, priority):
    if root is None:
        return TreapNode(key, priority)

    if key < root.key:
        root.left = insert(root.left, key, priority)
        # If left child has higher priority, rotate right
        if root.left is not None and root.left.priority > root.priority:
            root = right_rotate(root)
    elif key > root.key:
        root.right = insert(root.right, key, priority)
        # If right child has higher priority, rotate left
        if root.right is not None and root.right.priority > root.priority:
            root = left_rotate(root)
    # If key == root.key, do nothing (no duplicates)

    return root

def search(root, key):
    if root is None:
        return False
    if key == root.key:
        return True
    elif key < root.key:
        return search(root.left, key)
    else:
        return search(root.right, key)

def inorder(root):
    if root is None:
        return []
    return inorder(root.left) + [root.key] + inorder(root.right)

def collect_nodes(root):
    if root is None:
        return []
    return [root] + collect_nodes(root.left) + collect_nodes(root.right)

def run_treap(operations):
    root = None
    search_results = []

    for op in operations:
        if op[0] == 'insert':
            _, key, priority = op
            root = insert(root, key, priority)
        elif op[0] == 'search':
            _, key = op
            found = search(root, key)
            search_results.append((key, found))

    # Collect tree info for verification
    keys_inorder = inorder(root)
    all_nodes = collect_nodes(root)
    node_info = []
    for nd in all_nodes:
        left_pri = nd.left.priority if nd.left else -1
        right_pri = nd.right.priority if nd.right else -1
        left_key = nd.left.key if nd.left else None
        right_key = nd.right.key if nd.right else None
        node_info.append({
            'key': nd.key,
            'priority': nd.priority,
            'left_pri': left_pri,
            'right_pri': right_pri,
            'left_key': left_key,
            'right_key': right_key,
        })

    return {
        'search_results': search_results,
        'inorder': keys_inorder,
        'nodes': node_info,
    }

operations = OPERATIONS
result = run_treap(operations)
"""

BUGGY = r"""
class TreapNode:
    def __init__(self, key, priority):
        self.key = key
        self.priority = priority
        self.left = None
        self.right = None

def right_rotate(node):
    left_child = node.left
    # BUG: should be node.left = left_child.right
    # but uses left_child.left, which is wrong subtree
    node.left = left_child.left
    left_child.right = node
    return left_child

def left_rotate(node):
    right_child = node.right
    node.right = right_child.left
    right_child.left = node
    return right_child

def insert(root, key, priority):
    if root is None:
        return TreapNode(key, priority)

    if key < root.key:
        root.left = insert(root.left, key, priority)
        # If left child has higher priority, rotate right
        if root.left is not None and root.left.priority > root.priority:
            root = right_rotate(root)
    elif key > root.key:
        root.right = insert(root.right, key, priority)
        # If right child has higher priority, rotate left
        if root.right is not None and root.right.priority > root.priority:
            root = left_rotate(root)

    return root

def search(root, key):
    if root is None:
        return False
    if key == root.key:
        return True
    elif key < root.key:
        return search(root.left, key)
    else:
        return search(root.right, key)

def inorder(root):
    if root is None:
        return []
    return inorder(root.left) + [root.key] + inorder(root.right)

def collect_nodes(root):
    if root is None:
        return []
    return [root] + collect_nodes(root.left) + collect_nodes(root.right)

def run_treap(operations):
    root = None
    search_results = []

    for op in operations:
        if op[0] == 'insert':
            _, key, priority = op
            root = insert(root, key, priority)
        elif op[0] == 'search':
            _, key = op
            found = search(root, key)
            search_results.append((key, found))

    # Collect tree info for verification
    keys_inorder = inorder(root)
    all_nodes = collect_nodes(root)
    node_info = []
    for nd in all_nodes:
        left_pri = nd.left.priority if nd.left else -1
        right_pri = nd.right.priority if nd.right else -1
        left_key = nd.left.key if nd.left else None
        right_key = nd.right.key if nd.right else None
        node_info.append({
            'key': nd.key,
            'priority': nd.priority,
            'left_pri': left_pri,
            'right_pri': right_pri,
            'left_key': left_key,
            'right_key': right_key,
        })

    return {
        'search_results': search_results,
        'inorder': keys_inorder,
        'nodes': node_info,
    }

operations = OPERATIONS
result = run_treap(operations)
"""


def SPEC(OPERATIONS, result):
    """Verify treap properties: BST ordering, heap priority, all keys findable."""
    if not isinstance(result, dict):
        return False

    search_results = result.get('search_results', [])
    inorder_keys = result.get('inorder', [])
    nodes = result.get('nodes', [])

    # Collect all inserted keys
    inserted_keys = set()
    for op in OPERATIONS:
        if op[0] == 'insert':
            inserted_keys.add(op[1])

    # (1) BST property: inorder traversal should be sorted with no duplicates
    for i in range(1, len(inorder_keys)):
        if inorder_keys[i] <= inorder_keys[i - 1]:
            return False

    # (2) All inserted keys appear in inorder traversal
    if set(inorder_keys) != inserted_keys:
        return False

    # (3) Heap property: every node's priority >= children's priorities
    for node in nodes:
        if node['left_pri'] != -1 and node['left_pri'] > node['priority']:
            return False
        if node['right_pri'] != -1 and node['right_pri'] > node['priority']:
            return False

    # (4) BST child key property
    for node in nodes:
        if node['left_key'] is not None and node['left_key'] >= node['key']:
            return False
        if node['right_key'] is not None and node['right_key'] <= node['key']:
            return False

    # (5) All search results for inserted keys should be True
    for key, found in search_results:
        if key in inserted_keys and not found:
            return False

    return True


BUG_DESC = (
    "In right_rotate(node), the code sets node.left = left_child.left instead "
    "of node.left = left_child.right. This loses the subtree that should be "
    "re-parented during rotation, corrupting the BST structure so that nodes "
    "go missing or appear in wrong positions, breaking inorder sorted order."
)


def _generate_operations():
    import random
    num_inserts = random.randint(8, 15)
    keys = random.sample(range(1, 51), num_inserts)
    operations = []

    for key in keys:
        priority = random.randint(1, 100)
        operations.append(('insert', key, priority))

    # Search for half of the inserted keys
    search_keys = random.sample(keys, len(keys) // 2)
    for key in search_keys:
        operations.append(('search', key))

    return operations


INPUT_OVERRIDES = {
    "OPERATIONS": _generate_operations,
}
