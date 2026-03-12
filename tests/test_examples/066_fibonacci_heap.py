"""Fibonacci heap with decrease-key and delete-min.

Bug: in cascading cut, doesn't mark the parent as 'marked' when cutting
a second child, so future cuts don't cascade properly. This breaks the
amortized complexity guarantee and produces wrong min-extraction order.
"""

CORRECT = r"""
class FibNode:
    def __init__(self, key, payload=None):
        self.key = key
        self.payload = payload
        self.degree = 0
        self.marked = False
        self.parent = None
        self.child = None
        self.left = self
        self.right = self

def fib_insert(min_node, node):
    if min_node is None:
        return node
    # Insert into root list
    node.left = min_node
    node.right = min_node.right
    min_node.right.left = node
    min_node.right = node
    if node.key < min_node.key:
        return node
    return min_node

def fib_link(y, x):
    # Remove y from root list and make it child of x
    y.left.right = y.right
    y.right.left = y.left
    y.parent = x
    if x.child is None:
        x.child = y
        y.left = y
        y.right = y
    else:
        y.left = x.child
        y.right = x.child.right
        x.child.right.left = y
        x.child.right = y
    x.degree += 1
    y.marked = False

def fib_consolidate(min_node):
    if min_node is None:
        return None
    # Collect all roots
    roots = []
    cur = min_node
    while True:
        roots.append(cur)
        cur = cur.right
        if cur is min_node:
            break
    # Detach all
    for r in roots:
        r.left = r
        r.right = r

    max_degree = len(roots) + 10
    degree_table = [None] * max_degree

    for w in roots:
        x = w
        d = x.degree
        while d < max_degree and degree_table[d] is not None:
            y = degree_table[d]
            if x.key > y.key:
                x, y = y, x
            fib_link(y, x)
            degree_table[d] = None
            d += 1
        if d < max_degree:
            degree_table[d] = x

    new_min = None
    for node in degree_table:
        if node is not None:
            node.left = node
            node.right = node
            new_min = fib_insert(new_min, node)
    return new_min

def fib_extract_min(min_node):
    if min_node is None:
        return None, None
    z = min_node
    # Add children to root list
    if z.child is not None:
        children = []
        c = z.child
        while True:
            children.append(c)
            c = c.right
            if c is z.child:
                break
        for ch in children:
            ch.parent = None
            min_node = fib_insert(min_node, ch)
    # Remove z from root list
    if z.right is z:
        new_min = None
    else:
        z.left.right = z.right
        z.right.left = z.left
        new_min = fib_consolidate(z.right)
    return z, new_min

def fib_cut(min_node, x, y):
    # Cut x from y's child list
    if x.right is x:
        y.child = None
    else:
        if y.child is x:
            y.child = x.right
        x.left.right = x.right
        x.right.left = x.left
    y.degree -= 1
    x.parent = None
    x.marked = False
    x.left = x
    x.right = x
    return fib_insert(min_node, x)

def fib_cascading_cut(min_node, y):
    z = y.parent
    if z is not None:
        if not y.marked:
            # CORRECT: mark y so next cut from y cascades
            y.marked = True
        else:
            min_node = fib_cut(min_node, y, z)
            min_node = fib_cascading_cut(min_node, z)
    return min_node

def fib_decrease_key(min_node, x, new_key):
    x.key = new_key
    y = x.parent
    if y is not None and x.key < y.key:
        min_node = fib_cut(min_node, x, y)
        min_node = fib_cascading_cut(min_node, y)
    if x.key < min_node.key:
        min_node = x
    return min_node

data = DATA
ops = data["ops"]

min_node = None
node_map = {}
extracted = []

for op in ops:
    if op[0] == "insert":
        key, name = op[1], op[2]
        node = FibNode(key, name)
        node_map[name] = node
        min_node = fib_insert(min_node, node)
    elif op[0] == "extract_min":
        z, min_node = fib_extract_min(min_node)
        if z is not None:
            extracted.append((z.key, z.payload))
    elif op[0] == "decrease_key":
        name, new_key = op[1], op[2]
        if name in node_map:
            min_node = fib_decrease_key(min_node, node_map[name], new_key)

result = extracted
"""

BUGGY = r"""
class FibNode:
    def __init__(self, key, payload=None):
        self.key = key
        self.payload = payload
        self.degree = 0
        self.marked = False
        self.parent = None
        self.child = None
        self.left = self
        self.right = self

def fib_insert(min_node, node):
    if min_node is None:
        return node
    node.left = min_node
    node.right = min_node.right
    min_node.right.left = node
    min_node.right = node
    if node.key < min_node.key:
        return node
    return min_node

def fib_link(y, x):
    y.left.right = y.right
    y.right.left = y.left
    y.parent = x
    if x.child is None:
        x.child = y
        y.left = y
        y.right = y
    else:
        y.left = x.child
        y.right = x.child.right
        x.child.right.left = y
        x.child.right = y
    x.degree += 1
    y.marked = False

def fib_consolidate(min_node):
    if min_node is None:
        return None
    roots = []
    cur = min_node
    while True:
        roots.append(cur)
        cur = cur.right
        if cur is min_node:
            break
    for r in roots:
        r.left = r
        r.right = r

    max_degree = len(roots) + 10
    degree_table = [None] * max_degree

    for w in roots:
        x = w
        d = x.degree
        while d < max_degree and degree_table[d] is not None:
            y = degree_table[d]
            if x.key > y.key:
                x, y = y, x
            fib_link(y, x)
            degree_table[d] = None
            d += 1
        if d < max_degree:
            degree_table[d] = x

    new_min = None
    for node in degree_table:
        if node is not None:
            node.left = node
            node.right = node
            new_min = fib_insert(new_min, node)
    return new_min

def fib_extract_min(min_node):
    if min_node is None:
        return None, None
    z = min_node
    if z.child is not None:
        children = []
        c = z.child
        while True:
            children.append(c)
            c = c.right
            if c is z.child:
                break
        for ch in children:
            ch.parent = None
            min_node = fib_insert(min_node, ch)
    if z.right is z:
        new_min = None
    else:
        z.left.right = z.right
        z.right.left = z.left
        new_min = fib_consolidate(z.right)
    return z, new_min

def fib_cut(min_node, x, y):
    if x.right is x:
        y.child = None
    else:
        if y.child is x:
            y.child = x.right
        x.left.right = x.right
        x.right.left = x.left
    y.degree -= 1
    x.parent = None
    x.marked = False
    x.left = x
    x.right = x
    return fib_insert(min_node, x)

def fib_cascading_cut(min_node, y):
    z = y.parent
    if z is not None:
        if not y.marked:
            # BUG: doesn't mark y, so cascading cuts never trigger
            pass
        else:
            min_node = fib_cut(min_node, y, z)
            min_node = fib_cascading_cut(min_node, z)
    return min_node

def fib_decrease_key(min_node, x, new_key):
    x.key = new_key
    y = x.parent
    if y is not None and x.key < y.key:
        min_node = fib_cut(min_node, x, y)
        min_node = fib_cascading_cut(min_node, y)
    if x.key < min_node.key:
        min_node = x
    return min_node

data = DATA
ops = data["ops"]

min_node = None
node_map = {}
extracted = []

for op in ops:
    if op[0] == "insert":
        key, name = op[1], op[2]
        node = FibNode(key, name)
        node_map[name] = node
        min_node = fib_insert(min_node, node)
    elif op[0] == "extract_min":
        z, min_node = fib_extract_min(min_node)
        if z is not None:
            extracted.append((z.key, z.payload))
    elif op[0] == "decrease_key":
        name, new_key = op[1], op[2]
        if name in node_map:
            min_node = fib_decrease_key(min_node, node_map[name], new_key)

result = extracted
"""


def SPEC(data, result):
    import heapq
    ops = data["ops"]

    if not isinstance(result, list):
        return False

    # Simulate with a simple priority queue
    heap = []
    key_map = {}
    extracted_idx = 0

    for op in ops:
        if op[0] == "insert":
            key, name = op[1], op[2]
            key_map[name] = key
            heapq.heappush(heap, (key, name))
        elif op[0] == "extract_min":
            # Skip stale entries
            while heap and key_map.get(heap[0][1]) != heap[0][0]:
                heapq.heappop(heap)
            if heap:
                k, name = heapq.heappop(heap)
                del key_map[name]
                if extracted_idx >= len(result):
                    return False
                if result[extracted_idx] != (k, name):
                    return False
                extracted_idx += 1
        elif op[0] == "decrease_key":
            name, new_key = op[1], op[2]
            if name in key_map:
                key_map[name] = new_key
                heapq.heappush(heap, (new_key, name))

    if extracted_idx != len(result):
        return False
    return True


BUG_DESC = (
    "In fib_cascading_cut, when a node is unmarked, the code does 'pass' "
    "instead of 'y.marked = True'. Without marking, subsequent child losses "
    "from the same parent never trigger cascading cuts, allowing the heap "
    "structure to degrade and extract_min to return elements in wrong order."
)


def _gen():
    # The bug: in cascading_cut, when y is unmarked, does `pass` instead of
    # `y.marked = True`. This means a parent that loses a second child
    # won't cascade the cut upward. The heap structure degrades and
    # extract_min returns elements in wrong order.
    #
    # To trigger cascading cuts, we need:
    # 1. Build a heap and extract_min to consolidate (create multi-child nodes)
    # 2. decrease_key a child so it gets cut (parent becomes marked in correct code)
    # 3. decrease_key another child of the SAME parent -> should cascade in correct code
    # 4. Extract mins and check order
    #
    # Carefully constructed sequence:
    # Insert nodes with known keys, extract_min to consolidate,
    # then decrease_key children of the same parent twice.
    ops = [
        # Insert 8 nodes
        ["insert", 10, "a"],
        ["insert", 20, "b"],
        ["insert", 30, "c"],
        ["insert", 40, "d"],
        ["insert", 50, "e"],
        ["insert", 60, "f"],
        ["insert", 70, "g"],
        ["insert", 80, "h"],
        # Extract min to trigger consolidation (creates tree structure)
        ["extract_min"],  # extracts (10, "a")
        # Now the heap has been consolidated. Nodes b(20), c(30), d(40), etc.
        # are organized into a tree. After consolidation, some node (e.g., b=20)
        # will have children.
        #
        # Decrease key of a deep node below its parent to trigger a cut
        ["decrease_key", "e", 5],   # cut e from parent, parent gets marked
        ["decrease_key", "f", 3],   # cut f; if same parent, should cascade
        ["decrease_key", "g", 4],   # another cut
        ["decrease_key", "h", 2],   # another cut
        #
        # Now decrease_key more nodes that share parents
        ["decrease_key", "d", 1],
        ["decrease_key", "c", 6],
        #
        # Extract all mins - order should be: d(1), h(2), f(3), g(4), e(5), c(6), b(20)
        ["extract_min"],  # should be (1, "d")
        ["extract_min"],  # should be (2, "h")
        ["extract_min"],  # should be (3, "f")
        ["extract_min"],  # should be (4, "g")
        ["extract_min"],  # should be (5, "e")
        ["extract_min"],  # should be (6, "c")
        ["extract_min"],  # should be (20, "b")
    ]
    return {"ops": ops}


INPUT_OVERRIDES = {"DATA": _gen}
