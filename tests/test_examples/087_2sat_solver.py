"""2-SAT solver via implication graph and SCC. Bug: second implication for a clause is reversed."""

CORRECT = r"""
# 2-SAT Solver using implication graph + Tarjan's SCC
# Variables are 1-indexed. Literal x -> 2*x, NOT x -> 2*x+1
# CLAUSES is a list of (a, b) where each literal is signed: positive = var, negative = NOT var

num_vars = NUM_VARS
num_nodes = 2 * (num_vars + 1)

adj = [[] for _ in range(num_nodes)]
radj = [[] for _ in range(num_nodes)]

def lit_to_node(l):
    # Positive literal x -> 2*x, negative literal -x -> 2*x+1
    if l > 0:
        return 2 * l
    else:
        return 2 * (-l) + 1

def negate_node(n):
    return n ^ 1

def add_implication(a, b):
    # a -> b
    adj[a].append(b)
    radj[b].append(a)

# Build implication graph: (a OR b) means (NOT a -> b) AND (NOT b -> a)
for a, b in CLAUSES:
    na = lit_to_node(a)
    nb = lit_to_node(b)
    # NOT a -> b
    add_implication(negate_node(na), nb)
    # NOT b -> a
    add_implication(negate_node(nb), na)

# Kosaraju's algorithm for SCC
visited = [False] * num_nodes
order = []

def dfs1(v):
    stack = [(v, 0)]
    visited[v] = True
    while stack:
        node, idx = stack[-1]
        if idx < len(adj[node]):
            stack[-1] = (node, idx + 1)
            w = adj[node][idx]
            if not visited[w]:
                visited[w] = True
                stack.append((w, 0))
        else:
            stack.pop()
            order.append(node)

for i in range(num_nodes):
    if not visited[i]:
        dfs1(i)

comp = [-1] * num_nodes
comp_id = 0

def dfs2(v, c):
    stack = [v]
    comp[v] = c
    while stack:
        node = stack.pop()
        for w in radj[node]:
            if comp[w] == -1:
                comp[w] = c
                stack.append(w)

for v in reversed(order):
    if comp[v] == -1:
        dfs2(v, comp_id)
        comp_id += 1

# Check satisfiability: variable x is unsatisfiable if x and NOT x are in same SCC
satisfiable = True
assignment = [False] * (num_vars + 1)
for x in range(1, num_vars + 1):
    pos = lit_to_node(x)
    neg = lit_to_node(-x)
    if comp[pos] == comp[neg]:
        satisfiable = False
        break
    # If comp[pos] > comp[neg], then x is true (in Kosaraju's reverse-topo order)
    assignment[x] = comp[pos] > comp[neg]

if satisfiable:
    result = {"satisfiable": True, "assignment": assignment[1:num_vars + 1]}
else:
    result = {"satisfiable": False, "assignment": []}
"""

BUGGY = r"""
# 2-SAT Solver using implication graph + Tarjan's SCC

num_vars = NUM_VARS
num_nodes = 2 * (num_vars + 1)

adj = [[] for _ in range(num_nodes)]
radj = [[] for _ in range(num_nodes)]

def lit_to_node(l):
    if l > 0:
        return 2 * l
    else:
        return 2 * (-l) + 1

def negate_node(n):
    return n ^ 1

def add_implication(a, b):
    adj[a].append(b)
    radj[b].append(a)

# Build implication graph: (a OR b) means (NOT a -> b) AND (NOT b -> a)
for a, b in CLAUSES:
    na = lit_to_node(a)
    nb = lit_to_node(b)
    # NOT a -> b  (correct)
    add_implication(negate_node(na), nb)
    # BUG: NOT b -> NOT a instead of NOT b -> a
    # This reverses the second implication, breaking the equivalence
    add_implication(negate_node(nb), negate_node(na))

# Kosaraju's algorithm for SCC
visited = [False] * num_nodes
order = []

def dfs1(v):
    stack = [(v, 0)]
    visited[v] = True
    while stack:
        node, idx = stack[-1]
        if idx < len(adj[node]):
            stack[-1] = (node, idx + 1)
            w = adj[node][idx]
            if not visited[w]:
                visited[w] = True
                stack.append((w, 0))
        else:
            stack.pop()
            order.append(node)

for i in range(num_nodes):
    if not visited[i]:
        dfs1(i)

comp = [-1] * num_nodes
comp_id = 0

def dfs2(v, c):
    stack = [v]
    comp[v] = c
    while stack:
        node = stack.pop()
        for w in radj[node]:
            if comp[w] == -1:
                comp[w] = c
                stack.append(w)

for v in reversed(order):
    if comp[v] == -1:
        dfs2(v, comp_id)
        comp_id += 1

satisfiable = True
assignment = [False] * (num_vars + 1)
for x in range(1, num_vars + 1):
    pos = lit_to_node(x)
    neg = lit_to_node(-x)
    if comp[pos] == comp[neg]:
        satisfiable = False
        break
    assignment[x] = comp[pos] > comp[neg]

if satisfiable:
    result = {"satisfiable": True, "assignment": assignment[1:num_vars + 1]}
else:
    result = {"satisfiable": False, "assignment": []}
"""


def SPEC(num_vars, clauses, result):
    if result["satisfiable"]:
        # Verify: every clause must be satisfied
        assign = result["assignment"]
        if len(assign) != num_vars:
            return False
        for a, b in clauses:
            va = assign[abs(a) - 1] if a > 0 else not assign[abs(a) - 1]
            vb = assign[abs(b) - 1] if b > 0 else not assign[abs(b) - 1]
            if not (va or vb):
                return False
        return True
    else:
        # To verify unsatisfiable, brute-force check all assignments
        for mask in range(1 << num_vars):
            assign = [(mask >> i) & 1 == 1 for i in range(num_vars)]
            all_sat = True
            for a, b in clauses:
                va = assign[abs(a) - 1] if a > 0 else not assign[abs(a) - 1]
                vb = assign[abs(b) - 1] if b > 0 else not assign[abs(b) - 1]
                if not (va or vb):
                    all_sat = False
                    break
            if all_sat:
                return False  # Found a satisfying assignment but solver said unsat
        return True


BUG_DESC = "When encoding (a OR b), the second implication is NOT b -> NOT a instead of NOT b -> a, which is the contrapositive of the first implication rather than the required second implication, breaking the 2-SAT encoding."


def _gen_num_vars():
    return 4


def _gen_clauses():
    # (1 OR 2), (NOT 1 OR 3), (NOT 2 OR 4), (NOT 3 OR NOT 4), (1 OR NOT 3)
    # This is satisfiable (e.g., x1=T, x2=F, x3=T, x4=F)
    return [
        (1, 2),
        (-1, 3),
        (-2, 4),
        (-3, -4),
        (1, -3),
    ]


INPUT_OVERRIDES = {
    "NUM_VARS": _gen_num_vars,
    "CLAUSES": _gen_clauses,
}
