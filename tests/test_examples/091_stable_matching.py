"""Gale-Shapley stable matching algorithm.
Bug: when a woman rejects her current partner for a better proposal,
doesn't add the rejected partner back to the free list, causing him
to never propose again."""

CORRECT = r"""
# Gale-Shapley stable matching (proposer-optimal)
# PREFS_M: list of lists, prefs_m[i] = ranking of women by man i
# PREFS_W: list of lists, prefs_w[j] = ranking of men by woman j
# n men and n women, numbered 0..n-1

prefs_m = list(PREFS_M)
prefs_w = list(PREFS_W)
n = len(prefs_m)

# Build woman preference rank lookup: w_rank[w][m] = rank of m for w
w_rank = []
for w in range(n):
    rank = [0] * n
    for r, m in enumerate(prefs_w[w]):
        rank[m] = r
    w_rank.append(rank)

# next_proposal[m] = index into prefs_m[m] for next woman to propose to
next_proposal = [0] * n

# current_match[w] = current partner of woman w, or -1
current_match = [-1] * n

# free_men = list of currently unmatched men
free_men = list(range(n))

while free_men:
    m = free_men.pop(0)
    # Man m proposes to his next choice
    if next_proposal[m] >= n:
        # exhausted all proposals (shouldn't happen with valid input)
        continue
    w = prefs_m[m][next_proposal[m]]
    next_proposal[m] += 1

    if current_match[w] == -1:
        # Woman w is free, accept
        current_match[w] = m
    else:
        # Woman w is engaged to m_prime
        m_prime = current_match[w]
        if w_rank[w][m] < w_rank[w][m_prime]:
            # w prefers m over m_prime
            current_match[w] = m
            # CORRECT: add rejected partner back to free list
            free_men.append(m_prime)
        else:
            # w rejects m, m stays free
            free_men.append(m)

# Build result as dict: man -> woman
match = {}
for w in range(n):
    if current_match[w] != -1:
        match[current_match[w]] = w

result = match
"""

BUGGY = r"""
# Gale-Shapley stable matching (proposer-optimal)
# PREFS_M: list of lists, prefs_m[i] = ranking of women by man i
# PREFS_W: list of lists, prefs_w[j] = ranking of men by woman j
# n men and n women, numbered 0..n-1

prefs_m = list(PREFS_M)
prefs_w = list(PREFS_W)
n = len(prefs_m)

# Build woman preference rank lookup: w_rank[w][m] = rank of m for w
w_rank = []
for w in range(n):
    rank = [0] * n
    for r, m in enumerate(prefs_w[w]):
        rank[m] = r
    w_rank.append(rank)

# next_proposal[m] = index into prefs_m[m] for next woman to propose to
next_proposal = [0] * n

# current_match[w] = current partner of woman w, or -1
current_match = [-1] * n

# free_men = list of currently unmatched men
free_men = list(range(n))

while free_men:
    m = free_men.pop(0)
    # Man m proposes to his next choice
    if next_proposal[m] >= n:
        continue
    w = prefs_m[m][next_proposal[m]]
    next_proposal[m] += 1

    if current_match[w] == -1:
        # Woman w is free, accept
        current_match[w] = m
    else:
        # Woman w is engaged to m_prime
        m_prime = current_match[w]
        if w_rank[w][m] < w_rank[w][m_prime]:
            # w prefers m over m_prime
            current_match[w] = m
            # BUG: forgot to add rejected m_prime back to free list
            # m_prime will never propose again
        else:
            # w rejects m, m stays free
            free_men.append(m)

# Build result as dict: man -> woman
match = {}
for w in range(n):
    if current_match[w] != -1:
        match[current_match[w]] = w

result = match
"""


def SPEC(prefs_m, prefs_w, result):
    n = len(prefs_m)
    # Every man must be matched
    if len(result) != n:
        return False
    # Result must be a valid bijection: each man maps to unique woman
    women_used = set(result.values())
    if len(women_used) != n:
        return False
    if women_used != set(range(n)):
        return False
    # Check stability: no blocking pair
    # Build woman->man mapping
    w_to_m = {}
    for m, w in result.items():
        w_to_m[w] = m
    # w_rank[w][m] = rank of m in w's preference
    w_rank = []
    for w in range(n):
        rank = [0] * n
        for r, m_val in enumerate(prefs_w[w]):
            rank[m_val] = r
        w_rank.append(rank)
    # m_rank[m][w] = rank of w in m's preference
    m_rank = []
    for m in range(n):
        rank = [0] * n
        for r, w_val in enumerate(prefs_m[m]):
            rank[w_val] = r
        m_rank.append(rank)
    # Check for blocking pairs
    for m in range(n):
        w_current = result[m]
        for w in range(n):
            if w == w_current:
                continue
            m_other = w_to_m[w]
            # m prefers w over current, and w prefers m over current
            if m_rank[m][w] < m_rank[m][w_current] and w_rank[w][m] < w_rank[w][m_other]:
                return False
    return True


BUG_DESC = (
    "When a woman rejects her current partner for a better proposal, "
    "the rejected partner is not added back to the free list. He never "
    "proposes again, resulting in an incomplete matching."
)


def _gen():
    import random
    n = random.randint(3, 6)
    prefs_m = []
    for _ in range(n):
        perm = list(range(n))
        random.shuffle(perm)
        prefs_m.append(perm)
    prefs_w = []
    for _ in range(n):
        perm = list(range(n))
        random.shuffle(perm)
        prefs_w.append(perm)
    return prefs_m, prefs_w


def _gen_m():
    return _gen()[0]


def _gen_w():
    return _gen()[1]


def _gen_pair():
    import random
    n = random.randint(3, 6)
    prefs_m = []
    for _ in range(n):
        perm = list(range(n))
        random.shuffle(perm)
        prefs_m.append(perm)
    prefs_w = []
    for _ in range(n):
        perm = list(range(n))
        random.shuffle(perm)
        prefs_w.append(perm)
    return prefs_m


def _gen_w_from():
    import random
    n = random.randint(3, 6)
    prefs = []
    for _ in range(n):
        perm = list(range(n))
        random.shuffle(perm)
        prefs.append(perm)
    return prefs


INPUT_OVERRIDES = {"PREFS_M": _gen_pair, "PREFS_W": _gen_w_from}
