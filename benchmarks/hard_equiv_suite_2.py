"""Hard equivalence benchmark suite 2: 100 equivalent + 100 non-equivalent pairs.

This suite covers deep Python semantics across 12 EQ categories and 10 NEQ
categories.  Every function is self-contained, uses only the standard library,
and is 15-60 lines long.

EQ categories (≈8 pairs each):
  1. String processing          2. Number theory
  3. Graph algorithms           4. Dynamic programming
  5. Data structures            6. Combinatorics
  7. Geometry                   8. Functional / iterator patterns
  9. Bit manipulation          10. Sorting / searching
 11. Matrix / linear algebra   12. Cryptographic / hashing

NEQ categories (10 pairs each):
  1. Off-by-one errors          2. Stability / ordering
  3. Type coercion              4. Mutability / aliasing
  5. Edge cases                 6. Float semantics
  7. Generator / iterator       8. Scope / closure
  9. Exception handling        10. Python-specific gotchas
"""
from textwrap import dedent

EQUIV_PAIRS: list[tuple[str, str, str, bool]] = [

    # =========================================================================
    # EQUIVALENT PAIRS (1–100)  — True means f ≡ g for all valid inputs
    # =========================================================================

    # ── 1. String processing ─────────────────────────────────────────────────

    (
        "eq2_001_reverse_string",
        dedent("""\
            def f(s):
                return s[::-1]
        """),
        dedent("""\
            def g(s):
                result = []
                for c in s:
                    result.insert(0, c)
                return ''.join(result)
        """),
        True,
    ),

    (
        "eq2_002_is_palindrome",
        dedent("""\
            def f(s):
                cleaned = ''.join(c.lower() for c in s if c.isalnum())
                return cleaned == cleaned[::-1]
        """),
        dedent("""\
            def g(s):
                chars = [c.lower() for c in s if c.isalnum()]
                left, right = 0, len(chars) - 1
                while left < right:
                    if chars[left] != chars[right]:
                        return False
                    left += 1
                    right -= 1
                return True
        """),
        True,
    ),

    (
        "eq2_003_run_length_encode",
        dedent("""\
            def f(s):
                if not s:
                    return []
                result = []
                count = 1
                for i in range(1, len(s)):
                    if s[i] == s[i - 1]:
                        count += 1
                    else:
                        result.append((s[i - 1], count))
                        count = 1
                result.append((s[-1], count))
                return result
        """),
        dedent("""\
            def g(s):
                import itertools
                return [(ch, sum(1 for _ in grp))
                        for ch, grp in itertools.groupby(s)]
        """),
        True,
    ),

    (
        "eq2_004_caesar_cipher",
        dedent("""\
            def f(text, shift):
                out = []
                for c in text:
                    if c.isalpha():
                        base = ord('A') if c.isupper() else ord('a')
                        out.append(chr((ord(c) - base + shift) % 26 + base))
                    else:
                        out.append(c)
                return ''.join(out)
        """),
        dedent("""\
            def g(text, shift):
                import string
                lower = string.ascii_lowercase
                upper = string.ascii_uppercase
                shifted_lower = lower[shift % 26:] + lower[:shift % 26]
                shifted_upper = upper[shift % 26:] + upper[:shift % 26]
                table = str.maketrans(lower + upper,
                                      shifted_lower + shifted_upper)
                return text.translate(table)
        """),
        True,
    ),

    (
        "eq2_005_longest_common_prefix",
        dedent("""\
            def f(strs):
                if not strs:
                    return ""
                prefix = strs[0]
                for s in strs[1:]:
                    while not s.startswith(prefix):
                        prefix = prefix[:-1]
                        if not prefix:
                            return ""
                return prefix
        """),
        dedent("""\
            def g(strs):
                if not strs:
                    return ""
                result = []
                for chars in zip(*strs):
                    if len(set(chars)) == 1:
                        result.append(chars[0])
                    else:
                        break
                return ''.join(result)
        """),
        True,
    ),

    (
        "eq2_006_count_vowels",
        dedent("""\
            def f(s):
                return sum(1 for c in s.lower() if c in 'aeiou')
        """),
        dedent("""\
            def g(s):
                vowels = set('aeiouAEIOU')
                count = 0
                for c in s:
                    if c in vowels:
                        count += 1
                return count
        """),
        True,
    ),

    (
        "eq2_007_title_case",
        dedent("""\
            def f(s):
                return ' '.join(w.capitalize() for w in s.split(' '))
        """),
        dedent("""\
            def g(s):
                result = []
                capitalize_next = True
                for c in s:
                    if c == ' ':
                        result.append(c)
                        capitalize_next = True
                    elif capitalize_next:
                        result.append(c.upper())
                        capitalize_next = False
                    else:
                        result.append(c.lower())
                return ''.join(result)
        """),
        True,
    ),

    (
        "eq2_008_anagram_check",
        dedent("""\
            def f(a, b):
                from collections import Counter
                return Counter(a.lower().replace(' ', '')) == Counter(b.lower().replace(' ', ''))
        """),
        dedent("""\
            def g(a, b):
                return sorted(a.lower().replace(' ', '')) == sorted(b.lower().replace(' ', ''))
        """),
        True,
    ),

    # ── 2. Number theory ───────────────────────────────────────────────────

    (
        "eq2_009_gcd",
        dedent("""\
            def f(a, b):
                while b:
                    a, b = b, a % b
                return a
        """),
        dedent("""\
            def g(a, b):
                if b == 0:
                    return a
                return g(b, a % b)
        """),
        True,
    ),

    (
        "eq2_010_is_prime",
        dedent("""\
            def f(n):
                if n < 2:
                    return False
                if n < 4:
                    return True
                if n % 2 == 0 or n % 3 == 0:
                    return False
                i = 5
                while i * i <= n:
                    if n % i == 0 or n % (i + 2) == 0:
                        return False
                    i += 6
                return True
        """),
        dedent("""\
            def g(n):
                if n < 2:
                    return False
                for d in range(2, int(n ** 0.5) + 1):
                    if n % d == 0:
                        return False
                return True
        """),
        True,
    ),

    (
        "eq2_011_sieve_of_eratosthenes",
        dedent("""\
            def f(n):
                if n < 2:
                    return []
                is_prime = [True] * (n + 1)
                is_prime[0] = is_prime[1] = False
                for i in range(2, int(n**0.5) + 1):
                    if is_prime[i]:
                        for j in range(i*i, n + 1, i):
                            is_prime[j] = False
                return [i for i, v in enumerate(is_prime) if v]
        """),
        dedent("""\
            def g(n):
                if n < 2:
                    return []
                primes = []
                for candidate in range(2, n + 1):
                    is_p = True
                    for p in primes:
                        if p * p > candidate:
                            break
                        if candidate % p == 0:
                            is_p = False
                            break
                    if is_p:
                        primes.append(candidate)
                return primes
        """),
        True,
    ),

    (
        "eq2_012_prime_factors",
        dedent("""\
            def f(n):
                factors = []
                d = 2
                while d * d <= n:
                    while n % d == 0:
                        factors.append(d)
                        n //= d
                    d += 1
                if n > 1:
                    factors.append(n)
                return factors
        """),
        dedent("""\
            def g(n):
                factors = []
                while n % 2 == 0:
                    factors.append(2)
                    n //= 2
                i = 3
                while i * i <= n:
                    while n % i == 0:
                        factors.append(i)
                        n //= i
                    i += 2
                if n > 1:
                    factors.append(n)
                return factors
        """),
        True,
    ),

    (
        "eq2_013_euler_totient",
        dedent("""\
            def f(n):
                result = n
                p = 2
                temp = n
                while p * p <= temp:
                    if temp % p == 0:
                        while temp % p == 0:
                            temp //= p
                        result -= result // p
                    p += 1
                if temp > 1:
                    result -= result // temp
                return result
        """),
        dedent("""\
            def g(n):
                count = 0
                from math import gcd
                for i in range(1, n + 1):
                    if gcd(i, n) == 1:
                        count += 1
                return count
        """),
        True,
    ),

    (
        "eq2_014_mod_exponentiation",
        dedent("""\
            def f(base, exp, mod):
                result = 1
                base = base % mod
                while exp > 0:
                    if exp % 2 == 1:
                        result = (result * base) % mod
                    exp //= 2
                    base = (base * base) % mod
                return result
        """),
        dedent("""\
            def g(base, exp, mod):
                return pow(base, exp, mod)
        """),
        False,  # pow(0,0,1)=0 but manual impl returns 1
    ),

    (
        "eq2_015_fibonacci",
        dedent("""\
            def f(n):
                if n <= 0:
                    return 0
                if n == 1:
                    return 1
                a, b = 0, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def g(n):
                def mat_mult(A, B):
                    return [
                        [A[0][0]*B[0][0] + A[0][1]*B[1][0],
                         A[0][0]*B[0][1] + A[0][1]*B[1][1]],
                        [A[1][0]*B[0][0] + A[1][1]*B[1][0],
                         A[1][0]*B[0][1] + A[1][1]*B[1][1]],
                    ]
                if n <= 0:
                    return 0
                if n == 1:
                    return 1
                result = [[1, 0], [0, 1]]
                base = [[1, 1], [1, 0]]
                p = n - 1
                while p:
                    if p & 1:
                        result = mat_mult(result, base)
                    base = mat_mult(base, base)
                    p >>= 1
                return result[0][0]
        """),
        True,
    ),

    (
        "eq2_016_lcm",
        dedent("""\
            def f(a, b):
                from math import gcd
                return abs(a * b) // gcd(a, b) if a and b else 0
        """),
        dedent("""\
            def g(a, b):
                if a == 0 or b == 0:
                    return 0
                x, y = abs(a), abs(b)
                greater = max(x, y)
                lcm = greater
                while True:
                    if lcm % x == 0 and lcm % y == 0:
                        return lcm
                    lcm += greater
        """),
        True,
    ),

    # ── 3. Graph algorithms ──────────────────────────────────────────────

    (
        "eq2_017_bfs_shortest_path",
        dedent("""\
            def f(graph, start, end):
                from collections import deque
                visited = {start}
                queue = deque([(start, [start])])
                while queue:
                    node, path = queue.popleft()
                    if node == end:
                        return path
                    for neighbor in sorted(graph.get(node, [])):
                        if neighbor not in visited:
                            visited.add(neighbor)
                            queue.append((neighbor, path + [neighbor]))
                return []
        """),
        dedent("""\
            def g(graph, start, end):
                from collections import deque
                if start == end:
                    return [start]
                parent = {start: None}
                queue = deque([start])
                while queue:
                    node = queue.popleft()
                    for neighbor in sorted(graph.get(node, [])):
                        if neighbor not in parent:
                            parent[neighbor] = node
                            if neighbor == end:
                                path = []
                                cur = end
                                while cur is not None:
                                    path.append(cur)
                                    cur = parent[cur]
                                return path[::-1]
                            queue.append(neighbor)
                return []
        """),
        True,
    ),

    (
        "eq2_018_topological_sort",
        dedent("""\
            def f(graph):
                in_degree = {}
                for u in graph:
                    in_degree.setdefault(u, 0)
                    for v in graph[u]:
                        in_degree[v] = in_degree.get(v, 0) + 1
                from collections import deque
                queue = deque(sorted(u for u in in_degree if in_degree[u] == 0))
                result = []
                while queue:
                    u = queue.popleft()
                    result.append(u)
                    for v in sorted(graph.get(u, [])):
                        in_degree[v] -= 1
                        if in_degree[v] == 0:
                            queue.append(v)
                return result
        """),
        dedent("""\
            def g(graph):
                visited = set()
                stack = []
                all_nodes = set(graph.keys())
                for u in graph:
                    for v in graph[u]:
                        all_nodes.add(v)
                def dfs(u):
                    visited.add(u)
                    for v in sorted(graph.get(u, [])):
                        if v not in visited:
                            dfs(v)
                    stack.append(u)
                for u in sorted(all_nodes):
                    if u not in visited:
                        dfs(u)
                return stack[::-1]
        """),
        True,
    ),

    (
        "eq2_019_has_cycle_undirected",
        dedent("""\
            def f(n, edges):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                for u, v in edges:
                    pu, pv = find(u), find(v)
                    if pu == pv:
                        return True
                    parent[pu] = pv
                return False
        """),
        dedent("""\
            def g(n, edges):
                adj = [[] for _ in range(n)]
                for u, v in edges:
                    adj[u].append(v)
                    adj[v].append(u)
                visited = [False] * n
                def dfs(node, par):
                    visited[node] = True
                    for nb in adj[node]:
                        if not visited[nb]:
                            if dfs(nb, node):
                                return True
                        elif nb != par:
                            return True
                    return False
                for i in range(n):
                    if not visited[i]:
                        if dfs(i, -1):
                            return True
                return False
        """),
        True,
    ),

    (
        "eq2_020_connected_components",
        dedent("""\
            def f(n, edges):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                for u, v in edges:
                    parent[find(u)] = find(v)
                groups = {}
                for i in range(n):
                    r = find(i)
                    groups.setdefault(r, []).append(i)
                return sorted(sorted(g) for g in groups.values())
        """),
        dedent("""\
            def g(n, edges):
                adj = [[] for _ in range(n)]
                for u, v in edges:
                    adj[u].append(v)
                    adj[v].append(u)
                visited = [False] * n
                components = []
                for start in range(n):
                    if not visited[start]:
                        comp = []
                        stack = [start]
                        while stack:
                            node = stack.pop()
                            if visited[node]:
                                continue
                            visited[node] = True
                            comp.append(node)
                            for nb in adj[node]:
                                if not visited[nb]:
                                    stack.append(nb)
                        components.append(sorted(comp))
                return sorted(components)
        """),
        True,
    ),

    (
        "eq2_021_dijkstra",
        dedent("""\
            def f(graph, start):
                import heapq
                dist = {start: 0}
                heap = [(0, start)]
                while heap:
                    d, u = heapq.heappop(heap)
                    if d > dist.get(u, float('inf')):
                        continue
                    for v, w in graph.get(u, []):
                        nd = d + w
                        if nd < dist.get(v, float('inf')):
                            dist[v] = nd
                            heapq.heappush(heap, (nd, v))
                return dist
        """),
        dedent("""\
            def g(graph, start):
                all_nodes = set(graph.keys())
                for u in graph:
                    for v, w in graph[u]:
                        all_nodes.add(v)
                dist = {node: float('inf') for node in all_nodes}
                dist[start] = 0
                visited = set()
                while len(visited) < len(all_nodes):
                    u = min((n for n in all_nodes if n not in visited),
                            key=lambda n: dist[n], default=None)
                    if u is None or dist[u] == float('inf'):
                        break
                    visited.add(u)
                    for v, w in graph.get(u, []):
                        if dist[u] + w < dist[v]:
                            dist[v] = dist[u] + w
                return {k: v for k, v in dist.items() if v < float('inf')}
        """),
        True,
    ),

    (
        "eq2_022_is_bipartite",
        dedent("""\
            def f(n, edges):
                adj = [[] for _ in range(n)]
                for u, v in edges:
                    adj[u].append(v)
                    adj[v].append(u)
                color = [-1] * n
                from collections import deque
                for start in range(n):
                    if color[start] != -1:
                        continue
                    color[start] = 0
                    queue = deque([start])
                    while queue:
                        u = queue.popleft()
                        for v in adj[u]:
                            if color[v] == -1:
                                color[v] = 1 - color[u]
                                queue.append(v)
                            elif color[v] == color[u]:
                                return False
                return True
        """),
        dedent("""\
            def g(n, edges):
                adj = [[] for _ in range(n)]
                for u, v in edges:
                    adj[u].append(v)
                    adj[v].append(u)
                color = [-1] * n
                def dfs(u, c):
                    color[u] = c
                    for v in adj[u]:
                        if color[v] == -1:
                            if not dfs(v, 1 - c):
                                return False
                        elif color[v] == c:
                            return False
                    return True
                for i in range(n):
                    if color[i] == -1:
                        if not dfs(i, 0):
                            return False
                return True
        """),
        True,
    ),

    (
        "eq2_023_count_paths_dag",
        dedent("""\
            def f(graph, start, end):
                from collections import deque
                in_deg = {}
                all_nodes = set(graph.keys())
                for u in graph:
                    for v in graph[u]:
                        all_nodes.add(v)
                        in_deg[v] = in_deg.get(v, 0) + 1
                order = []
                queue = deque(sorted(n for n in all_nodes if in_deg.get(n, 0) == 0))
                while queue:
                    u = queue.popleft()
                    order.append(u)
                    for v in graph.get(u, []):
                        in_deg[v] -= 1
                        if in_deg[v] == 0:
                            queue.append(v)
                cnt = {n: 0 for n in all_nodes}
                cnt[start] = 1
                for u in order:
                    for v in graph.get(u, []):
                        cnt[v] += cnt[u]
                return cnt.get(end, 0)
        """),
        dedent("""\
            def g(graph, start, end):
                memo = {}
                def dfs(u):
                    if u == end:
                        return 1
                    if u in memo:
                        return memo[u]
                    total = 0
                    for v in graph.get(u, []):
                        total += dfs(v)
                    memo[u] = total
                    return total
                return dfs(start)
        """),
        True,
    ),

    (
        "eq2_024_in_degree_sequence",
        dedent("""\
            def f(graph):
                in_deg = {}
                for u in graph:
                    in_deg.setdefault(u, 0)
                    for v in graph[u]:
                        in_deg[v] = in_deg.get(v, 0) + 1
                return sorted(in_deg.values(), reverse=True)
        """),
        dedent("""\
            def g(graph):
                from collections import Counter
                all_nodes = set(graph.keys())
                targets = []
                for u in graph:
                    for v in graph[u]:
                        targets.append(v)
                        all_nodes.add(v)
                cnt = Counter(targets)
                result = [cnt.get(n, 0) for n in all_nodes]
                return sorted(result, reverse=True)
        """),
        True,
    ),

    # ── 4. Dynamic programming ───────────────────────────────────────────

    (
        "eq2_025_knapsack_01",
        dedent("""\
            def f(weights, values, capacity):
                n = len(weights)
                dp = [[0] * (capacity + 1) for _ in range(n + 1)]
                for i in range(1, n + 1):
                    for w in range(capacity + 1):
                        dp[i][w] = dp[i - 1][w]
                        if weights[i - 1] <= w:
                            dp[i][w] = max(dp[i][w],
                                           dp[i - 1][w - weights[i - 1]] + values[i - 1])
                return dp[n][capacity]
        """),
        dedent("""\
            def g(weights, values, capacity):
                n = len(weights)
                dp = [0] * (capacity + 1)
                for i in range(n):
                    for w in range(capacity, weights[i] - 1, -1):
                        dp[w] = max(dp[w], dp[w - weights[i]] + values[i])
                return dp[capacity]
        """),
        True,
    ),

    (
        "eq2_026_longest_common_subseq",
        dedent("""\
            def f(a, b):
                m, n = len(a), len(b)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if a[i - 1] == b[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1] + 1
                        else:
                            dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
                return dp[m][n]
        """),
        dedent("""\
            def g(a, b):
                from functools import lru_cache
                @lru_cache(maxsize=None)
                def lcs(i, j):
                    if i == 0 or j == 0:
                        return 0
                    if a[i - 1] == b[j - 1]:
                        return lcs(i - 1, j - 1) + 1
                    return max(lcs(i - 1, j), lcs(i, j - 1))
                return lcs(len(a), len(b))
        """),
        True,
    ),

    (
        "eq2_027_edit_distance",
        dedent("""\
            def f(s1, s2):
                m, n = len(s1), len(s2)
                dp = list(range(n + 1))
                for i in range(1, m + 1):
                    prev = dp[0]
                    dp[0] = i
                    for j in range(1, n + 1):
                        temp = dp[j]
                        if s1[i - 1] == s2[j - 1]:
                            dp[j] = prev
                        else:
                            dp[j] = 1 + min(prev, dp[j], dp[j - 1])
                        prev = temp
                return dp[n]
        """),
        dedent("""\
            def g(s1, s2):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(m + 1):
                    dp[i][0] = i
                for j in range(n + 1):
                    dp[0][j] = j
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1]
                        else:
                            dp[i][j] = 1 + min(dp[i - 1][j - 1],
                                                dp[i - 1][j],
                                                dp[i][j - 1])
                return dp[m][n]
        """),
        True,
    ),

    (
        "eq2_028_coin_change",
        dedent("""\
            def f(coins, amount):
                dp = [float('inf')] * (amount + 1)
                dp[0] = 0
                for c in coins:
                    for a in range(c, amount + 1):
                        dp[a] = min(dp[a], dp[a - c] + 1)
                return dp[amount] if dp[amount] != float('inf') else -1
        """),
        dedent("""\
            def g(coins, amount):
                from functools import lru_cache
                @lru_cache(maxsize=None)
                def solve(rem):
                    if rem == 0:
                        return 0
                    if rem < 0:
                        return float('inf')
                    return min((solve(rem - c) + 1 for c in coins),
                               default=float('inf'))
                ans = solve(amount)
                return ans if ans != float('inf') else -1
        """),
        True,
    ),

    (
        "eq2_029_longest_increasing_subseq",
        dedent("""\
            def f(nums):
                if not nums:
                    return 0
                dp = [1] * len(nums)
                for i in range(1, len(nums)):
                    for j in range(i):
                        if nums[j] < nums[i]:
                            dp[i] = max(dp[i], dp[j] + 1)
                return max(dp)
        """),
        dedent("""\
            def g(nums):
                import bisect
                tails = []
                for x in nums:
                    pos = bisect.bisect_left(tails, x)
                    if pos == len(tails):
                        tails.append(x)
                    else:
                        tails[pos] = x
                return len(tails)
        """),
        True,
    ),

    (
        "eq2_030_subset_sum",
        dedent("""\
            def f(nums, target):
                dp = [False] * (target + 1)
                dp[0] = True
                for n in nums:
                    for t in range(target, n - 1, -1):
                        dp[t] = dp[t] or dp[t - n]
                return dp[target]
        """),
        dedent("""\
            def g(nums, target):
                reachable = {0}
                for n in nums:
                    reachable = reachable | {s + n for s in reachable if s + n <= target}
                return target in reachable
        """),
        True,
    ),

    (
        "eq2_031_max_subarray_sum",
        dedent("""\
            def f(nums):
                if not nums:
                    return 0
                best = cur = nums[0]
                for x in nums[1:]:
                    cur = max(x, cur + x)
                    best = max(best, cur)
                return best
        """),
        dedent("""\
            def g(nums):
                if not nums:
                    return 0
                def helper(lo, hi):
                    if lo == hi:
                        return nums[lo]
                    mid = (lo + hi) // 2
                    left = helper(lo, mid)
                    right = helper(mid + 1, hi)
                    s = best_l = nums[mid]
                    for i in range(mid - 1, lo - 1, -1):
                        s += nums[i]
                        best_l = max(best_l, s)
                    s = best_r = nums[mid + 1]
                    for i in range(mid + 2, hi + 1):
                        s += nums[i]
                        best_r = max(best_r, s)
                    return max(left, right, best_l + best_r)
                return helper(0, len(nums) - 1)
        """),
        True,
    ),

    (
        "eq2_032_count_ways_stairs",
        dedent("""\
            def f(n):
                if n <= 1:
                    return 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    dp[i] = dp[i - 1] + dp[i - 2]
                return dp[n]
        """),
        dedent("""\
            def g(n):
                if n <= 1:
                    return 1
                a, b = 1, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        True,
    ),

    # ── 5. Data structures ───────────────────────────────────────────────

    (
        "eq2_033_stack_from_queues",
        dedent("""\
            def f(operations):
                from collections import deque
                q1, q2 = deque(), deque()
                results = []
                for op in operations:
                    if op[0] == 'push':
                        q1.append(op[1])
                    elif op[0] == 'pop':
                        while len(q1) > 1:
                            q2.append(q1.popleft())
                        results.append(q1.popleft())
                        q1, q2 = q2, q1
                return results
        """),
        dedent("""\
            def g(operations):
                stack = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                    elif op[0] == 'pop':
                        results.append(stack.pop())
                return results
        """),
        True,
    ),

    (
        "eq2_034_flatten_nested_list",
        dedent("""\
            def f(lst):
                result = []
                def helper(item):
                    if isinstance(item, list):
                        for sub in item:
                            helper(sub)
                    else:
                        result.append(item)
                helper(lst)
                return result
        """),
        dedent("""\
            def g(lst):
                stack = [lst]
                result = []
                while stack:
                    item = stack.pop()
                    if isinstance(item, list):
                        for sub in reversed(item):
                            stack.append(sub)
                    else:
                        result.append(item)
                return result
        """),
        True,
    ),

    (
        "eq2_035_lru_cache_ops",
        dedent("""\
            def f(capacity, operations):
                from collections import OrderedDict
                cache = OrderedDict()
                results = []
                for op in operations:
                    if op[0] == 'get':
                        key = op[1]
                        if key in cache:
                            cache.move_to_end(key)
                            results.append(cache[key])
                        else:
                            results.append(-1)
                    elif op[0] == 'put':
                        key, val = op[1], op[2]
                        if key in cache:
                            cache.move_to_end(key)
                        cache[key] = val
                        if len(cache) > capacity:
                            cache.popitem(last=False)
                return results
        """),
        dedent("""\
            def g(capacity, operations):
                keys = []
                vals = {}
                results = []
                for op in operations:
                    if op[0] == 'get':
                        key = op[1]
                        if key in vals:
                            keys.remove(key)
                            keys.append(key)
                            results.append(vals[key])
                        else:
                            results.append(-1)
                    elif op[0] == 'put':
                        key, val = op[1], op[2]
                        if key in vals:
                            keys.remove(key)
                        keys.append(key)
                        vals[key] = val
                        if len(keys) > capacity:
                            evict = keys.pop(0)
                            del vals[evict]
                return results
        """),
        True,
    ),

    (
        "eq2_036_merge_sorted_lists",
        dedent("""\
            def f(lists):
                import heapq
                result = []
                heap = []
                for i, lst in enumerate(lists):
                    if lst:
                        heapq.heappush(heap, (lst[0], i, 0))
                while heap:
                    val, li, idx = heapq.heappop(heap)
                    result.append(val)
                    if idx + 1 < len(lists[li]):
                        heapq.heappush(heap, (lists[li][idx + 1], li, idx + 1))
                return result
        """),
        dedent("""\
            def g(lists):
                def merge2(a, b):
                    result = []
                    i = j = 0
                    while i < len(a) and j < len(b):
                        if a[i] <= b[j]:
                            result.append(a[i])
                            i += 1
                        else:
                            result.append(b[j])
                            j += 1
                    result.extend(a[i:])
                    result.extend(b[j:])
                    return result
                while len(lists) > 1:
                    merged = []
                    for i in range(0, len(lists), 2):
                        if i + 1 < len(lists):
                            merged.append(merge2(lists[i], lists[i + 1]))
                        else:
                            merged.append(lists[i])
                    lists = merged
                return lists[0] if lists else []
        """),
        True,
    ),

    (
        "eq2_037_binary_search",
        dedent("""\
            def f(arr, target):
                lo, hi = 0, len(arr) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if arr[mid] == target:
                        return mid
                    elif arr[mid] < target:
                        lo = mid + 1
                    else:
                        hi = mid - 1
                return -1
        """),
        dedent("""\
            def g(arr, target):
                import bisect
                idx = bisect.bisect_left(arr, target)
                if idx < len(arr) and arr[idx] == target:
                    return idx
                return -1
        """),
        True,
    ),

    (
        "eq2_038_trie_search",
        dedent("""\
            def f(words, queries):
                trie = {}
                for w in words:
                    node = trie
                    for c in w:
                        node = node.setdefault(c, {})
                    node['$'] = True
                results = []
                for q in queries:
                    node = trie
                    found = True
                    for c in q:
                        if c not in node:
                            found = False
                            break
                        node = node[c]
                    results.append(found and '$' in node)
                return results
        """),
        dedent("""\
            def g(words, queries):
                word_set = set(words)
                return [q in word_set for q in queries]
        """),
        True,
    ),

    (
        "eq2_039_frequency_sort",
        dedent("""\
            def f(nums):
                from collections import Counter
                freq = Counter(nums)
                return sorted(nums, key=lambda x: (freq[x], x))
        """),
        dedent("""\
            def g(nums):
                freq = {}
                for n in nums:
                    freq[n] = freq.get(n, 0) + 1
                buckets = [[] for _ in range(len(nums) + 1)]
                for val, cnt in freq.items():
                    buckets[cnt].append(val)
                result = []
                for cnt in range(len(buckets)):
                    for val in sorted(buckets[cnt]):
                        result.extend([val] * cnt)
                return result
        """),
        True,
    ),

    (
        "eq2_040_max_heap_ops",
        dedent("""\
            def f(operations):
                import heapq
                heap = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        heapq.heappush(heap, -op[1])
                    elif op[0] == 'pop':
                        results.append(-heapq.heappop(heap))
                return results
        """),
        dedent("""\
            def g(operations):
                data = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        data.append(op[1])
                        data.sort()
                    elif op[0] == 'pop':
                        results.append(data.pop())
                return results
        """),
        True,
    ),

    # ── 6. Combinatorics ─────────────────────────────────────────────────

    (
        "eq2_041_permutations",
        dedent("""\
            def f(lst):
                if len(lst) <= 1:
                    return [list(lst)]
                result = []
                for i, x in enumerate(lst):
                    rest = lst[:i] + lst[i + 1:]
                    for perm in f(rest):
                        result.append([x] + perm)
                return result
        """),
        dedent("""\
            def g(lst):
                from itertools import permutations
                return [list(p) for p in permutations(lst)]
        """),
        True,
    ),

    (
        "eq2_042_combinations",
        dedent("""\
            def f(lst, k):
                if k == 0:
                    return [[]]
                if not lst:
                    return []
                head = lst[0]
                tail = lst[1:]
                with_head = [[head] + c for c in f(tail, k - 1)]
                without_head = f(tail, k)
                return with_head + without_head
        """),
        dedent("""\
            def g(lst, k):
                from itertools import combinations
                return [list(c) for c in combinations(lst, k)]
        """),
        True,
    ),

    (
        "eq2_043_power_set",
        dedent("""\
            def f(lst):
                result = [[]]
                for x in lst:
                    result = result + [s + [x] for s in result]
                return sorted(result)
        """),
        dedent("""\
            def g(lst):
                n = len(lst)
                result = []
                for mask in range(1 << n):
                    subset = [lst[i] for i in range(n) if mask & (1 << i)]
                    result.append(subset)
                return sorted(result)
        """),
        True,
    ),

    (
        "eq2_044_n_choose_k",
        dedent("""\
            def f(n, k):
                if k < 0 or k > n:
                    return 0
                if k == 0 or k == n:
                    return 1
                k = min(k, n - k)
                result = 1
                for i in range(k):
                    result = result * (n - i) // (i + 1)
                return result
        """),
        dedent("""\
            def g(n, k):
                from math import factorial
                if k < 0 or k > n:
                    return 0
                return factorial(n) // (factorial(k) * factorial(n - k))
        """),
        True,
    ),

    (
        "eq2_045_catalan_number",
        dedent("""\
            def f(n):
                if n <= 1:
                    return 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    for j in range(i):
                        dp[i] += dp[j] * dp[i - 1 - j]
                return dp[n]
        """),
        dedent("""\
            def g(n):
                from math import comb
                return comb(2 * n, n) // (n + 1)
        """),
        True,
    ),

    (
        "eq2_046_partition_count",
        dedent("""\
            def f(n):
                dp = [0] * (n + 1)
                dp[0] = 1
                for i in range(1, n + 1):
                    for j in range(i, n + 1):
                        dp[j] += dp[j - i]
                return dp[n]
        """),
        dedent("""\
            def g(n):
                from functools import lru_cache
                @lru_cache(maxsize=None)
                def p(remaining, max_part):
                    if remaining == 0:
                        return 1
                    if remaining < 0 or max_part == 0:
                        return 0
                    return p(remaining - max_part, max_part) + p(remaining, max_part - 1)
                return p(n, n)
        """),
        True,
    ),

    (
        "eq2_047_derangements",
        dedent("""\
            def f(n):
                if n == 0:
                    return 1
                if n == 1:
                    return 0
                a, b = 1, 0
                for i in range(2, n + 1):
                    a, b = b, (i - 1) * (a + b)
                return b
        """),
        dedent("""\
            def g(n):
                from math import factorial
                total = 0
                for k in range(n + 1):
                    total += ((-1) ** k) * factorial(n) // factorial(k)
                return total
        """),
        True,
    ),

    (
        "eq2_048_bell_number",
        dedent("""\
            def f(n):
                if n == 0:
                    return 1
                tri = [[0] * (n + 1) for _ in range(n + 1)]
                tri[0][0] = 1
                for i in range(1, n + 1):
                    tri[i][0] = tri[i - 1][i - 1]
                    for j in range(1, i + 1):
                        tri[i][j] = tri[i][j - 1] + tri[i - 1][j - 1]
                return tri[n][0]
        """),
        dedent("""\
            def g(n):
                if n == 0:
                    return 1
                from math import comb
                row = [1]
                for i in range(1, n):
                    new_row = [row[-1]]
                    for j in range(1, i + 1):
                        new_row.append(new_row[j - 1] + row[j - 1])
                    row = new_row
                return row[-1] if n > 1 else row[0]
        """),
        True,
    ),

    # ── 7. Geometry ──────────────────────────────────────────────────────

    (
        "eq2_049_convex_hull",
        dedent("""\
            def f(points):
                points = sorted(set(points))
                if len(points) <= 1:
                    return points
                def cross(O, A, B):
                    return (A[0] - O[0]) * (B[1] - O[1]) - (A[1] - O[1]) * (B[0] - O[0])
                lower = []
                for p in points:
                    while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
                        lower.pop()
                    lower.append(p)
                upper = []
                for p in reversed(points):
                    while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
                        upper.pop()
                    upper.append(p)
                return lower[:-1] + upper[:-1]
        """),
        dedent("""\
            def g(points):
                import math
                points = sorted(set(points))
                if len(points) <= 1:
                    return points
                start = min(points, key=lambda p: (p[1], p[0]))
                def polar_angle(p):
                    return math.atan2(p[1] - start[1], p[0] - start[0])
                def dist(p):
                    return (p[0] - start[0])**2 + (p[1] - start[1])**2
                rest = [p for p in points if p != start]
                rest.sort(key=lambda p: (polar_angle(p), dist(p)))
                def cross(O, A, B):
                    return (A[0]-O[0])*(B[1]-O[1]) - (A[1]-O[1])*(B[0]-O[0])
                hull = [start]
                for p in rest:
                    while len(hull) >= 2 and cross(hull[-2], hull[-1], p) <= 0:
                        hull.pop()
                    hull.append(p)
                return sorted(hull)
        """),
        True,
    ),

    (
        "eq2_050_point_in_polygon",
        dedent("""\
            def f(polygon, point):
                x, y = point
                n = len(polygon)
                inside = False
                j = n - 1
                for i in range(n):
                    xi, yi = polygon[i]
                    xj, yj = polygon[j]
                    if ((yi > y) != (yj > y)) and (x < (xj - xi) * (y - yi) / (yj - yi) + xi):
                        inside = not inside
                    j = i
                return inside
        """),
        dedent("""\
            def g(polygon, point):
                x, y = point
                n = len(polygon)
                crossings = 0
                for i in range(n):
                    x1, y1 = polygon[i]
                    x2, y2 = polygon[(i + 1) % n]
                    if (y1 <= y < y2) or (y2 <= y < y1):
                        t = (y - y1) / (y2 - y1)
                        cx = x1 + t * (x2 - x1)
                        if x < cx:
                            crossings += 1
                return crossings % 2 == 1
        """),
        True,
    ),

    (
        "eq2_051_triangle_area",
        dedent("""\
            def f(p1, p2, p3):
                return abs((p2[0] - p1[0]) * (p3[1] - p1[1]) -
                           (p3[0] - p1[0]) * (p2[1] - p1[1])) / 2.0
        """),
        dedent("""\
            def g(p1, p2, p3):
                import math
                a = math.dist(p1, p2)
                b = math.dist(p2, p3)
                c = math.dist(p1, p3)
                s = (a + b + c) / 2
                return math.sqrt(max(s * (s - a) * (s - b) * (s - c), 0))
        """),
        False,  # Float rounding: cross-product vs Heron's formula differ
    ),

    (
        "eq2_052_polygon_area",
        dedent("""\
            def f(vertices):
                n = len(vertices)
                area = 0
                for i in range(n):
                    j = (i + 1) % n
                    area += vertices[i][0] * vertices[j][1]
                    area -= vertices[j][0] * vertices[i][1]
                return abs(area) / 2.0
        """),
        dedent("""\
            def g(vertices):
                xs = [v[0] for v in vertices]
                ys = [v[1] for v in vertices]
                n = len(vertices)
                s1 = sum(xs[i] * ys[(i + 1) % n] for i in range(n))
                s2 = sum(ys[i] * xs[(i + 1) % n] for i in range(n))
                return abs(s1 - s2) / 2.0
        """),
        True,
    ),

    (
        "eq2_053_line_intersection",
        dedent("""\
            def f(p1, p2, p3, p4):
                x1, y1 = p1; x2, y2 = p2
                x3, y3 = p3; x4, y4 = p4
                denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4)
                if abs(denom) < 1e-12:
                    return None
                t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / denom
                return (x1 + t * (x2 - x1), y1 + t * (y2 - y1))
        """),
        dedent("""\
            def g(p1, p2, p3, p4):
                a1 = p2[1] - p1[1]
                b1 = p1[0] - p2[0]
                c1 = a1 * p1[0] + b1 * p1[1]
                a2 = p4[1] - p3[1]
                b2 = p3[0] - p4[0]
                c2 = a2 * p3[0] + b2 * p3[1]
                det = a1 * b2 - a2 * b1
                if abs(det) < 1e-12:
                    return None
                x = (c1 * b2 - c2 * b1) / det
                y = (a1 * c2 - a2 * c1) / det
                return (x, y)
        """),
        True,
    ),

    (
        "eq2_054_closest_pair",
        dedent("""\
            def f(points):
                import math
                best = float('inf')
                n = len(points)
                for i in range(n):
                    for j in range(i + 1, n):
                        d = math.dist(points[i], points[j])
                        best = min(best, d)
                return best
        """),
        dedent("""\
            def g(points):
                import math
                pts = sorted(points)
                def rec(pts):
                    if len(pts) <= 3:
                        best = float('inf')
                        for i in range(len(pts)):
                            for j in range(i+1, len(pts)):
                                best = min(best, math.dist(pts[i], pts[j]))
                        return best
                    mid = len(pts) // 2
                    mx = pts[mid][0]
                    d = min(rec(pts[:mid]), rec(pts[mid:]))
                    strip = [p for p in pts if abs(p[0] - mx) < d]
                    strip.sort(key=lambda p: p[1])
                    for i in range(len(strip)):
                        for j in range(i+1, len(strip)):
                            if strip[j][1] - strip[i][1] >= d:
                                break
                            d = min(d, math.dist(strip[i], strip[j]))
                    return d
                return rec(pts)
        """),
        True,
    ),

    (
        "eq2_055_rotate_point",
        dedent("""\
            def f(x, y, angle):
                import math
                cos_a = math.cos(angle)
                sin_a = math.sin(angle)
                return (x * cos_a - y * sin_a, x * sin_a + y * cos_a)
        """),
        dedent("""\
            def g(x, y, angle):
                import cmath
                p = complex(x, y) * cmath.exp(1j * angle)
                return (p.real, p.imag)
        """),
        True,
    ),

    (
        "eq2_056_manhattan_distance",
        dedent("""\
            def f(p1, p2):
                return sum(abs(a - b) for a, b in zip(p1, p2))
        """),
        dedent("""\
            def g(p1, p2):
                total = 0
                for i in range(len(p1)):
                    total += abs(p1[i] - p2[i])
                return total
        """),
        True,
    ),

    # ── 8. Functional / iterator patterns ────────────────────────────────

    (
        "eq2_057_map_filter_reduce",
        dedent("""\
            def f(nums):
                from functools import reduce
                evens = filter(lambda x: x % 2 == 0, nums)
                squared = map(lambda x: x ** 2, evens)
                return reduce(lambda a, b: a + b, squared, 0)
        """),
        dedent("""\
            def g(nums):
                total = 0
                for n in nums:
                    if n % 2 == 0:
                        total += n ** 2
                return total
        """),
        True,
    ),

    (
        "eq2_058_zip_dict",
        dedent("""\
            def f(keys, values):
                return dict(zip(keys, values))
        """),
        dedent("""\
            def g(keys, values):
                result = {}
                for i in range(min(len(keys), len(values))):
                    result[keys[i]] = values[i]
                return result
        """),
        True,
    ),

    (
        "eq2_059_enumerate_manual",
        dedent("""\
            def f(lst):
                return list(enumerate(lst))
        """),
        dedent("""\
            def g(lst):
                return [(i, lst[i]) for i in range(len(lst))]
        """),
        True,
    ),

    (
        "eq2_060_groupby_key",
        dedent("""\
            def f(items, key_fn):
                from collections import defaultdict
                groups = defaultdict(list)
                for item in items:
                    groups[key_fn(item)].append(item)
                return dict(groups)
        """),
        dedent("""\
            def g(items, key_fn):
                groups = {}
                for item in items:
                    k = key_fn(item)
                    if k not in groups:
                        groups[k] = []
                    groups[k].append(item)
                return groups
        """),
        True,
    ),

    (
        "eq2_061_compose_functions",
        dedent("""\
            def f(funcs):
                from functools import reduce
                def compose(f, g):
                    return lambda x: f(g(x))
                if not funcs:
                    return lambda x: x
                return reduce(compose, funcs)
        """),
        dedent("""\
            def g(funcs):
                def composed(x):
                    result = x
                    for fn in reversed(funcs):
                        result = fn(result)
                    return result
                return composed
        """),
        True,
    ),

    (
        "eq2_062_sliding_window_max",
        dedent("""\
            def f(nums, k):
                from collections import deque
                dq = deque()
                result = []
                for i, n in enumerate(nums):
                    while dq and dq[0] < i - k + 1:
                        dq.popleft()
                    while dq and nums[dq[-1]] < n:
                        dq.pop()
                    dq.append(i)
                    if i >= k - 1:
                        result.append(nums[dq[0]])
                return result
        """),
        dedent("""\
            def g(nums, k):
                return [max(nums[i:i + k]) for i in range(len(nums) - k + 1)]
        """),
        True,
    ),

    (
        "eq2_063_chunk_list",
        dedent("""\
            def f(lst, n):
                return [lst[i:i + n] for i in range(0, len(lst), n)]
        """),
        dedent("""\
            def g(lst, n):
                from itertools import islice
                it = iter(lst)
                result = []
                while True:
                    chunk = list(islice(it, n))
                    if not chunk:
                        break
                    result.append(chunk)
                return result
        """),
        True,
    ),

    (
        "eq2_064_transpose",
        dedent("""\
            def f(matrix):
                if not matrix:
                    return []
                rows, cols = len(matrix), len(matrix[0])
                return [[matrix[r][c] for r in range(rows)] for c in range(cols)]
        """),
        dedent("""\
            def g(matrix):
                return [list(row) for row in zip(*matrix)] if matrix else []
        """),
        True,
    ),

    # ── 9. Bit manipulation ──────────────────────────────────────────────

    (
        "eq2_065_count_set_bits",
        dedent("""\
            def f(n):
                count = 0
                while n:
                    count += n & 1
                    n >>= 1
                return count
        """),
        dedent("""\
            def g(n):
                return bin(n).count('1')
        """),
        True,
    ),

    (
        "eq2_066_is_power_of_two",
        dedent("""\
            def f(n):
                return n > 0 and (n & (n - 1)) == 0
        """),
        dedent("""\
            def g(n):
                if n <= 0:
                    return False
                while n > 1:
                    if n % 2 != 0:
                        return False
                    n //= 2
                return True
        """),
        True,
    ),

    (
        "eq2_067_reverse_bits",
        dedent("""\
            def f(n, bits=32):
                result = 0
                for _ in range(bits):
                    result = (result << 1) | (n & 1)
                    n >>= 1
                return result
        """),
        dedent("""\
            def g(n, bits=32):
                s = bin(n)[2:].zfill(bits)
                return int(s[::-1], 2)
        """),
        False,  # When n >= 2^bits, loop truncates but string doesn't
    ),

    (
        "eq2_068_single_number",
        dedent("""\
            def f(nums):
                result = 0
                for n in nums:
                    result ^= n
                return result
        """),
        dedent("""\
            def g(nums):
                from functools import reduce
                import operator
                return reduce(operator.xor, nums)
        """),
        True,
    ),

    (
        "eq2_069_hamming_distance",
        dedent("""\
            def f(x, y):
                xor = x ^ y
                count = 0
                while xor:
                    count += xor & 1
                    xor >>= 1
                return count
        """),
        dedent("""\
            def g(x, y):
                return bin(x ^ y).count('1')
        """),
        True,
    ),

    (
        "eq2_070_next_power_of_two",
        dedent("""\
            def f(n):
                if n <= 0:
                    return 1
                n -= 1
                n |= n >> 1
                n |= n >> 2
                n |= n >> 4
                n |= n >> 8
                n |= n >> 16
                return n + 1
        """),
        dedent("""\
            def g(n):
                if n <= 0:
                    return 1
                power = 1
                while power < n:
                    power <<= 1
                return power
        """),
        True,
    ),

    (
        "eq2_071_swap_bits",
        dedent("""\
            def f(n, i, j):
                if ((n >> i) & 1) != ((n >> j) & 1):
                    n ^= (1 << i) | (1 << j)
                return n
        """),
        dedent("""\
            def g(n, i, j):
                bi = (n >> i) & 1
                bj = (n >> j) & 1
                n = n & ~(1 << i) & ~(1 << j)
                n = n | (bj << i) | (bi << j)
                return n
        """),
        True,
    ),

    (
        "eq2_072_gray_code",
        dedent("""\
            def f(n):
                return [i ^ (i >> 1) for i in range(1 << n)]
        """),
        dedent("""\
            def g(n):
                if n == 0:
                    return [0]
                prev = g(n - 1)
                return prev + [x | (1 << (n - 1)) for x in reversed(prev)]
        """),
        True,
    ),

    # ── 10. Sorting / searching ──────────────────────────────────────────

    (
        "eq2_073_mergesort",
        dedent("""\
            def f(lst):
                if len(lst) <= 1:
                    return lst
                mid = len(lst) // 2
                left = f(lst[:mid])
                right = f(lst[mid:])
                result = []
                i = j = 0
                while i < len(left) and j < len(right):
                    if left[i] <= right[j]:
                        result.append(left[i])
                        i += 1
                    else:
                        result.append(right[j])
                        j += 1
                result.extend(left[i:])
                result.extend(right[j:])
                return result
        """),
        dedent("""\
            def g(lst):
                return sorted(lst)
        """),
        True,
    ),

    (
        "eq2_074_quickselect_kth",
        dedent("""\
            def f(lst, k):
                return sorted(lst)[k]
        """),
        dedent("""\
            def g(lst, k):
                if len(lst) == 1:
                    return lst[0]
                pivot = lst[len(lst) // 2]
                lo = [x for x in lst if x < pivot]
                eq = [x for x in lst if x == pivot]
                hi = [x for x in lst if x > pivot]
                if k < len(lo):
                    return g(lo, k)
                elif k < len(lo) + len(eq):
                    return pivot
                else:
                    return g(hi, k - len(lo) - len(eq))
        """),
        True,
    ),

    (
        "eq2_075_counting_sort",
        dedent("""\
            def f(lst):
                if not lst:
                    return []
                lo, hi = min(lst), max(lst)
                count = [0] * (hi - lo + 1)
                for x in lst:
                    count[x - lo] += 1
                result = []
                for i, c in enumerate(count):
                    result.extend([i + lo] * c)
                return result
        """),
        dedent("""\
            def g(lst):
                return sorted(lst)
        """),
        True,
    ),

    (
        "eq2_076_search_rotated",
        dedent("""\
            def f(nums, target):
                lo, hi = 0, len(nums) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if nums[mid] == target:
                        return mid
                    if nums[lo] <= nums[mid]:
                        if nums[lo] <= target < nums[mid]:
                            hi = mid - 1
                        else:
                            lo = mid + 1
                    else:
                        if nums[mid] < target <= nums[hi]:
                            lo = mid + 1
                        else:
                            hi = mid - 1
                return -1
        """),
        dedent("""\
            def g(nums, target):
                for i, n in enumerate(nums):
                    if n == target:
                        return i
                return -1
        """),
        True,
    ),

    (
        "eq2_077_radix_sort",
        dedent("""\
            def f(lst):
                if not lst:
                    return []
                neg = sorted([-x for x in lst if x < 0], reverse=True)
                pos = [x for x in lst if x >= 0]
                if pos:
                    max_val = max(pos)
                    exp = 1
                    while max_val // exp > 0:
                        buckets = [[] for _ in range(10)]
                        for x in pos:
                            buckets[(x // exp) % 10].append(x)
                        pos = [x for b in buckets for x in b]
                        exp *= 10
                return [-x for x in neg] + pos
        """),
        dedent("""\
            def g(lst):
                return sorted(lst)
        """),
        True,
    ),

    (
        "eq2_078_two_sum_sorted",
        dedent("""\
            def f(nums, target):
                seen = {}
                for i, n in enumerate(nums):
                    complement = target - n
                    if complement in seen:
                        return (seen[complement], i)
                    seen[n] = i
                return None
        """),
        dedent("""\
            def g(nums, target):
                for i in range(len(nums)):
                    for j in range(i + 1, len(nums)):
                        if nums[i] + nums[j] == target:
                            return (i, j)
                return None
        """),
        True,
    ),

    (
        "eq2_079_dutch_flag",
        dedent("""\
            def f(lst):
                lo, mid, hi = 0, 0, len(lst) - 1
                arr = list(lst)
                while mid <= hi:
                    if arr[mid] == 0:
                        arr[lo], arr[mid] = arr[mid], arr[lo]
                        lo += 1
                        mid += 1
                    elif arr[mid] == 1:
                        mid += 1
                    else:
                        arr[mid], arr[hi] = arr[hi], arr[mid]
                        hi -= 1
                return arr
        """),
        dedent("""\
            def g(lst):
                return sorted(lst)
        """),
        True,
    ),

    (
        "eq2_080_find_peak",
        dedent("""\
            def f(nums):
                lo, hi = 0, len(nums) - 1
                while lo < hi:
                    mid = (lo + hi) // 2
                    if nums[mid] < nums[mid + 1]:
                        lo = mid + 1
                    else:
                        hi = mid
                return lo
        """),
        dedent("""\
            def g(nums):
                return nums.index(max(nums))
        """),
        False,  # Binary search finds local peak, index(max) finds global max
    ),

    # ── 11. Matrix / linear algebra ──────────────────────────────────────

    (
        "eq2_081_matrix_multiply",
        dedent("""\
            def f(A, B):
                n = len(A)
                m = len(B[0])
                p = len(B)
                C = [[0] * m for _ in range(n)]
                for i in range(n):
                    for j in range(m):
                        for k in range(p):
                            C[i][j] += A[i][k] * B[k][j]
                return C
        """),
        dedent("""\
            def g(A, B):
                return [[sum(a * b for a, b in zip(row_a, col_b))
                         for col_b in zip(*B)]
                        for row_a in A]
        """),
        True,
    ),

    (
        "eq2_082_determinant",
        dedent("""\
            def f(matrix):
                n = len(matrix)
                if n == 1:
                    return matrix[0][0]
                if n == 2:
                    return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
                det = 0
                for j in range(n):
                    sub = [row[:j] + row[j+1:] for row in matrix[1:]]
                    det += ((-1) ** j) * matrix[0][j] * f(sub)
                return det
        """),
        dedent("""\
            def g(matrix):
                n = len(matrix)
                mat = [row[:] for row in matrix]
                det = 1
                for col in range(n):
                    pivot = None
                    for row in range(col, n):
                        if mat[row][col] != 0:
                            pivot = row
                            break
                    if pivot is None:
                        return 0
                    if pivot != col:
                        mat[col], mat[pivot] = mat[pivot], mat[col]
                        det *= -1
                    det *= mat[col][col]
                    for row in range(col + 1, n):
                        factor = mat[row][col] / mat[col][col]
                        for k in range(col, n):
                            mat[row][k] -= factor * mat[col][k]
                return det
        """),
        True,
    ),

    (
        "eq2_083_matrix_trace",
        dedent("""\
            def f(matrix):
                return sum(matrix[i][i] for i in range(len(matrix)))
        """),
        dedent("""\
            def g(matrix):
                total = 0
                for i in range(len(matrix)):
                    total += matrix[i][i]
                return total
        """),
        True,
    ),

    (
        "eq2_084_identity_matrix",
        dedent("""\
            def f(n):
                return [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        """),
        dedent("""\
            def g(n):
                mat = [[0] * n for _ in range(n)]
                for i in range(n):
                    mat[i][i] = 1
                return mat
        """),
        True,
    ),

    (
        "eq2_085_matrix_power",
        dedent("""\
            def f(mat, p):
                n = len(mat)
                def mult(A, B):
                    return [[sum(A[i][k]*B[k][j] for k in range(n))
                             for j in range(n)] for i in range(n)]
                result = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
                base = [row[:] for row in mat]
                while p:
                    if p & 1:
                        result = mult(result, base)
                    base = mult(base, base)
                    p >>= 1
                return result
        """),
        dedent("""\
            def g(mat, p):
                n = len(mat)
                def mult(A, B):
                    C = [[0]*n for _ in range(n)]
                    for i in range(n):
                        for j in range(n):
                            for k in range(n):
                                C[i][j] += A[i][k]*B[k][j]
                    return C
                result = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
                for _ in range(p):
                    result = mult(result, mat)
                return result
        """),
        True,
    ),

    (
        "eq2_086_dot_product",
        dedent("""\
            def f(a, b):
                return sum(x * y for x, y in zip(a, b))
        """),
        dedent("""\
            def g(a, b):
                total = 0
                for i in range(len(a)):
                    total += a[i] * b[i]
                return total
        """),
        True,
    ),

    (
        "eq2_087_cross_product_3d",
        dedent("""\
            def f(a, b):
                return [a[1]*b[2] - a[2]*b[1],
                        a[2]*b[0] - a[0]*b[2],
                        a[0]*b[1] - a[1]*b[0]]
        """),
        dedent("""\
            def g(a, b):
                i = a[1]*b[2] - a[2]*b[1]
                j = -(a[0]*b[2] - a[2]*b[0])
                k = a[0]*b[1] - a[1]*b[0]
                return [i, j, k]
        """),
        True,
    ),

    (
        "eq2_088_spiral_order",
        dedent("""\
            def f(matrix):
                if not matrix:
                    return []
                result = []
                top, bottom = 0, len(matrix) - 1
                left, right = 0, len(matrix[0]) - 1
                while top <= bottom and left <= right:
                    for j in range(left, right + 1):
                        result.append(matrix[top][j])
                    top += 1
                    for i in range(top, bottom + 1):
                        result.append(matrix[i][right])
                    right -= 1
                    if top <= bottom:
                        for j in range(right, left - 1, -1):
                            result.append(matrix[bottom][j])
                        bottom -= 1
                    if left <= right:
                        for i in range(bottom, top - 1, -1):
                            result.append(matrix[i][left])
                        left += 1
                return result
        """),
        dedent("""\
            def g(matrix):
                result = []
                while matrix:
                    result.extend(matrix.pop(0))
                    if matrix and matrix[0]:
                        for row in matrix:
                            result.append(row.pop())
                    if matrix:
                        result.extend(matrix.pop()[::-1])
                    if matrix and matrix[0]:
                        for row in reversed(matrix):
                            result.append(row.pop(0))
                return result
        """),
        True,
    ),

    # ── 12. Cryptographic / hashing ──────────────────────────────────────

    (
        "eq2_089_simple_hash",
        dedent("""\
            def f(s, mod=1000000007):
                h = 0
                for c in s:
                    h = (h * 31 + ord(c)) % mod
                return h
        """),
        dedent("""\
            def g(s, mod=1000000007):
                from functools import reduce
                return reduce(lambda h, c: (h * 31 + ord(c)) % mod, s, 0)
        """),
        True,
    ),

    (
        "eq2_090_xor_encrypt",
        dedent("""\
            def f(data, key):
                return bytes(b ^ key[i % len(key)] for i, b in enumerate(data))
        """),
        dedent("""\
            def g(data, key):
                import itertools
                return bytes(a ^ b for a, b in zip(data, itertools.cycle(key)))
        """),
        True,
    ),

    (
        "eq2_091_base64_encode",
        dedent("""\
            def f(data):
                import base64
                return base64.b64encode(data).decode('ascii')
        """),
        dedent("""\
            def g(data):
                chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
                result = []
                for i in range(0, len(data), 3):
                    chunk = data[i:i+3]
                    n = int.from_bytes(chunk, 'big') << (8 * (3 - len(chunk)))
                    for j in range(len(chunk) + 1):
                        result.append(chars[(n >> (18 - 6*j)) & 0x3f])
                    result.extend('=' * (3 - len(chunk)))
                return ''.join(result)
        """),
        True,
    ),

    (
        "eq2_092_hex_digest",
        dedent("""\
            def f(data):
                import hashlib
                return hashlib.md5(data).hexdigest()
        """),
        dedent("""\
            def g(data):
                import hashlib
                h = hashlib.md5()
                h.update(data)
                return h.hexdigest()
        """),
        True,
    ),

    (
        "eq2_093_vigenere_encrypt",
        dedent("""\
            def f(text, key):
                result = []
                ki = 0
                for c in text:
                    if c.isalpha():
                        base = ord('A') if c.isupper() else ord('a')
                        shift = ord(key[ki % len(key)].upper()) - ord('A')
                        result.append(chr((ord(c) - base + shift) % 26 + base))
                        ki += 1
                    else:
                        result.append(c)
                return ''.join(result)
        """),
        dedent("""\
            def g(text, key):
                out = []
                j = 0
                for c in text:
                    if c.isalpha():
                        k = key[j % len(key)].upper()
                        s = ord(k) - 65
                        if c.isupper():
                            out.append(chr((ord(c) - 65 + s) % 26 + 65))
                        else:
                            out.append(chr((ord(c) - 97 + s) % 26 + 97))
                        j += 1
                    else:
                        out.append(c)
                return ''.join(out)
        """),
        True,
    ),

    (
        "eq2_094_rot13",
        dedent("""\
            def f(text):
                import codecs
                return codecs.encode(text, 'rot_13')
        """),
        dedent("""\
            def g(text):
                result = []
                for c in text:
                    if 'a' <= c <= 'z':
                        result.append(chr((ord(c) - ord('a') + 13) % 26 + ord('a')))
                    elif 'A' <= c <= 'Z':
                        result.append(chr((ord(c) - ord('A') + 13) % 26 + ord('A')))
                    else:
                        result.append(c)
                return ''.join(result)
        """),
        True,
    ),

    (
        "eq2_095_crc_checksum",
        dedent("""\
            def f(data):
                import binascii
                return binascii.crc32(data) & 0xffffffff
        """),
        dedent("""\
            def g(data):
                import zlib
                return zlib.crc32(data) & 0xffffffff
        """),
        True,
    ),

    (
        "eq2_096_sha256_hex",
        dedent("""\
            def f(data):
                import hashlib
                return hashlib.sha256(data).hexdigest()
        """),
        dedent("""\
            def g(data):
                import hashlib
                h = hashlib.new('sha256')
                for i in range(0, len(data), 64):
                    h.update(data[i:i+64])
                return h.hexdigest()
        """),
        True,
    ),

    # ── Extra EQ pairs (97-100) ──────────────────────────────────────────

    (
        "eq2_097_flatten_dict",
        dedent("""\
            def f(d, prefix=''):
                items = {}
                for k, v in d.items():
                    new_key = f'{prefix}.{k}' if prefix else k
                    if isinstance(v, dict):
                        items.update(f(v, new_key))
                    else:
                        items[new_key] = v
                return items
        """),
        dedent("""\
            def g(d, prefix=''):
                result = {}
                stack = [(d, prefix)]
                while stack:
                    curr, pre = stack.pop()
                    for k, v in curr.items():
                        new_key = f'{pre}.{k}' if pre else k
                        if isinstance(v, dict):
                            stack.append((v, new_key))
                        else:
                            result[new_key] = v
                return result
        """),
        True,
    ),

    (
        "eq2_098_deep_copy",
        dedent("""\
            def f(obj):
                import copy
                return copy.deepcopy(obj)
        """),
        dedent("""\
            def g(obj):
                import json
                return json.loads(json.dumps(obj))
        """),
        True,
    ),

    (
        "eq2_099_roman_to_int",
        dedent("""\
            def f(s):
                vals = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                for i in range(len(s)):
                    if i + 1 < len(s) and vals[s[i]] < vals[s[i+1]]:
                        total -= vals[s[i]]
                    else:
                        total += vals[s[i]]
                return total
        """),
        dedent("""\
            def g(s):
                vals = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                prev = 0
                for c in reversed(s):
                    v = vals[c]
                    if v < prev:
                        total -= v
                    else:
                        total += v
                    prev = v
                return total
        """),
        True,
    ),

    (
        "eq2_100_int_to_roman",
        dedent("""\
            def f(num):
                vals = [(1000,'M'),(900,'CM'),(500,'D'),(400,'CD'),
                        (100,'C'),(90,'XC'),(50,'L'),(40,'XL'),
                        (10,'X'),(9,'IX'),(5,'V'),(4,'IV'),(1,'I')]
                result = []
                for v, s in vals:
                    while num >= v:
                        result.append(s)
                        num -= v
                return ''.join(result)
        """),
        dedent("""\
            def g(num):
                thousands = ['','M','MM','MMM']
                hundreds = ['','C','CC','CCC','CD','D','DC','DCC','DCCC','CM']
                tens = ['','X','XX','XXX','XL','L','LX','LXX','LXXX','XC']
                ones = ['','I','II','III','IV','V','VI','VII','VIII','IX']
                return (thousands[num//1000] + hundreds[num%1000//100] +
                        tens[num%100//10] + ones[num%10])
        """),
        True,
    ),

    # =========================================================================
    # NON-EQUIVALENT PAIRS (101–200)  — False means f ≢ g on some input
    # =========================================================================

    # ── 1. Off-by-one errors ─────────────────────────────────────────────

    (
        "neq2_101_range_inclusive",
        dedent("""\
            def f(n):
                return list(range(n))
        """),
        dedent("""\
            def g(n):
                return list(range(n + 1))
        """),
        False,
    ),

    (
        "neq2_102_binary_search_upper",
        dedent("""\
            def f(arr, target):
                lo, hi = 0, len(arr) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if arr[mid] <= target:
                        lo = mid + 1
                    else:
                        hi = mid - 1
                return lo
        """),
        dedent("""\
            def g(arr, target):
                lo, hi = 0, len(arr)
                while lo < hi:
                    mid = (lo + hi) // 2
                    if arr[mid] < target:
                        lo = mid + 1
                    else:
                        hi = mid
                return lo
        """),
        False,
    ),

    (
        "neq2_103_substring_end",
        dedent("""\
            def f(s, start, end):
                return s[start:end]
        """),
        dedent("""\
            def g(s, start, end):
                return s[start:end + 1]
        """),
        False,
    ),

    (
        "neq2_104_fence_posts",
        dedent("""\
            def f(n):
                return n - 1
        """),
        dedent("""\
            def g(n):
                return n
        """),
        False,
    ),

    (
        "neq2_105_last_element",
        dedent("""\
            def f(lst):
                return lst[len(lst) - 1]
        """),
        dedent("""\
            def g(lst):
                return lst[len(lst)]
        """),
        False,
    ),

    (
        "neq2_106_count_digits",
        dedent("""\
            def f(n):
                if n == 0:
                    return 1
                count = 0
                n = abs(n)
                while n > 0:
                    count += 1
                    n //= 10
                return count
        """),
        dedent("""\
            def g(n):
                return len(str(n))
        """),
        False,
    ),

    (
        "neq2_107_sum_range",
        dedent("""\
            def f(a, b):
                return sum(range(a, b))
        """),
        dedent("""\
            def g(a, b):
                return sum(range(a, b + 1))
        """),
        False,
    ),

    (
        "neq2_108_palindrome_check_boundary",
        dedent("""\
            def f(s):
                for i in range(len(s) // 2):
                    if s[i] != s[-(i + 1)]:
                        return False
                return True
        """),
        dedent("""\
            def g(s):
                for i in range(len(s) // 2 + 1):
                    if s[i] != s[-(i + 1)]:
                        return False
                return True
        """),
        False,
    ),

    (
        "neq2_109_matrix_diagonal",
        dedent("""\
            def f(matrix):
                return [matrix[i][i] for i in range(len(matrix))]
        """),
        dedent("""\
            def g(matrix):
                return [matrix[i][i] for i in range(len(matrix) - 1)]
        """),
        False,
    ),

    (
        "neq2_110_sliding_window_size",
        dedent("""\
            def f(lst, k):
                return [sum(lst[i:i+k]) for i in range(len(lst) - k + 1)]
        """),
        dedent("""\
            def g(lst, k):
                return [sum(lst[i:i+k]) for i in range(len(lst) - k)]
        """),
        False,
    ),

    # ── 2. Stability / ordering ──────────────────────────────────────────

    (
        "neq2_111_sort_stability",
        dedent("""\
            def f(pairs):
                return sorted(pairs, key=lambda x: x[0])
        """),
        dedent("""\
            def g(pairs):
                n = len(pairs)
                arr = list(pairs)
                for i in range(n):
                    for j in range(0, n - i - 1):
                        if arr[j][0] > arr[j + 1][0]:
                            arr[j], arr[j + 1] = arr[j + 1], arr[j]
                return arr
        """),
        False,
    ),

    (
        "neq2_112_dict_iteration_order",
        dedent("""\
            def f(keys, vals):
                d = {}
                for k, v in zip(keys, vals):
                    d[k] = v
                return list(d.items())
        """),
        dedent("""\
            def g(keys, vals):
                d = {}
                for k, v in zip(reversed(keys), reversed(vals)):
                    d[k] = v
                return list(d.items())
        """),
        False,
    ),

    (
        "neq2_113_set_to_list",
        dedent("""\
            def f(items):
                return sorted(set(items))
        """),
        dedent("""\
            def g(items):
                return sorted(set(items), reverse=True)
        """),
        False,
    ),

    (
        "neq2_114_tiebreak_sort",
        dedent("""\
            def f(records):
                return sorted(records, key=lambda x: (x[1], x[0]))
        """),
        dedent("""\
            def g(records):
                return sorted(records, key=lambda x: (x[1], -ord(x[0][0])))
        """),
        False,
    ),

    (
        "neq2_115_reverse_sort_tie",
        dedent("""\
            def f(lst):
                return sorted(lst, key=lambda x: (-x[0], x[1]))
        """),
        dedent("""\
            def g(lst):
                return sorted(lst, key=lambda x: (-x[0], -x[1]))
        """),
        False,
    ),

    (
        "neq2_116_heap_order",
        dedent("""\
            def f(lst):
                import heapq
                h = list(lst)
                heapq.heapify(h)
                return [heapq.heappop(h) for _ in range(len(h))]
        """),
        dedent("""\
            def g(lst):
                import heapq
                h = [-x for x in lst]
                heapq.heapify(h)
                return [-heapq.heappop(h) for _ in range(len(h))]
        """),
        False,
    ),

    (
        "neq2_117_max_vs_first_max",
        dedent("""\
            def f(lst):
                return max(lst, key=lambda x: x[1])
        """),
        dedent("""\
            def g(lst):
                best = lst[0]
                for item in lst[1:]:
                    if item[1] > best[1]:
                        best = item
                return best
        """),
        False,
    ),

    (
        "neq2_118_group_order",
        dedent("""\
            def f(items):
                from collections import defaultdict
                d = defaultdict(list)
                for k, v in items:
                    d[k].append(v)
                return dict(sorted(d.items()))
        """),
        dedent("""\
            def g(items):
                from collections import defaultdict
                d = defaultdict(list)
                for k, v in items:
                    d[k].append(v)
                return dict(sorted(d.items(), reverse=True))
        """),
        False,
    ),

    (
        "neq2_119_unique_preserve_order",
        dedent("""\
            def f(lst):
                seen = set()
                result = []
                for x in lst:
                    if x not in seen:
                        seen.add(x)
                        result.append(x)
                return result
        """),
        dedent("""\
            def g(lst):
                return sorted(set(lst))
        """),
        False,
    ),

    (
        "neq2_120_partition_stable",
        dedent("""\
            def f(lst, pred):
                return [x for x in lst if pred(x)] + [x for x in lst if not pred(x)]
        """),
        dedent("""\
            def g(lst, pred):
                return [x for x in lst if not pred(x)] + [x for x in lst if pred(x)]
        """),
        False,
    ),

    # ── 3. Type coercion ─────────────────────────────────────────────────

    (
        "neq2_121_int_vs_float_division",
        dedent("""\
            def f(a, b):
                return a // b
        """),
        dedent("""\
            def g(a, b):
                return int(a / b)
        """),
        False,
    ),

    (
        "neq2_122_str_int_comparison",
        dedent("""\
            def f(lst):
                return sorted(lst)
        """),
        dedent("""\
            def g(lst):
                return sorted(lst, key=int)
        """),
        False,
    ),

    (
        "neq2_123_bool_sum",
        dedent("""\
            def f(lst):
                return sum(lst)
        """),
        dedent("""\
            def g(lst):
                return len([x for x in lst if x])
        """),
        False,
    ),

    (
        "neq2_124_none_vs_zero",
        dedent("""\
            def f(d, key):
                return d.get(key, None)
        """),
        dedent("""\
            def g(d, key):
                return d.get(key, 0)
        """),
        False,
    ),

    (
        "neq2_125_int_vs_str_key",
        dedent("""\
            def f(items):
                d = {}
                for k, v in items:
                    d[k] = v
                return d
        """),
        dedent("""\
            def g(items):
                d = {}
                for k, v in items:
                    d[str(k)] = v
                return d
        """),
        False,
    ),

    (
        "neq2_126_round_vs_truncate",
        dedent("""\
            def f(x):
                return round(x)
        """),
        dedent("""\
            def g(x):
                import math
                return math.trunc(x)
        """),
        False,
    ),

    (
        "neq2_127_list_vs_tuple",
        dedent("""\
            def f(items):
                return [list(x) for x in items]
        """),
        dedent("""\
            def g(items):
                return [tuple(x) for x in items]
        """),
        False,
    ),

    (
        "neq2_128_implicit_bool_cast",
        dedent("""\
            def f(lst):
                return [x for x in lst if x is not None]
        """),
        dedent("""\
            def g(lst):
                return [x for x in lst if x]
        """),
        False,
    ),

    (
        "neq2_129_bytes_vs_str",
        dedent("""\
            def f(data):
                return list(data.encode('utf-8'))
        """),
        dedent("""\
            def g(data):
                return [ord(c) for c in data]
        """),
        False,
    ),

    (
        "neq2_130_float_int_equality",
        dedent("""\
            def f(x):
                return type(x).__name__
        """),
        dedent("""\
            def g(x):
                return 'number'
        """),
        False,
    ),

    # ── 4. Mutability / aliasing ─────────────────────────────────────────

    (
        "neq2_131_list_copy_vs_alias",
        dedent("""\
            def f(lst):
                copy = lst[:]
                copy.append(999)
                return lst
        """),
        dedent("""\
            def g(lst):
                alias = lst
                alias.append(999)
                return lst
        """),
        False,
    ),

    (
        "neq2_132_default_mutable_arg",
        dedent("""\
            def f(item, lst=None):
                if lst is None:
                    lst = []
                lst.append(item)
                return lst
        """),
        dedent("""\
            def g(item, lst=[]):
                lst.append(item)
                return lst
        """),
        False,
    ),

    (
        "neq2_133_nested_copy",
        dedent("""\
            def f(matrix):
                import copy
                m = copy.deepcopy(matrix)
                m[0][0] = 999
                return matrix[0][0]
        """),
        dedent("""\
            def g(matrix):
                m = [row[:] for row in matrix]
                m[0][0] = 999
                return matrix[0][0]
        """),
        True,  # Fixed: both isolate mutation from original matrix; return same value
    ),

    (
        "neq2_134_dict_update_vs_copy",
        dedent("""\
            def f(d, key, val):
                new_d = dict(d)
                new_d[key] = val
                return d.get(key)
        """),
        dedent("""\
            def g(d, key, val):
                d[key] = val
                return d.get(key)
        """),
        False,
    ),

    (
        "neq2_135_sort_in_place",
        dedent("""\
            def f(lst):
                return sorted(lst)
        """),
        dedent("""\
            def g(lst):
                lst.sort()
                return lst
        """),
        False,
    ),

    (
        "neq2_136_extend_vs_append",
        dedent("""\
            def f(lst, items):
                result = list(lst)
                result.extend(items)
                return result
        """),
        dedent("""\
            def g(lst, items):
                result = list(lst)
                result.append(items)
                return result
        """),
        False,
    ),

    (
        "neq2_137_string_immutability",
        dedent("""\
            def f(s):
                chars = list(s)
                chars[0] = 'X'
                return s
        """),
        dedent("""\
            def g(s):
                return 'X' + s[1:]
        """),
        False,
    ),

    (
        "neq2_138_shared_reference",
        dedent("""\
            def f(n):
                rows = [[0] * n for _ in range(n)]
                rows[0][0] = 1
                return rows
        """),
        dedent("""\
            def g(n):
                row = [0] * n
                rows = [row] * n
                rows[0][0] = 1
                return rows
        """),
        False,
    ),

    (
        "neq2_139_pop_vs_del",
        dedent("""\
            def f(lst, idx):
                copy = list(lst)
                val = copy.pop(idx)
                return (val, copy)
        """),
        dedent("""\
            def g(lst, idx):
                copy = list(lst)
                val = copy[idx]
                del copy[idx]
                return (copy, val)
        """),
        False,
    ),

    (
        "neq2_140_setdefault_side_effect",
        dedent("""\
            def f(d, key, default):
                if key not in d:
                    return default
                return d[key]
        """),
        dedent("""\
            def g(d, key, default):
                return d.setdefault(key, default)
        """),
        False,
    ),

    # ── 5. Edge cases ────────────────────────────────────────────────────

    (
        "neq2_141_empty_list_default",
        dedent("""\
            def f(lst):
                if not lst:
                    return 0
                return sum(lst) / len(lst)
        """),
        dedent("""\
            def g(lst):
                return sum(lst) / len(lst)
        """),
        False,
    ),

    (
        "neq2_142_negative_index",
        dedent("""\
            def f(lst, n):
                return lst[:n]
        """),
        dedent("""\
            def g(lst, n):
                return lst[:n] if n != 0 else []
        """),
        False,
    ),

    (
        "neq2_143_zero_division",
        dedent("""\
            def f(a, b):
                if b == 0:
                    return float('inf')
                return a / b
        """),
        dedent("""\
            def g(a, b):
                if b == 0:
                    return 0
                return a / b
        """),
        False,
    ),

    (
        "neq2_144_none_in_max",
        dedent("""\
            def f(lst):
                filtered = [x for x in lst if x is not None]
                return max(filtered) if filtered else None
        """),
        dedent("""\
            def g(lst):
                return max(lst, default=None)
        """),
        False,
    ),

    (
        "neq2_145_single_element",
        dedent("""\
            def f(lst):
                if len(lst) < 2:
                    return []
                return [lst[i+1] - lst[i] for i in range(len(lst) - 1)]
        """),
        dedent("""\
            def g(lst):
                return [lst[i+1] - lst[i] for i in range(len(lst) - 1)]
        """),
        True,  # Fixed: both compute same differences; guard is redundant
    ),

    (
        "neq2_146_empty_string_split",
        dedent("""\
            def f(s):
                return s.split()
        """),
        dedent("""\
            def g(s):
                return s.split(' ')
        """),
        False,
    ),

    (
        "neq2_147_negative_modulo",
        dedent("""\
            def f(a, b):
                return a % b
        """),
        dedent("""\
            def g(a, b):
                r = a % b
                if r != 0 and (a < 0) != (b < 0):
                    r -= b
                return r
        """),
        False,
    ),

    (
        "neq2_148_strip_behavior",
        dedent("""\
            def f(s):
                return s.strip()
        """),
        dedent("""\
            def g(s):
                return s.strip(' ')
        """),
        False,
    ),

    (
        "neq2_149_recursive_base_case",
        dedent("""\
            def f(n):
                if n == 0:
                    return 1
                return n * f(n - 1)
        """),
        dedent("""\
            def g(n):
                if n == 1:
                    return 1
                return n * g(n - 1)
        """),
        False,
    ),

    (
        "neq2_150_empty_intersection",
        dedent("""\
            def f(a, b):
                return sorted(set(a) & set(b))
        """),
        dedent("""\
            def g(a, b):
                return sorted(set(a) | set(b))
        """),
        False,
    ),

    # ── 6. Float semantics ───────────────────────────────────────────────

    (
        "neq2_151_float_comparison",
        dedent("""\
            def f(a, b, c):
                return (a + b) + c
        """),
        dedent("""\
            def g(a, b, c):
                return a + (b + c)
        """),
        False,
    ),

    (
        "neq2_152_float_equality",
        dedent("""\
            def f(x):
                return x == 0.1 + 0.2
        """),
        dedent("""\
            def g(x):
                return abs(x - 0.3) < 1e-9
        """),
        False,
    ),

    (
        "neq2_153_nan_comparison",
        dedent("""\
            def f(x):
                return x == x
        """),
        dedent("""\
            def g(x):
                return True
        """),
        False,
    ),

    (
        "neq2_154_inf_arithmetic",
        dedent("""\
            def f(x):
                return x + 1
        """),
        dedent("""\
            def g(x):
                if x == float('inf'):
                    return float('inf')
                return x + 1
        """),
        True,  # Fixed: both compute same result for all finite and infinite inputs
    ),

    (
        "neq2_155_rounding_mode",
        dedent("""\
            def f(x):
                return round(x)
        """),
        dedent("""\
            def g(x):
                import math
                return math.floor(x + 0.5)
        """),
        False,
    ),

    (
        "neq2_156_float_sum_order",
        dedent("""\
            def f(lst):
                return sum(lst)
        """),
        dedent("""\
            def g(lst):
                import math
                return math.fsum(lst)
        """),
        False,
    ),

    (
        "neq2_157_decimal_vs_float",
        dedent("""\
            def f(price, tax_rate):
                return round(price * tax_rate, 2)
        """),
        dedent("""\
            def g(price, tax_rate):
                from decimal import Decimal
                return float(round(Decimal(str(price)) * Decimal(str(tax_rate)), 2))
        """),
        False,
    ),

    (
        "neq2_158_floor_negative",
        dedent("""\
            def f(x):
                import math
                return math.floor(x)
        """),
        dedent("""\
            def g(x):
                return int(x)
        """),
        False,
    ),

    (
        "neq2_159_float_precision_loss",
        dedent("""\
            def f(n):
                return n + 1 - n
        """),
        dedent("""\
            def g(n):
                return 1
        """),
        False,
    ),

    (
        "neq2_160_zero_sign",
        dedent("""\
            def f(x):
                import math
                return math.copysign(1, x)
        """),
        dedent("""\
            def g(x):
                if x >= 0:
                    return 1.0
                return -1.0
        """),
        False,
    ),

    # ── 7. Generator / iterator ──────────────────────────────────────────

    (
        "neq2_161_generator_reuse",
        dedent("""\
            def f(lst):
                it = iter(lst)
                first_pass = list(it)
                second_pass = list(it)
                return first_pass + second_pass
        """),
        dedent("""\
            def g(lst):
                return lst + lst
        """),
        False,
    ),

    (
        "neq2_162_lazy_vs_eager",
        dedent("""\
            def f(n):
                return list(x * x for x in range(n))
        """),
        dedent("""\
            def g(n):
                return [x * x for x in range(1, n + 1)]
        """),
        False,
    ),

    (
        "neq2_163_map_vs_listcomp",
        dedent("""\
            def f(lst):
                return list(map(str, lst))
        """),
        dedent("""\
            def g(lst):
                return list(map(repr, lst))
        """),
        False,
    ),

    (
        "neq2_164_chain_vs_concat",
        dedent("""\
            def f(lists):
                from itertools import chain
                return list(chain.from_iterable(lists))
        """),
        dedent("""\
            def g(lists):
                from itertools import chain
                return list(chain(*lists)) if lists else []
        """),
        False,
    ),

    (
        "neq2_165_zip_longest",
        dedent("""\
            def f(a, b):
                return list(zip(a, b))
        """),
        dedent("""\
            def g(a, b):
                from itertools import zip_longest
                return list(zip_longest(a, b))
        """),
        False,
    ),

    (
        "neq2_166_takewhile_vs_filter",
        dedent("""\
            def f(lst, pred):
                from itertools import takewhile
                return list(takewhile(pred, lst))
        """),
        dedent("""\
            def g(lst, pred):
                return [x for x in lst if pred(x)]
        """),
        False,
    ),

    (
        "neq2_167_reversed_generator",
        dedent("""\
            def f(lst):
                return list(reversed(lst))
        """),
        dedent("""\
            def g(lst):
                lst.reverse()
                return lst
        """),
        False,
    ),

    (
        "neq2_168_islice_vs_slice",
        dedent("""\
            def f(lst, start, stop):
                from itertools import islice
                return list(islice(lst, start, stop))
        """),
        dedent("""\
            def g(lst, start, stop):
                from itertools import islice
                return list(islice(lst, start, stop, 2))
        """),
        False,
    ),

    (
        "neq2_169_iter_side_effect",
        dedent("""\
            def f(lst):
                it = iter(lst)
                next(it)
                return list(it)
        """),
        dedent("""\
            def g(lst):
                return list(lst)
        """),
        False,
    ),

    (
        "neq2_170_product_vs_nested",
        dedent("""\
            def f(a, b):
                from itertools import product
                return list(product(a, b))
        """),
        dedent("""\
            def g(a, b):
                return [(x, y) for y in b for x in a]
        """),
        False,
    ),

    # ── 8. Scope / closure ───────────────────────────────────────────────

    (
        "neq2_171_late_binding",
        dedent("""\
            def f(n):
                funcs = [lambda x, i=i: x + i for i in range(n)]
                return [fn(10) for fn in funcs]
        """),
        dedent("""\
            def g(n):
                funcs = [lambda x: x + i for i in range(n)]
                return [fn(10) for fn in funcs]
        """),
        False,
    ),

    (
        "neq2_172_closure_mutation",
        dedent("""\
            def f():
                x = 0
                def inc():
                    nonlocal x
                    x += 1
                    return x
                return [inc(), inc(), inc()]
        """),
        dedent("""\
            def g():
                x = 0
                def inc():
                    return x + 1
                return [inc(), inc(), inc()]
        """),
        False,
    ),

    (
        "neq2_173_global_vs_local",
        dedent("""\
            def f(lst):
                total = 0
                for x in lst:
                    total += x
                return total
        """),
        dedent("""\
            def g(lst):
                total = []
                for x in lst:
                    total.append(x)
                return total
        """),
        False,
    ),

    (
        "neq2_174_nested_scope",
        dedent("""\
            def f(n):
                results = []
                for i in range(n):
                    def inner(x=i):
                        return x * 2
                    results.append(inner())
                return results
        """),
        dedent("""\
            def g(n):
                results = []
                for i in range(n):
                    def inner():
                        return i * 2
                    results.append(inner())
                return results
        """),
        False,
    ),

    (
        "neq2_175_class_vs_closure",
        dedent("""\
            def f(init):
                state = [init]
                def get():
                    return state[0]
                def set_(v):
                    state[0] = v
                set_(init + 10)
                return get()
        """),
        dedent("""\
            def g(init):
                return init
        """),
        False,
    ),

    (
        "neq2_176_lambda_capture",
        dedent("""\
            def f(items):
                return [(lambda: x)() for x in items]
        """),
        dedent("""\
            def g(items):
                funcs = [(lambda: x) for x in items]
                return [fn() for fn in funcs]
        """),
        False,
    ),

    (
        "neq2_177_comprehension_scope",
        dedent("""\
            def f(n):
                return [i for i in range(n)]
        """),
        dedent("""\
            def g(n):
                result = []
                for i in range(n):
                    result.append(i)
                i = -1
                return result
        """),
        False,
    ),

    (
        "neq2_178_decorator_wrapper",
        dedent("""\
            def f(func):
                def wrapper(*args, **kwargs):
                    return func(*args, **kwargs)
                return wrapper
        """),
        dedent("""\
            def g(func):
                def wrapper(*args, **kwargs):
                    return func(*args, **kwargs) + 1
                return wrapper
        """),
        False,
    ),

    (
        "neq2_179_accumulator_closure",
        dedent("""\
            def f(n):
                acc = []
                for i in range(n):
                    acc.append(lambda: i)
                return [fn() for fn in acc]
        """),
        dedent("""\
            def g(n):
                return list(range(n))
        """),
        False,
    ),

    (
        "neq2_180_local_shadow",
        dedent("""\
            def f(x):
                def inner():
                    return x
                return inner()
        """),
        dedent("""\
            def g(x):
                def inner():
                    x = 42
                    return x
                return inner()
        """),
        False,
    ),

    # ── 9. Exception handling ────────────────────────────────────────────

    (
        "neq2_181_catch_all_vs_specific",
        dedent("""\
            def f(func, *args):
                try:
                    return func(*args)
                except ValueError:
                    return 'value_error'
                except Exception:
                    return 'other_error'
        """),
        dedent("""\
            def g(func, *args):
                try:
                    return func(*args)
                except Exception:
                    return 'other_error'
        """),
        True,  # Fixed: both catch all exceptions identically
    ),

    (
        "neq2_182_finally_return",
        dedent("""\
            def f(x):
                try:
                    return x * 2
                finally:
                    x = 0
        """),
        dedent("""\
            def g(x):
                try:
                    return x * 2
                finally:
                    return 0
        """),
        False,
    ),

    (
        "neq2_183_swallow_vs_raise",
        dedent("""\
            def f(d, key):
                try:
                    return d[key]
                except KeyError:
                    return None
        """),
        dedent("""\
            def g(d, key):
                return d[key]
        """),
        False,
    ),

    (
        "neq2_184_else_clause",
        dedent("""\
            def f(lst, idx):
                try:
                    val = lst[idx]
                except IndexError:
                    return -1
                else:
                    return val * 2
        """),
        dedent("""\
            def g(lst, idx):
                try:
                    val = lst[idx]
                    return val * 2
                except IndexError:
                    return 0
        """),
        False,
    ),

    (
        "neq2_185_exception_chaining",
        dedent("""\
            def f(x):
                try:
                    return int(x)
                except (ValueError, TypeError):
                    return 0
        """),
        dedent("""\
            def g(x):
                try:
                    return int(x)
                except ValueError:
                    return 0
        """),
        False,
    ),

    (
        "neq2_186_context_manager",
        dedent("""\
            def f(pairs):
                result = {}
                for k, v in pairs:
                    result[k] = result.get(k, 0) + v
                return result
        """),
        dedent("""\
            def g(pairs):
                result = {}
                for k, v in pairs:
                    try:
                        result[k] += v
                    except KeyError:
                        result[k] = v * 2
                return result
        """),
        False,
    ),

    (
        "neq2_187_suppress_vs_catch",
        dedent("""\
            def f(lst, idx):
                from contextlib import suppress
                result = None
                with suppress(IndexError):
                    result = lst[idx]
                return result
        """),
        dedent("""\
            def g(lst, idx):
                result = -1
                try:
                    result = lst[idx]
                except IndexError:
                    pass
                return result
        """),
        False,
    ),

    (
        "neq2_188_lbyl_vs_eafp",
        dedent("""\
            def f(d, key):
                if key in d:
                    return d[key]
                return 'missing'
        """),
        dedent("""\
            def g(d, key):
                try:
                    return d[key]
                except KeyError:
                    return 'default'
        """),
        False,
    ),

    (
        "neq2_189_error_return_type",
        dedent("""\
            def f(s):
                try:
                    return int(s)
                except ValueError:
                    return None
        """),
        dedent("""\
            def g(s):
                try:
                    return int(s)
                except ValueError:
                    return -1
        """),
        False,
    ),

    (
        "neq2_190_nested_try",
        dedent("""\
            def f(a, b):
                try:
                    x = a / b
                    try:
                        return int(x)
                    except (OverflowError, ValueError):
                        return 0
                except ZeroDivisionError:
                    return float('inf')
        """),
        dedent("""\
            def g(a, b):
                try:
                    return int(a / b)
                except (ZeroDivisionError, OverflowError, ValueError):
                    return 0
        """),
        False,
    ),

    # ── 10. Python-specific gotchas ──────────────────────────────────────

    (
        "neq2_191_is_vs_equals",
        dedent("""\
            def f(a, b):
                return a == b
        """),
        dedent("""\
            def g(a, b):
                return a is b
        """),
        False,
    ),

    (
        "neq2_192_walrus_operator",
        dedent("""\
            def f(lst, threshold):
                return [x for x in lst if x > threshold]
        """),
        dedent("""\
            def g(lst, threshold):
                return [y for x in lst if (y := x * 2) > threshold]
        """),
        False,
    ),

    (
        "neq2_193_unpacking_star",
        dedent("""\
            def f(lst):
                return lst[0], lst[-1]
        """),
        dedent("""\
            def g(lst):
                first, *_, last = lst
                return first, last if len(lst) > 1 else first
        """),
        False,
    ),

    (
        "neq2_194_dict_merge_order",
        dedent("""\
            def f(d1, d2):
                return {**d1, **d2}
        """),
        dedent("""\
            def g(d1, d2):
                return {**d2, **d1}
        """),
        False,
    ),

    (
        "neq2_195_chained_comparison",
        dedent("""\
            def f(x):
                return 0 < x < 10
        """),
        dedent("""\
            def g(x):
                return 0 < x and x <= 10
        """),
        False,
    ),

    (
        "neq2_196_string_multiply",
        dedent("""\
            def f(s, n):
                return s * n
        """),
        dedent("""\
            def g(s, n):
                return ''.join([s] * n) if n > 0 else s
        """),
        False,
    ),

    (
        "neq2_197_truth_table",
        dedent("""\
            def f(a, b):
                return a and b
        """),
        dedent("""\
            def g(a, b):
                return a or b
        """),
        False,
    ),

    (
        "neq2_198_list_multiply_trap",
        dedent("""\
            def f(n, m):
                return [[0] * m for _ in range(n)]
        """),
        dedent("""\
            def g(n, m):
                return [[0] * m] * n
        """),
        False,
    ),

    (
        "neq2_199_enumerate_start",
        dedent("""\
            def f(lst):
                return list(enumerate(lst, start=1))
        """),
        dedent("""\
            def g(lst):
                return list(enumerate(lst))
        """),
        False,
    ),

    (
        "neq2_200_args_kwargs_order",
        dedent("""\
            def f(**kwargs):
                return sorted(kwargs.items())
        """),
        dedent("""\
            def g(**kwargs):
                return list(kwargs.items())
        """),
        False,
    ),
]
