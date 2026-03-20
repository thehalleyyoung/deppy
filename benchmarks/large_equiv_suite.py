"""
Benchmark suite of 100 equivalence pairs of Python programs.

Each entry is a tuple:
    (name: str, source_f: str, source_g: str, expected_equivalent: bool)

Pairs 1-50:  equivalent   (expected_equivalent = True)
Pairs 51-100: non-equivalent (expected_equivalent = False)
"""

from textwrap import dedent

EQUIV_PAIRS: list[tuple[str, str, str, bool]] = [

    # =========================================================================
    # EQUIVALENT PAIRS (1-50)
    # =========================================================================

    # --- arithmetic / math ---------------------------------------------------

    (
        "sum_loop_vs_builtin",
        dedent("""\
            def f(xs):
                total = 0
                for x in xs:
                    total += x
                return total
        """),
        dedent("""\
            def g(xs):
                return sum(xs)
        """),
        True,
    ),

    (
        "max_loop_vs_builtin",
        dedent("""\
            def f(xs):
                if not xs:
                    raise ValueError
                m = xs[0]
                for x in xs[1:]:
                    if x > m:
                        m = x
                return m
        """),
        dedent("""\
            def g(xs):
                return max(xs)
        """),
        True,
    ),

    (
        "factorial_iterative_vs_recursive",
        dedent("""\
            def f(n):
                result = 1
                for i in range(2, n + 1):
                    result *= i
                return result
        """),
        dedent("""\
            def g(n):
                if n <= 1:
                    return 1
                return n * g(n - 1)
        """),
        True,
    ),

    (
        "power_loop_vs_builtin",
        dedent("""\
            def f(base, exp):
                result = 1
                for _ in range(exp):
                    result *= base
                return result
        """),
        dedent("""\
            def g(base, exp):
                return base ** exp
        """),
        True,
    ),

    (
        "abs_manual_vs_builtin",
        dedent("""\
            def f(x):
                if x < 0:
                    return -x
                return x
        """),
        dedent("""\
            def g(x):
                return abs(x)
        """),
        True,
    ),

    # --- list ops ------------------------------------------------------------

    (
        "reverse_loop_vs_slice",
        dedent("""\
            def f(xs):
                result = []
                for i in range(len(xs) - 1, -1, -1):
                    result.append(xs[i])
                return result
        """),
        dedent("""\
            def g(xs):
                return xs[::-1]
        """),
        True,
    ),

    (
        "flatten_loop_vs_comprehension",
        dedent("""\
            def f(nested):
                result = []
                for sublist in nested:
                    for item in sublist:
                        result.append(item)
                return result
        """),
        dedent("""\
            def g(nested):
                return [item for sublist in nested for item in sublist]
        """),
        True,
    ),

    (
        "filter_loop_vs_comprehension",
        dedent("""\
            def f(xs):
                result = []
                for x in xs:
                    if x % 2 == 0:
                        result.append(x)
                return result
        """),
        dedent("""\
            def g(xs):
                return [x for x in xs if x % 2 == 0]
        """),
        True,
    ),

    (
        "map_loop_vs_comprehension",
        dedent("""\
            def f(xs):
                result = []
                for x in xs:
                    result.append(x * x)
                return result
        """),
        dedent("""\
            def g(xs):
                return [x * x for x in xs]
        """),
        True,
    ),

    (
        "zip_manual_vs_builtin",
        dedent("""\
            def f(a, b):
                result = []
                n = min(len(a), len(b))
                for i in range(n):
                    result.append((a[i], b[i]))
                return result
        """),
        dedent("""\
            def g(a, b):
                return list(zip(a, b))
        """),
        True,
    ),

    # --- string ops ----------------------------------------------------------

    (
        "join_loop_vs_builtin",
        dedent("""\
            def f(words):
                if not words:
                    return ""
                s = words[0]
                for w in words[1:]:
                    s = s + " " + w
                return s
        """),
        dedent("""\
            def g(words):
                return " ".join(words)
        """),
        True,
    ),

    (
        "count_char_loop_vs_method",
        dedent("""\
            def f(s, ch):
                c = 0
                for x in s:
                    if x == ch:
                        c += 1
                return c
        """),
        dedent("""\
            def g(s, ch):
                return s.count(ch)
        """),
        True,
    ),

    (
        "is_palindrome_two_ways",
        dedent("""\
            def f(s):
                n = len(s)
                for i in range(n // 2):
                    if s[i] != s[n - 1 - i]:
                        return False
                return True
        """),
        dedent("""\
            def g(s):
                return s == s[::-1]
        """),
        True,
    ),

    # --- dict ops ------------------------------------------------------------

    (
        "word_count_manual_vs_counter",
        dedent("""\
            def f(words):
                d = {}
                for w in words:
                    d[w] = d.get(w, 0) + 1
                return d
        """),
        dedent("""\
            from collections import Counter
            def g(words):
                return dict(Counter(words))
        """),
        True,
    ),

    (
        "invert_dict_loop_vs_comprehension",
        dedent("""\
            def f(d):
                result = {}
                for k, v in d.items():
                    result[v] = k
                return result
        """),
        dedent("""\
            def g(d):
                return {v: k for k, v in d.items()}
        """),
        True,
    ),

    (
        "merge_dicts_loop_vs_unpack",
        dedent("""\
            def f(a, b):
                result = {}
                for k, v in a.items():
                    result[k] = v
                for k, v in b.items():
                    result[k] = v
                return result
        """),
        dedent("""\
            def g(a, b):
                return {**a, **b}
        """),
        True,
    ),

    # --- sorting / searching -------------------------------------------------

    (
        "bubble_sort_vs_sorted",
        dedent("""\
            def f(xs):
                a = list(xs)
                n = len(a)
                for i in range(n):
                    for j in range(0, n - i - 1):
                        if a[j] > a[j + 1]:
                            a[j], a[j + 1] = a[j + 1], a[j]
                return a
        """),
        dedent("""\
            def g(xs):
                return sorted(xs)
        """),
        True,
    ),

    (
        "insertion_sort_vs_sorted",
        dedent("""\
            def f(xs):
                a = list(xs)
                for i in range(1, len(a)):
                    key = a[i]
                    j = i - 1
                    while j >= 0 and a[j] > key:
                        a[j + 1] = a[j]
                        j -= 1
                    a[j + 1] = key
                return a
        """),
        dedent("""\
            def g(xs):
                return sorted(xs)
        """),
        True,
    ),

    (
        "binary_search_two_impls",
        dedent("""\
            def f(xs, target):
                lo, hi = 0, len(xs) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if xs[mid] == target:
                        return mid
                    elif xs[mid] < target:
                        lo = mid + 1
                    else:
                        hi = mid - 1
                return -1
        """),
        dedent("""\
            def g(xs, target):
                lo, hi = 0, len(xs)
                while lo < hi:
                    mid = lo + (hi - lo) // 2
                    if xs[mid] < target:
                        lo = mid + 1
                    elif xs[mid] > target:
                        hi = mid
                    else:
                        return mid
                return -1
        """),
        True,
    ),

    # --- functools / itertools -----------------------------------------------

    (
        "reduce_sum_vs_builtin",
        dedent("""\
            from functools import reduce
            def f(xs):
                return reduce(lambda a, b: a + b, xs, 0)
        """),
        dedent("""\
            def g(xs):
                return sum(xs)
        """),
        True,
    ),

    (
        "product_reduce_vs_loop",
        dedent("""\
            from functools import reduce
            import operator
            def f(xs):
                return reduce(operator.mul, xs, 1)
        """),
        dedent("""\
            def g(xs):
                p = 1
                for x in xs:
                    p *= x
                return p
        """),
        True,
    ),

    (
        "chain_vs_nested_loop",
        dedent("""\
            from itertools import chain
            def f(a, b, c):
                return list(chain(a, b, c))
        """),
        dedent("""\
            def g(a, b, c):
                result = []
                for seq in [a, b, c]:
                    result.extend(seq)
                return result
        """),
        True,
    ),

    (
        "enumerate_manual_vs_builtin",
        dedent("""\
            def f(xs):
                result = []
                i = 0
                for x in xs:
                    result.append((i, x))
                    i += 1
                return result
        """),
        dedent("""\
            def g(xs):
                return list(enumerate(xs))
        """),
        True,
    ),

    # --- collections ---------------------------------------------------------

    (
        "defaultdict_vs_setdefault",
        dedent("""\
            from collections import defaultdict
            def f(pairs):
                d = defaultdict(list)
                for k, v in pairs:
                    d[k].append(v)
                return dict(d)
        """),
        dedent("""\
            def g(pairs):
                d = {}
                for k, v in pairs:
                    d.setdefault(k, []).append(v)
                return d
        """),
        True,
    ),

    (
        "deque_rotate_vs_slice",
        dedent("""\
            from collections import deque
            def f(xs, k):
                d = deque(xs)
                d.rotate(k)
                return list(d)
        """),
        dedent("""\
            def g(xs, k):
                if not xs:
                    return list(xs)
                k = k % len(xs)
                return list(xs[-k:]) + list(xs[:-k]) if k else list(xs)
        """),
        True,
    ),

    # --- math functions ------------------------------------------------------

    (
        "gcd_euclidean_two_impls",
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
        "fibonacci_iter_vs_memo",
        dedent("""\
            def f(n):
                if n <= 1:
                    return n
                a, b = 0, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def g(n, memo={}):
                if n <= 1:
                    return n
                if n not in memo:
                    memo[n] = g(n - 1) + g(n - 2)
                return memo[n]
        """),
        True,
    ),

    (
        "is_prime_trial_div_two_ways",
        dedent("""\
            def f(n):
                if n < 2:
                    return False
                for i in range(2, int(n ** 0.5) + 1):
                    if n % i == 0:
                        return False
                return True
        """),
        dedent("""\
            def g(n):
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
        True,
    ),

    # --- graph algorithms ----------------------------------------------------

    (
        "bfs_vs_iterative_dfs_reachable_set",
        dedent("""\
            from collections import deque
            def f(graph, start):
                visited = set()
                q = deque([start])
                while q:
                    node = q.popleft()
                    if node in visited:
                        continue
                    visited.add(node)
                    for nb in graph.get(node, []):
                        if nb not in visited:
                            q.append(nb)
                return visited
        """),
        dedent("""\
            def g(graph, start):
                visited = set()
                stack = [start]
                while stack:
                    node = stack.pop()
                    if node in visited:
                        continue
                    visited.add(node)
                    for nb in graph.get(node, []):
                        if nb not in visited:
                            stack.append(nb)
                return visited
        """),
        True,
    ),

    (
        "topological_sort_kahn_vs_dfs",
        dedent("""\
            from collections import deque
            def f(graph, vertices):
                in_deg = {v: 0 for v in vertices}
                for u in vertices:
                    for v in graph.get(u, []):
                        in_deg[v] = in_deg.get(v, 0) + 1
                q = deque(v for v in vertices if in_deg[v] == 0)
                order = []
                while q:
                    u = q.popleft()
                    order.append(u)
                    for v in graph.get(u, []):
                        in_deg[v] -= 1
                        if in_deg[v] == 0:
                            q.append(v)
                return order
        """),
        dedent("""\
            def g(graph, vertices):
                visited = set()
                stack = []
                def dfs(u):
                    visited.add(u)
                    for v in graph.get(u, []):
                        if v not in visited:
                            dfs(v)
                    stack.append(u)
                for v in vertices:
                    if v not in visited:
                        dfs(v)
                return stack[::-1]
        """),
        True,
    ),

    # --- class methods -------------------------------------------------------

    (
        "class_property_vs_method",
        dedent("""\
            class Rect:
                def __init__(self, w, h):
                    self.w = w
                    self.h = h
                def area(self):
                    return self.w * self.h
            def f(w, h):
                return Rect(w, h).area()
        """),
        dedent("""\
            def g(w, h):
                return w * h
        """),
        True,
    ),

    (
        "dataclass_vs_manual_init",
        dedent("""\
            class Point:
                def __init__(self, x, y):
                    self.x = x
                    self.y = y
            def f(x, y):
                p = Point(x, y)
                return (p.x ** 2 + p.y ** 2) ** 0.5
        """),
        dedent("""\
            import math
            def g(x, y):
                return math.hypot(x, y)
        """),
        True,
    ),

    # --- os.path patterns ----------------------------------------------------

    (
        "path_join_manual_vs_ospath",
        dedent("""\
            import os.path
            def f(directory, filename):
                return os.path.join(directory, filename)
        """),
        dedent("""\
            def g(directory, filename):
                if directory.endswith('/') or directory.endswith('\\\\'):
                    return directory + filename
                return directory + '/' + filename
        """),
        True,
    ),

    (
        "splitext_manual_vs_ospath",
        dedent("""\
            import os.path
            def f(path):
                return os.path.splitext(path)
        """),
        dedent("""\
            def g(path):
                dot = path.rfind('.')
                slash = max(path.rfind('/'), path.rfind('\\\\'))
                if dot > slash and dot > 0:
                    return (path[:dot], path[dot:])
                return (path, '')
        """),
        True,
    ),

    # --- numpy-style patterns ------------------------------------------------

    (
        "np_dot_vs_loop",
        dedent("""\
            import numpy as np
            def f(a, b):
                return np.dot(a, b)
        """),
        dedent("""\
            import numpy as np
            def g(a, b):
                return np.sum(a * b)
        """),
        True,
    ),

    (
        "np_mean_vs_manual",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.mean(arr)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                return np.sum(arr) / arr.size
        """),
        True,
    ),

    (
        "np_argmax_vs_loop",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.argmax(arr)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                flat = arr.ravel()
                best = 0
                for i in range(1, len(flat)):
                    if flat[i] > flat[best]:
                        best = i
                return best
        """),
        True,
    ),

    (
        "np_outer_vs_broadcast",
        dedent("""\
            import numpy as np
            def f(a, b):
                return np.outer(a, b)
        """),
        dedent("""\
            import numpy as np
            def g(a, b):
                return a.reshape(-1, 1) * b.reshape(1, -1)
        """),
        True,
    ),

    (
        "np_cumsum_vs_loop",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.cumsum(arr)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                out = np.empty_like(arr)
                s = 0
                for i in range(len(arr)):
                    s += arr[i]
                    out[i] = s
                return out
        """),
        True,
    ),

    (
        "np_normalize_two_ways",
        dedent("""\
            import numpy as np
            def f(v):
                return v / np.linalg.norm(v)
        """),
        dedent("""\
            import numpy as np
            def g(v):
                return v / np.sqrt(np.sum(v ** 2))
        """),
        True,
    ),

    # --- torch-style patterns ------------------------------------------------

    (
        "torch_relu_vs_clamp",
        dedent("""\
            import torch
            def f(x):
                return torch.relu(x)
        """),
        dedent("""\
            import torch
            def g(x):
                return torch.clamp(x, min=0)
        """),
        True,
    ),

    (
        "torch_mse_manual_vs_builtin",
        dedent("""\
            import torch
            def f(pred, target):
                return torch.mean((pred - target) ** 2)
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(pred, target):
                return F.mse_loss(pred, target)
        """),
        True,
    ),

    (
        "torch_softmax_manual_vs_builtin",
        dedent("""\
            import torch
            def f(x, dim=-1):
                e = torch.exp(x - torch.max(x, dim=dim, keepdim=True).values)
                return e / e.sum(dim=dim, keepdim=True)
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(x, dim=-1):
                return F.softmax(x, dim=dim)
        """),
        True,
    ),

    (
        "torch_linear_manual_vs_module",
        dedent("""\
            import torch
            def f(x, weight, bias):
                return x @ weight.t() + bias
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(x, weight, bias):
                return F.linear(x, weight, bias)
        """),
        True,
    ),

    (
        "torch_batchnorm_inference_two_ways",
        dedent("""\
            import torch
            def f(x, mean, var, gamma, beta, eps=1e-5):
                return gamma * (x - mean) / torch.sqrt(var + eps) + beta
        """),
        dedent("""\
            import torch
            def g(x, mean, var, gamma, beta, eps=1e-5):
                x_hat = (x - mean) * torch.rsqrt(var + eps)
                return gamma * x_hat + beta
        """),
        True,
    ),

    (
        "torch_cosine_sim_two_ways",
        dedent("""\
            import torch
            def f(a, b):
                return torch.dot(a, b) / (torch.norm(a) * torch.norm(b))
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(a, b):
                return F.cosine_similarity(a.unsqueeze(0), b.unsqueeze(0)).squeeze()
        """),
        True,
    ),

    # --- triton-style patterns -----------------------------------------------

    (
        "triton_add_kernel_two_block_sizes",
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def f(x_ptr, y_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(0)
                offs = pid * BLOCK + tl.arange(0, BLOCK)
                mask = offs < n
                x = tl.load(x_ptr + offs, mask=mask)
                y = tl.load(y_ptr + offs, mask=mask)
                tl.store(out_ptr + offs, x + y, mask=mask)
        """),
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def g(x_ptr, y_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(axis=0)
                start = pid * BLOCK
                offs = start + tl.arange(0, BLOCK)
                valid = offs < n
                a = tl.load(x_ptr + offs, mask=valid)
                b = tl.load(y_ptr + offs, mask=valid)
                tl.store(out_ptr + offs, a + b, mask=valid)
        """),
        True,
    ),

    (
        "triton_softmax_row_two_ways",
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def f(inp_ptr, out_ptr, n_cols, BLOCK: tl.constexpr):
                row = tl.program_id(0)
                offs = tl.arange(0, BLOCK)
                mask = offs < n_cols
                x = tl.load(inp_ptr + row * n_cols + offs, mask=mask, other=-float('inf'))
                x_max = tl.max(x, axis=0)
                ex = tl.exp(x - x_max)
                sm = ex / tl.sum(ex, axis=0)
                tl.store(out_ptr + row * n_cols + offs, sm, mask=mask)
        """),
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def g(inp_ptr, out_ptr, n_cols, BLOCK: tl.constexpr):
                row_id = tl.program_id(0)
                col_offs = tl.arange(0, BLOCK)
                valid = col_offs < n_cols
                base = row_id * n_cols
                vals = tl.load(inp_ptr + base + col_offs, mask=valid, other=-float('inf'))
                m = tl.max(vals, axis=0)
                numerator = tl.exp(vals - m)
                denominator = tl.sum(numerator, axis=0)
                tl.store(out_ptr + base + col_offs, numerator / denominator, mask=valid)
        """),
        True,
    ),

    # --- miscellaneous equivalent pairs --------------------------------------

    (
        "matrix_transpose_two_ways",
        dedent("""\
            def f(matrix):
                rows = len(matrix)
                cols = len(matrix[0]) if rows else 0
                result = []
                for j in range(cols):
                    row = []
                    for i in range(rows):
                        row.append(matrix[i][j])
                    result.append(row)
                return result
        """),
        dedent("""\
            def g(matrix):
                return [list(row) for row in zip(*matrix)]
        """),
        True,
    ),

    (
        "all_manual_vs_builtin",
        dedent("""\
            def f(xs):
                for x in xs:
                    if not x:
                        return False
                return True
        """),
        dedent("""\
            def g(xs):
                return all(xs)
        """),
        True,
    ),

    # =========================================================================
    # NON-EQUIVALENT PAIRS (51-100)
    # =========================================================================

    # --- off-by-one errors ---------------------------------------------------

    (
        "range_off_by_one",
        dedent("""\
            def f(n):
                return list(range(n))
        """),
        dedent("""\
            def g(n):
                return list(range(1, n + 1))
        """),
        False,
    ),

    (
        "sum_range_inclusive_vs_exclusive",
        dedent("""\
            def f(n):
                return sum(range(n + 1))
        """),
        dedent("""\
            def g(n):
                return sum(range(n))
        """),
        False,
    ),

    (
        "fibonacci_off_by_one",
        dedent("""\
            def f(n):
                if n <= 1:
                    return n
                a, b = 0, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def g(n):
                if n <= 1:
                    return n
                a, b = 0, 1
                for _ in range(2, n):
                    a, b = b, a + b
                return b
        """),
        False,
    ),

    # --- wrong operator ------------------------------------------------------

    (
        "add_vs_multiply",
        dedent("""\
            def f(a, b):
                return a + b
        """),
        dedent("""\
            def g(a, b):
                return a * b
        """),
        False,
    ),

    (
        "floor_div_vs_true_div",
        dedent("""\
            def f(a, b):
                return a // b
        """),
        dedent("""\
            def g(a, b):
                return a / b
        """),
        False,
    ),

    (
        "bitwise_and_vs_logical_and",
        dedent("""\
            def f(a, b):
                return a & b
        """),
        dedent("""\
            def g(a, b):
                return a and b
        """),
        False,
    ),

    (
        "modulo_vs_integer_div",
        dedent("""\
            def f(a, b):
                return a % b
        """),
        dedent("""\
            def g(a, b):
                return a // b
        """),
        False,
    ),

    # --- wrong comparison direction ------------------------------------------

    (
        "min_vs_max",
        dedent("""\
            def f(xs):
                return min(xs)
        """),
        dedent("""\
            def g(xs):
                return max(xs)
        """),
        False,
    ),

    (
        "sort_asc_vs_desc",
        dedent("""\
            def f(xs):
                return sorted(xs)
        """),
        dedent("""\
            def g(xs):
                return sorted(xs, reverse=True)
        """),
        False,
    ),

    (
        "leq_vs_lt",
        dedent("""\
            def f(xs, threshold):
                return [x for x in xs if x <= threshold]
        """),
        dedent("""\
            def g(xs, threshold):
                return [x for x in xs if x < threshold]
        """),
        False,
    ),

    # --- missing edge case ---------------------------------------------------

    (
        "safe_div_vs_unsafe_div",
        dedent("""\
            def f(a, b):
                if b == 0:
                    return 0
                return a / b
        """),
        dedent("""\
            def g(a, b):
                return a / b
        """),
        False,
    ),

    (
        "empty_list_guard_missing",
        dedent("""\
            def f(xs):
                if not xs:
                    return None
                return xs[0]
        """),
        dedent("""\
            def g(xs):
                return xs[0]
        """),
        False,
    ),

    (
        "negative_index_handling",
        dedent("""\
            def f(xs, i):
                if i < 0:
                    i = 0
                return xs[i] if i < len(xs) else None
        """),
        dedent("""\
            def g(xs, i):
                return xs[i] if i < len(xs) else None
        """),
        False,
    ),

    # --- different reduction -------------------------------------------------

    (
        "sum_vs_product",
        dedent("""\
            def f(xs):
                result = 0
                for x in xs:
                    result += x
                return result
        """),
        dedent("""\
            def g(xs):
                result = 1
                for x in xs:
                    result *= x
                return result
        """),
        False,
    ),

    (
        "any_vs_all",
        dedent("""\
            def f(xs):
                return any(xs)
        """),
        dedent("""\
            def g(xs):
                return all(xs)
        """),
        False,
    ),

    (
        "union_vs_intersection",
        dedent("""\
            def f(a, b):
                return a | b
        """),
        dedent("""\
            def g(a, b):
                return a & b
        """),
        False,
    ),

    # --- subtle numerical differences ----------------------------------------

    (
        "unstable_vs_stable_softmax",
        dedent("""\
            import numpy as np
            def f(x):
                e = np.exp(x)
                return e / np.sum(e)
        """),
        dedent("""\
            import numpy as np
            def g(x):
                e = np.exp(x - np.max(x))
                return e / np.sum(e)
        """),
        False,
    ),

    (
        "naive_vs_kahan_summation",
        dedent("""\
            def f(xs):
                s = 0.0
                for x in xs:
                    s += x
                return s
        """),
        dedent("""\
            def g(xs):
                s = 0.0
                c = 0.0
                for x in xs:
                    y = x - c
                    t = s + y
                    c = (t - s) - y
                    s = t
                return s
        """),
        False,
    ),

    (
        "l1_vs_l2_norm",
        dedent("""\
            import numpy as np
            def f(v):
                return np.sum(np.abs(v))
        """),
        dedent("""\
            import numpy as np
            def g(v):
                return np.sqrt(np.sum(v ** 2))
        """),
        False,
    ),

    (
        "mean_vs_median",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.mean(arr)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                return np.median(arr)
        """),
        False,
    ),

    # --- torch non-equivalent ------------------------------------------------

    (
        "torch_relu_vs_leaky_relu",
        dedent("""\
            import torch
            def f(x):
                return torch.relu(x)
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(x):
                return F.leaky_relu(x, negative_slope=0.01)
        """),
        False,
    ),

    (
        "torch_sigmoid_vs_tanh",
        dedent("""\
            import torch
            def f(x):
                return torch.sigmoid(x)
        """),
        dedent("""\
            import torch
            def g(x):
                return torch.tanh(x)
        """),
        False,
    ),

    (
        "torch_cross_entropy_vs_mse",
        dedent("""\
            import torch
            import torch.nn.functional as F
            def f(logits, targets):
                return F.cross_entropy(logits, targets)
        """),
        dedent("""\
            import torch
            import torch.nn.functional as F
            def g(logits, targets):
                one_hot = F.one_hot(targets, logits.shape[-1]).float()
                return F.mse_loss(logits, one_hot)
        """),
        False,
    ),

    (
        "torch_sum_vs_mean_reduction",
        dedent("""\
            import torch
            def f(x):
                return torch.sum(x)
        """),
        dedent("""\
            import torch
            def g(x):
                return torch.mean(x)
        """),
        False,
    ),

    (
        "torch_matmul_vs_elementwise",
        dedent("""\
            import torch
            def f(a, b):
                return torch.matmul(a, b)
        """),
        dedent("""\
            import torch
            def g(a, b):
                return a * b
        """),
        False,
    ),

    (
        "torch_dropout_vs_identity",
        dedent("""\
            import torch
            import torch.nn.functional as F
            def f(x):
                return F.dropout(x, p=0.5, training=True)
        """),
        dedent("""\
            import torch
            def g(x):
                return x
        """),
        False,
    ),

    (
        "torch_layer_norm_vs_batch_norm",
        dedent("""\
            import torch
            import torch.nn.functional as F
            def f(x):
                return F.layer_norm(x, x.shape[-1:])
        """),
        dedent("""\
            import torch
            def g(x):
                mean = x.mean(dim=0, keepdim=True)
                var = x.var(dim=0, keepdim=True, unbiased=False)
                return (x - mean) / torch.sqrt(var + 1e-5)
        """),
        False,
    ),

    # --- numpy non-equivalent ------------------------------------------------

    (
        "np_axis0_vs_axis1_sum",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.sum(arr, axis=0)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                return np.sum(arr, axis=1)
        """),
        False,
    ),

    (
        "np_std_vs_var",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.std(arr)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                return np.var(arr)
        """),
        False,
    ),

    (
        "np_clip_wrong_bounds",
        dedent("""\
            import numpy as np
            def f(arr):
                return np.clip(arr, 0, 1)
        """),
        dedent("""\
            import numpy as np
            def g(arr):
                return np.clip(arr, -1, 1)
        """),
        False,
    ),

    # --- triton non-equivalent -----------------------------------------------

    (
        "triton_add_vs_mul_kernel",
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def f(x_ptr, y_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(0)
                offs = pid * BLOCK + tl.arange(0, BLOCK)
                mask = offs < n
                x = tl.load(x_ptr + offs, mask=mask)
                y = tl.load(y_ptr + offs, mask=mask)
                tl.store(out_ptr + offs, x + y, mask=mask)
        """),
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def g(x_ptr, y_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(0)
                offs = pid * BLOCK + tl.arange(0, BLOCK)
                mask = offs < n
                x = tl.load(x_ptr + offs, mask=mask)
                y = tl.load(y_ptr + offs, mask=mask)
                tl.store(out_ptr + offs, x * y, mask=mask)
        """),
        False,
    ),

    (
        "triton_missing_mask",
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def f(x_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(0)
                offs = pid * BLOCK + tl.arange(0, BLOCK)
                mask = offs < n
                x = tl.load(x_ptr + offs, mask=mask)
                tl.store(out_ptr + offs, x * 2.0, mask=mask)
        """),
        dedent("""\
            import triton
            import triton.language as tl
            @triton.jit
            def g(x_ptr, out_ptr, n, BLOCK: tl.constexpr):
                pid = tl.program_id(0)
                offs = pid * BLOCK + tl.arange(0, BLOCK)
                x = tl.load(x_ptr + offs)
                tl.store(out_ptr + offs, x * 2.0)
        """),
        False,
    ),

    # --- string non-equivalent -----------------------------------------------

    (
        "strip_vs_lstrip",
        dedent("""\
            def f(s):
                return s.strip()
        """),
        dedent("""\
            def g(s):
                return s.lstrip()
        """),
        False,
    ),

    (
        "split_default_vs_explicit",
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
        "lower_vs_upper",
        dedent("""\
            def f(s):
                return s.lower()
        """),
        dedent("""\
            def g(s):
                return s.upper()
        """),
        False,
    ),

    # --- dict non-equivalent -------------------------------------------------

    (
        "dict_get_default_none_vs_zero",
        dedent("""\
            def f(d, key):
                return d.get(key)
        """),
        dedent("""\
            def g(d, key):
                return d.get(key, 0)
        """),
        False,
    ),

    (
        "dict_keys_vs_values",
        dedent("""\
            def f(d):
                return list(d.keys())
        """),
        dedent("""\
            def g(d):
                return list(d.values())
        """),
        False,
    ),

    # --- graph non-equivalent ------------------------------------------------

    (
        "bfs_vs_dfs_order",
        dedent("""\
            from collections import deque
            def f(graph, start):
                visited = []
                seen = set()
                q = deque([start])
                while q:
                    node = q.popleft()
                    if node in seen:
                        continue
                    seen.add(node)
                    visited.append(node)
                    for nb in sorted(graph.get(node, [])):
                        if nb not in seen:
                            q.append(nb)
                return visited
        """),
        dedent("""\
            def g(graph, start):
                visited = []
                seen = set()
                stack = [start]
                while stack:
                    node = stack.pop()
                    if node in seen:
                        continue
                    seen.add(node)
                    visited.append(node)
                    for nb in sorted(graph.get(node, []), reverse=True):
                        if nb not in seen:
                            stack.append(nb)
                return visited
        """),
        False,
    ),

    (
        "shortest_path_unweighted_vs_weighted",
        dedent("""\
            from collections import deque
            def f(graph, start, end):
                dist = {start: 0}
                q = deque([start])
                while q:
                    u = q.popleft()
                    for v in graph.get(u, []):
                        if v not in dist:
                            dist[v] = dist[u] + 1
                            q.append(v)
                return dist.get(end, -1)
        """),
        dedent("""\
            import heapq
            def g(graph, start, end):
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
                return dist.get(end, -1)
        """),
        False,
    ),

    # --- functional non-equivalent -------------------------------------------

    (
        "map_vs_filter",
        dedent("""\
            def f(xs):
                return [x * 2 for x in xs]
        """),
        dedent("""\
            def g(xs):
                return [x for x in xs if x * 2 > 0]
        """),
        False,
    ),

    (
        "left_fold_vs_right_fold",
        dedent("""\
            def f(xs, op, init):
                acc = init
                for x in xs:
                    acc = op(acc, x)
                return acc
        """),
        dedent("""\
            def g(xs, op, init):
                acc = init
                for x in reversed(xs):
                    acc = op(x, acc)
                return acc
        """),
        False,
    ),

    (
        "first_vs_last_element",
        dedent("""\
            def f(xs):
                return xs[0] if xs else None
        """),
        dedent("""\
            def g(xs):
                return xs[-1] if xs else None
        """),
        False,
    ),

    (
        "prepend_vs_append",
        dedent("""\
            def f(xs, val):
                return [val] + xs
        """),
        dedent("""\
            def g(xs, val):
                return xs + [val]
        """),
        False,
    ),

    (
        "count_zeros_vs_count_ones",
        dedent("""\
            def f(xs):
                return sum(1 for x in xs if x == 0)
        """),
        dedent("""\
            def g(xs):
                return sum(1 for x in xs if x == 1)
        """),
        False,
    ),

    # ── Extra pairs to reach 100 ──

    ("eq_abs_manual", dedent("""\
        def f(x):
            return abs(x)
    """), dedent("""\
        def g(x):
            return x if x >= 0 else -x
    """), True),

    ("eq_pow2_mul", dedent("""\
        def f(x):
            return x ** 2
    """), dedent("""\
        def g(x):
            return x * x
    """), True),

    ("eq_double_add", dedent("""\
        def f(x):
            return x * 2
    """), dedent("""\
        def g(x):
            return x + x
    """), True),

    ("neq_floor_ceil", dedent("""\
        def f(a, b):
            return a // b
    """), dedent("""\
        def g(a, b):
            return -(-a // b)
    """), False),

    ("neq_and_or_logic", dedent("""\
        def f(a, b):
            return a and b
    """), dedent("""\
        def g(a, b):
            return a or b
    """), False),

    ("neq_index_first_last", dedent("""\
        def f(lst):
            return lst[0]
    """), dedent("""\
        def g(lst):
            return lst[-1]
    """), False),

]

assert len(EQUIV_PAIRS) == 100, f"Expected 100 pairs, got {len(EQUIV_PAIRS)}"
_n_eq = sum(1 for _, _, _, eq in EQUIV_PAIRS if eq)
_n_neq = sum(1 for _, _, _, eq in EQUIV_PAIRS if not eq)
assert _n_eq + _n_neq == 100, f"Expected 100 total, got {_n_eq + _n_neq}"
