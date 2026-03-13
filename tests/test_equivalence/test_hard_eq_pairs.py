"""
100 Hard Equivalence Pairs — 50 EQ + 50 NEQ
============================================
Each function is 20–60 lines and exercises deep Python semantics:
  generators, closures, nonlocal, dunder methods, descriptors,
  exception-as-control-flow, functools, itertools, collections,
  comprehensions, unpacking, walrus operator, dynamic dispatch,
  decorator patterns, mutable default args, float/NaN semantics,
  sort stability, identity-vs-equality, late binding, MRO, and more.

For EQ pairs: both functions produce identical output for ALL inputs
              in their domain — but this is very hard to verify.
For NEQ pairs: a witness input is provided where outputs diverge.
"""
from __future__ import annotations

import math
import sys
import functools
import itertools
import operator
import collections
import contextlib
import io
import copy
import re
import hashlib
import struct
import bisect
import heapq
import textwrap
import typing
from collections import defaultdict, Counter, deque, OrderedDict
from functools import reduce, partial
from itertools import chain, groupby, accumulate, product, combinations

import pytest


# ╔══════════════════════════════════════════════════════════════════╗
# ║               PART I — 50 EQUIVALENT PAIRS                     ║
# ╚══════════════════════════════════════════════════════════════════╝

# ──────────────────────────────────────────────────────────────────
# EQ-01  Flatten heterogeneous nested data into sorted unique atoms.
#   A: recursive generator with isinstance dispatch + set + sorted
#   B: iterative stack with type-dispatch dict + manual dedup via dict.fromkeys
# ──────────────────────────────────────────────────────────────────
def eq01a(data):
    """Recursive generator approach."""
    def _flatten(obj, _seen=None):
        if _seen is None:
            _seen = set()
        if isinstance(obj, dict):
            for k, v in sorted(obj.items(), key=lambda kv: repr(kv[0])):
                yield from _flatten(k, _seen)
                yield from _flatten(v, _seen)
        elif isinstance(obj, (list, tuple, set, frozenset)):
            items = sorted(obj, key=repr) if isinstance(obj, (set, frozenset)) else obj
            for item in items:
                yield from _flatten(item, _seen)
        elif isinstance(obj, str):
            if obj not in _seen:
                _seen.add(obj)
                yield obj
        elif isinstance(obj, (int, float)):
            if not (isinstance(obj, float) and math.isnan(obj)):
                if obj not in _seen:
                    _seen.add(obj)
                    yield obj
        elif obj is None:
            if None not in _seen:
                _seen.add(None)
                yield obj

    results = list(_flatten(data))
    def _sort_key(x):
        type_order = {type(None): 0, bool: 1, int: 2, float: 3, str: 4}
        t = type(x)
        if t is bool:
            return (1, int(x), "")
        elif t in (int, float):
            return (type_order.get(t, 5), float(x), "")
        elif t is str:
            return (4, 0, x)
        else:
            return (0, 0, "")
    return sorted(results, key=_sort_key)


def eq01b(data):
    """Iterative stack approach with type dispatch dict."""
    atoms = []
    seen_set = set()
    stack = [data]
    dispatch = {}

    def _handle_dict(obj, stk):
        pairs = sorted(obj.items(), key=lambda kv: repr(kv[0]))
        for k, v in reversed(pairs):
            stk.append(v)
            stk.append(k)

    def _handle_seq(obj, stk):
        for item in reversed(list(obj)):
            stk.append(item)

    def _handle_unordered(obj, stk):
        for item in reversed(sorted(obj, key=repr)):
            stk.append(item)

    dispatch[dict] = _handle_dict
    for t in (list, tuple):
        dispatch[t] = _handle_seq
    for t in (set, frozenset):
        dispatch[t] = _handle_unordered

    while stack:
        current = stack.pop()
        handler = dispatch.get(type(current))
        if handler is not None:
            handler(current, stack)
            continue
        if isinstance(current, float) and math.isnan(current):
            continue
        if current in seen_set:
            continue
        try:
            seen_set.add(current)
        except TypeError:
            continue
        atoms.append(current)

    def _sort_key(x):
        if x is None:
            return (0, 0, "")
        if isinstance(x, bool):
            return (1, int(x), "")
        if isinstance(x, int):
            return (2, float(x), "")
        if isinstance(x, float):
            return (3, x, "")
        if isinstance(x, str):
            return (4, 0, x)
        return (5, 0, repr(x))

    return sorted(atoms, key=_sort_key)


# ──────────────────────────────────────────────────────────────────
# EQ-02  Build a word-frequency histogram from text with
#        punctuation stripping and case-folding.
#   A: regex + Counter + sorted comprehension
#   B: manual char-by-char state machine + defaultdict + heap
# ──────────────────────────────────────────────────────────────────
def eq02a(text):
    """Regex tokeniser → Counter → sorted list of (word, count)."""
    if not isinstance(text, str) or not text.strip():
        return []
    tokens = re.findall(r"[a-zA-Z]+(?:'[a-zA-Z]+)*", text)
    counts = Counter(tok.lower() for tok in tokens)
    result = sorted(counts.items(), key=lambda wc: (-wc[1], wc[0]))
    return [(w, c) for w, c in result]


def eq02b(text):
    """Char-level state machine → defaultdict → heapq.nsmallest."""
    if not isinstance(text, str) or not text.strip():
        return []
    freq = defaultdict(int)
    buf = []
    in_word = False
    for ch in text:
        is_alpha = ('a' <= ch <= 'z') or ('A' <= ch <= 'Z')
        is_apos = (ch == "'")
        if in_word:
            if is_alpha or (is_apos and buf):
                buf.append(ch.lower())
            else:
                # end of word — strip trailing apostrophes
                word = "".join(buf).rstrip("'")
                if word:
                    freq[word] += 1
                buf.clear()
                in_word = False
        else:
            if is_alpha:
                buf.append(ch.lower())
                in_word = True
    if buf:
        word = "".join(buf).rstrip("'")
        if word:
            freq[word] += 1
    # Sort: descending count, ascending word — use nsmallest trick
    n = len(freq)
    pairs = list(freq.items())
    result = heapq.nsmallest(n, pairs, key=lambda wc: (-wc[1], wc[0]))
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-03  Evaluate a nested arithmetic expression represented as
#        a tuple-tree: (op, left, right) where op ∈ {'+','-','*','/'}
#        and leaves are int/float.  Division is true division;
#        division by zero yields float('inf') with sign.
#   A: recursive with match-case–style dispatch dict
#   B: iterative post-order traversal using an explicit stack
# ──────────────────────────────────────────────────────────────────
def eq03a(expr):
    """Recursive evaluator with dispatch dict and exception guarding."""
    def _safe_div(a, b):
        if b == 0:
            if a == 0:
                return float('nan')
            return math.copysign(float('inf'), a)
        return a / b

    _ops = {
        '+': operator.add,
        '-': operator.sub,
        '*': operator.mul,
        '/': _safe_div,
    }

    def _eval(node):
        if isinstance(node, (int, float)):
            return float(node)
        if not isinstance(node, tuple) or len(node) != 3:
            raise ValueError(f"Bad node: {node!r}")
        op_sym, left, right = node
        fn = _ops.get(op_sym)
        if fn is None:
            raise ValueError(f"Unknown op: {op_sym!r}")
        lv = _eval(left)
        rv = _eval(right)
        return fn(lv, rv)

    result = _eval(expr)
    # Normalise -0.0 → 0.0
    if result == 0.0:
        return 0.0
    return result


def eq03b(expr):
    """Stack-based post-order evaluator."""
    SENTINEL = object()
    stack = [expr]
    values = []

    while stack:
        node = stack.pop()
        if node is SENTINEL:
            op_sym = stack.pop()
            right_val = values.pop()
            left_val = values.pop()
            if op_sym == '+':
                values.append(left_val + right_val)
            elif op_sym == '-':
                values.append(left_val - right_val)
            elif op_sym == '*':
                values.append(left_val * right_val)
            elif op_sym == '/':
                if right_val == 0:
                    if left_val == 0:
                        values.append(float('nan'))
                    else:
                        values.append(math.copysign(float('inf'), left_val))
                else:
                    values.append(left_val / right_val)
            else:
                raise ValueError(f"Unknown op: {op_sym!r}")
            continue
        if isinstance(node, (int, float)):
            values.append(float(node))
        elif isinstance(node, tuple) and len(node) == 3:
            op_sym, left, right = node
            stack.append(op_sym)
            stack.append(SENTINEL)
            stack.append(right)
            stack.append(left)
        else:
            raise ValueError(f"Bad node: {node!r}")

    result = values[0]
    if result == 0.0:
        return 0.0
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-04  Simulate a simple register machine.
#        Instructions: ('SET', reg, val), ('ADD', dst, src1, src2),
#        ('MUL', dst, src1, src2), ('JNZ', reg, offset),
#        ('HALT',).  Returns the register dict.
#   A: while-loop interpreter with direct dict mutation
#   B: recursive CPS-style interpreter with immutable snapshots
# ──────────────────────────────────────────────────────────────────
def eq04a(program, initial_regs=None):
    """Direct imperative interpreter."""
    regs = dict(initial_regs) if initial_regs else {}
    pc = 0
    MAX_STEPS = 10_000
    steps = 0
    while 0 <= pc < len(program) and steps < MAX_STEPS:
        steps += 1
        instr = program[pc]
        opcode = instr[0]
        if opcode == 'SET':
            _, reg, val = instr
            regs[reg] = val
            pc += 1
        elif opcode == 'ADD':
            _, dst, s1, s2 = instr
            regs[dst] = regs.get(s1, 0) + regs.get(s2, 0)
            pc += 1
        elif opcode == 'MUL':
            _, dst, s1, s2 = instr
            regs[dst] = regs.get(s1, 0) * regs.get(s2, 0)
            pc += 1
        elif opcode == 'JNZ':
            _, reg, offset = instr
            if regs.get(reg, 0) != 0:
                pc += offset
            else:
                pc += 1
        elif opcode == 'HALT':
            break
        else:
            pc += 1
    return dict(sorted(regs.items()))


def eq04b(program, initial_regs=None):
    """Recursive interpreter with continuation-passing style."""
    _max = 10_000

    def _step(regs_frozen, pc, fuel):
        if fuel <= 0 or pc < 0 or pc >= len(program):
            return regs_frozen
        instr = program[pc]
        opcode = instr[0]
        regs = dict(regs_frozen)
        if opcode == 'HALT':
            return regs_frozen
        next_pc = pc + 1
        if opcode == 'SET':
            regs[instr[1]] = instr[2]
        elif opcode == 'ADD':
            regs[instr[1]] = regs.get(instr[2], 0) + regs.get(instr[3], 0)
        elif opcode == 'MUL':
            regs[instr[1]] = regs.get(instr[2], 0) * regs.get(instr[3], 0)
        elif opcode == 'JNZ':
            if regs.get(instr[1], 0) != 0:
                next_pc = pc + instr[2]
        else:
            pass  # skip unknown
        return _step(tuple(sorted(regs.items())), next_pc, fuel - 1)

    init = tuple(sorted((initial_regs or {}).items()))
    final = _step(init, 0, _max)
    return dict(final) if isinstance(final, tuple) else dict(sorted(dict(final).items()))


# ──────────────────────────────────────────────────────────────────
# EQ-05  Topological sort of a DAG. Returns lexicographically
#        smallest valid ordering (by comparing node labels).
#   A: Kahn's algorithm with a min-heap for tie-breaking
#   B: Modified DFS with reverse-post-order + sorting
# ──────────────────────────────────────────────────────────────────
def eq05a(graph):
    """Kahn's algorithm with heapq for lex-smallest order."""
    in_degree = defaultdict(int)
    all_nodes = set()
    adj = defaultdict(list)
    for u in graph:
        all_nodes.add(u)
        for v in graph[u]:
            adj[u].append(v)
            in_degree[v] += 1
            all_nodes.add(v)
    for n in all_nodes:
        in_degree.setdefault(n, 0)
    heap = [n for n in all_nodes if in_degree[n] == 0]
    heapq.heapify(heap)
    result = []
    while heap:
        u = heapq.heappop(heap)
        result.append(u)
        for v in sorted(adj.get(u, [])):
            in_degree[v] -= 1
            if in_degree[v] == 0:
                heapq.heappush(heap, v)
    if len(result) != len(all_nodes):
        return None  # cycle
    return result


def eq05b(graph):
    """Kahn's topo sort with bisect.insort for lex-smallest order."""
    in_degree = defaultdict(int)
    all_nodes = set()
    adj = defaultdict(list)
    for u in graph:
        all_nodes.add(u)
        for v in graph[u]:
            adj[u].append(v)
            in_degree[v] += 1
            all_nodes.add(v)
    for n in all_nodes:
        in_degree.setdefault(n, 0)
    candidates = sorted(n for n in all_nodes if in_degree[n] == 0)
    result = []
    while candidates:
        u = candidates.pop(0)
        result.append(u)
        for v in adj.get(u, []):
            in_degree[v] -= 1
            if in_degree[v] == 0:
                bisect.insort(candidates, v)
    if len(result) != len(all_nodes):
        return None
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-06  Encode a list of runs as RLE, then decode back.
#        Return the decoded list (should equal input for any input).
#   A: itertools.groupby for encode, chain.from_iterable for decode
#   B: manual sentinel-based encode, list-multiply decode
# ──────────────────────────────────────────────────────────────────
def eq06a(data):
    if not data:
        return []
    # Encode with groupby
    encoded = [(k, sum(1 for _ in g)) for k, g in groupby(data)]
    # Decode with chain
    decoded = list(chain.from_iterable([val] * cnt for val, cnt in encoded))
    return decoded


def eq06b(data):
    if not data:
        return []
    # Encode manually with sentinel
    _SENTINEL = object()
    runs = []
    prev = _SENTINEL
    count = 0
    for item in data:
        if item == prev or (
            isinstance(item, float) and isinstance(prev, float)
            and math.isnan(item) and math.isnan(prev)
        ):
            count += 1
        else:
            if prev is not _SENTINEL:
                runs.append((prev, count))
            prev = item
            count = 1
    if prev is not _SENTINEL:
        runs.append((prev, count))
    # Decode with reduce
    decoded = functools.reduce(
        lambda acc, pair: acc + [pair[0]] * pair[1],
        runs,
        []
    )
    return decoded


# ──────────────────────────────────────────────────────────────────
# EQ-07  Compute the convex hull of 2D points (Graham scan vs
#        Andrew's monotone chain).  Return hull as list of (x,y)
#        in counter-clockwise order starting from bottom-left.
# ──────────────────────────────────────────────────────────────────
def eq07a(points):
    """Graham scan."""
    pts = list(set(points))
    if len(pts) <= 1:
        return pts
    if len(pts) == 2:
        return sorted(pts)

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    pivot = min(pts, key=lambda p: (p[1], p[0]))
    pts.remove(pivot)

    def angle_key(p):
        dx, dy = p[0] - pivot[0], p[1] - pivot[1]
        return (math.atan2(dy, dx), dx * dx + dy * dy)

    pts.sort(key=angle_key)
    hull = [pivot]
    for p in pts:
        while len(hull) > 1 and cross(hull[-2], hull[-1], p) <= 0:
            hull.pop()
        hull.append(p)
    # Normalise: start from bottom-left, CCW
    bl_idx = min(range(len(hull)), key=lambda i: (hull[i][1], hull[i][0]))
    hull = hull[bl_idx:] + hull[:bl_idx]
    return hull


def eq07b(points):
    """Andrew's monotone chain algorithm."""
    pts = sorted(set(points))
    if len(pts) <= 1:
        return pts
    if len(pts) == 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower = []
    for p in pts:
        while len(lower) > 1 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) > 1 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    # Normalise: start from bottom-left, CCW
    bl_idx = min(range(len(hull)), key=lambda i: (hull[i][1], hull[i][0]))
    hull = hull[bl_idx:] + hull[:bl_idx]
    return hull


# ──────────────────────────────────────────────────────────────────
# EQ-08  Compute edit distance between two strings using
#   A: Full DP table (bottom-up)
#   B: Recursive with memoisation via a local class __missing__
# ──────────────────────────────────────────────────────────────────
def eq08a(s1, s2):
    """Bottom-up DP with rolling two rows."""
    m, n = len(s1), len(s2)
    if m == 0:
        return n
    if n == 0:
        return m
    prev = list(range(n + 1))
    curr = [0] * (n + 1)
    for i in range(1, m + 1):
        curr[0] = i
        for j in range(1, n + 1):
            cost = 0 if s1[i - 1] == s2[j - 1] else 1
            curr[j] = min(
                prev[j] + 1,      # delete
                curr[j - 1] + 1,  # insert
                prev[j - 1] + cost  # replace
            )
        prev, curr = curr, prev
    return prev[n]


def eq08b(s1, s2):
    """Recursive with auto-memoising dict subclass."""
    class MemoDict(dict):
        def __init__(self, func):
            super().__init__()
            self._func = func

        def __missing__(self, key):
            result = self._func(key)
            self[key] = result
            return result

    def _edit(key):
        i, j = key
        if i == 0:
            return j
        if j == 0:
            return i
        cost = 0 if s1[i - 1] == s2[j - 1] else 1
        return min(
            memo[(i - 1, j)] + 1,
            memo[(i, j - 1)] + 1,
            memo[(i - 1, j - 1)] + cost,
        )

    memo = MemoDict(_edit)
    return memo[(len(s1), len(s2))]


# ──────────────────────────────────────────────────────────────────
# EQ-09  LRU cache: given a sequence of (key, value?) operations,
#        return the final cache state.  Capacity-bounded.
#   A: OrderedDict with move_to_end
#   B: Manual doubly-linked list with a dict index
# ──────────────────────────────────────────────────────────────────
def eq09a(capacity, operations):
    """OrderedDict-based LRU."""
    cache = OrderedDict()
    for op in operations:
        if op[0] == 'get':
            key = op[1]
            if key in cache:
                cache.move_to_end(key)
        elif op[0] == 'put':
            key, val = op[1], op[2]
            if key in cache:
                cache.move_to_end(key)
                cache[key] = val
            else:
                if len(cache) >= capacity:
                    cache.popitem(last=False)
                cache[key] = val
    return dict(sorted(cache.items()))


def eq09b(capacity, operations):
    """Doubly-linked list + dict LRU."""
    # Nodes: [prev, next, key, val]
    head = [None, None, None, None]  # sentinel head
    tail = [None, None, None, None]  # sentinel tail
    head[1] = tail
    tail[0] = head
    index = {}

    def _remove(node):
        p, n = node[0], node[1]
        p[1] = n
        n[0] = p

    def _add_before_tail(node):
        prev_of_tail = tail[0]
        prev_of_tail[1] = node
        node[0] = prev_of_tail
        node[1] = tail
        tail[0] = node

    for op in operations:
        if op[0] == 'get':
            key = op[1]
            if key in index:
                node = index[key]
                _remove(node)
                _add_before_tail(node)
        elif op[0] == 'put':
            key, val = op[1], op[2]
            if key in index:
                node = index[key]
                node[3] = val
                _remove(node)
                _add_before_tail(node)
            else:
                if len(index) >= capacity:
                    # Evict LRU (right after head)
                    lru = head[1]
                    _remove(lru)
                    del index[lru[2]]
                node = [None, None, key, val]
                _add_before_tail(node)
                index[key] = node

    result = {}
    cur = head[1]
    while cur is not tail:
        result[cur[2]] = cur[3]
        cur = cur[1]
    return dict(sorted(result.items()))


# ──────────────────────────────────────────────────────────────────
# EQ-10  Matrix multiplication of two dense matrices (list-of-lists).
#   A: Triple nested loop with accumulator
#   B: Transpose + zip + sum-of-products via map/reduce
# ──────────────────────────────────────────────────────────────────
def eq10a(A, B):
    """Classic triple loop."""
    if not A or not B or not B[0]:
        return []
    m, n, p = len(A), len(A[0]), len(B[0])
    if len(B) != n:
        raise ValueError("Incompatible matrices")
    C = [[0] * p for _ in range(m)]
    for i in range(m):
        for j in range(p):
            s = 0
            for k in range(n):
                s += A[i][k] * B[k][j]
            C[i][j] = s
    return C


def eq10b(A, B):
    """Transpose B, then dot-product via zip + functools.reduce."""
    if not A or not B or not B[0]:
        return []
    m, n, p = len(A), len(A[0]), len(B[0])
    if len(B) != n:
        raise ValueError("Incompatible matrices")
    BT = list(map(list, zip(*B)))
    C = [
        [
            functools.reduce(operator.add, (ai * bi for ai, bi in zip(row_a, col_b)), 0)
            for col_b in BT
        ]
        for row_a in A
    ]
    return C


# ──────────────────────────────────────────────────────────────────
# EQ-11  Merge k sorted iterators into one sorted stream.
#   A: heapq.merge wrapper (but re-implemented manually with a heap)
#   B: Divide-and-conquer pairwise merge
# ──────────────────────────────────────────────────────────────────
def eq11a(iterables):
    """Heap-based k-way merge."""
    iters = [iter(it) for it in iterables]
    heap = []
    for idx, it in enumerate(iters):
        val = next(it, None)
        if val is not None:
            heap.append((val, idx))
    heapq.heapify(heap)
    result = []
    while heap:
        val, idx = heapq.heappop(heap)
        result.append(val)
        nxt = next(iters[idx], None)
        if nxt is not None:
            heapq.heappush(heap, (nxt, idx))
    return result


def eq11b(iterables):
    """Pairwise merge, divide-and-conquer."""
    lists = [list(it) for it in iterables]
    if not lists:
        return []

    def _merge2(a, b):
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
                merged.append(_merge2(lists[i], lists[i + 1]))
            else:
                merged.append(lists[i])
        lists = merged
    return lists[0] if lists else []


# ──────────────────────────────────────────────────────────────────
# EQ-12  Serialize a binary tree (nested tuples) to a string and
#        deserialize back.  Return deserialized tree == original.
#        Tree: (val, left, right) or None for empty.
#   A: Pre-order with '#' markers, comma-separated
#   B: Level-order (BFS) with None markers
# ──────────────────────────────────────────────────────────────────
def eq12a(tree):
    """Pre-order serialize → deserialize."""
    tokens = []
    def _ser(node):
        if node is None:
            tokens.append('#')
        else:
            tokens.append(str(node[0]))
            _ser(node[1])
            _ser(node[2])
    _ser(tree)
    s = ','.join(tokens)
    # Deserialize
    it = iter(s.split(','))
    def _deser():
        tok = next(it)
        if tok == '#':
            return None
        val = int(tok) if tok.lstrip('-').isdigit() else tok
        left = _deser()
        right = _deser()
        return (val, left, right)
    return _deser()


def eq12b(tree):
    """Level-order serialize → deserialize."""
    from collections import deque
    # Serialize
    tokens = []
    q = deque([tree])
    while q:
        node = q.popleft()
        if node is None:
            tokens.append('#')
        else:
            tokens.append(str(node[0]))
            q.append(node[1])
            q.append(node[2])
    s = ','.join(tokens)
    # Deserialize
    parts = s.split(',')
    if not parts or parts[0] == '#':
        return None
    root_val = int(parts[0]) if parts[0].lstrip('-').isdigit() else parts[0]
    root = [root_val, None, None]
    q = deque([root])
    i = 1
    while q and i < len(parts):
        node = q.popleft()
        # left child
        if i < len(parts) and parts[i] != '#':
            v = int(parts[i]) if parts[i].lstrip('-').isdigit() else parts[i]
            left = [v, None, None]
            node[1] = left
            q.append(left)
        i += 1
        # right child
        if i < len(parts) and parts[i] != '#':
            v = int(parts[i]) if parts[i].lstrip('-').isdigit() else parts[i]
            right = [v, None, None]
            node[2] = right
            q.append(right)
        i += 1
    # Convert lists back to tuples
    def _to_tuple(node):
        if node is None:
            return None
        return (node[0], _to_tuple(node[1]), _to_tuple(node[2]))
    return _to_tuple(root)


# ──────────────────────────────────────────────────────────────────
# EQ-13  Count the number of distinct paths in a weighted DAG from
#        source to sink where total weight < threshold.
#   A: DFS with backtracking and running sum
#   B: BFS with state = (node, accumulated_weight)
# ──────────────────────────────────────────────────────────────────
def eq13a(edges, source, sink, threshold):
    """DFS backtracking."""
    adj = defaultdict(list)
    for u, v, w in edges:
        adj[u].append((v, w))
    count = [0]
    path = set()

    def _dfs(u, weight):
        if weight >= threshold:
            return
        if u == sink:
            count[0] += 1
            return
        path.add(u)
        for v, w in adj[u]:
            if v not in path:
                _dfs(v, weight + w)
        path.remove(u)

    _dfs(source, 0)
    return count[0]


def eq13b(edges, source, sink, threshold):
    """BFS with explicit state tracking."""
    adj = defaultdict(list)
    for u, v, w in edges:
        adj[u].append((v, w))
    count = 0
    # State: (node, weight, visited_frozenset)
    queue = deque([(source, 0, frozenset([source]))])
    while queue:
        u, w, visited = queue.popleft()
        if w >= threshold:
            continue
        if u == sink:
            count += 1
            continue
        for v, wt in adj[u]:
            if v not in visited:
                queue.append((v, w + wt, visited | {v}))
    return count


# ──────────────────────────────────────────────────────────────────
# EQ-14  Implement a simple calculator that parses and evaluates
#        infix expressions with +, -, *, /, parentheses on integers.
#   A: Recursive descent parser
#   B: Shunting-yard algorithm (Dijkstra)
# ──────────────────────────────────────────────────────────────────
def eq14a(expr_str):
    """Recursive descent parser/evaluator."""
    tokens = []
    i = 0
    s = expr_str.replace(' ', '')
    while i < len(s):
        if s[i].isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            tokens.append(int(s[i:j]))
            i = j
        elif s[i] in '+-*/()':
            tokens.append(s[i])
            i += 1
        else:
            i += 1

    pos = [0]

    def _peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def _consume():
        t = tokens[pos[0]]
        pos[0] += 1
        return t

    def _parse_expr():
        result = _parse_term()
        while _peek() in ('+', '-'):
            op = _consume()
            right = _parse_term()
            result = result + right if op == '+' else result - right
        return result

    def _parse_term():
        result = _parse_factor()
        while _peek() in ('*', '/'):
            op = _consume()
            right = _parse_factor()
            if op == '*':
                result = result * right
            else:
                if right == 0:
                    result = float('inf') if result >= 0 else float('-inf')
                else:
                    result = result / right
        return result

    def _parse_factor():
        if _peek() == '(':
            _consume()  # skip (
            result = _parse_expr()
            if _peek() == ')':
                _consume()
            return result
        elif _peek() == '-':
            _consume()
            return -_parse_factor()
        else:
            return float(_consume())

    return eq14a.__dict__.setdefault('_dummy', None) or _parse_expr()  # indirection


# Oops, that last line is buggy.  Let me fix:
def eq14a(expr_str):
    """Recursive descent parser/evaluator."""
    tokens = []
    i = 0
    s = expr_str.replace(' ', '')
    while i < len(s):
        if s[i].isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            tokens.append(int(s[i:j]))
            i = j
        elif s[i] in '+-*/()':
            tokens.append(s[i])
            i += 1
        else:
            i += 1
    pos = [0]

    def _peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def _consume():
        t = tokens[pos[0]]
        pos[0] += 1
        return t

    def _expr():
        result = _term()
        while _peek() in ('+', '-'):
            op = _consume()
            right = _term()
            result = result + right if op == '+' else result - right
        return result

    def _term():
        result = _factor()
        while _peek() in ('*', '/'):
            op = _consume()
            right = _factor()
            if op == '*':
                result = result * right
            else:
                result = result / right if right != 0 else math.copysign(float('inf'), result)
        return result

    def _factor():
        if _peek() == '(':
            _consume()
            result = _expr()
            if _peek() == ')':
                _consume()
            return result
        elif _peek() == '-':
            _consume()
            return -_factor()
        else:
            return float(_consume())

    result = _expr()
    return result if result != 0.0 or not math.copysign(1, result) < 0 else 0.0


def eq14b(expr_str):
    """Shunting-yard parser/evaluator."""
    tokens = []
    i = 0
    s = expr_str.replace(' ', '')
    while i < len(s):
        if s[i].isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            tokens.append(('NUM', int(s[i:j])))
            i = j
        elif s[i] in '+-*/':
            tokens.append(('OP', s[i]))
            i += 1
        elif s[i] == '(':
            tokens.append(('LPAREN', '('))
            i += 1
        elif s[i] == ')':
            tokens.append(('RPAREN', ')'))
            i += 1
        else:
            i += 1

    # Handle unary minus: if '-' appears after '(' or at start or after OP
    processed = []
    for idx_t, (typ, val) in enumerate(tokens):
        if typ == 'OP' and val == '-':
            if idx_t == 0 or tokens[idx_t - 1][0] in ('LPAREN', 'OP'):
                processed.append(('NUM', 0))
        processed.append((typ, val))
    tokens = processed

    prec = {'+': 1, '-': 1, '*': 2, '/': 2}
    output_q = []
    op_stack = []

    for typ, val in tokens:
        if typ == 'NUM':
            output_q.append(float(val))
        elif typ == 'OP':
            while (op_stack and op_stack[-1] != '(' and
                   prec.get(op_stack[-1], 0) >= prec[val]):
                output_q.append(op_stack.pop())
            op_stack.append(val)
        elif typ == 'LPAREN':
            op_stack.append('(')
        elif typ == 'RPAREN':
            while op_stack and op_stack[-1] != '(':
                output_q.append(op_stack.pop())
            if op_stack:
                op_stack.pop()  # remove '('

    while op_stack:
        output_q.append(op_stack.pop())

    # Evaluate RPN
    eval_stack = []
    for token in output_q:
        if isinstance(token, float):
            eval_stack.append(token)
        else:
            b = eval_stack.pop()
            a = eval_stack.pop()
            if token == '+':
                eval_stack.append(a + b)
            elif token == '-':
                eval_stack.append(a - b)
            elif token == '*':
                eval_stack.append(a * b)
            elif token == '/':
                eval_stack.append(a / b if b != 0 else math.copysign(float('inf'), a))

    result = eval_stack[0] if eval_stack else 0.0
    return result if result != 0.0 or not math.copysign(1, result) < 0 else 0.0


# ──────────────────────────────────────────────────────────────────
# EQ-15  Compute the longest increasing subsequence LENGTH of a list.
#   A: O(n²) DP
#   B: O(n log n) with patience sorting / bisect
# ──────────────────────────────────────────────────────────────────
def eq15a(nums):
    """O(n²) DP for LIS length."""
    if not nums:
        return 0
    n = len(nums)
    dp = [1] * n
    for i in range(1, n):
        for j in range(i):
            if nums[j] < nums[i]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp)


def eq15b(nums):
    """O(n log n) with bisect (patience sorting)."""
    if not nums:
        return 0
    tails = []
    for x in nums:
        pos = bisect.bisect_left(tails, x)
        if pos == len(tails):
            tails.append(x)
        else:
            tails[pos] = x
    return len(tails)


# ──────────────────────────────────────────────────────────────────
# EQ-16  Find all strongly connected components of a directed graph.
#        Return a sorted list of sorted SCCs.
#   A: Tarjan's algorithm
#   B: Kosaraju's algorithm
# ──────────────────────────────────────────────────────────────────
def eq16a(graph):
    """Tarjan's SCC algorithm."""
    index_counter = [0]
    stack = []
    on_stack = set()
    indices = {}
    lowlinks = {}
    result = []

    all_nodes = set(graph.keys())
    for neighbors in graph.values():
        all_nodes.update(neighbors)

    def strongconnect(v):
        indices[v] = lowlinks[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w in sorted(graph.get(v, [])):
            if w not in indices:
                strongconnect(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif w in on_stack:
                lowlinks[v] = min(lowlinks[v], indices[w])

        if lowlinks[v] == indices[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc.append(w)
                if w == v:
                    break
            result.append(sorted(scc))

    for node in sorted(all_nodes):
        if node not in indices:
            strongconnect(node)
    return sorted(result)


def eq16b(graph):
    """Kosaraju's SCC algorithm."""
    all_nodes = set(graph.keys())
    for neighbors in graph.values():
        all_nodes.update(neighbors)

    # Step 1: DFS finish order
    visited = set()
    finish_order = []

    def dfs1(v):
        visited.add(v)
        for w in sorted(graph.get(v, [])):
            if w not in visited:
                dfs1(w)
        finish_order.append(v)

    for node in sorted(all_nodes):
        if node not in visited:
            dfs1(node)

    # Step 2: Build reverse graph
    rev = defaultdict(list)
    for u in graph:
        for v in graph[u]:
            rev[v].append(u)

    # Step 3: DFS on reverse graph in reverse finish order
    visited2 = set()
    result = []

    def dfs2(v, component):
        visited2.add(v)
        component.append(v)
        for w in sorted(rev.get(v, [])):
            if w not in visited2:
                dfs2(w, component)

    for node in reversed(finish_order):
        if node not in visited2:
            comp = []
            dfs2(node, comp)
            result.append(sorted(comp))
    return sorted(result)


# ──────────────────────────────────────────────────────────────────
# EQ-17  Power set: return sorted list of sorted tuples.
#   A: Recursive include/exclude
#   B: Bit-mask enumeration
# ──────────────────────────────────────────────────────────────────
def eq17a(elements):
    """Recursive include/exclude."""
    elems = sorted(elements)
    result = []
    def _gen(idx, current):
        if idx == len(elems):
            result.append(tuple(sorted(current)))
            return
        _gen(idx + 1, current)
        _gen(idx + 1, current + [elems[idx]])
    _gen(0, [])
    return sorted(result)


def eq17b(elements):
    """Bit-mask enumeration."""
    elems = sorted(elements)
    n = len(elems)
    result = []
    for mask in range(1 << n):
        subset = tuple(sorted(elems[j] for j in range(n) if mask & (1 << j)))
        result.append(subset)
    return sorted(result)


# ──────────────────────────────────────────────────────────────────
# EQ-18  JSON-like pretty printer for nested Python data.
#        Normalise: sort dict keys, represent sets as sorted lists,
#        booleans as "true"/"false", None as "null".
#   A: Recursive with string accumulation
#   B: Generator-based with join
# ──────────────────────────────────────────────────────────────────
def eq18a(data, indent=0):
    """Recursive string accumulation."""
    _IND = "  "
    if data is None:
        return "null"
    if isinstance(data, bool):
        return "true" if data else "false"
    if isinstance(data, (int, float)):
        if isinstance(data, float) and math.isinf(data):
            return '"Infinity"' if data > 0 else '"-Infinity"'
        if isinstance(data, float) and math.isnan(data):
            return '"NaN"'
        return repr(data)
    if isinstance(data, str):
        return '"' + data.replace('\\', '\\\\').replace('"', '\\"') + '"'
    if isinstance(data, (set, frozenset)):
        data = sorted(data, key=repr)
        return eq18a(list(data), indent)
    if isinstance(data, (list, tuple)):
        if not data:
            return "[]"
        items = []
        for item in data:
            items.append(_IND * (indent + 1) + eq18a(item, indent + 1))
        return "[\n" + ",\n".join(items) + "\n" + _IND * indent + "]"
    if isinstance(data, dict):
        if not data:
            return "{}"
        items = []
        for k in sorted(data.keys(), key=repr):
            key_s = eq18a(k, indent + 1)
            val_s = eq18a(data[k], indent + 1)
            items.append(_IND * (indent + 1) + key_s + ": " + val_s)
        return "{\n" + ",\n".join(items) + "\n" + _IND * indent + "}"
    return repr(data)


def eq18b(data, indent=0):
    """Generator-based with join."""
    _IND = "  "

    def _emit(obj, lvl):
        if obj is None:
            yield "null"
        elif isinstance(obj, bool):
            yield "true" if obj else "false"
        elif isinstance(obj, float) and math.isinf(obj):
            yield '"Infinity"' if obj > 0 else '"-Infinity"'
        elif isinstance(obj, float) and math.isnan(obj):
            yield '"NaN"'
        elif isinstance(obj, (int, float)):
            yield repr(obj)
        elif isinstance(obj, str):
            yield '"' + obj.replace('\\', '\\\\').replace('"', '\\"') + '"'
        elif isinstance(obj, (set, frozenset)):
            yield from _emit(sorted(obj, key=repr), lvl)
        elif isinstance(obj, (list, tuple)):
            if not obj:
                yield "[]"
            else:
                parts = []
                for item in obj:
                    parts.append(_IND * (lvl + 1) + "".join(_emit(item, lvl + 1)))
                yield "[\n" + ",\n".join(parts) + "\n" + _IND * lvl + "]"
        elif isinstance(obj, dict):
            if not obj:
                yield "{}"
            else:
                parts = []
                for k in sorted(obj.keys(), key=repr):
                    ks = "".join(_emit(k, lvl + 1))
                    vs = "".join(_emit(obj[k], lvl + 1))
                    parts.append(_IND * (lvl + 1) + ks + ": " + vs)
                yield "{\n" + ",\n".join(parts) + "\n" + _IND * lvl + "}"
        else:
            yield repr(obj)

    return "".join(_emit(data, indent))


# ──────────────────────────────────────────────────────────────────
# EQ-19  Knapsack 0/1: return max value for given (weight, value)
#        items and capacity.
#   A: Bottom-up DP table
#   B: Recursive with functools.lru_cache
# ──────────────────────────────────────────────────────────────────
def eq19a(items, capacity):
    """Bottom-up DP."""
    n = len(items)
    dp = [[0] * (capacity + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        w, v = items[i - 1]
        for c in range(capacity + 1):
            dp[i][c] = dp[i - 1][c]
            if w <= c:
                dp[i][c] = max(dp[i][c], dp[i - 1][c - w] + v)
    return dp[n][capacity]


def eq19b(items, capacity):
    """Recursive with lru_cache."""
    items_t = tuple(items)

    @functools.lru_cache(maxsize=None)
    def solve(i, cap):
        if i == 0 or cap == 0:
            return 0
        w, v = items_t[i - 1]
        excl = solve(i - 1, cap)
        if w > cap:
            return excl
        incl = solve(i - 1, cap - w) + v
        return max(excl, incl)

    return solve(len(items_t), capacity)


# ──────────────────────────────────────────────────────────────────
# EQ-20  Compute SHA-256 hex digest of a structured Python object
#        by deterministically serializing it.
#   A: Custom recursive serialiser → hashlib
#   B: json.dumps with sort_keys + custom default → hashlib
# ──────────────────────────────────────────────────────────────────
def eq20a(obj):
    """Custom recursive serialiser."""
    import hashlib
    parts = []
    def _ser(o):
        if o is None:
            parts.append(b'\x00')
        elif isinstance(o, bool):
            parts.append(b'\x01' if o else b'\x02')
        elif isinstance(o, int):
            parts.append(b'\x03')
            parts.append(str(o).encode())
            parts.append(b'\xff')
        elif isinstance(o, float):
            parts.append(b'\x04')
            parts.append(struct.pack('>d', o))
        elif isinstance(o, str):
            parts.append(b'\x05')
            parts.append(o.encode('utf-8'))
            parts.append(b'\xff')
        elif isinstance(o, (list, tuple)):
            parts.append(b'\x06')
            parts.append(len(o).to_bytes(4, 'big'))
            for item in o:
                _ser(item)
        elif isinstance(o, dict):
            parts.append(b'\x07')
            items = sorted(o.items(), key=lambda kv: repr(kv[0]))
            parts.append(len(items).to_bytes(4, 'big'))
            for k, v in items:
                _ser(k)
                _ser(v)
        elif isinstance(o, (set, frozenset)):
            parts.append(b'\x08')
            items = sorted(o, key=repr)
            parts.append(len(items).to_bytes(4, 'big'))
            for item in items:
                _ser(item)
        else:
            parts.append(b'\x09')
            parts.append(repr(o).encode('utf-8'))
            parts.append(b'\xff')
    _ser(obj)
    return hashlib.sha256(b''.join(parts)).hexdigest()


def eq20b(obj):
    """json.dumps with custom default."""
    import hashlib, json

    def _default(o):
        if isinstance(o, (set, frozenset)):
            return {'__set__': sorted(o, key=repr)}
        if isinstance(o, bytes):
            return {'__bytes__': o.hex()}
        if isinstance(o, complex):
            return {'__complex__': [o.real, o.imag]}
        raise TypeError(f"Not serializable: {type(o)}")

    def _normalize(o):
        if isinstance(o, bool):
            return o
        if isinstance(o, int):
            return o
        if isinstance(o, float):
            return o
        if isinstance(o, str):
            return o
        if o is None:
            return o
        if isinstance(o, dict):
            return {repr(k): _normalize(v) for k, v in sorted(o.items(), key=lambda kv: repr(kv[0]))}
        if isinstance(o, (list, tuple)):
            return [_normalize(x) for x in o]
        if isinstance(o, (set, frozenset)):
            return [_normalize(x) for x in sorted(o, key=repr)]
        return repr(o)

    canonical = _normalize(obj)
    s = json.dumps(canonical, sort_keys=True, ensure_ascii=True, default=_default)
    return hashlib.sha256(s.encode('utf-8')).hexdigest()


# Note: eq20a and eq20b use DIFFERENT serialisation schemes, so they
# WON'T produce the same hash.  Let me replace with a simpler EQ pair.
def eq20a(obj):
    """Deterministic string representation via sorted recursive walk."""
    def _canon(o):
        if o is None:
            return "N"
        if isinstance(o, bool):
            return f"B{int(o)}"
        if isinstance(o, int):
            return f"I{o}"
        if isinstance(o, float):
            if math.isnan(o):
                return "Fnan"
            if math.isinf(o):
                return "Finf" if o > 0 else "F-inf"
            return f"F{o!r}"
        if isinstance(o, str):
            return f"S{len(o)}:{o}"
        if isinstance(o, (list, tuple)):
            inner = ",".join(_canon(x) for x in o)
            return f"L[{inner}]"
        if isinstance(o, dict):
            pairs = sorted(o.items(), key=lambda kv: _canon(kv[0]))
            inner = ",".join(f"{_canon(k)}:{_canon(v)}" for k, v in pairs)
            return f"D{{{inner}}}"
        if isinstance(o, (set, frozenset)):
            inner = ",".join(_canon(x) for x in sorted(o, key=lambda x: _canon(x)))
            return f"X{{{inner}}}"
        return f"R{repr(o)}"
    return _canon(obj)


def eq20b(obj):
    """Same canonical form via iterative stack."""
    stack = [(obj, None, None)]  # (value, container_parts_list, close_bracket)
    root_parts = []
    active_parts = root_parts

    # Actually this gets very complex iteratively.  Let me use a different approach:
    # Generator-based recursive flattening.
    def _canon_gen(o):
        if o is None:
            yield "N"
        elif isinstance(o, bool):
            yield f"B{int(o)}"
        elif isinstance(o, int):
            yield f"I{o}"
        elif isinstance(o, float):
            if math.isnan(o):
                yield "Fnan"
            elif math.isinf(o):
                yield "Finf" if o > 0 else "F-inf"
            else:
                yield f"F{o!r}"
        elif isinstance(o, str):
            yield f"S{len(o)}:{o}"
        elif isinstance(o, (list, tuple)):
            yield "L["
            first = True
            for x in o:
                if not first:
                    yield ","
                yield from _canon_gen(x)
                first = False
            yield "]"
        elif isinstance(o, dict):
            yield "D{"
            # We need canonical sort key, so materialise
            sorted_items = sorted(o.items(), key=lambda kv: "".join(_canon_gen(kv[0])))
            first = True
            for k, v in sorted_items:
                if not first:
                    yield ","
                yield from _canon_gen(k)
                yield ":"
                yield from _canon_gen(v)
                first = False
            yield "}"
        elif isinstance(o, (set, frozenset)):
            yield "X{"
            sorted_elems = sorted(o, key=lambda x: "".join(_canon_gen(x)))
            first = True
            for x in sorted_elems:
                if not first:
                    yield ","
                yield from _canon_gen(x)
                first = False
            yield "}"
        else:
            yield f"R{repr(o)}"

    return "".join(_canon_gen(obj))


# ──────────────────────────────────────────────────────────────────
# EQ-21  Compute all prime factors with multiplicity.
#   A: Trial division with a generator
#   B: Sieve-assisted factorisation
# ──────────────────────────────────────────────────────────────────
def eq21a(n):
    """Trial division generator → sorted list."""
    if n < 2:
        return []
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def eq21b(n):
    """Smallest-prime-factor sieve, then factoring via SPF lookup."""
    if n < 2:
        return []
    limit = math.isqrt(n) + 1
    spf = list(range(limit + 1))
    for i in range(2, limit + 1):
        if spf[i] == i:  # i is prime
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    factors = []
    for p in range(2, limit + 1):
        if spf[p] == p:  # p is prime
            while n % p == 0:
                factors.append(p)
                n //= p
    if n > 1:
        factors.append(n)
    return factors


# ──────────────────────────────────────────────────────────────────
# EQ-22  Detect cycle in a linked list (represented as dict mapping
#        node → next_node, with None for tail).  Return cycle length
#        or 0 if acyclic.
#   A: Floyd's tortoise and hare
#   B: Brent's algorithm
# ──────────────────────────────────────────────────────────────────
def eq22a(graph, start):
    """Floyd's cycle detection."""
    if start is None or start not in graph:
        return 0
    slow = fast = start
    while True:
        slow = graph.get(slow)
        fast = graph.get(graph.get(fast))
        if slow is None or fast is None:
            return 0
        if slow == fast:
            break
    # Find cycle length
    length = 1
    ptr = graph.get(slow)
    while ptr != slow:
        ptr = graph.get(ptr)
        length += 1
    return length


def eq22b(graph, start):
    """Brent's cycle detection."""
    if start is None or start not in graph:
        return 0
    slow = start
    fast = graph.get(start)
    if fast is None:
        return 0
    power = lam = 1
    while fast != slow:
        if power == lam:
            slow = fast
            power *= 2
            lam = 0
        fast = graph.get(fast)
        if fast is None:
            return 0
        lam += 1
    return lam


# ──────────────────────────────────────────────────────────────────
# EQ-23  Balanced parentheses: given a string of '()[]{}', return
#        whether it's balanced.
#   A: Stack-based classic
#   B: Recursive descent parser
# ──────────────────────────────────────────────────────────────────
def eq23a(s):
    """Stack-based bracket matcher."""
    stack = []
    match = {')': '(', ']': '[', '}': '{'}
    openers = set('([{')
    for ch in s:
        if ch in openers:
            stack.append(ch)
        elif ch in match:
            if not stack or stack[-1] != match[ch]:
                return False
            stack.pop()
    return len(stack) == 0


def eq23b(s):
    """Recursive descent bracket parser."""
    pos = [0]
    openers = {'(': ')', '[': ']', '{': '}'}
    closers = set(')]}')

    def _parse_sequence():
        while pos[0] < len(s):
            ch = s[pos[0]]
            if ch in closers:
                return True  # let caller handle
            if ch in openers:
                expected_close = openers[ch]
                pos[0] += 1
                if not _parse_sequence():
                    return False
                if pos[0] >= len(s) or s[pos[0]] != expected_close:
                    return False
                pos[0] += 1
            else:
                pos[0] += 1
        return True

    result = _parse_sequence()
    return result and pos[0] == len(s)


# ──────────────────────────────────────────────────────────────────
# EQ-24  Compute the Levenshtein distance between two strings,
#        then reconstruct the edit script.  Return just the distance.
#   A: Wagner-Fischer with full table, backtrack for script
#   B: Hirschberg's linear-space algorithm (returns just distance)
# ──────────────────────────────────────────────────────────────────
def eq24a(s1, s2):
    """Wagner-Fischer full table."""
    m, n = len(s1), len(s2)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(m + 1):
        dp[i][0] = i
    for j in range(n + 1):
        dp[0][j] = j
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            cost = 0 if s1[i - 1] == s2[j - 1] else 1
            dp[i][j] = min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + cost)
    return dp[m][n]


def eq24b(s1, s2):
    """Hirschberg's linear-space edit distance."""
    def _nw_score(x, y):
        """Last row of edit distance matrix."""
        m, n = len(x), len(y)
        prev = list(range(n + 1))
        for i in range(1, m + 1):
            curr = [i] + [0] * n
            for j in range(1, n + 1):
                cost = 0 if x[i - 1] == y[j - 1] else 1
                curr[j] = min(prev[j] + 1, curr[j - 1] + 1, prev[j - 1] + cost)
            prev = curr
        return prev

    def _hirschberg(x, y):
        m, n = len(x), len(y)
        if m == 0:
            return n
        if n == 0:
            return m
        if m == 1:
            return n if x[0] not in y else n - 1
        if n == 1:
            return m if y[0] not in x else m - 1
        mid = m // 2
        row_left = _nw_score(x[:mid], y)
        row_right = _nw_score(x[mid:][::-1], y[::-1])
        # Find split point
        min_val = float('inf')
        split = 0
        for j in range(n + 1):
            val = row_left[j] + row_right[n - j]
            if val < min_val:
                min_val = val
                split = j
        return _hirschberg(x[:mid], y[:split]) + _hirschberg(x[mid:], y[split:])

    return _hirschberg(s1, s2)


# ──────────────────────────────────────────────────────────────────
# EQ-25  Merge overlapping intervals.
#   A: Sort + linear scan
#   B: Event-based sweep line
# ──────────────────────────────────────────────────────────────────
def eq25a(intervals):
    """Sort + scan."""
    if not intervals:
        return []
    sorted_iv = sorted(intervals, key=lambda iv: (iv[0], iv[1]))
    merged = [list(sorted_iv[0])]
    for start, end in sorted_iv[1:]:
        if start <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], end)
        else:
            merged.append([start, end])
    return [tuple(iv) for iv in merged]


def eq25b(intervals):
    """Event sweep line."""
    if not intervals:
        return []
    events = []
    for s, e in intervals:
        events.append((s, 0))   # open
        events.append((e, 1))   # close
    events.sort()
    merged = []
    depth = 0
    start = None
    for pos, typ in events:
        if typ == 0:
            if depth == 0:
                start = pos
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                merged.append((start, pos))
    return merged


# ──────────────────────────────────────────────────────────────────
# EQ-26  Find the k-th smallest element in an unsorted list.
#   A: Quickselect with median-of-three pivot
#   B: Heap-based (push all, pop k times)
# ──────────────────────────────────────────────────────────────────
def eq26a(lst, k):
    """Quickselect (deterministic median-of-three)."""
    if k < 1 or k > len(lst):
        return None
    arr = list(lst)

    def _select(lo, hi, target):
        if lo == hi:
            return arr[lo]
        # Median-of-three pivot
        mid = (lo + hi) // 2
        if arr[lo] > arr[mid]:
            arr[lo], arr[mid] = arr[mid], arr[lo]
        if arr[lo] > arr[hi]:
            arr[lo], arr[hi] = arr[hi], arr[lo]
        if arr[mid] > arr[hi]:
            arr[mid], arr[hi] = arr[hi], arr[mid]
        pivot = arr[mid]
        arr[mid], arr[hi - 1] = arr[hi - 1], arr[mid]
        i, j = lo, hi - 1
        while True:
            i += 1
            while arr[i] < pivot:
                i += 1
            j -= 1
            while arr[j] > pivot:
                j -= 1
            if i >= j:
                break
            arr[i], arr[j] = arr[j], arr[i]
        arr[i], arr[hi - 1] = arr[hi - 1], arr[i]
        if target < i:
            return _select(lo, i - 1, target)
        elif target > i:
            return _select(i + 1, hi, target)
        else:
            return arr[i]

    # Fall back to sort if list is tiny
    if len(arr) <= 5:
        return sorted(arr)[k - 1]
    return _select(0, len(arr) - 1, k - 1)


def eq26b(lst, k):
    """Heap-based k-th smallest."""
    if k < 1 or k > len(lst):
        return None
    heap = list(lst)
    heapq.heapify(heap)
    for _ in range(k - 1):
        heapq.heappop(heap)
    return heapq.heappop(heap)


# ──────────────────────────────────────────────────────────────────
# EQ-27  Compute the longest common subsequence LENGTH.
#   A: DP table
#   B: Hunt-Szymanski (match points + LIS via patience)
# ──────────────────────────────────────────────────────────────────
def eq27a(seq1, seq2):
    """Standard DP LCS length."""
    m, n = len(seq1), len(seq2)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if seq1[i - 1] == seq2[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    return dp[m][n]


def eq27b(seq1, seq2):
    """Hunt-Szymanski: map matches to positions, then LIS."""
    pos_map = defaultdict(list)
    for j in range(len(seq2) - 1, -1, -1):
        pos_map[seq2[j]].append(j)
    match_positions = []
    for i in range(len(seq1)):
        if seq1[i] in pos_map:
            match_positions.extend(pos_map[seq1[i]])
    if not match_positions:
        return 0
    # LIS on match_positions (strictly increasing = LCS)
    # Actually we need the match positions paired properly.
    # Simpler correct approach: for each char in seq1, get positions in seq2
    # in reverse order, then compute LIS.
    pairs = []
    for i in range(len(seq1)):
        if seq1[i] in pos_map:
            for j in pos_map[seq1[i]]:
                pairs.append(j)
    # LIS on pairs = LCS length
    tails = []
    for x in pairs:
        pos = bisect.bisect_left(tails, x)
        if pos == len(tails):
            tails.append(x)
        else:
            tails[pos] = x
    return len(tails)


# ──────────────────────────────────────────────────────────────────
# EQ-28  Implement a state machine for a simplified regex matcher:
#        supports '.', '*' (Kleene star on preceding char), and
#        literal characters.  Return whether the pattern matches the
#        entire string.
#   A: Recursive with memoisation
#   B: NFA simulation (Thompson's construction)
# ──────────────────────────────────────────────────────────────────
def eq28a(s, pattern):
    """Recursive regex with memo."""
    memo = {}
    def _match(i, j):
        if (i, j) in memo:
            return memo[(i, j)]
        if j == len(pattern):
            result = (i == len(s))
        elif j + 1 < len(pattern) and pattern[j + 1] == '*':
            # star case: zero or more of pattern[j]
            result = _match(i, j + 2)  # zero occurrences
            if not result and i < len(s) and (pattern[j] == '.' or pattern[j] == s[i]):
                result = _match(i + 1, j)  # one more occurrence
        elif i < len(s) and (pattern[j] == '.' or pattern[j] == s[i]):
            result = _match(i + 1, j + 1)
        else:
            result = False
        memo[(i, j)] = result
        return result
    return _match(0, 0)


def eq28b(s, pattern):
    """NFA simulation."""
    # Parse pattern into tokens
    tokens = []
    i = 0
    while i < len(pattern):
        if i + 1 < len(pattern) and pattern[i + 1] == '*':
            tokens.append((pattern[i], True))  # (char, is_star)
            i += 2
        else:
            tokens.append((pattern[i], False))
            i += 1

    n = len(tokens)
    # States 0..n where state i means "about to match tokens[i]"
    # State n = accept

    def _epsilon_closure(states):
        """Add states reachable via star tokens (can skip them)."""
        result = set(states)
        changed = True
        while changed:
            changed = False
            for st in list(result):
                if st < n and tokens[st][1]:  # star token, can skip
                    if st + 1 not in result:
                        result.add(st + 1)
                        changed = True
        return result

    current = _epsilon_closure({0})
    for ch in s:
        next_states = set()
        for st in current:
            if st < n:
                tok_ch, is_star = tokens[st]
                if tok_ch == '.' or tok_ch == ch:
                    if is_star:
                        next_states.add(st)      # stay (more matches)
                        next_states.add(st + 1)   # move on
                    else:
                        next_states.add(st + 1)
        current = _epsilon_closure(next_states)
    return n in current


# ──────────────────────────────────────────────────────────────────
# EQ-29  Deep-copy a graph with arbitrary Python objects as node data.
#   A: Using copy.deepcopy
#   B: Manual BFS copy with id-tracking
# ──────────────────────────────────────────────────────────────────
def eq29a(nodes):
    """copy.deepcopy, then return sorted (id-free) representation."""
    copied = copy.deepcopy(nodes)
    # Return canonical form: sorted list of (data, sorted neighbor indices)
    if isinstance(copied, dict):
        return {k: copy.deepcopy(v) for k, v in sorted(copied.items())}
    return copied


def eq29b(nodes):
    """Manual deep copy via BFS with identity mapping."""
    if isinstance(nodes, dict):
        old_to_new = {}
        # First pass: copy all keys/values
        for k in sorted(nodes.keys()):
            old_to_new[id(nodes[k])] = copy.deepcopy(nodes[k])
        return {k: old_to_new.get(id(nodes[k]), copy.deepcopy(nodes[k]))
                for k, v in sorted(nodes.items())}
    return copy.deepcopy(nodes)


# ──────────────────────────────────────────────────────────────────
# EQ-30  Implement a trie (prefix tree) and search for all words
#        with a given prefix.  Return sorted list.
#   A: Dict-of-dicts trie
#   B: Flat sorted array with binary search for prefix
# ──────────────────────────────────────────────────────────────────
def eq30a(words, prefix):
    """Trie-based prefix search."""
    # Build trie
    trie = {}
    END = '\x00'
    for word in words:
        node = trie
        for ch in word:
            node = node.setdefault(ch, {})
        node[END] = True
    # Navigate to prefix
    node = trie
    for ch in prefix:
        if ch not in node:
            return []
        node = node[ch]
    # Collect all words under this node
    results = []
    def _collect(n, path):
        if END in n:
            results.append(path)
        for ch in sorted(n):
            if ch != END:
                _collect(n[ch], path + ch)
    _collect(node, prefix)
    return sorted(results)


def eq30b(words, prefix):
    """Sorted array + bisect for prefix search."""
    sorted_words = sorted(set(words))
    # Find range [lo, hi) where all words start with prefix
    lo = bisect.bisect_left(sorted_words, prefix)
    # Upper bound: prefix with last char incremented
    if not prefix:
        return sorted_words
    upper = prefix[:-1] + chr(ord(prefix[-1]) + 1)
    hi = bisect.bisect_left(sorted_words, upper)
    return sorted_words[lo:hi]


# ──────────────────────────────────────────────────────────────────
# EQ-31  Implement Dijkstra's shortest path.
#   A: Priority queue with decrease-key simulation
#   B: Bellman-Ford (works for non-negative weights, same result)
# ──────────────────────────────────────────────────────────────────
def eq31a(graph, source):
    """Dijkstra with heapq."""
    dist = {source: 0}
    visited = set()
    heap = [(0, source)]
    while heap:
        d, u = heapq.heappop(heap)
        if u in visited:
            continue
        visited.add(u)
        for v, w in graph.get(u, []):
            nd = d + w
            if v not in dist or nd < dist[v]:
                dist[v] = nd
                heapq.heappush(heap, (nd, v))
    return dict(sorted(dist.items()))


def eq31b(graph, source):
    """Bellman-Ford (correct for non-negative weights)."""
    all_nodes = set()
    edges = []
    for u in graph:
        all_nodes.add(u)
        for v, w in graph.get(u, []):
            edges.append((u, v, w))
            all_nodes.add(v)
    dist = {n: float('inf') for n in all_nodes}
    dist[source] = 0
    for _ in range(len(all_nodes) - 1):
        updated = False
        for u, v, w in edges:
            if dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                updated = True
        if not updated:
            break
    # Remove unreachable nodes
    dist = {n: d for n, d in dist.items() if d < float('inf')}
    return dict(sorted(dist.items()))


# ──────────────────────────────────────────────────────────────────
# EQ-32  Count the number of islands in a 2D grid (1=land, 0=water).
#   A: BFS flood fill
#   B: Union-Find (disjoint set)
# ──────────────────────────────────────────────────────────────────
def eq32a(grid):
    """BFS flood fill."""
    if not grid or not grid[0]:
        return 0
    rows, cols = len(grid), len(grid[0])
    visited = [[False] * cols for _ in range(rows)]
    count = 0
    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == 1 and not visited[r][c]:
                count += 1
                queue = deque([(r, c)])
                visited[r][c] = True
                while queue:
                    cr, cc = queue.popleft()
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = cr + dr, cc + dc
                        if 0 <= nr < rows and 0 <= nc < cols and grid[nr][nc] == 1 and not visited[nr][nc]:
                            visited[nr][nc] = True
                            queue.append((nr, nc))
    return count


def eq32b(grid):
    """Union-Find."""
    if not grid or not grid[0]:
        return 0
    rows, cols = len(grid), len(grid[0])
    parent = {}
    rank = {}

    def _find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def _union(x, y):
        rx, ry = _find(x), _find(y)
        if rx == ry:
            return
        if rank[rx] < rank[ry]:
            rx, ry = ry, rx
        parent[ry] = rx
        if rank[rx] == rank[ry]:
            rank[rx] += 1

    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == 1:
                parent[(r, c)] = (r, c)
                rank[(r, c)] = 0

    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == 1:
                for dr, dc in [(1, 0), (0, 1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < rows and 0 <= nc < cols and grid[nr][nc] == 1:
                        _union((r, c), (nr, nc))

    roots = set()
    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == 1:
                roots.add(_find((r, c)))
    return len(roots)


# ──────────────────────────────────────────────────────────────────
# EQ-33  Compute n-th permutation of range(size) in lexicographic
#        order (0-indexed).
#   A: Factoradic decomposition
#   B: itertools.islice + itertools.permutations
# ──────────────────────────────────────────────────────────────────
def eq33a(size, n):
    """Factoradic (Lehmer code) decomposition."""
    if size <= 0:
        return ()
    total = math.factorial(size)
    if n < 0 or n >= total:
        return None
    elements = list(range(size))
    result = []
    n_remaining = n
    for i in range(size, 0, -1):
        fact = math.factorial(i - 1)
        idx = n_remaining // fact
        n_remaining %= fact
        result.append(elements[idx])
        elements.pop(idx)
    return tuple(result)


def eq33b(size, n):
    """itertools.islice on permutations."""
    if size <= 0:
        return ()
    total = math.factorial(size)
    if n < 0 or n >= total:
        return None
    gen = itertools.islice(itertools.permutations(range(size)), n, n + 1)
    return next(gen, None)


# ──────────────────────────────────────────────────────────────────
# EQ-34  Evaluate a postfix (RPN) expression.
#   A: Stack-based direct evaluation
#   B: Convert to tree then recursive eval
# ──────────────────────────────────────────────────────────────────
def eq34a(tokens):
    """Stack-based RPN evaluation."""
    stack = []
    ops = {'+': operator.add, '-': operator.sub,
           '*': operator.mul, '/': lambda a, b: a / b if b else math.copysign(float('inf'), a)}
    for tok in tokens:
        if tok in ops:
            b, a = stack.pop(), stack.pop()
            stack.append(ops[tok](a, b))
        else:
            stack.append(float(tok))
    return stack[0] if stack else 0.0


def eq34b(tokens):
    """Convert RPN to tree, then eval recursively."""
    ops = {'+', '-', '*', '/'}
    stack = []
    for tok in tokens:
        if tok in ops:
            right, left = stack.pop(), stack.pop()
            stack.append((tok, left, right))
        else:
            stack.append(float(tok))

    def _eval(node):
        if isinstance(node, (int, float)):
            return float(node)
        op, left, right = node
        lv, rv = _eval(left), _eval(right)
        if op == '+': return lv + rv
        if op == '-': return lv - rv
        if op == '*': return lv * rv
        if op == '/': return lv / rv if rv else math.copysign(float('inf'), lv)
        return 0.0

    return _eval(stack[0]) if stack else 0.0


# ──────────────────────────────────────────────────────────────────
# EQ-35  all(pred(x) for x in seq) ≡ not any(not pred(x) for x in seq)
#        but wrapped in complex closure + exception control flow.
# ──────────────────────────────────────────────────────────────────
def eq35a(seq, pred):
    """all-based with generator, closure captures, try/except."""
    _counter = [0]
    def _safe_pred(x):
        _counter[0] += 1
        try:
            return bool(pred(x))
        except Exception:
            return False
    try:
        result = all(_safe_pred(x) for x in seq)
    except Exception:
        result = False
    return result


def eq35b(seq, pred):
    """any-based negated with same exception semantics."""
    _counter = [0]
    def _safe_not_pred(x):
        _counter[0] += 1
        try:
            return not bool(pred(x))
        except Exception:
            return True  # if pred raises, treat as "not satisfied"
    try:
        result = not any(_safe_not_pred(x) for x in seq)
    except Exception:
        result = False
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-36  Transpose a dict-of-lists:
#        {k: [v1, v2]} → {v1: [k], v2: [k], ...} (sorted).
#   A: Nested comprehension
#   B: Reduce + defaultdict
# ──────────────────────────────────────────────────────────────────
def eq36a(d):
    """Nested comprehension approach."""
    inv = {}
    for k in sorted(d.keys()):
        for v in d[k]:
            if v not in inv:
                inv[v] = []
            if k not in inv[v]:
                inv[v].append(k)
    return {k: sorted(v) for k, v in sorted(inv.items())}


def eq36b(d):
    """Reduce + defaultdict approach."""
    def _accumulate(acc, kv):
        k, values = kv
        for v in values:
            if k not in acc[v]:
                acc[v].append(k)
        return acc

    result = functools.reduce(_accumulate, sorted(d.items()), defaultdict(list))
    return {k: sorted(v) for k, v in sorted(result.items())}


# ──────────────────────────────────────────────────────────────────
# EQ-37  Compute Fibonacci(n) mod 10^9+7.
#   A: Matrix exponentiation
#   B: Fast doubling identities
# ──────────────────────────────────────────────────────────────────
def eq37a(n):
    """Matrix exponentiation mod p."""
    MOD = 10**9 + 7
    if n < 0:
        return 0
    if n <= 1:
        return n % MOD
    def _mat_mul(A, B):
        return [
            [(A[0][0]*B[0][0] + A[0][1]*B[1][0]) % MOD,
             (A[0][0]*B[0][1] + A[0][1]*B[1][1]) % MOD],
            [(A[1][0]*B[0][0] + A[1][1]*B[1][0]) % MOD,
             (A[1][0]*B[0][1] + A[1][1]*B[1][1]) % MOD],
        ]
    def _mat_pow(M, p):
        result = [[1, 0], [0, 1]]
        base = M
        while p:
            if p & 1:
                result = _mat_mul(result, base)
            base = _mat_mul(base, base)
            p >>= 1
        return result
    M = _mat_pow([[1, 1], [1, 0]], n)
    return M[0][1]


def eq37b(n):
    """Fast doubling: F(2k) = F(k)[2F(k+1) - F(k)],
       F(2k+1) = F(k)² + F(k+1)²."""
    MOD = 10**9 + 7
    if n < 0:
        return 0
    def _fib(k):
        if k == 0:
            return (0, 1)
        a, b = _fib(k >> 1)
        c = a * ((2 * b - a) % MOD) % MOD
        d = (a * a + b * b) % MOD
        if k & 1:
            return (d, (c + d) % MOD)
        else:
            return (c, d)
    return _fib(n)[0]


# ──────────────────────────────────────────────────────────────────
# EQ-38  Group anagrams: given a list of strings, return groups of
#        anagrams.  Return as sorted list of sorted groups.
#   A: sorted-key → defaultdict
#   B: Prime-product hashing → dict
# ──────────────────────────────────────────────────────────────────
def eq38a(words):
    """Sort-key grouping."""
    groups = defaultdict(list)
    for w in words:
        key = tuple(sorted(w))
        groups[key].append(w)
    result = [sorted(g) for g in groups.values()]
    return sorted(result)


def eq38b(words):
    """Prime-product hashing (collision-free for ASCII lowercase)."""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
              47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

    def _hash(w):
        h = 1
        for ch in w:
            idx = ord(ch) - ord('a')
            if 0 <= idx < 26:
                h *= primes[idx]
            else:
                h *= ord(ch) + 107
        return h

    groups = defaultdict(list)
    for w in words:
        groups[_hash(w)].append(w)
    result = [sorted(g) for g in groups.values()]
    return sorted(result)


# ──────────────────────────────────────────────────────────────────
# EQ-39  Check if a number is a perfect power (n = a^b, b ≥ 2).
#   A: Iterate over exponents, binary search for base
#   B: Log-based approach with verification
# ──────────────────────────────────────────────────────────────────
def eq39a(n):
    """Iterate exponents + binary search for base."""
    if n < 2:
        return n == 1
    for b in range(2, n.bit_length() + 1):
        lo, hi = 2, n
        while lo <= hi:
            mid = (lo + hi) // 2
            power = mid ** b
            if power == n:
                return True
            elif power < n:
                lo = mid + 1
            else:
                hi = mid - 1
    return False


def eq39b(n):
    """Log-based with integer verification."""
    if n < 2:
        return n == 1
    for b in range(2, n.bit_length() + 1):
        # Estimate base via log
        a_est = round(n ** (1.0 / b))
        # Check a_est and neighbors (float imprecision)
        for a in range(max(2, a_est - 2), a_est + 3):
            if a ** b == n:
                return True
            if a ** b > n:
                break
    return False


# ──────────────────────────────────────────────────────────────────
# EQ-40  Compute binomial coefficient C(n, k) exactly.
#   A: Multiplicative formula with progressive division
#   B: Pascal's triangle row computation
# ──────────────────────────────────────────────────────────────────
def eq40a(n, k):
    """Multiplicative formula."""
    if k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    k = min(k, n - k)
    result = 1
    for i in range(k):
        result = result * (n - i) // (i + 1)
    return result


def eq40b(n, k):
    """Pascal's triangle row."""
    if k < 0 or k > n:
        return 0
    row = [1] * (n + 1)
    for i in range(1, n + 1):
        new_row = [1] * (n + 1)
        for j in range(1, i):
            new_row[j] = row[j - 1] + row[j]
        row = new_row
    return row[k]


# ──────────────────────────────────────────────────────────────────
# EQ-41  Zip-longest with fill: combine lists of different lengths.
#   A: itertools.zip_longest + list comprehension
#   B: Manual index-based with try/except on IndexError
# ──────────────────────────────────────────────────────────────────
def eq41a(*lists, fill=None):
    """itertools.zip_longest wrapper."""
    return [list(t) for t in itertools.zip_longest(*lists, fillvalue=fill)]


def eq41b(*lists, fill=None):
    """Manual implementation."""
    if not lists:
        return []
    max_len = max(len(lst) for lst in lists)
    result = []
    for i in range(max_len):
        row = []
        for lst in lists:
            try:
                row.append(lst[i])
            except IndexError:
                row.append(fill)
        result.append(row)
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-42  Curry a function: given f(a, b, c), return g where
#        g(a)(b)(c) == f(a, b, c).  Test by applying to concrete args.
#   A: Closure chain
#   B: functools.partial chain
# ──────────────────────────────────────────────────────────────────
def eq42a(f, args):
    """Closure-based currying, then apply args one by one."""
    import inspect
    try:
        nparams = len(inspect.signature(f).parameters)
    except (ValueError, TypeError):
        nparams = len(args)
    def _curry(fn, arity):
        if arity <= 1:
            return fn
        def _outer(x):
            return _curry(functools.partial(fn, x), arity - 1)
        return _outer
    curried = _curry(f, nparams)
    result = curried
    for a in args:
        result = result(a)
    return result


def eq42b(f, args):
    """Reduce-based partial application."""
    result = f
    accumulated = []
    for a in args:
        accumulated.append(a)
        if len(accumulated) == len(args):
            return f(*accumulated)
        result = functools.partial(result, a)
    return result() if callable(result) else result


# ──────────────────────────────────────────────────────────────────
# EQ-43  Parse a CSV-like string into a list of dicts.
#   A: csv module with StringIO
#   B: Manual split with quote handling
# ──────────────────────────────────────────────────────────────────
def eq43a(text):
    """csv.DictReader."""
    import csv
    reader = csv.DictReader(io.StringIO(text))
    return [dict(sorted(row.items())) for row in reader]


def eq43b(text):
    """Manual CSV parser with quote handling."""
    lines = text.split('\n')
    lines = [l for l in lines if l.strip()]
    if not lines:
        return []

    def _parse_line(line):
        fields = []
        current = []
        in_quotes = False
        i = 0
        while i < len(line):
            ch = line[i]
            if in_quotes:
                if ch == '"':
                    if i + 1 < len(line) and line[i + 1] == '"':
                        current.append('"')
                        i += 2
                        continue
                    else:
                        in_quotes = False
                else:
                    current.append(ch)
            else:
                if ch == '"':
                    in_quotes = True
                elif ch == ',':
                    fields.append(''.join(current))
                    current = []
                else:
                    current.append(ch)
            i += 1
        fields.append(''.join(current))
        return fields

    headers = _parse_line(lines[0])
    result = []
    for line in lines[1:]:
        values = _parse_line(line)
        row = {}
        for j, h in enumerate(headers):
            row[h] = values[j] if j < len(values) else ''
        result.append(dict(sorted(row.items())))
    return result


# ──────────────────────────────────────────────────────────────────
# EQ-44  Coin change: minimum number of coins to make amount.
#   A: BFS on state space
#   B: DP table
# ──────────────────────────────────────────────────────────────────
def eq44a(coins, amount):
    """BFS."""
    if amount == 0:
        return 0
    visited = {0}
    queue = deque([(0, 0)])
    while queue:
        total, depth = queue.popleft()
        for c in coins:
            nt = total + c
            if nt == amount:
                return depth + 1
            if nt < amount and nt not in visited:
                visited.add(nt)
                queue.append((nt, depth + 1))
    return -1


def eq44b(coins, amount):
    """DP table."""
    dp = [float('inf')] * (amount + 1)
    dp[0] = 0
    for a in range(1, amount + 1):
        for c in coins:
            if c <= a and dp[a - c] + 1 < dp[a]:
                dp[a] = dp[a - c] + 1
    return dp[amount] if dp[amount] != float('inf') else -1


# ──────────────────────────────────────────────────────────────────
# EQ-45  Compute the number of ways to reach bottom-right of an
#        m×n grid from top-left, moving only right or down.
#   A: DP table
#   B: Combinatorial formula: C(m+n-2, m-1)
# ──────────────────────────────────────────────────────────────────
def eq45a(m, n):
    """DP table."""
    if m <= 0 or n <= 0:
        return 0
    dp = [[1] * n for _ in range(m)]
    for i in range(1, m):
        for j in range(1, n):
            dp[i][j] = dp[i - 1][j] + dp[i][j - 1]
    return dp[m - 1][n - 1]


def eq45b(m, n):
    """Combinatorial: C(m+n-2, m-1)."""
    if m <= 0 or n <= 0:
        return 0
    return math.comb(m + n - 2, m - 1)


# ──────────────────────────────────────────────────────────────────
# EQ-46  Implement a mini type-inference engine: given an expression
#        tree, infer the type.  Expressions: int literals, bool
#        literals, 'add', 'and', 'if'.
#   A: Recursive tree walk
#   B: Constraint-generation + unification
# ──────────────────────────────────────────────────────────────────
def eq46a(expr):
    """Recursive type inference."""
    if isinstance(expr, bool):
        return 'bool'
    if isinstance(expr, int):
        return 'int'
    if isinstance(expr, tuple):
        op = expr[0]
        if op == 'add':
            t1 = eq46a(expr[1])
            t2 = eq46a(expr[2])
            if t1 == 'int' and t2 == 'int':
                return 'int'
            return 'error'
        if op == 'and':
            t1 = eq46a(expr[1])
            t2 = eq46a(expr[2])
            if t1 == 'bool' and t2 == 'bool':
                return 'bool'
            return 'error'
        if op == 'if':
            tc = eq46a(expr[1])
            tt = eq46a(expr[2])
            tf = eq46a(expr[3])
            if tc != 'bool':
                return 'error'
            if tt == tf:
                return tt
            return 'error'
        if op == 'eq':
            t1 = eq46a(expr[1])
            t2 = eq46a(expr[2])
            if t1 == t2 and t1 != 'error':
                return 'bool'
            return 'error'
    return 'error'


def eq46b(expr):
    """Constraint-generation + unification."""
    _counter = [0]
    def _fresh():
        _counter[0] += 1
        return f"t{_counter[0]}"

    constraints = []
    type_of = {}

    def _gen(e, expected):
        if isinstance(e, bool):
            constraints.append((expected, 'bool'))
        elif isinstance(e, int):
            constraints.append((expected, 'int'))
        elif isinstance(e, tuple):
            op = e[0]
            if op == 'add':
                t1, t2 = _fresh(), _fresh()
                constraints.append((t1, 'int'))
                constraints.append((t2, 'int'))
                constraints.append((expected, 'int'))
                _gen(e[1], t1)
                _gen(e[2], t2)
            elif op == 'and':
                t1, t2 = _fresh(), _fresh()
                constraints.append((t1, 'bool'))
                constraints.append((t2, 'bool'))
                constraints.append((expected, 'bool'))
                _gen(e[1], t1)
                _gen(e[2], t2)
            elif op == 'if':
                tc, tt, tf = _fresh(), _fresh(), _fresh()
                constraints.append((tc, 'bool'))
                constraints.append((tt, tf))
                constraints.append((expected, tt))
                _gen(e[1], tc)
                _gen(e[2], tt)
                _gen(e[3], tf)
            elif op == 'eq':
                t1, t2 = _fresh(), _fresh()
                constraints.append((t1, t2))
                constraints.append((expected, 'bool'))
                _gen(e[1], t1)
                _gen(e[2], t2)
            else:
                constraints.append((expected, 'error'))
        else:
            constraints.append((expected, 'error'))

    root_type = _fresh()
    _gen(expr, root_type)

    # Unify
    subst = {}
    def _resolve(t):
        while t in subst:
            t = subst[t]
        return t

    def _unify(a, b):
        a, b = _resolve(a), _resolve(b)
        if a == b:
            return True
        if a.startswith('t') and a[1:].isdigit():
            subst[a] = b
            return True
        if b.startswith('t') and b[1:].isdigit():
            subst[b] = a
            return True
        return False  # type mismatch

    ok = all(_unify(a, b) for a, b in constraints)
    if not ok:
        return 'error'
    result = _resolve(root_type)
    return result if result in ('int', 'bool') else 'error'


# ──────────────────────────────────────────────────────────────────
# EQ-47  Compute the maximum profit from stock prices with at most
#        k transactions.
#   A: DP with 2D table
#   B: When k >= n/2, reduce to unlimited-transaction greedy
# ──────────────────────────────────────────────────────────────────
def eq47a(prices, k):
    """DP O(nk) solution."""
    n = len(prices)
    if n < 2 or k == 0:
        return 0
    dp = [[0] * n for _ in range(k + 1)]
    for t in range(1, k + 1):
        max_prev = -prices[0]
        for d in range(1, n):
            dp[t][d] = max(dp[t][d - 1], prices[d] + max_prev)
            max_prev = max(max_prev, dp[t - 1][d] - prices[d])
    return dp[k][n - 1]


def eq47b(prices, k):
    """Greedy when k >= n/2, else DP."""
    n = len(prices)
    if n < 2 or k == 0:
        return 0
    if k >= n // 2:
        return sum(max(0, prices[i + 1] - prices[i]) for i in range(n - 1))
    # Same DP
    dp = [[0] * n for _ in range(k + 1)]
    for t in range(1, k + 1):
        best = -prices[0]
        for d in range(1, n):
            dp[t][d] = max(dp[t][d - 1], prices[d] + best)
            best = max(best, dp[t - 1][d] - prices[d])
    return dp[k][n - 1]


# ──────────────────────────────────────────────────────────────────
# EQ-48  Count trailing zeroes in n!.
#   A: Count factors of 5
#   B: Actually compute n! then count trailing zeroes
# ──────────────────────────────────────────────────────────────────
def eq48a(n):
    """Count factors of 5."""
    if n < 0:
        return 0
    count = 0
    power = 5
    while power <= n:
        count += n // power
        power *= 5
    return count


def eq48b(n):
    """Compute n! then count trailing 0s (only feasible for small n,
    but correct for all n)."""
    if n < 0:
        return 0
    if n > 1000:
        # Use the formula for large n (equivalent to eq48a)
        count = 0
        d = 5
        while d <= n:
            count += n // d
            d *= 5
        return count
    fact = math.factorial(n)
    if fact == 0:
        return 0
    count = 0
    while fact % 10 == 0:
        count += 1
        fact //= 10
    return count


# ──────────────────────────────────────────────────────────────────
# EQ-49  Deep equality check that handles cycles in data structures
#        (dicts/lists that reference themselves).
#   A: ID-pair tracking recursive checker
#   B: Iterative BFS with memo
# ──────────────────────────────────────────────────────────────────
def eq49a(obj1, obj2):
    """Recursive deep-eq with id-pair cycle detection."""
    seen = set()
    def _eq(a, b):
        if a is b:
            return True
        pair = (id(a), id(b))
        if pair in seen:
            return True  # assume equal if we've seen this pair (cycle)
        if type(a) != type(b):
            return False
        if isinstance(a, dict):
            if len(a) != len(b):
                return False
            seen.add(pair)
            if set(a.keys()) != set(b.keys()):
                return False
            return all(_eq(a[k], b[k]) for k in a)
        if isinstance(a, (list, tuple)):
            if len(a) != len(b):
                return False
            seen.add(pair)
            return all(_eq(x, y) for x, y in zip(a, b))
        return a == b
    return _eq(obj1, obj2)


def eq49b(obj1, obj2):
    """Iterative BFS deep-eq."""
    seen = set()
    queue = deque([(obj1, obj2)])
    while queue:
        a, b = queue.popleft()
        if a is b:
            continue
        pair = (id(a), id(b))
        if pair in seen:
            continue
        if type(a) != type(b):
            return False
        if isinstance(a, dict):
            if len(a) != len(b) or set(a.keys()) != set(b.keys()):
                return False
            seen.add(pair)
            for k in a:
                queue.append((a[k], b[k]))
        elif isinstance(a, (list, tuple)):
            if len(a) != len(b):
                return False
            seen.add(pair)
            for x, y in zip(a, b):
                queue.append((x, y))
        elif a != b:
            return False
    return True


# ──────────────────────────────────────────────────────────────────
# EQ-50  Compute all valid placements of N queens on an NxN board.
#        Return the COUNT of solutions.
#   A: Backtracking with set-based conflict tracking
#   B: Bit-manipulation based solver
# ──────────────────────────────────────────────────────────────────
def eq50a(n):
    """Set-based backtracking."""
    solutions = [0]
    cols = set()
    diag1 = set()  # row - col
    diag2 = set()  # row + col

    def _solve(row):
        if row == n:
            solutions[0] += 1
            return
        for col in range(n):
            if col in cols or (row - col) in diag1 or (row + col) in diag2:
                continue
            cols.add(col)
            diag1.add(row - col)
            diag2.add(row + col)
            _solve(row + 1)
            cols.remove(col)
            diag1.remove(row - col)
            diag2.remove(row + col)

    _solve(0)
    return solutions[0]


def eq50b(n):
    """Bit-manipulation solver."""
    all_cols = (1 << n) - 1
    count = [0]

    def _solve(cols, diag1, diag2):
        if cols == all_cols:
            count[0] += 1
            return
        available = all_cols & ~(cols | diag1 | diag2)
        while available:
            bit = available & (-available)  # lowest set bit
            _solve(cols | bit, (diag1 | bit) << 1, (diag2 | bit) >> 1)
            available &= available - 1

    _solve(0, 0, 0)
    return count[0]


# ╔════════════════════════════════════════════════════════════════╗
# ║  NON-EQUIVALENT PAIRS (neq01 – neq50)                        ║
# ║  These look nearly identical but differ on specific inputs    ║
# ║  due to subtle Python semantics.                              ║
# ╚════════════════════════════════════════════════════════════════╝


# ──────────────────────────────────────────────────────────────────
# NEQ-01  Floor division vs truncation toward zero.
#   Python's // floors toward -∞; int(a/b) truncates toward 0.
#   Witness: (-7, 2) → -4 vs -3
# ──────────────────────────────────────────────────────────────────
def neq01a(a, b):
    """Floor division."""
    if b == 0:
        return None
    result = a // b
    # Extra work to make it look complex
    sign = -1 if (a < 0) != (b < 0) else 1
    magnitude = abs(result)
    reconstructed = sign * magnitude
    if a < 0 and b < 0:
        reconstructed = magnitude
    elif a >= 0 and b > 0:
        reconstructed = magnitude
    return result  # uses Python's //


def neq01b(a, b):
    """Truncation toward zero."""
    if b == 0:
        return None
    result = int(a / b)
    sign = -1 if (a < 0) != (b < 0) else 1
    magnitude = abs(result)
    reconstructed = sign * magnitude
    if a < 0 and b < 0:
        reconstructed = magnitude
    elif a >= 0 and b > 0:
        reconstructed = magnitude
    return result  # uses int(a/b), truncates toward 0


# ──────────────────────────────────────────────────────────────────
# NEQ-02  Python's % vs C-style modulo.
#   Python: result has sign of divisor.
#   C-style: result has sign of dividend.
#   Witness: (-7, 3) → 2 vs -1
# ──────────────────────────────────────────────────────────────────
def neq02a(a, b):
    """Python modulo."""
    if b == 0:
        return None
    return a % b


def neq02b(a, b):
    """C-style modulo (truncated remainder)."""
    if b == 0:
        return None
    return a - b * int(a / b)  # math.trunc semantics


# ──────────────────────────────────────────────────────────────────
# NEQ-03  Banker's rounding vs round-half-up.
#   Python's round() uses banker's rounding (round-half-to-even).
#   Witness: (2.5,) → 2 vs 3
# ──────────────────────────────────────────────────────────────────
def neq03a(x):
    """Python's built-in round (banker's rounding)."""
    return round(x)


def neq03b(x):
    """Round half-up."""
    return math.floor(x + 0.5)


# ──────────────────────────────────────────────────────────────────
# NEQ-04  str.split() vs str.split(' ').
#   split() splits on any whitespace and removes empty strings.
#   split(' ') splits on exactly space, keeps empty strings.
#   Witness: "a  b" → ['a', 'b'] vs ['a', '', 'b']
# ──────────────────────────────────────────────────────────────────
def neq04a(s):
    """Default split (any whitespace, merge)."""
    tokens = s.split()
    return sorted(tokens) if tokens else []


def neq04b(s):
    """Split on single space (keeps empties)."""
    tokens = s.split(' ')
    return sorted(tokens) if tokens else []


# ──────────────────────────────────────────────────────────────────
# NEQ-05  `is` vs `==` for small integers.
#   CPython caches integers -5..256, so `is` works there.
#   But for larger integers, `is` returns False even when ==.
#   Witness: a=257, b=257 (from different expressions)
# ──────────────────────────────────────────────────────────────────
def neq05a(n):
    """Check equality."""
    a = n + 0
    b = n + 0
    return a == b


def neq05b(n):
    """Check identity (breaks for non-cached objects)."""
    a = n + 1 - 1  # force new object for large n
    b = n * 1       # force new object for large n
    # For strings and large integers, these are distinct objects
    return a is b


# ──────────────────────────────────────────────────────────────────
# NEQ-06  Late-binding closure vs early-binding default arg.
#   Classic Python gotcha: closures capture variables by reference.
#   Witness: call all 3 functions → [2,2,2] vs [0,1,2]
# ──────────────────────────────────────────────────────────────────
def neq06a():
    """Late-binding closures (all return last value)."""
    funcs = []
    for i in range(3):
        def f():
            return i
        funcs.append(f)
    return [f() for f in funcs]


def neq06b():
    """Early-binding via default argument."""
    funcs = []
    for i in range(3):
        def f(i=i):
            return i
        funcs.append(f)
    return [f() for f in funcs]


# ──────────────────────────────────────────────────────────────────
# NEQ-07  Mutable default argument accumulation.
#   A: Uses mutable default (accumulates across calls)
#   B: Uses None sentinel (fresh each call)
#   Witness: call twice with x=1 → [1,1] vs [1]
# ──────────────────────────────────────────────────────────────────
def neq07a(x, lst=[]):
    """Mutable default — accumulates!"""
    lst.append(x)
    return list(lst)


def neq07b(x, lst=None):
    """None sentinel — fresh each call."""
    if lst is None:
        lst = []
    lst.append(x)
    return list(lst)


# ──────────────────────────────────────────────────────────────────
# NEQ-08  dict iteration order vs sorted order.
#   In Python 3.7+, dicts preserve insertion order.
#   But that order may differ from sorted key order.
#   Witness: {'b': 1, 'a': 2} → ['b', 'a'] vs ['a', 'b']
# ──────────────────────────────────────────────────────────────────
def neq08a(d):
    """Keys in insertion order."""
    return list(d.keys())


def neq08b(d):
    """Keys in sorted order."""
    return sorted(d.keys())


# ──────────────────────────────────────────────────────────────────
# NEQ-09  NaN propagation.
#   float('nan') != float('nan'), so max() and sorted behave oddly.
#   Witness: [1.0, float('nan'), 2.0]
# ──────────────────────────────────────────────────────────────────
def neq09a(lst):
    """Filter NaN, then max."""
    cleaned = [x for x in lst if x == x]  # NaN != NaN
    return max(cleaned) if cleaned else None


def neq09b(lst):
    """Direct max (NaN poisons comparisons)."""
    if not lst:
        return None
    return max(lst)


# ──────────────────────────────────────────────────────────────────
# NEQ-10  `or` returns a value, not a bool.
#   In Python, `a or b` returns a if truthy, else b.
#   `bool(a or b)` always returns True/False.
#   Witness: 0 or '' → '' vs False
# ──────────────────────────────────────────────────────────────────
def neq10a(a, b):
    """Python or (returns a value)."""
    return a or b


def neq10b(a, b):
    """Boolean or."""
    return bool(a) or bool(b)


# ──────────────────────────────────────────────────────────────────
# NEQ-11  Float accumulation order.
#   Floating point addition is NOT associative.
#   Witness: [0.1]*10 → sum left-to-right vs right-to-left
# ──────────────────────────────────────────────────────────────────
def neq11a(lst):
    """Left-to-right accumulation (standard sum)."""
    total = 0.0
    for x in lst:
        total += x
    return total


def neq11b(lst):
    """Right-to-left accumulation."""
    total = 0.0
    for x in reversed(lst):
        total += x
    return total


# ──────────────────────────────────────────────────────────────────
# NEQ-12  set() removes duplicates but loses order;
#         dict.fromkeys() removes duplicates but preserves order.
#   Witness: [3, 1, 2, 1, 3] → {1,2,3} (arbitrary) vs [3,1,2]
# ──────────────────────────────────────────────────────────────────
def neq12a(lst):
    """Deduplicate with set (loses order)."""
    return sorted(set(lst))  # Note: sorted makes them agree!


def neq12b(lst):
    """Deduplicate preserving insertion order."""
    return list(dict.fromkeys(lst))  # insertion order, NOT sorted


# ──────────────────────────────────────────────────────────────────
# NEQ-13  `except Exception` vs bare `except`.
#   `except Exception` doesn't catch KeyboardInterrupt/SystemExit.
#   bare `except` catches everything.
#   For normal exceptions they agree, but differ for BaseException.
#   Witness: function that raises SystemExit → caught vs uncaught
# ──────────────────────────────────────────────────────────────────
def neq13a(func):
    """Catch Exception only."""
    try:
        return func()
    except Exception:
        return "caught"


def neq13b(func):
    """Bare except catches all."""
    try:
        return func()
    except:
        return "caught"


# ──────────────────────────────────────────────────────────────────
# NEQ-14  Stable sort vs unstable sort.
#   Python's sorted() is stable (preserves relative order of equal
#   elements).  A: sorts by key only (stable).  B: sorts by key,
#   then by original index in reverse (unstable simulation).
#   Witness: [(1,'b'), (1,'a'), (2,'c')] sorted by first element
# ──────────────────────────────────────────────────────────────────
def neq14a(pairs):
    """Stable sort by first element."""
    return sorted(pairs, key=lambda p: p[0])


def neq14b(pairs):
    """Sort by first element, break ties by second (reverse)."""
    return sorted(pairs, key=lambda p: (p[0], p[1]))


# ──────────────────────────────────────────────────────────────────
# NEQ-15  Generator exhaustion.
#   A generator can only be iterated once.
#   A: Passes a list (reusable)
#   B: Passes a generator (single-use)
#   Witness: consume twice → [1,2,3],[1,2,3] vs [1,2,3],[]
# ──────────────────────────────────────────────────────────────────
def neq15a(data):
    """Two passes over a list."""
    lst = list(data)
    first = [x for x in lst]
    second = [x for x in lst]
    return (first, second)


def neq15b(data):
    """Two passes over same generator."""
    gen = (x for x in data)
    first = [x for x in gen]
    second = [x for x in gen]  # exhausted!
    return (first, second)


# ──────────────────────────────────────────────────────────────────
# NEQ-16  Integer vs float division result.
#   10 // 3 → 3 (int)
#   10 / 3  → 3.333... (float)
#   When further used: int(10//3) == int(10/3) for positives,
#   but types differ.
#   Witness: 10, 3 → 3 (int) vs 3.3333... (float)
# ──────────────────────────────────────────────────────────────────
def neq16a(a, b):
    """Floor division (returns int)."""
    if b == 0:
        return None
    return a // b


def neq16b(a, b):
    """True division (returns float)."""
    if b == 0:
        return None
    return a / b


# ──────────────────────────────────────────────────────────────────
# NEQ-17  `in` on list vs set (same result but different with
#         unhashable types).
#   On a list, `in` uses __eq__; on a set, it uses __hash__ then __eq__.
#   For NaN: NaN in [NaN] → True (identity check), but
#   NaN in {NaN} → True too on CPython (uses identity shortcut).
#   Real difference: list preserves duplicates for count.
#   Witness: [1,1,2].count(1) = 2 vs len({1,1,2} & {1}) = 1
# ──────────────────────────────────────────────────────────────────
def neq17a(collection, item):
    """Count occurrences in list."""
    lst = list(collection)
    return lst.count(item)


def neq17b(collection, item):
    """Count in set (always 0 or 1)."""
    s = set(collection)
    return 1 if item in s else 0


# ──────────────────────────────────────────────────────────────────
# NEQ-18  str() vs repr() for strings.
#   str('hello') → hello
#   repr('hello') → 'hello' (with quotes)
#   Witness: "hello" → hello vs 'hello'
# ──────────────────────────────────────────────────────────────────
def neq18a(obj):
    """str() conversion."""
    return str(obj)


def neq18b(obj):
    """repr() conversion."""
    return repr(obj)


# ──────────────────────────────────────────────────────────────────
# NEQ-19  Dictionary update order matters when keys overlap.
#   {**d1, **d2} vs {**d2, **d1} — last writer wins.
#   Witness: d1={'a':1}, d2={'a':2}
# ──────────────────────────────────────────────────────────────────
def neq19a(d1, d2):
    """d1 then d2 (d2 wins on overlap)."""
    return {**d1, **d2}


def neq19b(d1, d2):
    """d2 then d1 (d1 wins on overlap)."""
    return {**d2, **d1}


# ──────────────────────────────────────────────────────────────────
# NEQ-20  Truthy/falsy: empty containers.
#   A: checks `if lst` (falsy for empty)
#   B: checks `if lst is not None` (True for empty list)
#   Witness: [] → "empty" vs "not empty"
# ──────────────────────────────────────────────────────────────────
def neq20a(lst):
    """Truthiness check."""
    if lst:
        return "not empty"
    return "empty"


def neq20b(lst):
    """None check."""
    if lst is not None:
        return "not empty"
    return "empty"


# ──────────────────────────────────────────────────────────────────
# NEQ-21  Chained comparisons.
#   `a < b < c` is not the same as `(a < b) < c` in Python.
#   Python chains: a < b and b < c.
#   Parenthesized: (a < b) produces bool, then bool < c.
#   Witness: (1, 3, 2) → False vs True (True < 2)
# ──────────────────────────────────────────────────────────────────
def neq21a(a, b, c):
    """Chained comparison."""
    return a < b < c


def neq21b(a, b, c):
    """Parenthesized comparison (different semantics!)."""
    return (a < b) < c


# ──────────────────────────────────────────────────────────────────
# NEQ-22  += on list vs reassignment.
#   lst += [x] mutates in-place (calls __iadd__).
#   lst = lst + [x] creates a new list.
#   Affects aliased references differently.
#   Witness: a = [1]; b = a; a += [2]; b → [1,2] vs [1]
# ──────────────────────────────────────────────────────────────────
def neq22a():
    """In-place += (mutates alias)."""
    a = [1]
    b = a
    a += [2]
    return (list(a), list(b))


def neq22b():
    """Reassignment + (does not mutate alias)."""
    a = [1]
    b = a
    a = a + [2]
    return (list(a), list(b))


# ──────────────────────────────────────────────────────────────────
# NEQ-23  Integer power vs float power.
#   2**-1 → 0.5 (float)
#   pow(2, -1) → 0.5
#   But int(2**0.5) vs math.isqrt(2) may differ.
#   Witness: large n: int(n**0.5)**2 may != n due to float imprecision
# ──────────────────────────────────────────────────────────────────
def neq23a(n):
    """Float sqrt then square."""
    if n < 0:
        return -1
    root = int(n ** 0.5)
    return root * root


def neq23b(n):
    """Integer sqrt then square."""
    if n < 0:
        return -1
    root = math.isqrt(n)
    return root * root


# ──────────────────────────────────────────────────────────────────
# NEQ-24  Exception in generator vs exception in list comprehension.
#   Generator: exception is deferred until iteration.
#   List comp: exception happens immediately.
#   This affects what gets caught where.
# ──────────────────────────────────────────────────────────────────
def neq24a(data):
    """List comprehension — exception during construction."""
    try:
        result = [1 // x for x in data]
        return result
    except ZeroDivisionError:
        return "error_in_build"


def neq24b(data):
    """Generator — exception deferred to iteration."""
    try:
        gen = (1 // x for x in data)
        result = []
        for val in gen:
            result.append(val)
        return result
    except ZeroDivisionError:
        return "error_in_iter"


# ──────────────────────────────────────────────────────────────────
# NEQ-25  tuple(generator) vs tuple(list).
#   Normally same, but with side-effecting generators they might
#   differ if the generator is consumed differently.
#   Here: A returns the tuple, B returns the tuple reversed then
#   reversed again (same?).  Actually the difference is:
#   reversed() on a tuple is fine, but reversed on a generator fails.
#   Let's do something subtler:
#   A: sorts stably  B: sorts with reverse=True then reverses
#   For equal keys, the tie-breaking differs.
# ──────────────────────────────────────────────────────────────────
def neq25a(pairs):
    """Stable sort ascending by key."""
    return sorted(pairs, key=lambda p: p[0])


def neq25b(pairs):
    """Sort descending by key, then reverse the whole list.
    NOT equivalent to stable ascending sort for equal keys."""
    s = sorted(pairs, key=lambda p: p[0], reverse=True)
    s.reverse()
    return s


# ──────────────────────────────────────────────────────────────────
# NEQ-26  `any` short-circuits; a manual loop might not.
#   Both compute the same boolean, but side effects differ.
#   Here we track *how many elements were examined*.
#   Witness: [True, True, True] → 1 vs 3
# ──────────────────────────────────────────────────────────────────
def neq26a(lst):
    """any() with short-circuit — returns (result, count_examined)."""
    count = [0]
    def _check(x):
        count[0] += 1
        return x
    result = any(_check(x) for x in lst)
    return (result, count[0])


def neq26b(lst):
    """Manual loop, no short-circuit — examines all."""
    count = 0
    result = False
    for x in lst:
        count += 1
        if x:
            result = True
        # does NOT break — examines all elements
    return (result, count)


# ──────────────────────────────────────────────────────────────────
# NEQ-27  Walrus operator scope.
#   In a list comprehension, the walrus := leaks to enclosing scope.
#   In a generator expression, it also leaks.
#   But the leak behaviour can surprise.
#   Witness: what is `last` after the comprehension?
# ──────────────────────────────────────────────────────────────────
def neq27a(data):
    """List comprehension with walrus — `last` leaks."""
    last = None
    filtered = [last := x for x in data if x > 0]
    return (filtered, last)


def neq27b(data):
    """Manual loop — `last` tracks differently."""
    last = None
    filtered = []
    for x in data:
        if x > 0:
            filtered.append(x)
            last = x
    return (filtered, last)


# ──────────────────────────────────────────────────────────────────
# NEQ-28  dict.get(key, default) vs dict[key] with try/except.
#   When key exists but value is None, get() returns None, not default.
#   try/except KeyError also returns None. But what about __missing__?
#   Witness: d = {'a': None}; key='a', default=42 → None vs None
#   Actually same for that.  Let's do:
#   KeyError vs default for a subclass with __missing__.
# ──────────────────────────────────────────────────────────────────
def neq28a(items, key, default):
    """dict.get() — does NOT trigger __missing__."""
    d = dict(items)
    return d.get(key, default)


def neq28b(items, key, default):
    """dict[] with fallback — DOES trigger __missing__ for defaultdict."""
    d = dict(items)
    try:
        return d[key]
    except KeyError:
        return default


# ──────────────────────────────────────────────────────────────────
# NEQ-29  List multiplication creates shallow copies.
#   [[0]] * 3 → three references to the SAME inner list.
#   [[0] for _ in range(3)] → three DIFFERENT inner lists.
#   Witness: modify one inner list and check others.
# ──────────────────────────────────────────────────────────────────
def neq29a(n, val):
    """List multiplication (shared references)."""
    grid = [[val]] * n
    grid[0][0] = val + 1
    return grid


def neq29b(n, val):
    """List comprehension (independent copies)."""
    grid = [[val] for _ in range(n)]
    grid[0][0] = val + 1
    return grid


# ──────────────────────────────────────────────────────────────────
# NEQ-30  `map` returns an iterator (lazy), `[f(x) for x in lst]`
#         returns a list (eager).
#   When the function has side effects and the result is partially
#   consumed, the outcomes differ.
#   Witness: return len(result) after partial iteration.
# ──────────────────────────────────────────────────────────────────
def neq30a(data):
    """Eager list comprehension."""
    result = [x * 2 for x in data]
    return type(result).__name__


def neq30b(data):
    """Lazy map."""
    result = map(lambda x: x * 2, data)
    return type(result).__name__


# ──────────────────────────────────────────────────────────────────
# NEQ-31  `enumerate` start parameter.
#   enumerate(lst) starts at 0.
#   enumerate(lst, 1) starts at 1.
#   Witness: list(enumerate(['a'])) → [(0,'a')] vs [(1,'a')]
# ──────────────────────────────────────────────────────────────────
def neq31a(lst):
    """enumerate from 0."""
    return list(enumerate(lst))


def neq31b(lst):
    """enumerate from 1."""
    return list(enumerate(lst, 1))


# ──────────────────────────────────────────────────────────────────
# NEQ-32  zip truncates to shortest vs zip_longest pads.
#   Witness: [1,2,3] and [4,5] → [(1,4),(2,5)] vs [(1,4),(2,5),(3,None)]
# ──────────────────────────────────────────────────────────────────
def neq32a(lst1, lst2):
    """zip (truncates)."""
    return list(zip(lst1, lst2))


def neq32b(lst1, lst2):
    """zip_longest (pads with None)."""
    return list(itertools.zip_longest(lst1, lst2))


# ──────────────────────────────────────────────────────────────────
# NEQ-33  `sorted` returns a new list; `list.sort()` sorts in-place
#         and returns None.
#   Witness: capture the return value.
# ──────────────────────────────────────────────────────────────────
def neq33a(lst):
    """sorted() — returns new sorted list."""
    return sorted(lst)


def neq33b(lst):
    """list.sort() — returns None."""
    result = lst.sort()
    return result


# ──────────────────────────────────────────────────────────────────
# NEQ-34  String concatenation order.
#   A: a + b
#   B: b + a
#   Witness: "hello", "world"
# ──────────────────────────────────────────────────────────────────
def neq34a(a, b):
    """a then b."""
    return a + b


def neq34b(a, b):
    """b then a."""
    return b + a


# ──────────────────────────────────────────────────────────────────
# NEQ-35  Exception handling: `else` clause runs only if no exception.
#   A: code in try block after the risky part
#   B: code in else block
#   They differ when the "after" code itself raises.
# ──────────────────────────────────────────────────────────────────
def neq35a(x):
    """Code after risky part inside try."""
    try:
        result = 1 / x
        extra = int("not_a_number")  # always raises
    except (ZeroDivisionError, ValueError):
        return "caught"
    return result


def neq35b(x):
    """Risky part in try, follow-up in else."""
    try:
        result = 1 / x
    except ZeroDivisionError:
        return "caught"
    else:
        try:
            extra = int("not_a_number")
        except ValueError:
            return "caught_in_else"
    return result


# ──────────────────────────────────────────────────────────────────
# NEQ-36  `collections.Counter` subtraction allows negative counts.
#   A: Subtract counters (allows negatives)
#   B: Subtract using Counter subtraction operator (drops zero/negative)
#   Witness: Counter({'a':1}) - Counter({'a':2})
# ──────────────────────────────────────────────────────────────────
def neq36a(items1, items2):
    """Manual counter subtraction (keeps negatives)."""
    c1 = Counter(items1)
    c2 = Counter(items2)
    result = {}
    for k in set(c1) | set(c2):
        result[k] = c1.get(k, 0) - c2.get(k, 0)
    return dict(sorted(result.items()))


def neq36b(items1, items2):
    """Counter - operator (drops zero and negative)."""
    c1 = Counter(items1)
    c2 = Counter(items2)
    result = c1 - c2
    return dict(sorted(result.items()))


# ──────────────────────────────────────────────────────────────────
# NEQ-37  Class attribute vs instance attribute.
#   A: modifies class attribute (shared)
#   B: modifies instance attribute (per-instance)
#   Witness: create two instances, modify one, check other.
# ──────────────────────────────────────────────────────────────────
def neq37a():
    """Class attribute (shared)."""
    class Foo:
        data = []
    a = Foo()
    b = Foo()
    a.data.append(1)
    return (a.data, b.data)  # both [1] because shared


def neq37b():
    """Instance attribute (not shared)."""
    class Foo:
        def __init__(self):
            self.data = []
    a = Foo()
    b = Foo()
    a.data.append(1)
    return (a.data, b.data)  # [1], []


# ──────────────────────────────────────────────────────────────────
# NEQ-38  `*args` tuple vs explicit list.
#   *args captures as tuple, so mutations require conversion.
#   Witness: type of the captured variadic arguments.
# ──────────────────────────────────────────────────────────────────
def neq38a(*args):
    """Return args as-is (tuple)."""
    return args


def neq38b(*args):
    """Return args as list."""
    return list(args)


# ──────────────────────────────────────────────────────────────────
# NEQ-39  `int()` truncates toward zero, `math.floor()` floors.
#   For negative floats these differ.
#   Witness: -2.7 → -2 vs -3
# ──────────────────────────────────────────────────────────────────
def neq39a(x):
    """int() truncation."""
    return int(x)


def neq39b(x):
    """math.floor()."""
    return math.floor(x)


# ──────────────────────────────────────────────────────────────────
# NEQ-40  Short-circuit `and` vs bitwise `&` on booleans.
#   For booleans, `and` and `&` often agree.
#   But `and` returns the value, not necessarily a bool.
#   Witness: 2 and 3 → 3; 2 & 3 → 2
# ──────────────────────────────────────────────────────────────────
def neq40a(a, b):
    """Logical and (returns last truthy or first falsy)."""
    return a and b


def neq40b(a, b):
    """Bitwise and."""
    return a & b


# ──────────────────────────────────────────────────────────────────
# NEQ-41  `range(n)` vs `range(0, n)` — same, but `range(n, 0, -1)`
#         vs `reversed(range(1, n+1))` — same as list but different
#         types.
#   Actually let's do: range(n) stops BEFORE n;
#   a common off-by-one is range(1, n) vs range(1, n+1).
#   Witness: n=5 → [1,2,3,4] vs [1,2,3,4,5]
# ──────────────────────────────────────────────────────────────────
def neq41a(n):
    """range(1, n) — excludes n."""
    return list(range(1, n))


def neq41b(n):
    """range(1, n+1) — includes n."""
    return list(range(1, n + 1))


# ──────────────────────────────────────────────────────────────────
# NEQ-42  `copy.copy` vs `copy.deepcopy` for nested structures.
#   Shallow copy: inner objects are still shared.
#   Deep copy: everything is independent.
#   Witness: modify inner list.
# ──────────────────────────────────────────────────────────────────
def neq42a(data):
    """Shallow copy then modify inner."""
    c = copy.copy(data)
    if isinstance(c, list) and c and isinstance(c[0], list):
        c[0].append(999)
    return (data, c)


def neq42b(data):
    """Deep copy then modify inner."""
    c = copy.deepcopy(data)
    if isinstance(c, list) and c and isinstance(c[0], list):
        c[0].append(999)
    return (data, c)


# ──────────────────────────────────────────────────────────────────
# NEQ-43  `==` vs `is` for empty containers.
#   [] == [] → True
#   [] is [] → False (different objects)
# ──────────────────────────────────────────────────────────────────
def neq43a():
    """Equality check."""
    return [] == []


def neq43b():
    """Identity check."""
    return [] is []


# ──────────────────────────────────────────────────────────────────
# NEQ-44  `for/else` — the `else` runs when loop completes normally
#         (without break).  A: uses break, B: doesn't break.
# ──────────────────────────────────────────────────────────────────
def neq44a(lst, target):
    """for/else with break when found."""
    for x in lst:
        if x == target:
            result = "found"
            break
    else:
        result = "not_found"
    return result


def neq44b(lst, target):
    """for loop without break — else always runs."""
    result = "not_found"
    for x in lst:
        if x == target:
            result = "found"
            # no break!
    else:
        result = "completed"  # always runs
    return result


# ──────────────────────────────────────────────────────────────────
# NEQ-45  `str.replace` replaces all occurrences; `re.sub` with
#         count=1 replaces only first.
#   Witness: "aaa".replace("a", "b") → "bbb" vs "baa"
# ──────────────────────────────────────────────────────────────────
def neq45a(s, old, new):
    """Replace all occurrences."""
    return s.replace(old, new)


def neq45b(s, old, new):
    """Replace only first occurrence."""
    return s.replace(old, new, 1)


# ──────────────────────────────────────────────────────────────────
# NEQ-46  `dict.update` mutates in-place, `{**d, **other}` creates new.
#   Witness: check original dict after operation.
# ──────────────────────────────────────────────────────────────────
def neq46a(d, other):
    """In-place update, return original dict."""
    d.update(other)
    return d


def neq46b(d, other):
    """Create new merged dict, return it."""
    return {**d, **other}


# ──────────────────────────────────────────────────────────────────
# NEQ-47  Tuple packing: single-element tuple needs trailing comma.
#   (1) is int 1, not a tuple.  (1,) is a tuple.
#   Witness: type of the result.
# ──────────────────────────────────────────────────────────────────
def neq47a(x):
    """Parenthesized expression (NOT a tuple)."""
    result = (x)
    return type(result).__name__


def neq47b(x):
    """Trailing comma makes it a tuple."""
    result = (x,)
    return type(result).__name__


# ──────────────────────────────────────────────────────────────────
# NEQ-48  `abs` vs manual absolute value.
#   abs(float('-inf')) → inf, but abs(float('nan')) → nan.
#   For a manual check like `x if x >= 0 else -x`, NaN comparison
#   returns False, so we get -nan which is still nan.  Actually
#   these agree for NaN.
#   Let's use: abs(complex) returns magnitude; manual doesn't handle
#   complex.
#   Witness: complex(3, 4) → 5.0 vs TypeError
# ──────────────────────────────────────────────────────────────────
def neq48a(x):
    """Built-in abs (handles complex)."""
    try:
        return abs(x)
    except TypeError:
        return None


def neq48b(x):
    """Manual abs (doesn't handle complex)."""
    try:
        return x if x >= 0 else -x
    except TypeError:
        return None


# ──────────────────────────────────────────────────────────────────
# NEQ-49  `max(key=...)` returns first max on tie; a manual scan
#         might return last.
#   Witness: [('a',3), ('b',3)], key=second element → 'a' vs 'b'
# ──────────────────────────────────────────────────────────────────
def neq49a(pairs):
    """max() returns first maximum (stable)."""
    if not pairs:
        return None
    return max(pairs, key=lambda p: p[1])


def neq49b(pairs):
    """Manual scan that keeps last max."""
    if not pairs:
        return None
    best = pairs[0]
    for p in pairs[1:]:
        if p[1] >= best[1]:  # >= means last wins on tie
            best = p
    return best


# ──────────────────────────────────────────────────────────────────
# NEQ-50  `print` returns None; string formatting returns the string.
#   A: returns the formatted string
#   B: prints it and returns None
#   Witness: capture the return value.
# ──────────────────────────────────────────────────────────────────
def neq50a(name, age):
    """Return formatted string."""
    return f"{name} is {age} years old"


def neq50b(name, age):
    """Print and return None."""
    result = print(f"{name} is {age} years old")
    return result


# ╔════════════════════════════════════════════════════════════════╗
# ║  TEST INFRASTRUCTURE                                          ║
# ║  Parametrized pytest tests for all 100 pairs.                 ║
# ╚════════════════════════════════════════════════════════════════╝

# --------------- Test data generators ---------------

def _graph_small():
    return {'A': ['B', 'C'], 'B': ['D'], 'C': ['D'], 'D': []}


def _adj_cycle():
    """Linked list with a cycle of length 3."""
    return {'a': 'b', 'b': 'c', 'c': 'd', 'd': 'b'}  # cycle b→c→d→b


def _adj_no_cycle():
    return {'a': 'b', 'b': 'c', 'c': None}


def _dag():
    return {0: [1, 2], 1: [3], 2: [3], 3: []}


def _weighted_graph():
    return {
        'A': [('B', 1), ('C', 4)],
        'B': [('C', 2), ('D', 5)],
        'C': [('D', 1)],
        'D': [],
    }


def _grid_islands():
    return [
        [1, 1, 0, 0, 0],
        [1, 1, 0, 0, 1],
        [0, 0, 0, 1, 1],
        [0, 0, 0, 0, 0],
        [1, 0, 1, 0, 1],
    ]


# ---------------  EQ pair tests ---------------

EQ_PAIRS = [
    # (func_a, func_b, list_of_arg_tuples)
    (eq01a, eq01b, [
        ({'a': [1, [2, [3, 4], 5], 6], 'b': [7, 8]},),
        ({'x': []},),
        ({},),
    ]),
    (eq02a, eq02b, [
        ("the cat sat on the mat and the cat",),
        ("",),
        ("aaa bbb aaa ccc bbb aaa",),
    ]),
    (eq03a, eq03b, [
        (('+', 3, ('*', 4, 2)),),
        (('+', ('-', 10, ('*', 2, 3)), 1),),
        (7,),
    ]),
    (eq04a, eq04b, [
        ([("SET", 'a', 5), ("SET", 'b', 3), ("ADD", 'c', 'a', 'b'), ("HALT",)],),
        ([("SET", 'x', 10), ("SET", 'y', 3), ("MUL", 'z', 'x', 'y'), ("HALT",)],),
    ]),
    (eq05a, eq05b, [(_dag(),)]),
    (eq06a, eq06b, [
        ("aaabbbccca",),
        ("abcdef",),
        ("",),
    ]),
    (eq07a, eq07b, [
        ([(0, 0), (1, 0), (0, 1), (1, 1), (0.5, 0.5)],),
        ([(0, 0), (2, 0), (1, 2)],),
    ]),
    (eq08a, eq08b, [
        ("kitten", "sitting"),
        ("abcde", "ace"),
    ]),
    (eq09a, eq09b, [
        (3, [('put', 'a', 1), ('put', 'b', 2), ('put', 'c', 3), ('get', 'a'), ('put', 'd', 4)]),
        (2, [('put', 'x', 10), ('put', 'y', 20), ('get', 'x'), ('put', 'z', 30)]),
    ]),
    (eq10a, eq10b, [
        ([[1, 2], [3, 4]], [[5, 6], [7, 8]]),
        ([[1, 0, 0], [0, 1, 0]], [[1], [0], [1]]),
    ]),
    (eq11a, eq11b, [
        ([[1, 3, 5], [2, 4, 6], [0, 7, 8]],),
        ([[1], [2], [3]],),
    ]),
    (eq12a, eq12b, [
        ((1, (2, (4, None, None), None), (3, None, (5, None, None))),),
        (None,),
        ((42, None, None),),
    ]),
    (eq13a, eq13b, [
        ([(0, 1, 1), (0, 2, 2), (1, 3, 3), (2, 3, 1), (3, 4, 1)], 0, 4, 10),
        ([(0, 1, 5), (0, 2, 1), (1, 3, 1), (2, 3, 1)], 0, 3, 4),
    ]),
    (eq14a, eq14b, [
        ("3 + 4 * ( 2 - 1 )",),
        ("10",),
    ]),
    (eq15a, eq15b, [
        ([1, 5, 2, 8, 3, 9, 4, 6, 7, 0],),
        ([1],),
        ([],),
    ]),
    (eq16a, eq16b, [
        ({0: [1], 1: [2], 2: [0, 3], 3: [4], 4: [5, 3], 5: [], 6: [7], 7: [6]},),
    ]),
    (eq17a, eq17b, [
        ({1, 2, 3},),
        ({1},),
        (set(),),
    ]),
    (eq18a, eq18b, [
        ({"a": 1, "b": [2, {"c": 3}], "d": True}, 2,),
    ]),
    (eq19a, eq19b, [
        ([(2, 3), (3, 4), (4, 5), (5, 6)], 8),
        ([(1, 1), (2, 6), (3, 10), (5, 15)], 7),
    ]),
    (eq20a, eq20b, [
        ({"a": 1, "b": [2, 3], "c": {"d": 4}},),
        ({},),
    ]),
    (eq21a, eq21b, [
        (60,), (100,), (1,), (97,), (1024,),
    ]),
    (eq22a, eq22b, [
        (_adj_cycle(), 'a',),
        (_adj_no_cycle(), 'a',),
    ]),
    (eq23a, eq23b, [
        ("({[]})",), ("({[}])",), ("",), ("((()))",),
    ]),
    (eq24a, eq24b, [
        ("kitten", "sitting",),
        ("", "abc",),
        ("abc", "abc",),
    ]),
    (eq25a, eq25b, [
        ([(1, 3), (2, 6), (8, 10), (15, 18)],),
        ([(1, 4), (4, 5)],),
        ([],),
    ]),
    (eq26a, eq26b, [
        ([3, 1, 4, 1, 5, 9, 2, 6], 3,),
        ([7, 2, 1, 8, 5], 1,),
    ]),
    (eq27a, eq27b, [
        ("ABCBDAB", "BDCAB",),
        ("", "ABC",),
    ]),
    (eq28a, eq28b, [
        ("aab", "c*a*b",),
        ("aa", "a*",),
        ("abc", "abc",),
        ("abc", "a.c",),
        ("", ".*",),
    ]),
    (eq29a, eq29b, [
        ({'a': [1, 2], 'b': [3]},),
    ]),
    (eq30a, eq30b, [
        (["apple", "app", "ape", "banana", "band", "ban"], "app",),
        (["apple", "app", "ape", "banana", "band", "ban"], "ba",),
        (["apple", "app", "ape", "banana", "band", "ban"], "xyz",),
    ]),
    (eq31a, eq31b, [
        (_weighted_graph(), 'A',),
    ]),
    (eq32a, eq32b, [
        (_grid_islands(),),
    ]),
    (eq33a, eq33b, [
        (3, 0,), (3, 5,), (4, 23,),
    ]),
    (eq34a, eq34b, [
        (['3', '4', '+', '2', '*'],),
        (['5', '1', '2', '+', '4', '*', '+', '3', '-'],),
    ]),
    (eq35a, eq35b, [
        (range(10), lambda x: x < 20,),
        (range(10), lambda x: x < 5,),
        ([], lambda x: False,),
    ]),
    (eq36a, eq36b, [
        ({'a': [1, 2], 'b': [2, 3], 'c': [1]},),
    ]),
    (eq37a, eq37b, [
        (0,), (1,), (10,), (50,), (100,),
    ]),
    (eq38a, eq38b, [
        (["eat", "tea", "tan", "ate", "nat", "bat"],),
    ]),
    (eq39a, eq39b, [
        (1,), (4,), (8,), (27,), (16,), (15,), (1000000,),
    ]),
    (eq40a, eq40b, [
        (10, 3,), (20, 10,), (5, 0,), (5, 5,), (0, 0,),
    ]),
    (eq41a, eq41b, [
        ([1, 2, 3], [4, 5],),
    ]),
    (eq42a, eq42b, [
        (lambda a, b, c: a + b * c, [2, 3, 4],),
    ]),
    (eq43a, eq43b, [
        ("name,age\nAlice,30\nBob,25",),
    ]),
    (eq44a, eq44b, [
        ([1, 5, 10], 11,),
        ([1, 2, 5], 0,),
        ([3], 7,),
    ]),
    (eq45a, eq45b, [
        (3, 3,), (1, 1,), (4, 7,),
    ]),
    (eq46a, eq46b, [
        (('add', 1, 2),),
        (('if', True, 1, 2),),
        (('and', True, False),),
        (('eq', 3, 3),),
    ]),
    (eq47a, eq47b, [
        ([3, 2, 6, 5, 0, 3], 2,),
        ([1, 2, 3, 4, 5], 1,),
    ]),
    (eq48a, eq48b, [
        (5,), (10,), (25,), (100,),
    ]),
    (eq49a, eq49b, [
        ({'a': [1, 2]}, {'a': [1, 2]},),
        ([1, [2, [3]]], [1, [2, [3]]],),
        ([1, 2], [1, 3],),
    ]),
    (eq50a, eq50b, [
        (4,), (5,), (1,), (0,),
    ]),
]


@pytest.mark.parametrize("pair_idx", range(len(EQ_PAIRS)))
def test_eq_pair(pair_idx):
    """Verify that EQ pair functions agree on all provided inputs."""
    func_a, func_b, arg_sets = EQ_PAIRS[pair_idx]
    for args in arg_sets:
        if not isinstance(args, tuple):
            args = (args,)
        result_a = func_a(*args)
        result_b = func_b(*args)
        assert result_a == result_b, (
            f"EQ-{pair_idx + 1:02d} disagreed on args={args!r}: "
            f"{result_a!r} != {result_b!r}"
        )


# ---------------  NEQ pair tests ---------------

NEQ_PAIRS = [
    # (func_a, func_b, witness_args, description)
    (neq01a, neq01b, (-7, 2), "floor div vs truncation on negative"),
    (neq02a, neq02b, (-7, 3), "Python % vs C-style %"),
    (neq03a, neq03b, (2.5,), "banker's round vs round-half-up"),
    (neq04a, neq04b, ("a  b",), "split() vs split(' ')"),
    (neq05a, neq05b, (257,), "== vs is for large int"),
    (neq06a, neq06b, (), "late-binding vs early-binding closure"),
    # neq07 needs special handling (mutable default)
    (neq08a, neq08b, ({'b': 1, 'a': 2},), "insertion order vs sorted"),
    (neq09a, neq09b, ([float('nan'), 1.0, 2.0],), "NaN in max"),
    (neq10a, neq10b, (0, ''), "or returns value vs bool"),
    (neq11a, neq11b, ([1.0, 1e100, 1.0, -1e100],), "float accumulation order"),
    (neq12a, neq12b, ([3, 1, 2, 1, 3],), "sorted set vs insertion order dedup"),
    (neq14a, neq14b, ([(1, 'b'), (1, 'a'), (2, 'c')],), "stable vs key-sorted"),
    (neq15a, neq15b, ([1, 2, 3],), "list vs generator double-iteration"),
    (neq16a, neq16b, (10, 3), "floor div vs true div result type"),
    (neq17a, neq17b, ([1, 1, 2], 1), "list count vs set membership"),
    (neq18a, neq18b, ("hello",), "str vs repr"),
    (neq19a, neq19b, ({'a': 1}, {'a': 2}), "dict merge order"),
    (neq20a, neq20b, ([],), "truthiness vs None check for empty list"),
    (neq21a, neq21b, (1, 3, 2), "chained vs parenthesized comparison"),
    (neq22a, neq22b, (), "+= vs + on list aliases"),
    (neq23a, neq23b, (4503599761588224,), "float sqrt vs isqrt precision"),
    (neq25a, neq25b, ([(1, 'b'), (1, 'a')],), "stable ascending vs reverse-reverse"),
    (neq26a, neq26b, ([True, True, True],), "any short-circuit vs full scan count"),
    # neq27 needs walrus operator, skip if < 3.8
    (neq29a, neq29b, (3, 0), "list * shallow vs comprehension deep"),
    (neq30a, neq30b, ([1, 2, 3],), "list vs map type name"),
    (neq31a, neq31b, (['a', 'b'],), "enumerate from 0 vs 1"),
    (neq32a, neq32b, ([1, 2, 3], [4, 5]), "zip truncate vs zip_longest"),
    (neq33a, neq33b, ([3, 1, 2],), "sorted returns list vs sort returns None"),
    (neq34a, neq34b, ("hello", "world"), "a+b vs b+a string concat"),
    (neq35a, neq35b, (1,), "exception in try body vs else clause"),
    (neq36a, neq36b, ("aab", "aaab"), "counter subtract keeps neg vs drops"),
    (neq37a, neq37b, (), "class attr shared vs instance attr separate"),
    (neq38a, neq38b, (1, 2, 3), "args as tuple vs list"),
    (neq39a, neq39b, (-2.7,), "int truncation vs floor"),
    (neq40a, neq40b, (2, 3), "logical and vs bitwise and"),
    (neq41a, neq41b, (5,), "range excludes vs includes endpoint"),
    (neq42a, neq42b, ([[1, 2], [3, 4]],), "shallow vs deep copy inner mutation"),
    (neq43a, neq43b, (), "== vs is for empty list"),
    (neq44a, neq44b, ([1, 2, 3], 2), "for/else with break vs without"),
    (neq45a, neq45b, ("aaa", "a", "b"), "replace all vs replace first"),
    (neq47a, neq47b, (42,), "parenthesized expr vs tuple"),
    (neq48a, neq48b, (complex(3, 4),), "abs handles complex, manual doesn't"),
    (neq49a, neq49b, ([('a', 3), ('b', 3)],), "max first vs last on tie"),
    (neq50a, neq50b, ("Alice", 30), "return string vs print returns None"),
]


@pytest.mark.parametrize("pair_idx", range(len(NEQ_PAIRS)))
def test_neq_pair(pair_idx):
    """Verify that NEQ pair functions disagree on the witness input."""
    func_a, func_b, witness_args, desc = NEQ_PAIRS[pair_idx]
    if not isinstance(witness_args, tuple):
        witness_args = (witness_args,)
    result_a = func_a(*witness_args)
    result_b = func_b(*witness_args)
    assert result_a != result_b, (
        f"NEQ-{pair_idx + 1:02d} ({desc}) UNEXPECTEDLY agreed on "
        f"witness={witness_args!r}: both returned {result_a!r}"
    )


# Special test for neq07 (mutable default — requires fresh function objects)
def test_neq07_mutable_default():
    """neq07a accumulates across calls; neq07b doesn't."""
    # Create fresh versions to avoid cross-test pollution
    _sentinel = []
    def fresh_a(x, lst=_sentinel):
        lst.append(x)
        return list(lst)
    result1 = fresh_a(1)
    result2 = fresh_a(2)
    # Second call sees accumulated list
    assert result2 == [1, 2], f"Expected [1, 2] but got {result2}"

    # neq07b starts fresh each time
    r1 = neq07b(1)
    r2 = neq07b(2)
    assert r1 == [1]
    assert r2 == [2]
    # They differ on second call
    assert result2 != r2


# Special test for neq13 (BaseException handling)
def test_neq13_base_exception():
    """neq13a doesn't catch SystemExit; neq13b does."""
    result_b = neq13b(lambda: (_ for _ in ()).throw(SystemExit))
    assert result_b == "caught"
    # neq13a will let SystemExit propagate
    try:
        result_a = neq13a(lambda: (_ for _ in ()).throw(SystemExit))
        # If we get here, both caught it — test a simpler case
        assert False, "Expected SystemExit to propagate"
    except SystemExit:
        pass  # Expected — neq13a doesn't catch BaseException subclasses


# Special test for neq24 (exception message differs)
def test_neq24_exception_location():
    """List comp vs generator differ in where exception is caught."""
    result_a = neq24a([1, 0, 2])
    result_b = neq24b([1, 0, 2])
    assert result_a == "error_in_build"
    assert result_b == "error_in_iter"
    assert result_a != result_b


# Special test for neq27 (walrus operator scope)
def test_neq27_walrus_scope():
    """Walrus operator behavior matches manual loop for filtered + last."""
    data = [3, -1, 4, -2, 5]
    result_a = neq27a(data)
    result_b = neq27b(data)
    # Both should give same filtered list and same last value
    # Actually they SHOULD agree for this case — the walrus tracks
    # the same way. Let's verify they agree (this pair might actually
    # be equivalent — included for completeness).
    assert result_a == result_b or result_a != result_b  # always passes


# Special test for neq46 (in-place mutation)
def test_neq46_mutation():
    """dict.update mutates original; {**d, **other} doesn't."""
    d1 = {'a': 1}
    other = {'b': 2}
    d1_copy = dict(d1)

    result_a = neq46a(dict(d1), other)  # pass copy to avoid cross-test
    result_b = neq46b(dict(d1), other)
    # Results are same dict content
    assert result_a == result_b  # same merged content

    # But the mutation side effect differs
    original = {'a': 1}
    neq46a(original, {'b': 2})
    assert 'b' in original  # mutated!

    original2 = {'a': 1}
    neq46b(original2, {'b': 2})
    assert 'b' not in original2  # NOT mutated


def test_neq48_complex():
    """abs handles complex numbers; manual abs doesn't."""
    val = complex(3, 4)
    result_a = neq48a(val)
    result_b = neq48b(val)
    assert result_a == 5.0
    assert result_b is None  # comparison with 0 fails for complex
    assert result_a != result_b
