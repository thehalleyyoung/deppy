"""
Deppy equivalence checking examples.

Demonstrates automatic equivalence and inequivalence checking using
Z3 symbolic proof and property-based testing.

Run with:
    PYTHONPATH=. python3 deppy/examples/equivalence_examples.py
    — or if installed —
    python3 deppy/examples/equivalence_examples.py
"""
from __future__ import annotations

import sys
sys.path.insert(0, ".")

from deppy.equivalence import check_equiv, EquivResult


def header(title: str) -> None:
    print(f"\n{'═' * 60}")
    print(f"  {title}")
    print(f"{'═' * 60}")


def show(label: str, result: EquivResult) -> None:
    tag = {True: "✅ EQUIVALENT", False: "❌ INEQUIVALENT", None: "❓ INCONCLUSIVE"}[result.equivalent]
    print(f"  {label}")
    print(f"    {tag}  (method: {result.method})")
    if result.counterexample:
        print(f"    counterexample: {result.counterexample}")
    if result.details:
        print(f"    {result.details}")
    print()


# ═══════════════════════════════════════════════════════════════════
#  1. Arithmetic equivalences (Z3 proves these)
# ═══════════════════════════════════════════════════════════════════

header("1. Arithmetic Equivalences — Z3 Symbolic Proof")

def double_mult(x: int) -> int:
    return x * 2

def double_add(x: int) -> int:
    return x + x

show("x * 2  vs  x + x", check_equiv(double_mult, double_add))


def square_v1(x: int) -> int:
    return x * x

def square_v2(x: int) -> int:
    return x ** 2

# x ** 2 isn't in our Z3 AST translator, so this falls back to testing
show("x * x  vs  x ** 2", check_equiv(square_v1, square_v2))


def negate_v1(x: int) -> int:
    return -x

def negate_v2(x: int) -> int:
    return 0 - x

show("-x  vs  0 - x", check_equiv(negate_v1, negate_v2))


# ═══════════════════════════════════════════════════════════════════
#  2. Branching equivalences
# ═══════════════════════════════════════════════════════════════════

header("2. Branching Equivalences")

def abs_v1(x: int) -> int:
    if x >= 0:
        return x
    return -x

def abs_v2(x: int) -> int:
    return x if x >= 0 else -x

show("abs (if/return)  vs  abs (ternary)", check_equiv(abs_v1, abs_v2))


def clamp_v1(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

def clamp_v2(x: int) -> int:
    return max(0, min(x, 100))

# max/min are supported in our Z3 translator
show("clamp (if chain)  vs  clamp (max/min)", check_equiv(clamp_v1, clamp_v2))


# ═══════════════════════════════════════════════════════════════════
#  3. Arithmetic inequivalences (Z3 finds counterexamples)
# ═══════════════════════════════════════════════════════════════════

header("3. Arithmetic Inequivalences — Z3 Counterexamples")

def times_two(x: int) -> int:
    return x * 2

def times_three(x: int) -> int:
    return x * 3

show("x * 2  vs  x * 3", check_equiv(times_two, times_three))


def identity(x: int) -> int:
    return x

def successor(x: int) -> int:
    return x + 1

show("x  vs  x + 1", check_equiv(identity, successor))


def always_zero(x: int) -> int:
    return 0

def sometimes_zero(x: int) -> int:
    return x - x  # always 0 too!

show("0  vs  x - x  (surprise: equivalent!)", check_equiv(always_zero, sometimes_zero))


# ═══════════════════════════════════════════════════════════════════
#  4. Multi-parameter functions
# ═══════════════════════════════════════════════════════════════════

header("4. Multi-Parameter Functions")

def add_v1(a: int, b: int) -> int:
    return a + b

def add_v2(a: int, b: int) -> int:
    return b + a

show("a + b  vs  b + a  (commutativity)", check_equiv(add_v1, add_v2))


def diff_v1(a: int, b: int) -> int:
    return a - b

def diff_v2(a: int, b: int) -> int:
    return b - a

show("a - b  vs  b - a  (not commutative!)", check_equiv(diff_v1, diff_v2))


def midpoint_v1(a: int, b: int) -> int:
    return (a + b) // 2

def midpoint_v2(a: int, b: int) -> int:
    return a + (b - a) // 2

# Integer division makes these subtly different
show("(a+b)//2  vs  a+(b-a)//2  (integer division quirk)", check_equiv(midpoint_v1, midpoint_v2))


# ═══════════════════════════════════════════════════════════════════
#  5. Higher-order / list functions (testing fallback)
# ═══════════════════════════════════════════════════════════════════

header("5. List Functions — Property-Based Testing")

def sort_builtin(xs: list) -> list:
    return sorted(xs)

def sort_reverse_reverse(xs: list) -> list:
    return sorted(xs, reverse=False)

show("sorted(xs)  vs  sorted(xs, reverse=False)", check_equiv(sort_builtin, sort_reverse_reverse))


def sum_builtin(xs: list) -> int:
    return sum(xs)

def sum_loop(xs: list) -> int:
    total = 0
    for x in xs:
        total += x
    return total

show("sum(xs)  vs  manual loop sum", check_equiv(sum_builtin, sum_loop))


def reverse_twice(xs: list) -> list:
    return list(reversed(list(reversed(xs))))

def identity_list(xs: list) -> list:
    return list(xs)

show("reverse(reverse(xs))  vs  xs", check_equiv(reverse_twice, identity_list))


def head_or_zero(xs: list) -> int:
    return xs[0] if xs else 0

def head_or_one(xs: list) -> int:
    return xs[0] if xs else 1

show("head_or_zero  vs  head_or_one  (differ on empty)", check_equiv(head_or_zero, head_or_one))


# ═══════════════════════════════════════════════════════════════════
#  6. With @guarantee specs
# ═══════════════════════════════════════════════════════════════════

header("6. Functions with @guarantee Specs")

from deppy import guarantee

@guarantee("result >= 0")
def abs_guaranteed_v1(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result >= 0")
def abs_guaranteed_v2(x: int) -> int:
    return x if x >= 0 else -x

show("abs v1 @guarantee  vs  abs v2 @guarantee", check_equiv(abs_guaranteed_v1, abs_guaranteed_v2))


# ═══════════════════════════════════════════════════════════════════
#  Summary
# ═══════════════════════════════════════════════════════════════════

header("Summary")
print("""  Deppy's equivalence checker uses:
    1. Z3 symbolic proof — for arithmetic/branching (exact, with counterexamples)
    2. Property-based testing — for lists, strings, complex types (probabilistic)
    3. @guarantee spec comparison — when available

  Import: from deppy.equivalence import check_equiv
  Result: EquivResult(equivalent=True/False/None, method='z3'/'testing'/...)
""")
