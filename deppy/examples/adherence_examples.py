"""
Deppy spec adherence / non-adherence examples.

Demonstrates automatic detection of whether functions satisfy their
@guarantee specs — proving correctness or finding counterexamples.

Run with:
    PYTHONPATH=. python3 deppy/examples/adherence_examples.py
    — or if installed —
    python3 deppy/examples/adherence_examples.py
"""
from __future__ import annotations

import sys
sys.path.insert(0, ".")

from deppy import guarantee, requires, check_adherence
from deppy.equivalence import AdherenceResult


def header(title: str) -> None:
    print(f"\n{'═' * 64}")
    print(f"  {title}")
    print(f"{'═' * 64}")


def show(results: list[AdherenceResult]) -> None:
    for r in results:
        tag = {True: "✅ PROVED", False: "❌ VIOLATION", None: "❓ INCONCLUSIVE"}[r.adheres]
        print(f"    {tag}  @guarantee({r.spec!r})")
        print(f"      method: {r.method}")
        if r.counterexample:
            print(f"      counterexample: {r.counterexample}")
        if r.details:
            print(f"      {r.details}")
    print()


# ═══════════════════════════════════════════════════════════════════
#  1. Correct specs — Z3 proves adherence
# ═══════════════════════════════════════════════════════════════════

header("1. Correct Specs — Z3 Proves Adherence")

@guarantee("result >= 0")
def square(x: int) -> int:
    return x * x

print("  square(x) = x * x")
show(check_adherence(square))


@guarantee("result >= 0")
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    return -x

print("  abs_val(x) = x if x >= 0 else -x")
show(check_adherence(abs_val))


@requires("n > 0")
@guarantee("result > 0")
def double_pos(n: int) -> int:
    return n * 2

print("  double_pos(n) = n * 2  [requires n > 0]")
show(check_adherence(double_pos))


@guarantee("result >= x")
@guarantee("result >= y")
def max_of(x: int, y: int) -> int:
    if x >= y:
        return x
    return y

print("  max_of(x, y)  [guarantees result >= x AND result >= y]")
show(check_adherence(max_of))


# ═══════════════════════════════════════════════════════════════════
#  2. Incorrect specs — Z3 finds counterexamples
# ═══════════════════════════════════════════════════════════════════

header("2. Incorrect Specs — Z3 Finds Counterexamples")

@guarantee("result > 0")  # WRONG: square(0) = 0, not > 0
def square_buggy(x: int) -> int:
    return x * x

print("  square_buggy(x) = x * x  with @guarantee('result > 0')  ← wrong!")
show(check_adherence(square_buggy))


@guarantee("result >= 0")  # WRONG: identity(-1) = -1
def identity(x: int) -> int:
    return x

print("  identity(x) = x  with @guarantee('result >= 0')  ← wrong!")
show(check_adherence(identity))


@guarantee("result != 0")  # WRONG: sub(5, 5) = 0
def sub(a: int, b: int) -> int:
    return a - b

print("  sub(a, b) = a - b  with @guarantee('result != 0')  ← wrong!")
show(check_adherence(sub))


@guarantee("result < x")  # WRONG: double(1) = 2 > 1
def double(x: int) -> int:
    return x * 2

print("  double(x) = x * 2  with @guarantee('result < x')  ← wrong!")
show(check_adherence(double))


# ═══════════════════════════════════════════════════════════════════
#  3. Subtle bugs — spec almost right
# ═══════════════════════════════════════════════════════════════════

header("3. Subtle Bugs — Spec Almost Right")

@guarantee("result >= 1")  # Off-by-one: abs(0) = 0, not >= 1
def abs_offbyone(x: int) -> int:
    if x >= 0:
        return x
    return -x

print("  abs(x)  with @guarantee('result >= 1')  ← off-by-one!")
show(check_adherence(abs_offbyone))


@guarantee("result == x + y")  # Typo: actually computes x * y
def add_typo(x: int, y: int) -> int:
    return x * y

print("  actually x*y  with @guarantee('result == x + y')  ← implementation typo!")
show(check_adherence(add_typo))


# ═══════════════════════════════════════════════════════════════════
#  4. Checking ad-hoc specs (not from @guarantee)
# ═══════════════════════════════════════════════════════════════════

header("4. Ad-Hoc Spec Checking (no decorator needed)")

def clamp(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

print("  clamp(x) — checking various properties:")
show(check_adherence(clamp, spec="result >= 0"))
show(check_adherence(clamp, spec="result <= 100"))
show(check_adherence(clamp, spec="result >= 0 and result <= 100"))
show(check_adherence(clamp, spec="result == x"))  # Not always true!


def triple(x: int) -> int:
    return x * 3

print("  triple(x) = x * 3 — checking various specs:")
show(check_adherence(triple, spec="result == x * 3"))
show(check_adherence(triple, spec="result >= x"))  # False for negative x


# ═══════════════════════════════════════════════════════════════════
#  5. Multi-guarantee — some pass, some fail
# ═══════════════════════════════════════════════════════════════════

header("5. Mixed Results — Some Specs Hold, Some Don't")

@guarantee("result >= 0")      # TRUE
@guarantee("result <= 100")    # FALSE: clamp_partial(200) = 200
def clamp_partial(x: int) -> int:
    if x < 0:
        return 0
    return x  # forgot the upper bound!

print("  clamp_partial(x) — missing upper bound clamp:")
show(check_adherence(clamp_partial))


# ═══════════════════════════════════════════════════════════════════
#  Summary
# ═══════════════════════════════════════════════════════════════════

header("Summary")
print("""  deppy.check_adherence(fn) automatically:
    ✅ Proves specs correct (Z3 symbolic: ∀ inputs, spec holds)
    ❌ Finds violations with concrete counterexamples
    ❓ Falls back to testing when Z3 can't handle the spec

  Usage:
    from deppy import guarantee, check_adherence

    @guarantee("result >= 0")
    def f(x: int) -> int: return x * x

    results = check_adherence(f)       # checks @guarantee specs
    results = check_adherence(f, spec="result > 0")  # check ad-hoc spec
""")
