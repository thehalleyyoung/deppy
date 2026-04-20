"""
Deppy equivalence / inequivalence benchmark dataset.

200+ pairs of Python functions, each labeled with expected equivalence
and organized by category. Used for regression testing and accuracy
measurement of the equivalence checker.

Run with:
    PYTHONPATH=. python3 deppy/tests/equiv_benchmark.py

Categories:
  A. Arithmetic identities (equiv)
  B. Polynomial / algebraic (equiv)
  C. Branching refactors (equiv)
  D. Assignment patterns (equiv)
  E. Multi-parameter (equiv)
  F. Builtin rewrites (equiv)
  G. Edge-case equivalences (equiv)
  H. Arithmetic inequiv
  I. Branching inequiv
  J. Subtle bug inequiv
  K. Spec adherence (correct)
  L. Spec adherence (violated)
"""
from __future__ import annotations

# ═══════════════════════════════════════════════════════════════════
#  Category A: Arithmetic identities (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def a01_f(x: int) -> int: return x * 2
def a01_g(x: int) -> int: return x + x

def a02_f(x: int) -> int: return x * 3
def a02_g(x: int) -> int: return x + x + x

def a03_f(x: int) -> int: return x * 4
def a03_g(x: int) -> int: return x + x + x + x

def a04_f(x: int) -> int: return x * 5
def a04_g(x: int) -> int: return x * 4 + x

def a05_f(x: int) -> int: return x * 0
def a05_g(x: int) -> int: return 0

def a06_f(x: int) -> int: return x * 1
def a06_g(x: int) -> int: return x

def a07_f(x: int) -> int: return -x
def a07_g(x: int) -> int: return 0 - x

def a08_f(x: int) -> int: return -x
def a08_g(x: int) -> int: return x * -1

def a09_f(x: int) -> int: return x - x
def a09_g(x: int) -> int: return 0

def a10_f(x: int) -> int: return x + 0
def a10_g(x: int) -> int: return x

def a11_f(x: int) -> int: return -(-x)
def a11_g(x: int) -> int: return x

def a12_f(x: int) -> int: return x * 2 + x * 3
def a12_g(x: int) -> int: return x * 5

def a13_f(x: int) -> int: return (x + 1) - 1
def a13_g(x: int) -> int: return x

def a14_f(x: int) -> int: return x * 2 - x
def a14_g(x: int) -> int: return x

def a15_f(x: int) -> int: return x * 6
def a15_g(x: int) -> int: return x * 2 * 3

def a16_f(x: int) -> int: return x + x + x + x + x
def a16_g(x: int) -> int: return 5 * x

def a17_f(x: int) -> int: return x * 10
def a17_g(x: int) -> int: return (x * 5) * 2

def a18_f(x: int) -> int: return x * 7 - x * 3
def a18_g(x: int) -> int: return x * 4

def a19_f(x: int) -> int: return x * 100 + x
def a19_g(x: int) -> int: return x * 101

def a20_f(x: int) -> int: return (x + 5) * 2 - 10
def a20_g(x: int) -> int: return x * 2


# ═══════════════════════════════════════════════════════════════════
#  Category B: Polynomial / algebraic (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def b01_f(x: int) -> int: return x ** 2
def b01_g(x: int) -> int: return x * x

def b02_f(x: int) -> int: return x ** 3
def b02_g(x: int) -> int: return x * x * x

def b03_f(x: int) -> int: return (x + 1) ** 2
def b03_g(x: int) -> int: return x * x + 2 * x + 1

def b04_f(x: int) -> int: return (x - 1) ** 2
def b04_g(x: int) -> int: return x * x - 2 * x + 1

def b05_f(x: int, y: int) -> int: return (x + y) ** 2
def b05_g(x: int, y: int) -> int: return x * x + 2 * x * y + y * y

def b06_f(x: int, y: int) -> int: return (x + y) * (x - y)
def b06_g(x: int, y: int) -> int: return x * x - y * y

def b07_f(x: int) -> int: return (x + 1) * (x - 1)
def b07_g(x: int) -> int: return x * x - 1

def b08_f(x: int) -> int: return (x + 2) * (x + 3)
def b08_g(x: int) -> int: return x * x + 5 * x + 6

def b09_f(x: int) -> int: return (2 * x + 1) ** 2
def b09_g(x: int) -> int: return 4 * x * x + 4 * x + 1

def b10_f(x: int) -> int: return x ** 4
def b10_g(x: int) -> int:
    s = x * x
    return s * s

def b11_f(x: int, y: int) -> int: return (x - y) ** 2
def b11_g(x: int, y: int) -> int: return x * x - 2 * x * y + y * y

def b12_f(x: int) -> int: return (x + 1) ** 3
def b12_g(x: int) -> int: return x ** 3 + 3 * x ** 2 + 3 * x + 1

def b13_f(x: int) -> int: return 2 * (x + 3)
def b13_g(x: int) -> int: return 2 * x + 6

def b14_f(x: int) -> int: return 3 * (x - 2) + 6
def b14_g(x: int) -> int: return 3 * x

def b15_f(x: int, y: int) -> int: return (x + y) * (x + y)
def b15_g(x: int, y: int) -> int: return x ** 2 + 2 * x * y + y ** 2


# ═══════════════════════════════════════════════════════════════════
#  Category C: Branching refactors (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def c01_f(x: int) -> int:
    if x >= 0:
        return x
    return -x
def c01_g(x: int) -> int:
    return x if x >= 0 else -x

def c02_f(x: int) -> int:
    if x < 0:
        return -x
    return x
def c02_g(x: int) -> int:
    return abs(x)

def c03_f(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x
def c03_g(x: int) -> int:
    return max(0, min(x, 100))

def c04_f(x: int, y: int) -> int:
    if x >= y:
        return x
    return y
def c04_g(x: int, y: int) -> int:
    return max(x, y)

def c05_f(x: int, y: int) -> int:
    if x <= y:
        return x
    return y
def c05_g(x: int, y: int) -> int:
    return min(x, y)

def c06_f(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
def c06_g(x: int) -> int:
    if x > 0:
        return 1
    if x == 0:
        return 0
    return -1

def c07_f(x: int) -> int:
    if x == 0:
        return 0
    if x > 0:
        return 1
    return -1
def c07_g(x: int) -> int:
    if x < 0:
        return -1
    if x > 0:
        return 1
    return 0

def c08_f(x: int) -> int:
    if x > 0:
        return x
    return 0
def c08_g(x: int) -> int:
    return max(x, 0)

def c09_f(x: int) -> int:
    if x > 255:
        return 255
    return x
def c09_g(x: int) -> int:
    return min(x, 255)

def c10_f(x: int) -> int:
    if x < -128:
        return -128
    if x > 127:
        return 127
    return x
def c10_g(x: int) -> int:
    return max(-128, min(x, 127))

def c11_f(x: int) -> int:
    if x >= 0:
        return x * 2
    else:
        return -x * 2
def c11_g(x: int) -> int:
    return abs(x) * 2

def c12_f(x: int, y: int) -> int:
    if x > y:
        return x - y
    else:
        return y - x
def c12_g(x: int, y: int) -> int:
    return abs(x - y)

def c13_f(a: int, b: int, c: int) -> int:
    return max(a, max(b, c))
def c13_g(a: int, b: int, c: int) -> int:
    return max(max(a, b), c)

def c14_f(a: int, b: int, c: int) -> int:
    return min(a, min(b, c))
def c14_g(a: int, b: int, c: int) -> int:
    return min(min(a, b), c)

def c15_f(x: int) -> int:
    if x > 10:
        return 10
    if x < 0:
        return 0
    return x
def c15_g(x: int) -> int:
    if x < 0:
        return 0
    if x > 10:
        return 10
    return x

def c16_f(x: int) -> int:
    if x >= 0:
        if x <= 100:
            return x
        return 100
    return 0
def c16_g(x: int) -> int:
    return max(0, min(x, 100))

def c17_f(x: int, y: int) -> int:
    if x >= 0 and y >= 0:
        return x + y
    if x < 0 and y < 0:
        return x + y
    if x >= 0:
        return x + y
    return x + y
def c17_g(x: int, y: int) -> int:
    return x + y

def c18_f(x: int) -> int:
    r = x
    if r < 0:
        r = -r
    return r
def c18_g(x: int) -> int:
    return abs(x)

def c19_f(x: int) -> int:
    r = x
    if r < 0:
        r = 0
    return r
def c19_g(x: int) -> int:
    return max(0, x)

def c20_f(x: int) -> int:
    r = x
    if r > 50:
        r = 50
    if r < 0:
        r = 0
    return r
def c20_g(x: int) -> int:
    return max(0, min(x, 50))


# ═══════════════════════════════════════════════════════════════════
#  Category D: Assignment patterns (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def d01_f(x: int, y: int) -> int:
    r = x
    r += y
    return r
def d01_g(x: int, y: int) -> int:
    return x + y

def d02_f(x: int) -> int:
    r = x
    r *= 3
    return r
def d02_g(x: int) -> int:
    return x * 3

def d03_f(x: int) -> int:
    t = x * 2
    return t + 1
def d03_g(x: int) -> int:
    return x * 2 + 1

def d04_f(x: int) -> int:
    a = x + 1
    b = a * 2
    return b - 2
def d04_g(x: int) -> int:
    return (x + 1) * 2 - 2

def d05_f(x: int) -> int:
    a = x + 1
    b = a * a
    return b
def d05_g(x: int) -> int:
    return (x + 1) ** 2

def d06_f(x: int, y: int) -> int:
    s = x + y
    d = x - y
    return s * d
def d06_g(x: int, y: int) -> int:
    return x * x - y * y

def d07_f(x: int) -> int:
    r = 0
    r += x
    r += x
    r += x
    return r
def d07_g(x: int) -> int:
    return x * 3

def d08_f(x: int, y: int) -> int:
    r = x
    r += y
    r += y
    return r
def d08_g(x: int, y: int) -> int:
    return x + 2 * y

def d09_f(x: int) -> int:
    r = x
    r -= 1
    r *= 2
    return r
def d09_g(x: int) -> int:
    return (x - 1) * 2

def d10_f(x: int) -> int:
    a = x * 2
    b = a + 3
    c = b - 1
    return c
def d10_g(x: int) -> int:
    return x * 2 + 2

def d11_f(x: int, y: int) -> int:
    r = x - y
    r += y
    return r
def d11_g(x: int, y: int) -> int:
    return x

def d12_f(x: int) -> int:
    a = x + 5
    a -= 5
    return a
def d12_g(x: int) -> int:
    return x

def d13_f(x: int) -> int:
    a = x
    b = a
    c = b
    return c
def d13_g(x: int) -> int:
    return x

def d14_f(x: int) -> int:
    r = 1
    r *= x
    r *= x
    return r
def d14_g(x: int) -> int:
    return x ** 2

def d15_f(x: int, y: int) -> int:
    a = x + y
    b = x - y
    return a + b
def d15_g(x: int, y: int) -> int:
    return 2 * x


# ═══════════════════════════════════════════════════════════════════
#  Category E: Multi-parameter (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def e01_f(a: int, b: int) -> int: return a + b
def e01_g(a: int, b: int) -> int: return b + a

def e02_f(a: int, b: int) -> int: return a * b
def e02_g(a: int, b: int) -> int: return b * a

def e03_f(a: int, b: int, c: int) -> int: return (a + b) + c
def e03_g(a: int, b: int, c: int) -> int: return a + (b + c)

def e04_f(a: int, b: int, c: int) -> int: return (a * b) * c
def e04_g(a: int, b: int, c: int) -> int: return a * (b * c)

def e05_f(a: int, b: int, c: int) -> int: return a * (b + c)
def e05_g(a: int, b: int, c: int) -> int: return a * b + a * c

def e06_f(a: int, b: int, c: int) -> int: return a + b + c
def e06_g(a: int, b: int, c: int) -> int: return c + b + a

def e07_f(a: int, b: int) -> int: return (a + b) * (a + b)
def e07_g(a: int, b: int) -> int: return a ** 2 + 2 * a * b + b ** 2

def e08_f(a: int, b: int) -> int: return (a + b) * (a - b)
def e08_g(a: int, b: int) -> int: return a ** 2 - b ** 2

def e09_f(a: int, b: int, c: int) -> int: return a * b + a * c + b * c
def e09_g(a: int, b: int, c: int) -> int: return b * c + a * c + a * b

def e10_f(a: int, b: int) -> int:
    return max(a, b) + min(a, b)
def e10_g(a: int, b: int) -> int:
    return a + b

def e11_f(a: int, b: int) -> int:
    return max(a, b) - min(a, b)
def e11_g(a: int, b: int) -> int:
    return abs(a - b)

def e12_f(a: int, b: int) -> int:
    return max(a, b) * min(a, b)
def e12_g(a: int, b: int) -> int:
    return a * b

def e13_f(x: int, y: int, z: int) -> int:
    return max(x, max(y, z)) - min(x, min(y, z))
def e13_g(x: int, y: int, z: int) -> int:
    return max(max(x, y), z) - min(min(x, y), z)

def e14_f(a: int, b: int) -> int:
    if a > b:
        return a * 2 - b
    return b * 2 - a
def e14_g(a: int, b: int) -> int:
    return max(a, b) * 2 - min(a, b)

def e15_f(a: int, b: int) -> int:
    return (a + b) * (a + b) - (a - b) * (a - b)
def e15_g(a: int, b: int) -> int:
    return 4 * a * b


# ═══════════════════════════════════════════════════════════════════
#  Category F: Builtin rewrites (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def f01_f(x: int) -> int: return abs(x)
def f01_g(x: int) -> int:
    if x >= 0:
        return x
    return -x

def f02_f(x: int) -> int: return max(x, -x)
def f02_g(x: int) -> int: return abs(x)

def f03_f(x: int) -> int: return abs(-x)
def f03_g(x: int) -> int: return abs(x)

def f04_f(x: int) -> int: return abs(x) * abs(x)
def f04_g(x: int) -> int: return x * x

def f05_f(x: int) -> int: return max(x, 0) + min(x, 0)
def f05_g(x: int) -> int: return x

def f06_f(x: int, y: int) -> int: return max(x, y) + min(x, y)
def f06_g(x: int, y: int) -> int: return x + y

def f07_f(x: int) -> int: return abs(x * 2)
def f07_g(x: int) -> int: return abs(x) * 2

def f08_f(x: int) -> int: return min(max(x, 0), 100)
def f08_g(x: int) -> int: return max(0, min(x, 100))

def f09_f(x: int) -> int: return max(0, x) - min(0, x)
def f09_g(x: int) -> int: return abs(x)

def f10_f(x: int, y: int) -> int:
    return min(x, y) + abs(x - y)
def f10_g(x: int, y: int) -> int:
    return max(x, y)


# ═══════════════════════════════════════════════════════════════════
#  Category G: Edge-case equivalences (EQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def g01_f(x: int) -> int:
    if x > 0:
        return x
    if x == 0:
        return 0
    return -x
def g01_g(x: int) -> int:
    return abs(x)

def g02_f(x: int) -> int:
    if x > 100:
        return 100
    if x > 50:
        return x
    if x >= 0:
        return x
    return 0
def g02_g(x: int) -> int:
    return max(0, min(x, 100))

def g03_f(x: int) -> int:
    if x >= 10:
        return 10
    if x <= -10:
        return -10
    return x
def g03_g(x: int) -> int:
    return max(-10, min(x, 10))

def g04_f(x: int) -> int:
    r = x
    if r > 0:
        r = r - 1
        r = r + 1
    return r
def g04_g(x: int) -> int:
    return x

def g05_f(a: int, b: int) -> int:
    if a > b:
        return a
    if b > a:
        return b
    return a
def g05_g(a: int, b: int) -> int:
    return max(a, b)

def g06_f(x: int) -> int:
    a = x + 1
    b = x - 1
    return a * b
def g06_g(x: int) -> int:
    return x ** 2 - 1

def g07_f(x: int) -> int:
    a = abs(x)
    if a == 0:
        return 0
    return a
def g07_g(x: int) -> int:
    return abs(x)

def g08_f(x: int, y: int) -> int:
    m = max(x, y)
    n = min(x, y)
    return m - n
def g08_g(x: int, y: int) -> int:
    return abs(x - y)

def g09_f(x: int) -> int:
    if x > 0:
        return x * x
    if x < 0:
        return x * x
    return 0
def g09_g(x: int) -> int:
    return x * x

def g10_f(x: int) -> int:
    if x >= 0:
        return x % 1
    return 0
def g10_g(x: int) -> int:
    return 0


# ═══════════════════════════════════════════════════════════════════
#  Category H: Arithmetic inequivalence (INEQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def h01_f(x: int) -> int: return x * 2
def h01_g(x: int) -> int: return x * 3

def h02_f(x: int) -> int: return x
def h02_g(x: int) -> int: return x + 1

def h03_f(x: int) -> int: return x + 1
def h03_g(x: int) -> int: return x - 1

def h04_f(x: int) -> int: return -x
def h04_g(x: int) -> int: return x

def h05_f(x: int) -> int: return x * x
def h05_g(x: int) -> int: return x * 2

def h06_f(x: int) -> int: return x ** 2
def h06_g(x: int) -> int: return x ** 3

def h07_f(x: int) -> int: return x * 3 + 1
def h07_g(x: int) -> int: return x * 3

def h08_f(x: int) -> int: return x * 2 + x
def h08_g(x: int) -> int: return x * 2

def h09_f(x: int) -> int: return x * x + 1
def h09_g(x: int) -> int: return x * x

def h10_f(x: int) -> int: return x + 1
def h10_g(x: int) -> int: return x + 2

def h11_f(x: int) -> int: return x * 10
def h11_g(x: int) -> int: return x * 11

def h12_f(x: int) -> int: return (x + 1) ** 2
def h12_g(x: int) -> int: return x ** 2 + 1

def h13_f(x: int) -> int: return x * x - 1
def h13_g(x: int) -> int: return x * x + 1

def h14_f(x: int) -> int: return 2 * x + 3
def h14_g(x: int) -> int: return 3 * x + 2

def h15_f(x: int, y: int) -> int: return x + y
def h15_g(x: int, y: int) -> int: return x - y

def h16_f(x: int, y: int) -> int: return x * y
def h16_g(x: int, y: int) -> int: return x + y

def h17_f(x: int, y: int) -> int: return x - y
def h17_g(x: int, y: int) -> int: return y - x

def h18_f(x: int) -> int: return x * x * x
def h18_g(x: int) -> int: return x * x * x + 1

def h19_f(x: int) -> int: return abs(x) + 1
def h19_g(x: int) -> int: return abs(x)

def h20_f(x: int) -> int: return x % 3
def h20_g(x: int) -> int: return x % 5


# ═══════════════════════════════════════════════════════════════════
#  Category I: Branching inequivalence (INEQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def i01_f(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
def i01_g(x: int) -> int:
    if x >= 0:
        return 1
    return -1

def i02_f(x: int) -> int:
    if x >= 0:
        return x
    return -x
def i02_g(x: int) -> int:
    if x >= 0:
        return -x
    return x

def i03_f(x: int) -> int: return max(0, min(x, 100))
def i03_g(x: int) -> int: return max(0, min(x, 200))

def i04_f(x: int) -> int: return max(x, 0)
def i04_g(x: int) -> int: return max(x, 1)

def i05_f(x: int) -> int:
    if x > 10:
        return 1
    return 0
def i05_g(x: int) -> int:
    if x > 20:
        return 1
    return 0

def i06_f(x: int) -> int:
    if x > 0:
        return 1
    return 0
def i06_g(x: int) -> int:
    if x > 0:
        return 0
    return 1

def i07_f(x: int) -> int:
    if x >= 0:
        return x + 1
    return -x
def i07_g(x: int) -> int:
    return abs(x)

def i08_f(x: int, y: int) -> int: return max(x, y)
def i08_g(x: int, y: int) -> int: return min(x, y)

def i09_f(x: int) -> int: return max(0, x)
def i09_g(x: int) -> int: return max(0, min(x, 100))

def i10_f(x: int) -> int:
    if x > 0:
        return x * 2
    return 0
def i10_g(x: int) -> int:
    if x > 0:
        return x * 2
    return -x

def i11_f(x: int) -> int:
    if x > 0:
        return x + 1
    return 0
def i11_g(x: int) -> int:
    if x >= 0:
        return x + 1
    return 0

def i12_f(x: int) -> int:
    if x < 0:
        return 0
    if x > 50:
        return 50
    return x
def i12_g(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

def i13_f(a: int, b: int) -> int:
    if a > b:
        return a
    return b
def i13_g(a: int, b: int) -> int:
    if a >= b:
        return b
    return a

def i14_f(x: int) -> int:
    return abs(x) + x
def i14_g(x: int) -> int:
    return abs(x)

def i15_f(x: int) -> int:
    if x >= 0:
        return x * x
    return -x * x
def i15_g(x: int) -> int:
    return x * x

def i16_f(x: int, y: int) -> int: return max(x * 2, y)
def i16_g(x: int, y: int) -> int: return max(x, y)

def i17_f(x: int) -> int:
    if x == 0:
        return 1
    return x
def i17_g(x: int) -> int:
    return x

def i18_f(x: int) -> int: return max(x, -x) + 1
def i18_g(x: int) -> int: return max(x, -x)

def i19_f(x: int) -> int:
    r = x
    if r < 0:
        r = 0
    r += 1
    return r
def i19_g(x: int) -> int:
    return max(0, x)

def i20_f(x: int) -> int:
    if x > 0:
        return x
    if x < 0:
        return -x
    return 1  # bug: should be 0
def i20_g(x: int) -> int:
    return abs(x)


# ═══════════════════════════════════════════════════════════════════
#  Category J: Subtle bugs (INEQUIVALENT)
# ═══════════════════════════════════════════════════════════════════

def j01_f(x: int) -> int:
    if x > 0:
        return x
    return -x  # correct abs
def j01_g(x: int) -> int:
    if x > 0:
        return x
    return x  # bug: forgot negation

def j02_f(x: int) -> int:
    return max(0, min(x, 100))
def j02_g(x: int) -> int:
    return max(0, min(x, 99))  # off-by-one

def j03_f(a: int, b: int) -> int:
    if b == 0:
        return 0
    return a // b
def j03_g(a: int, b: int) -> int:
    if b == 0:
        return a  # bug: returns a instead of 0
    return a // b

def j04_f(x: int) -> int:
    if x < 0:
        return 0
    return x + 1
def j04_g(x: int) -> int:
    if x <= 0:  # bug: <= instead of <
        return 0
    return x + 1

def j05_f(x: int) -> int:
    return (x + 1) * 2
def j05_g(x: int) -> int:
    return x * 2 + 1  # bug: should be +2

def j06_f(x: int, y: int) -> int:
    return x * y + x
def j06_g(x: int, y: int) -> int:
    return x * (y + 2)  # bug: y+2 instead of y+1

def j07_f(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
def j07_g(x: int) -> int:
    if x > 0:
        return 1
    return -1  # bug: missing zero case

def j08_f(x: int) -> int:
    r = x
    if r < 0:
        r = -r
    return r
def j08_g(x: int) -> int:
    r = x
    if r < 0:
        r = 0  # bug: zeros out negatives instead of abs
    return r

def j09_f(x: int) -> int:
    return x ** 2
def j09_g(x: int) -> int:
    return x * 2  # bug: square vs double

def j10_f(x: int, y: int) -> int:
    return (x + y) ** 2
def j10_g(x: int, y: int) -> int:
    return x ** 2 + y ** 2  # bug: missing cross term


# ═══════════════════════════════════════════════════════════════════
#  Category K: Spec adherence — CORRECT (function satisfies its spec)
# ═══════════════════════════════════════════════════════════════════

from deppy import guarantee, requires

@guarantee("result >= 0")
def k01(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result >= 0")
def k02(x: int) -> int:
    return x * x

@guarantee("result >= x")
def k03(x: int) -> int:
    return abs(x)

@guarantee("result <= 100")
def k04(x: int) -> int:
    return min(x, 100)

@guarantee("result >= 0")
def k05(x: int) -> int:
    return max(0, x)

@guarantee("result >= 0 and result <= 100")
def k06(x: int) -> int:
    return max(0, min(x, 100))

@requires("x > 0")
@guarantee("result > 0")
def k07(x: int) -> int:
    return x * 2

@requires("x >= 0")
@guarantee("result >= x")
def k08(x: int) -> int:
    return x + 1

@guarantee("result >= x and result >= y")
def k09(x: int, y: int) -> int:
    return max(x, y)

@guarantee("result <= x and result <= y")
def k10(x: int, y: int) -> int:
    return min(x, y)

@requires("n >= 0")
@guarantee("result >= 0")
def k11(n: int) -> int:
    return n * n

@guarantee("result == x + y")
def k12(x: int, y: int) -> int:
    return x + y

@guarantee("result * result <= x * x")
def k13(x: int) -> int:
    return 0

@guarantee("result >= 0")
def k14(x: int) -> int:
    if x > 0:
        return x
    return 0

@guarantee("result >= -128 and result <= 127")
def k15(x: int) -> int:
    return max(-128, min(x, 127))

@requires("a > 0")
@requires("b > 0")
@guarantee("result > 0")
def k16(a: int, b: int) -> int:
    return a + b

@guarantee("result == x or result == -x")
def k17(x: int) -> int:
    return abs(x)

@requires("x >= 0")
@guarantee("result >= 0")
def k18(x: int) -> int:
    return x

@guarantee("result >= 0")
def k19(x: int, y: int) -> int:
    return abs(x) + abs(y)

@guarantee("result >= x - 1")
def k20(x: int) -> int:
    return x


# ═══════════════════════════════════════════════════════════════════
#  Category L: Spec adherence — VIOLATED (function breaks its spec)
# ═══════════════════════════════════════════════════════════════════

@guarantee("result > 0")
def l01(x: int) -> int:
    return abs(x)  # fails at x=0

@guarantee("result > x")
def l02(x: int) -> int:
    return x  # fails everywhere

@guarantee("result >= 0")
def l03(x: int) -> int:
    return x  # fails for negatives

@guarantee("result != 0")
def l04(x: int) -> int:
    return x * x  # fails at x=0

@guarantee("result > 0")
def l05(x: int) -> int:
    return x * x  # fails at x=0

@guarantee("result == x * 2")
def l06(x: int) -> int:
    return x * 2 + 1  # off by one

@guarantee("result <= 100")
def l07(x: int) -> int:
    return x  # fails for x>100

@guarantee("result >= 0 and result <= 50")
def l08(x: int) -> int:
    return max(0, min(x, 100))  # upper bound too high

@guarantee("result > x")
def l09(x: int) -> int:
    return x + 1  # WAIT: this is actually correct!  x+1 > x always...
# Actually, this IS correct for ints. Let me make a real violation:

@guarantee("result > x")
def l09_real(x: int) -> int:
    if x >= 0:
        return x + 1
    return x  # bug: returns x when negative, not x+1

@guarantee("result == x + y")
def l10(x: int, y: int) -> int:
    return x - y  # wrong op

@guarantee("result >= x and result >= y")
def l11(x: int, y: int) -> int:
    return min(x, y)  # wrong: min doesn't satisfy max's spec

@guarantee("result >= 0")
def l12(x: int) -> int:
    return x - 1  # fails for x=0

@guarantee("result <= x")
def l13(x: int) -> int:
    return x + 1  # always exceeds x

@guarantee("result == abs(x)")
def l14(x: int) -> int:
    return x  # fails for negatives

@guarantee("result >= 0 and result <= 10")
def l15(x: int) -> int:
    return max(0, x)  # no upper bound

@guarantee("result > 0")
def l16(x: int, y: int) -> int:
    return x + y  # no constraint forces this positive

@guarantee("result != x")
def l17(x: int) -> int:
    if x > 0:
        return x + 1
    return x  # fails at x <= 0

@guarantee("result * result == x")
def l18(x: int) -> int:
    return x  # x*x != x in general

@guarantee("result >= 0")
def l19(x: int) -> int:
    return -abs(x)  # always non-positive

@guarantee("result == max(x, y)")
def l20(x: int, y: int) -> int:
    return x  # wrong when y > x


# ═══════════════════════════════════════════════════════════════════
#  Registry and runner
# ═══════════════════════════════════════════════════════════════════

EQUIV_PAIRS = [
    # Category A: Arithmetic identities
    ("A01: x*2 = x+x", a01_f, a01_g, True),
    ("A02: x*3 = x+x+x", a02_f, a02_g, True),
    ("A03: x*4 = x+x+x+x", a03_f, a03_g, True),
    ("A04: x*5 = x*4+x", a04_f, a04_g, True),
    ("A05: x*0 = 0", a05_f, a05_g, True),
    ("A06: x*1 = x", a06_f, a06_g, True),
    ("A07: -x = 0-x", a07_f, a07_g, True),
    ("A08: -x = x*-1", a08_f, a08_g, True),
    ("A09: x-x = 0", a09_f, a09_g, True),
    ("A10: x+0 = x", a10_f, a10_g, True),
    ("A11: -(-x) = x", a11_f, a11_g, True),
    ("A12: x*2+x*3 = x*5", a12_f, a12_g, True),
    ("A13: (x+1)-1 = x", a13_f, a13_g, True),
    ("A14: x*2-x = x", a14_f, a14_g, True),
    ("A15: x*6 = x*2*3", a15_f, a15_g, True),
    ("A16: 5*x = x+x+x+x+x", a16_f, a16_g, True),
    ("A17: x*10 = (x*5)*2", a17_f, a17_g, True),
    ("A18: x*7-x*3 = x*4", a18_f, a18_g, True),
    ("A19: x*100+x = x*101", a19_f, a19_g, True),
    ("A20: (x+5)*2-10 = x*2", a20_f, a20_g, True),
    # Category B: Polynomial / algebraic
    ("B01: x² = x*x", b01_f, b01_g, True),
    ("B02: x³ = x*x*x", b02_f, b02_g, True),
    ("B03: (x+1)² = x²+2x+1", b03_f, b03_g, True),
    ("B04: (x-1)² = x²-2x+1", b04_f, b04_g, True),
    ("B05: (x+y)² = x²+2xy+y²", b05_f, b05_g, True),
    ("B06: (x+y)(x-y) = x²-y²", b06_f, b06_g, True),
    ("B07: (x+1)(x-1) = x²-1", b07_f, b07_g, True),
    ("B08: (x+2)(x+3) = x²+5x+6", b08_f, b08_g, True),
    ("B09: (2x+1)² = 4x²+4x+1", b09_f, b09_g, True),
    ("B10: x⁴ = (x²)²", b10_f, b10_g, True),
    ("B11: (x-y)² = x²-2xy+y²", b11_f, b11_g, True),
    ("B12: (x+1)³ = x³+3x²+3x+1", b12_f, b12_g, True),
    ("B13: 2(x+3) = 2x+6", b13_f, b13_g, True),
    ("B14: 3(x-2)+6 = 3x", b14_f, b14_g, True),
    ("B15: (x+y)² via mul = x²+2xy+y²", b15_f, b15_g, True),
    # Category C: Branching refactors
    ("C01: abs if/ret = ternary", c01_f, c01_g, True),
    ("C02: abs neg-first = abs()", c02_f, c02_g, True),
    ("C03: clamp if-chain = max/min", c03_f, c03_g, True),
    ("C04: max if = max()", c04_f, c04_g, True),
    ("C05: min if = min()", c05_f, c05_g, True),
    ("C06: sign order 1 = 2", c06_f, c06_g, True),
    ("C07: sign order 3 = 4", c07_f, c07_g, True),
    ("C08: relu if = max", c08_f, c08_g, True),
    ("C09: clamp upper = min", c09_f, c09_g, True),
    ("C10: signed byte clamp", c10_f, c10_g, True),
    ("C11: abs*2 branch = abs*2", c11_f, c11_g, True),
    ("C12: |x-y| branch = abs(x-y)", c12_f, c12_g, True),
    ("C13: max3 nest left = right", c13_f, c13_g, True),
    ("C14: min3 nest left = right", c14_f, c14_g, True),
    ("C15: clamp guard order swap", c15_f, c15_g, True),
    ("C16: nested if = max/min", c16_f, c16_g, True),
    ("C17: redundant branches = a+b", c17_f, c17_g, True),
    ("C18: mutating abs = abs()", c18_f, c18_g, True),
    ("C19: mutating relu = max(0,x)", c19_f, c19_g, True),
    ("C20: mutating clamp = max/min", c20_f, c20_g, True),
    # Category D: Assignment patterns
    ("D01: r=x;r+=y = x+y", d01_f, d01_g, True),
    ("D02: r=x;r*=3 = x*3", d02_f, d02_g, True),
    ("D03: t=x*2;t+1 = x*2+1", d03_f, d03_g, True),
    ("D04: a=x+1;b=a*2;b-2", d04_f, d04_g, True),
    ("D05: a=(x+1);a*a = (x+1)²", d05_f, d05_g, True),
    ("D06: s,d pattern = x²-y²", d06_f, d06_g, True),
    ("D07: triple augassign = x*3", d07_f, d07_g, True),
    ("D08: r+=y twice = x+2y", d08_f, d08_g, True),
    ("D09: r-=1;r*=2 = (x-1)*2", d09_f, d09_g, True),
    ("D10: chain a=x*2;b=a+3;c=b-1", d10_f, d10_g, True),
    ("D11: x-y+y = x", d11_f, d11_g, True),
    ("D12: x+5-5 = x", d12_f, d12_g, True),
    ("D13: a=b=c=x = x", d13_f, d13_g, True),
    ("D14: r=1;r*=x;r*=x = x²", d14_f, d14_g, True),
    ("D15: (x+y)+(x-y) = 2x", d15_f, d15_g, True),
    # Category E: Multi-parameter
    ("E01: a+b = b+a", e01_f, e01_g, True),
    ("E02: a*b = b*a", e02_f, e02_g, True),
    ("E03: (a+b)+c = a+(b+c)", e03_f, e03_g, True),
    ("E04: (a*b)*c = a*(b*c)", e04_f, e04_g, True),
    ("E05: a*(b+c) = a*b+a*c", e05_f, e05_g, True),
    ("E06: a+b+c = c+b+a", e06_f, e06_g, True),
    ("E07: (a+b)² = a²+2ab+b²", e07_f, e07_g, True),
    ("E08: (a+b)(a-b) = a²-b²", e08_f, e08_g, True),
    ("E09: symmetric sum of products", e09_f, e09_g, True),
    ("E10: max+min = a+b", e10_f, e10_g, True),
    ("E11: max-min = |a-b|", e11_f, e11_g, True),
    ("E12: max*min = a*b", e12_f, e12_g, True),
    ("E13: range max-min 3-param", e13_f, e13_g, True),
    ("E14: 2*max-min branch", e14_f, e14_g, True),
    ("E15: (a+b)²-(a-b)² = 4ab", e15_f, e15_g, True),
    # Category F: Builtin rewrites
    ("F01: abs = if/else", f01_f, f01_g, True),
    ("F02: max(x,-x) = abs", f02_f, f02_g, True),
    ("F03: abs(-x) = abs(x)", f03_f, f03_g, True),
    ("F04: abs²= x²", f04_f, f04_g, True),
    ("F05: max(x,0)+min(x,0) = x", f05_f, f05_g, True),
    ("F06: max+min = sum", f06_f, f06_g, True),
    ("F07: abs(2x) = 2*abs(x)", f07_f, f07_g, True),
    ("F08: min(max) = max(min) clamp", f08_f, f08_g, True),
    ("F09: max(0,x)-min(0,x) = abs", f09_f, f09_g, True),
    ("F10: min+|diff| = max", f10_f, f10_g, True),
    # Category G: Edge cases
    ("G01: 3-way abs = abs()", g01_f, g01_g, True),
    ("G02: multi-range clamp", g02_f, g02_g, True),
    ("G03: symmetric clamp ±10", g03_f, g03_g, True),
    ("G04: noop +1-1 in branch", g04_f, g04_g, True),
    ("G05: max via explicit 3-way", g05_f, g05_g, True),
    ("G06: (x+1)(x-1) = x²-1 via vars", g06_f, g06_g, True),
    ("G07: abs with zero guard = abs", g07_f, g07_g, True),
    ("G08: max-min = |diff|", g08_f, g08_g, True),
    ("G09: x² via pos/neg split", g09_f, g09_g, True),
    ("G10: x%1 = 0", g10_f, g10_g, True),
    # Category H: Arithmetic inequiv
    ("H01: x*2 ≠ x*3", h01_f, h01_g, False),
    ("H02: x ≠ x+1", h02_f, h02_g, False),
    ("H03: x+1 ≠ x-1", h03_f, h03_g, False),
    ("H04: -x ≠ x", h04_f, h04_g, False),
    ("H05: x² ≠ 2x", h05_f, h05_g, False),
    ("H06: x² ≠ x³", h06_f, h06_g, False),
    ("H07: 3x+1 ≠ 3x", h07_f, h07_g, False),
    ("H08: 3x ≠ 2x", h08_f, h08_g, False),
    ("H09: x²+1 ≠ x²", h09_f, h09_g, False),
    ("H10: x+1 ≠ x+2", h10_f, h10_g, False),
    ("H11: 10x ≠ 11x", h11_f, h11_g, False),
    ("H12: (x+1)² ≠ x²+1", h12_f, h12_g, False),
    ("H13: x²-1 ≠ x²+1", h13_f, h13_g, False),
    ("H14: 2x+3 ≠ 3x+2", h14_f, h14_g, False),
    ("H15: x+y ≠ x-y", h15_f, h15_g, False),
    ("H16: x*y ≠ x+y", h16_f, h16_g, False),
    ("H17: x-y ≠ y-x", h17_f, h17_g, False),
    ("H18: x³ ≠ x³+1", h18_f, h18_g, False),
    ("H19: |x|+1 ≠ |x|", h19_f, h19_g, False),
    ("H20: x%3 ≠ x%5", h20_f, h20_g, False),
    # Category I: Branching inequiv
    ("I01: sign missing zero", i01_f, i01_g, False),
    ("I02: abs vs neg-abs", i02_f, i02_g, False),
    ("I03: clamp 100 ≠ 200", i03_f, i03_g, False),
    ("I04: relu ≠ relu(1)", i04_f, i04_g, False),
    ("I05: threshold 10 ≠ 20", i05_f, i05_g, False),
    ("I06: flipped branch", i06_f, i06_g, False),
    ("I07: abs+1 on pos ≠ abs", i07_f, i07_g, False),
    ("I08: max ≠ min", i08_f, i08_g, False),
    ("I09: relu ≠ clamp", i09_f, i09_g, False),
    ("I10: neg branch 0 vs -x", i10_f, i10_g, False),
    ("I11: relu > vs >=", i11_f, i11_g, False),
    ("I12: clamp 50 ≠ 100", i12_f, i12_g, False),
    ("I13: max vs wrong min", i13_f, i13_g, False),
    ("I14: |x|+x ≠ |x|", i14_f, i14_g, False),
    ("I15: signed x² ≠ x²", i15_f, i15_g, False),
    ("I16: max(2x,y) ≠ max(x,y)", i16_f, i16_g, False),
    ("I17: x with 0→1 ≠ x", i17_f, i17_g, False),
    ("I18: |x|+1 ≠ |x|", i18_f, i18_g, False),
    ("I19: relu+1 ≠ relu", i19_f, i19_g, False),
    ("I20: abs with zero bug", i20_f, i20_g, False),
    # Category J: Subtle bugs
    ("J01: forgot negation", j01_f, j01_g, False),
    ("J02: off-by-one clamp", j02_f, j02_g, False),
    ("J03: div-by-zero handler wrong", j03_f, j03_g, False),
    ("J04: <= vs < boundary", j04_f, j04_g, False),
    ("J05: +2 vs +1 after double", j05_f, j05_g, False),
    ("J06: factor wrong +2 vs +1", j06_f, j06_g, False),
    ("J07: sign missing zero case", j07_f, j07_g, False),
    ("J08: abs→0 instead of neg", j08_f, j08_g, False),
    ("J09: square vs double", j09_f, j09_g, False),
    ("J10: (x+y)² missing 2xy", j10_f, j10_g, False),
]

ADHERENCE_CORRECT = [
    ("K01: |x| >= 0", k01),
    ("K02: x² >= 0", k02),
    ("K03: |x| >= x", k03),
    ("K04: min(x,100) <= 100", k04),
    ("K05: max(0,x) >= 0", k05),
    ("K06: clamp [0,100]", k06),
    ("K07: 2x > 0 when x > 0", k07),
    ("K08: x+1 >= x when x >= 0", k08),
    ("K09: max >= both", k09),
    ("K10: min <= both", k10),
    ("K11: n² >= 0 when n >= 0", k11),
    ("K12: x+y == x+y", k12),
    ("K13: 0² <= x²", k13),
    ("K14: relu >= 0", k14),
    ("K15: byte clamp bounds", k15),
    ("K16: a+b > 0 when a,b > 0", k16),
    ("K17: |x| == x or -x", k17),
    ("K18: x >= 0 when x >= 0", k18),
    ("K19: |x|+|y| >= 0", k19),
    ("K20: x >= x-1", k20),
]

ADHERENCE_VIOLATED = [
    ("L01: |x| > 0 — fails x=0", l01),
    ("L02: x > x — impossible", l02),
    ("L03: x >= 0 — neg fails", l03),
    ("L04: x² != 0 — fails x=0", l04),
    ("L05: x² > 0 — fails x=0", l05),
    ("L06: 2x+1 ≠ 2x", l06),
    ("L07: x <= 100 — unbounded", l07),
    ("L08: clamp(100) ∉ [0,50]", l08),
    ("L09: partial x > x", l09_real),
    ("L10: x-y ≠ x+y", l10),
    ("L11: min ≱ both", l11),
    ("L12: x-1 < 0 at x=0", l12),
    ("L13: x+1 > x", l13),
    ("L14: x ≠ |x|", l14),
    ("L15: relu ∉ [0,10]", l15),
    ("L16: x+y > 0 — not always", l16),
    ("L17: x ≠ x at x≤0", l17),
    ("L18: x² ≠ x", l18),
    ("L19: -|x| < 0", l19),
    ("L20: x ≠ max(x,y)", l20),
]


def run_benchmark() -> None:
    """Run the full benchmark and report accuracy."""
    from deppy.equivalence import check_equiv, check_adherence

    total = len(EQUIV_PAIRS) + len(ADHERENCE_CORRECT) + len(ADHERENCE_VIOLATED)
    passed = 0
    failed_list: list[str] = []

    # ── Equivalence / inequivalence ──
    equiv_pass = equiv_fail = 0
    for name, f, g, expected in EQUIV_PAIRS:
        r = check_equiv(f, g)
        ok = r.equivalent is expected
        if ok:
            equiv_pass += 1
            passed += 1
        else:
            equiv_fail += 1
            failed_list.append(f"  ✗ {name}: expected {'EQ' if expected else 'NEQ'}, got {r}")

    # ── Spec adherence (correct) ──
    adh_pass = adh_fail = 0
    for name, fn in ADHERENCE_CORRECT:
        results = check_adherence(fn)
        ok = all(r.adheres is True for r in results)
        if ok:
            adh_pass += 1
            passed += 1
        else:
            adh_fail += 1
            failed_list.append(f"  ✗ {name}: expected ADHERES, got {results}")

    # ── Spec adherence (violated) ──
    vio_pass = vio_fail = 0
    for name, fn in ADHERENCE_VIOLATED:
        results = check_adherence(fn)
        ok = any(r.adheres is False for r in results)
        if ok:
            vio_pass += 1
            passed += 1
        else:
            vio_fail += 1
            failed_list.append(f"  ✗ {name}: expected VIOLATES, got {results}")

    # ── Report ──
    print("═" * 60)
    print(f"  Deppy Equivalence Benchmark: {passed}/{total}")
    print("═" * 60)
    print(f"  Equiv/Inequiv: {equiv_pass}/{len(EQUIV_PAIRS)}")
    print(f"  Adherence OK:  {adh_pass}/{len(ADHERENCE_CORRECT)}")
    print(f"  Adherence Vio: {vio_pass}/{len(ADHERENCE_VIOLATED)}")
    print("═" * 60)

    if failed_list:
        print(f"\nFailed ({len(failed_list)}):")
        for line in failed_list:
            print(line)
    else:
        print("\n🎉 All benchmarks passed!")

    print()


if __name__ == "__main__":
    run_benchmark()
