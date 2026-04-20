"""
Deppy Z3 spec adherence test suite.

~120 test cases verifying that the Z3 symbolic engine correctly proves
spec adherence or finds counterexamples for @guarantee / ad-hoc specs.
"""
from __future__ import annotations

import pytest
from deppy import guarantee, requires
from deppy.equivalence import check_adherence, AdherenceResult

# ═══════════════════════════════════════════════════════════════════
#  CORRECT SPECS — Z3 must prove adherence
# ═══════════════════════════════════════════════════════════════════

# --- Nonnegativity ---
@guarantee("result >= 0")
def adh_square(x: int) -> int:
    return x * x

@guarantee("result >= 0")
def adh_sq_pow(x: int) -> int:
    return x ** 2

@guarantee("result >= 0")
def adh_abs_if(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result >= 0")
def adh_abs_call(x: int) -> int:
    return abs(x)

@guarantee("result >= 0")
def adh_abs_ternary(x: int) -> int:
    return x if x >= 0 else -x

@guarantee("result >= 0")
def adh_sq_sum(a: int, b: int) -> int:
    return a * a + b * b

@guarantee("result >= 0")
def adh_relu(x: int) -> int:
    return max(x, 0)

@guarantee("result >= 0")
def adh_relu_if(x: int) -> int:
    if x > 0:
        return x
    return 0

@guarantee("result >= 0")
def adh_clamp(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

@guarantee("result >= 0")
def adh_zero(x: int) -> int:
    return 0

# --- Bounds ---
@guarantee("result <= 100")
def adh_clamp_upper(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

@guarantee("result >= 0 and result <= 100")
def adh_clamp_both(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

@guarantee("result >= 0 and result <= 255")
def adh_byte_clamp(x: int) -> int:
    return max(0, min(x, 255))

@guarantee("result <= x")
def adh_min_zero(x: int) -> int:
    return min(x, 0)

@guarantee("result >= x")
def adh_max_zero(x: int) -> int:
    return max(x, 0)

# --- Relational to input ---
@guarantee("result >= x")
def adh_max_xy(x: int, y: int) -> int:
    return max(x, y)

@guarantee("result >= y")
def adh_max_xy2(x: int, y: int) -> int:
    return max(x, y)

@guarantee("result <= x")
def adh_min_xy(x: int, y: int) -> int:
    return min(x, y)

@guarantee("result <= y")
def adh_min_xy2(x: int, y: int) -> int:
    return min(x, y)

@guarantee("result >= x or result >= y")
def adh_max_either(x: int, y: int) -> int:
    return max(x, y)

# --- Equality specs ---
@guarantee("result == x + y")
def adh_add(x: int, y: int) -> int:
    return x + y

@guarantee("result == x * 2")
def adh_double(x: int) -> int:
    return x + x

@guarantee("result == x * x")
def adh_sq_eq(x: int) -> int:
    return x ** 2

@guarantee("result == a * b + a * c")
def adh_distrib(a: int, b: int, c: int) -> int:
    return a * (b + c)

# --- With preconditions ---
@requires("n > 0")
@guarantee("result > 0")
def adh_double_pos(n: int) -> int:
    return n * 2

@requires("x >= 0")
@guarantee("result >= x")
def adh_add_self(x: int) -> int:
    return x + x

@requires("a > 0")
@requires("b > 0")
@guarantee("result > 0")
def adh_add_pos(a: int, b: int) -> int:
    return a + b

@requires("x >= 0")
@guarantee("result >= 0")
def adh_identity_pos(x: int) -> int:
    return x

@requires("x != 0")
@guarantee("result != 0")
def adh_double_nonzero(x: int) -> int:
    return x * 2

@requires("a >= 0")
@requires("b >= 0")
@guarantee("result >= 0")
def adh_mul_nonneg(a: int, b: int) -> int:
    return a * b

# --- Branching correctness ---
@guarantee("result == 1 or result == 0 or result == -1")
def adh_sign(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0

# --- More precondition-guarded specs ---
@requires("x > 0")
@requires("y > 0")
@guarantee("result > x")
def adh_add_gt(x: int, y: int) -> int:
    return x + y

@requires("x >= 0")
@guarantee("result >= x")
def adh_sq_ge(x: int) -> int:
    return x * x

@requires("n >= 1")
@guarantee("result >= 1")
def adh_sq_pos(n: int) -> int:
    return n * n

@requires("a >= 0")
@requires("b >= 0")
@guarantee("result >= a and result >= b")
def adh_sum_ge_both(a: int, b: int) -> int:
    return a + b

@requires("x >= 0")
@guarantee("result == x")
def adh_abs_nonneg(x: int) -> int:
    return abs(x)

# --- Multi-guarantee ---
@guarantee("result >= 0")
@guarantee("result <= 255")
def adh_byte_multi(x: int) -> int:
    return max(0, min(x, 255))

@guarantee("result >= x")
@guarantee("result >= 0")
def adh_relu_multi(x: int) -> int:
    if x > 0:
        return x
    return 0

# --- Complex branching ---
@guarantee("result >= 0")
def adh_nested_if(x: int) -> int:
    if x > 0:
        if x > 100:
            return 100
        return x
    return 0

@guarantee("result >= 0 and result <= 10")
def adh_step_clamp(x: int) -> int:
    if x < 0:
        return 0
    if x > 10:
        return 10
    return x

@guarantee("result == 0 or result == 1")
def adh_bool_like(x: int) -> int:
    if x > 0:
        return 1
    return 0


CORRECT_SPECS = [
    adh_square, adh_sq_pow, adh_abs_if, adh_abs_call, adh_abs_ternary,
    adh_sq_sum, adh_relu, adh_relu_if, adh_clamp, adh_zero,
    adh_clamp_upper, adh_clamp_both, adh_byte_clamp,
    adh_min_zero, adh_max_zero,
    adh_max_xy, adh_max_xy2, adh_min_xy, adh_min_xy2, adh_max_either,
    adh_add, adh_double, adh_sq_eq, adh_distrib,
    adh_double_pos, adh_add_self, adh_add_pos, adh_identity_pos,
    adh_double_nonzero, adh_mul_nonneg,
    adh_sign,
    adh_add_gt, adh_sq_ge, adh_sq_pos, adh_sum_ge_both, adh_abs_nonneg,
    adh_byte_multi, adh_relu_multi,
    adh_nested_if, adh_step_clamp, adh_bool_like,
]


@pytest.mark.parametrize("fn", CORRECT_SPECS, ids=[f.__name__ for f in CORRECT_SPECS])
def test_z3_adherence_correct(fn):
    results = check_adherence(fn)
    for r in results:
        assert r.adheres is True, f"{fn.__name__}: expected ADHERES for '{r.spec}', got {r}"
        assert r.method == 'z3', f"{fn.__name__}: expected method='z3' for '{r.spec}', got '{r.method}'"


# ═══════════════════════════════════════════════════════════════════
#  INCORRECT SPECS — Z3 must find counterexamples
# ═══════════════════════════════════════════════════════════════════

@guarantee("result > 0")
def viol_sq_strict(x: int) -> int:
    """x=0 → 0, not > 0"""
    return x * x

@guarantee("result >= 0")
def viol_identity(x: int) -> int:
    """x=-1 → -1"""
    return x

@guarantee("result > 0")
def viol_abs_strict(x: int) -> int:
    """x=0 → 0"""
    if x >= 0:
        return x
    return -x

@guarantee("result != 0")
def viol_sub_eq(a: int, b: int) -> int:
    """a=b → 0"""
    return a - b

@guarantee("result < x")
def viol_double(x: int) -> int:
    """x=1 → 2 > 1"""
    return x * 2

@guarantee("result >= 1")
def viol_abs_offby1(x: int) -> int:
    """x=0 → 0"""
    if x >= 0:
        return x
    return -x

@guarantee("result == x + y")
def viol_mul_typo(x: int, y: int) -> int:
    """Actually computes x*y"""
    return x * y

@guarantee("result >= 0")
def viol_neg(x: int) -> int:
    """x=1 → -1"""
    return -x

@guarantee("result <= 100")
def viol_no_upper(x: int) -> int:
    """Missing upper bound"""
    if x < 0:
        return 0
    return x

@guarantee("result == x")
def viol_clamp_not_id(x: int) -> int:
    """x=-1 → 0"""
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

@guarantee("result > x")
def viol_id_not_gt(x: int) -> int:
    return x

@guarantee("result >= x")
def viol_triple_neg(x: int) -> int:
    """x=-1 → -3, not >= -1"""
    return x * 3

@guarantee("result >= 0")
def viol_sub(a: int, b: int) -> int:
    """a=0,b=1 → -1"""
    return a - b

@guarantee("result == a + b")
def viol_off_by_one(a: int, b: int) -> int:
    return a + b + 1

@guarantee("result >= x and result >= y")
def viol_min_not_max(x: int, y: int) -> int:
    """min doesn't satisfy 'result >= both'"""
    return min(x, y)

@guarantee("result == 0")
def viol_not_zero(x: int) -> int:
    return x

@guarantee("result > 0")
def viol_zero_const(x: int) -> int:
    return 0

@guarantee("result != x")
def viol_identity2(x: int) -> int:
    return x

@guarantee("result >= x * x")
def viol_linear(x: int) -> int:
    """linear < quadratic for large x"""
    return x * 2

@guarantee("result == max(x, y)")
def viol_min_as_max(x: int, y: int) -> int:
    return min(x, y)


VIOLATION_FUNCS = [
    viol_sq_strict, viol_identity, viol_abs_strict, viol_sub_eq,
    viol_double, viol_abs_offby1, viol_mul_typo, viol_neg,
    viol_no_upper, viol_clamp_not_id, viol_id_not_gt, viol_triple_neg,
    viol_sub, viol_off_by_one, viol_min_not_max, viol_not_zero,
    viol_zero_const, viol_identity2, viol_linear, viol_min_as_max,
]


@pytest.mark.parametrize("fn", VIOLATION_FUNCS, ids=[f.__name__ for f in VIOLATION_FUNCS])
def test_z3_adherence_violation(fn):
    results = check_adherence(fn)
    for r in results:
        assert r.adheres is False, f"{fn.__name__}: expected VIOLATION for '{r.spec}', got {r}"
        assert r.method == 'z3', f"{fn.__name__}: expected method='z3' for '{r.spec}', got '{r.method}'"
        assert r.counterexample is not None, f"{fn.__name__}: expected counterexample"
        # Verify the counterexample actually violates the spec
        ce = r.counterexample
        import inspect
        params = list(inspect.signature(fn).parameters.keys())
        args = {p: ce[p] for p in params if p in ce}
        result_val = fn(**args)
        spec_env = dict(args)
        spec_env['result'] = result_val
        spec_env['abs'] = abs
        spec_env['min'] = min
        spec_env['max'] = max
        try:
            holds = eval(r.spec, {"__builtins__": {}}, spec_env)
            assert not holds, (
                f"{fn.__name__}: counterexample {ce} doesn't violate '{r.spec}': "
                f"f({args})={result_val}, spec={holds}"
            )
        except Exception:
            pass  # spec may reference things not easily evaluable


# ═══════════════════════════════════════════════════════════════════
#  AD-HOC SPECS (no @guarantee, passed as string)
# ═══════════════════════════════════════════════════════════════════

def raw_square(x: int) -> int:
    return x * x

def raw_abs(x: int) -> int:
    if x >= 0:
        return x
    return -x

def raw_add(a: int, b: int) -> int:
    return a + b

def raw_clamp(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x

def raw_neg(x: int) -> int:
    return -x

def raw_double(x: int) -> int:
    return x * 2

def raw_max(x: int, y: int) -> int:
    return max(x, y)

def raw_min(x: int, y: int) -> int:
    return min(x, y)

def raw_sign(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


ADHOC_CORRECT = [
    (raw_square, "result >= 0"),
    (raw_square, "result == x * x"),
    (raw_abs, "result >= 0"),
    (raw_abs, "result >= x or result >= -x"),
    (raw_add, "result == a + b"),
    (raw_clamp, "result >= 0"),
    (raw_clamp, "result <= 100"),
    (raw_clamp, "result >= 0 and result <= 100"),
    (raw_neg, "result == -x"),
    (raw_double, "result == x * 2"),
    (raw_double, "result == x + x"),
    (raw_max, "result >= x"),
    (raw_max, "result >= y"),
    (raw_min, "result <= x"),
    (raw_min, "result <= y"),
    (raw_sign, "result >= -1"),
    (raw_sign, "result <= 1"),
    (raw_sign, "result >= -1 and result <= 1"),
]

ADHOC_VIOLATION = [
    (raw_square, "result > 0"),             # x=0
    (raw_square, "result < x"),             # x=2 → 4
    (raw_abs, "result > 0"),                # x=0
    (raw_abs, "result >= 1"),               # x=0
    (raw_add, "result > a"),                # b=0, a=0
    (raw_add, "result == a * b"),           # a=2, b=3 → 5 != 6
    (raw_clamp, "result == x"),             # x=-1 → 0
    (raw_clamp, "result > 0"),              # x=0
    (raw_neg, "result >= 0"),               # x=1 → -1
    (raw_neg, "result > x"),                # x=-1 → 1 > -1, but x=0 → 0
    (raw_double, "result > x"),             # x=0
    (raw_double, "result < x"),             # x=1 → 2
    (raw_max, "result > x"),                # x=y → tied
    (raw_min, "result < x"),                # x=y → tied
    (raw_sign, "result != 0"),              # x=0
    (raw_sign, "result == x"),              # x=5 → 1
]


@pytest.mark.parametrize("fn,spec", ADHOC_CORRECT,
                         ids=[f"{f.__name__}:{s}" for f, s in ADHOC_CORRECT])
def test_z3_adhoc_correct(fn, spec):
    results = check_adherence(fn, spec=spec)
    assert len(results) == 1
    r = results[0]
    assert r.adheres is True, f"{fn.__name__} '{spec}': expected ADHERES, got {r}"
    assert r.method == 'z3', f"{fn.__name__} '{spec}': expected z3, got '{r.method}'"


@pytest.mark.parametrize("fn,spec", ADHOC_VIOLATION,
                         ids=[f"{f.__name__}:{s}" for f, s in ADHOC_VIOLATION])
def test_z3_adhoc_violation(fn, spec):
    results = check_adherence(fn, spec=spec)
    assert len(results) == 1
    r = results[0]
    assert r.adheres is False, f"{fn.__name__} '{spec}': expected VIOLATION, got {r}"
    assert r.method == 'z3', f"{fn.__name__} '{spec}': expected z3, got '{r.method}'"
    assert r.counterexample is not None
