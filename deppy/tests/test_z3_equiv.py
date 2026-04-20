"""
Deppy Z3 equivalence / inequivalence test suite.

~120 test cases verifying that the Z3 symbolic engine correctly proves
equivalences and finds counterexamples for pure arithmetic and
branching functions.

All functions are defined at module scope so inspect.getsource works.
"""
from __future__ import annotations

import pytest
from deppy.equivalence import check_equiv, EquivResult

# ═══════════════════════════════════════════════════════════════════
#  EQUIVALENCE PAIRS — Z3 must prove these equal
# ═══════════════════════════════════════════════════════════════════

# --- Arithmetic identities ---
def e_double_mult(x: int) -> int: return x * 2
def e_double_add(x: int) -> int: return x + x

def e_triple_mult(x: int) -> int: return x * 3
def e_triple_add(x: int) -> int: return x + x + x

def e_quad_mult(x: int) -> int: return x * 4
def e_quad_shift(x: int) -> int: return (x + x) + (x + x)

def e_zero_mul(x: int) -> int: return x * 0
def e_zero_const(x: int) -> int: return 0

def e_one_mul(x: int) -> int: return x * 1
def e_identity(x: int) -> int: return x

def e_neg_v1(x: int) -> int: return -x
def e_neg_v2(x: int) -> int: return 0 - x

def e_neg_v3(x: int) -> int: return -x
def e_neg_v4(x: int) -> int: return x * -1

def e_sub_self(x: int) -> int: return x - x
def e_zero(x: int) -> int: return 0

def e_add_zero(x: int) -> int: return x + 0
def e_id2(x: int) -> int: return x

def e_sq_v1(x: int) -> int: return x * x
def e_sq_v2(x: int) -> int: return x ** 2

def e_cube_v1(x: int) -> int: return x * x * x
def e_cube_v2(x: int) -> int: return x ** 3

def e_distrib_v1(x: int) -> int:
    return 2 * (x + 3)
def e_distrib_v2(x: int) -> int:
    return 2 * x + 6

def e_distrib2_v1(x: int) -> int:
    return (x + 1) * (x + 1)
def e_distrib2_v2(x: int) -> int:
    return x * x + 2 * x + 1

def e_foil_v1(x: int) -> int:
    return (x + 2) * (x - 2)
def e_foil_v2(x: int) -> int:
    return x * x - 4

# --- Commutativity / associativity (multi-param) ---
def e_add_comm_v1(a: int, b: int) -> int: return a + b
def e_add_comm_v2(a: int, b: int) -> int: return b + a

def e_mul_comm_v1(a: int, b: int) -> int: return a * b
def e_mul_comm_v2(a: int, b: int) -> int: return b * a

def e_add_assoc_v1(a: int, b: int, c: int) -> int: return (a + b) + c
def e_add_assoc_v2(a: int, b: int, c: int) -> int: return a + (b + c)

def e_mul_assoc_v1(a: int, b: int, c: int) -> int: return (a * b) * c
def e_mul_assoc_v2(a: int, b: int, c: int) -> int: return a * (b * c)

def e_distrib3_v1(a: int, b: int, c: int) -> int: return a * (b + c)
def e_distrib3_v2(a: int, b: int, c: int) -> int: return a * b + a * c

def e_sum3_v1(a: int, b: int, c: int) -> int: return a + b + c
def e_sum3_v2(a: int, b: int, c: int) -> int: return c + b + a

# --- Assignment-based ---
def e_aug_add(a: int, b: int) -> int:
    r = a
    r += b
    return r
def e_plain_add(a: int, b: int) -> int:
    return a + b

def e_aug_mul(x: int) -> int:
    r = x
    r *= 3
    return r
def e_plain_mul3(x: int) -> int:
    return x * 3

def e_temp_var(x: int) -> int:
    t = x * 2
    return t + 1
def e_inline(x: int) -> int:
    return x * 2 + 1

def e_multi_assign(x: int) -> int:
    a = x + 1
    b = a * 2
    return b - 2
def e_multi_inline(x: int) -> int:
    return (x + 1) * 2 - 2

# --- Branching equivalences ---
def e_abs_ifret(x: int) -> int:
    if x >= 0:
        return x
    return -x
def e_abs_ternary(x: int) -> int:
    return x if x >= 0 else -x

def e_abs_neg(x: int) -> int:
    if x < 0:
        return -x
    return x
def e_abs_ternary2(x: int) -> int:
    return -x if x < 0 else x

def e_abs_call(x: int) -> int:
    return abs(x)
def e_abs_manual(x: int) -> int:
    if x >= 0:
        return x
    return -x

def e_max_if(x: int, y: int) -> int:
    if x >= y:
        return x
    return y
def e_max_call(x: int, y: int) -> int:
    return max(x, y)

def e_min_if(x: int, y: int) -> int:
    if x <= y:
        return x
    return y
def e_min_call(x: int, y: int) -> int:
    return min(x, y)

def e_clamp_if(x: int) -> int:
    if x < 0:
        return 0
    if x > 100:
        return 100
    return x
def e_clamp_maxmin(x: int) -> int:
    return max(0, min(x, 100))

def e_sign_v1(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0
def e_sign_v2(x: int) -> int:
    if x > 0:
        return 1
    if x == 0:
        return 0
    return -1

def e_sign_v3(x: int) -> int:
    if x == 0:
        return 0
    if x > 0:
        return 1
    return -1
def e_sign_v4(x: int) -> int:
    if x < 0:
        return -1
    if x > 0:
        return 1
    return 0

def e_relu_v1(x: int) -> int:
    if x > 0:
        return x
    return 0
def e_relu_v2(x: int) -> int:
    return max(x, 0)

def e_clamp_upper(x: int) -> int:
    if x > 255:
        return 255
    return x
def e_clamp_upper2(x: int) -> int:
    return min(x, 255)

def e_median_v1(a: int, b: int, c: int) -> int:
    return max(min(a, b), min(max(a, b), c))
def e_median_v2(a: int, b: int, c: int) -> int:
    return min(max(a, b), max(min(a, b), c))


EQUIV_PAIRS = [
    ("double: x*2 vs x+x", e_double_mult, e_double_add),
    ("triple: x*3 vs x+x+x", e_triple_mult, e_triple_add),
    ("quad: x*4 vs (x+x)+(x+x)", e_quad_mult, e_quad_shift),
    ("zero_mul: x*0 vs 0", e_zero_mul, e_zero_const),
    ("one_mul: x*1 vs x", e_one_mul, e_identity),
    ("neg: -x vs 0-x", e_neg_v1, e_neg_v2),
    ("neg: -x vs x*-1", e_neg_v3, e_neg_v4),
    ("sub_self: x-x vs 0", e_sub_self, e_zero),
    ("add_zero: x+0 vs x", e_add_zero, e_id2),
    ("square: x*x vs x**2", e_sq_v1, e_sq_v2),
    ("cube: x*x*x vs x**3", e_cube_v1, e_cube_v2),
    ("distrib: 2*(x+3) vs 2*x+6", e_distrib_v1, e_distrib_v2),
    ("distrib: (x+1)² vs x²+2x+1", e_distrib2_v1, e_distrib2_v2),
    ("foil: (x+2)(x-2) vs x²-4", e_foil_v1, e_foil_v2),
    ("add_comm: a+b vs b+a", e_add_comm_v1, e_add_comm_v2),
    ("mul_comm: a*b vs b*a", e_mul_comm_v1, e_mul_comm_v2),
    ("add_assoc: (a+b)+c vs a+(b+c)", e_add_assoc_v1, e_add_assoc_v2),
    ("mul_assoc: (a*b)*c vs a*(b*c)", e_mul_assoc_v1, e_mul_assoc_v2),
    ("distrib3: a*(b+c) vs a*b+a*c", e_distrib3_v1, e_distrib3_v2),
    ("sum3_comm: a+b+c vs c+b+a", e_sum3_v1, e_sum3_v2),
    ("augassign add: r=a;r+=b vs a+b", e_aug_add, e_plain_add),
    ("augassign mul: r=x;r*=3 vs x*3", e_aug_mul, e_plain_mul3),
    ("temp_var: t=x*2; t+1 vs x*2+1", e_temp_var, e_inline),
    ("multi_assign chain", e_multi_assign, e_multi_inline),
    ("abs: if/return vs ternary", e_abs_ifret, e_abs_ternary),
    ("abs: negative-first vs nonneg-first", e_abs_neg, e_abs_ternary2),
    ("abs: call vs manual", e_abs_call, e_abs_manual),
    ("max: if vs call", e_max_if, e_max_call),
    ("min: if vs call", e_min_if, e_min_call),
    ("clamp: if-chain vs max(0,min(x,100))", e_clamp_if, e_clamp_maxmin),
    ("sign: pos/neg/zero guard orderings", e_sign_v1, e_sign_v2),
    ("sign: zero-first vs neg-first", e_sign_v3, e_sign_v4),
    ("relu: if vs max(x,0)", e_relu_v1, e_relu_v2),
    ("clamp_upper: if vs min(x,255)", e_clamp_upper, e_clamp_upper2),
    ("median: two implementations", e_median_v1, e_median_v2),
]

# ── Additional equivalence pairs ──

def e_diff_sq_v1(x: int, y: int) -> int:
    return (x - y) * (x + y)
def e_diff_sq_v2(x: int, y: int) -> int:
    return x * x - y * y

def e_abs_sq(x: int) -> int:
    return abs(x) * abs(x)
def e_sq_plain(x: int) -> int:
    return x * x

def e_max3_v1(a: int, b: int, c: int) -> int:
    return max(a, max(b, c))
def e_max3_v2(a: int, b: int, c: int) -> int:
    return max(max(a, b), c)

def e_min3_v1(a: int, b: int, c: int) -> int:
    return min(a, min(b, c))
def e_min3_v2(a: int, b: int, c: int) -> int:
    return min(min(a, b), c)

def e_abs_max(x: int) -> int:
    return max(x, -x)
def e_abs_explicit(x: int) -> int:
    return abs(x)

def e_noop_sub_add(x: int, y: int) -> int:
    r = x - y
    r += y
    return r
def e_noop_id(x: int, y: int) -> int:
    return x

def e_pow4_v1(x: int) -> int:
    return x ** 4
def e_pow4_v2(x: int) -> int:
    a = x * x
    return a * a

def e_double_neg(x: int) -> int:
    return -(-x)
def e_plain_id(x: int) -> int:
    return x

def e_bounded_v1(x: int) -> int:
    r = x
    if r < 0:
        r = 0
    if r > 50:
        r = 50
    return r
def e_bounded_v2(x: int) -> int:
    return max(0, min(x, 50))

def e_relu_aug(x: int) -> int:
    r = x
    if r < 0:
        r = 0
    return r
def e_relu_max2(x: int) -> int:
    return max(0, x)

def e_safe_pred_v1(x: int) -> int:
    if x > 0:
        return x - 1
    return 0
def e_safe_pred_v2(x: int) -> int:
    return max(x - 1, 0)


EQUIV_PAIRS_EXTRA = [
    ("diff_of_squares: (x-y)(x+y) vs x²-y²", e_diff_sq_v1, e_diff_sq_v2),
    ("|x|² vs x²", e_abs_sq, e_sq_plain),
    ("max3: nested left vs right", e_max3_v1, e_max3_v2),
    ("min3: nested left vs right", e_min3_v1, e_min3_v2),
    ("abs via max(x,-x) vs abs(x)", e_abs_max, e_abs_explicit),
    ("noop: x-y+y vs x", e_noop_sub_add, e_noop_id),
    ("x⁴: x**4 vs (x*x)*(x*x)", e_pow4_v1, e_pow4_v2),
    ("double negation: -(-x) vs x", e_double_neg, e_plain_id),
    ("bounded: if-chain vs max/min", e_bounded_v1, e_bounded_v2),
    ("relu: augassign vs max", e_relu_aug, e_relu_max2),
    ("safe_pred: if vs max(x-1,0)", e_safe_pred_v1, e_safe_pred_v2),
]


@pytest.mark.parametrize("name,f,g", EQUIV_PAIRS_EXTRA,
                         ids=[t[0] for t in EQUIV_PAIRS_EXTRA])
def test_z3_equivalence_extra(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is True, f"{name}: expected EQUIVALENT, got {r}"
    assert r.method == 'z3', f"{name}: expected method='z3', got '{r.method}'"


@pytest.mark.parametrize("name,f,g", EQUIV_PAIRS, ids=[t[0] for t in EQUIV_PAIRS])
def test_z3_equivalence(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is True, f"{name}: expected EQUIVALENT, got {r}"
    assert r.method == 'z3', f"{name}: expected method='z3', got '{r.method}'"


# ═══════════════════════════════════════════════════════════════════
#  INEQUIVALENCE PAIRS — Z3 must find counterexample
# ═══════════════════════════════════════════════════════════════════

def n_times2(x: int) -> int: return x * 2
def n_times3(x: int) -> int: return x * 3

def n_id(x: int) -> int: return x
def n_succ(x: int) -> int: return x + 1

def n_add1(x: int) -> int: return x + 1
def n_sub1(x: int) -> int: return x - 1

def n_neg(x: int) -> int: return -x
def n_id2(x: int) -> int: return x

def n_sq(x: int) -> int: return x * x
def n_dbl(x: int) -> int: return x * 2

def n_sq2(x: int) -> int: return x ** 2
def n_cube(x: int) -> int: return x ** 3

def n_abs(x: int) -> int:
    if x >= 0:
        return x
    return -x
def n_neg_abs(x: int) -> int:
    if x >= 0:
        return -x
    return x

def n_clamp100(x: int) -> int:
    return max(0, min(x, 100))
def n_clamp200(x: int) -> int:
    return max(0, min(x, 200))

def n_relu(x: int) -> int:
    return max(x, 0)
def n_leaky_relu(x: int) -> int:
    if x >= 0:
        return x
    return 0  # vs the "leaky" would be x//10, but let's use a shifted threshold

def n_sign_strict(x: int) -> int:
    if x > 0:
        return 1
    return -1
def n_sign_full(x: int) -> int:
    if x > 0:
        return 1
    if x == 0:
        return 0
    return -1

def n_add(a: int, b: int) -> int: return a + b
def n_sub(a: int, b: int) -> int: return a - b

def n_aminus_b(a: int, b: int) -> int: return a - b
def n_bminus_a(a: int, b: int) -> int: return b - a

def n_mul(a: int, b: int) -> int: return a * b
def n_add2(a: int, b: int) -> int: return a + b

def n_max(x: int, y: int) -> int: return max(x, y)
def n_min(x: int, y: int) -> int: return min(x, y)

def n_abs_plus1(x: int) -> int:
    return abs(x) + 1
def n_abs_plain(x: int) -> int:
    return abs(x)

def n_triple_add1(x: int) -> int: return x * 3 + 1
def n_triple(x: int) -> int: return x * 3

def n_double_plus(x: int) -> int: return x * 2 + x
def n_double_only(x: int) -> int: return x * 2

def n_sq_plus1(x: int) -> int: return x * x + 1
def n_sq_plain(x: int) -> int: return x * x

def n_off1(x: int) -> int: return x + 1
def n_off2(x: int) -> int: return x + 2

def n_threshold10(x: int) -> int:
    if x > 10:
        return 1
    return 0
def n_threshold20(x: int) -> int:
    if x > 20:
        return 1
    return 0

def n_clamp_low(x: int) -> int:
    return max(0, x)
def n_clamp_both(x: int) -> int:
    return max(0, min(x, 100))

def n_avg_v1(a: int, b: int) -> int:
    return (a + b) // 2
def n_avg_v2(a: int, b: int) -> int:
    return a // 2 + b // 2

def n_swap_guard(x: int) -> int:
    if x >= 0:
        return x + 1
    return -x
def n_no_swap(x: int) -> int:
    if x >= 0:
        return x
    return -x

def n_mod3(x: int) -> int: return x % 3
def n_mod5(x: int) -> int: return x % 5

def n_flipped_branch(x: int) -> int:
    if x > 0:
        return 1
    return 0
def n_flipped_branch2(x: int) -> int:
    if x > 0:
        return 0
    return 1


INEQUIV_PAIRS = [
    ("x*2 vs x*3", n_times2, n_times3),
    ("x vs x+1", n_id, n_succ),
    ("x+1 vs x-1", n_add1, n_sub1),
    ("-x vs x", n_neg, n_id2),
    ("x² vs x*2", n_sq, n_dbl),
    ("x² vs x³", n_sq2, n_cube),
    ("abs vs neg-abs", n_abs, n_neg_abs),
    ("clamp 100 vs clamp 200", n_clamp100, n_clamp200),
    ("sign_strict vs sign_full (missing zero)", n_sign_strict, n_sign_full),
    ("a+b vs a-b", n_add, n_sub),
    ("a-b vs b-a", n_aminus_b, n_bminus_a),
    ("a*b vs a+b", n_mul, n_add2),
    ("max vs min", n_max, n_min),
    ("abs+1 vs abs", n_abs_plus1, n_abs_plain),
    ("3x+1 vs 3x", n_triple_add1, n_triple),
    ("2x+x vs 2x", n_double_plus, n_double_only),
    ("x²+1 vs x²", n_sq_plus1, n_sq_plain),
    ("x+1 vs x+2", n_off1, n_off2),
    ("threshold>10 vs threshold>20", n_threshold10, n_threshold20),
    ("clamp_low vs clamp_both", n_clamp_low, n_clamp_both),
    ("avg floor vs split floor", n_avg_v1, n_avg_v2),
    ("abs+1 on positive vs abs", n_swap_guard, n_no_swap),
    ("x%3 vs x%5", n_mod3, n_mod5),
    ("flipped branch outputs", n_flipped_branch, n_flipped_branch2),
]

# ── Additional inequivalence pairs ──

def n_sq_vs_cube2(x: int) -> int: return x ** 2
def n_cube2(x: int) -> int: return x ** 3

def n_clamp_5(x: int) -> int: return max(0, min(x, 5))
def n_clamp_10(x: int) -> int: return max(0, min(x, 10))

def n_neg_shift(x: int) -> int: return -(x + 1)
def n_neg_plain(x: int) -> int: return -x

def n_abs_shift(x: int) -> int: return abs(x) + x
def n_abs_only(x: int) -> int: return abs(x)

def n_max_ab(a: int, b: int) -> int: return max(a, b)
def n_max_double(a: int, b: int) -> int: return max(a * 2, b)

def n_relu_1(x: int) -> int: return max(x, 1)
def n_relu_0(x: int) -> int: return max(x, 0)

def n_sign_pos(x: int) -> int:
    if x >= 0:
        return 1
    return -1
def n_sign_nonneg(x: int) -> int:
    if x > 0:
        return 1
    return -1

def n_sq_neg(x: int) -> int: return -(x * x)
def n_sq_pos(x: int) -> int: return x * x

def n_half_floor(x: int) -> int: return x // 2
def n_half_ceil(x: int) -> int: return (x + 1) // 2


INEQUIV_PAIRS_EXTRA = [
    ("x² vs x³ (pow)", n_sq_vs_cube2, n_cube2),
    ("clamp 5 vs clamp 10", n_clamp_5, n_clamp_10),
    ("-(x+1) vs -x", n_neg_shift, n_neg_plain),
    ("|x|+x vs |x|", n_abs_shift, n_abs_only),
    ("max(a,b) vs max(2a,b)", n_max_ab, n_max_double),
    ("relu offset 1 vs 0", n_relu_1, n_relu_0),
    ("sign >= vs >", n_sign_pos, n_sign_nonneg),
    ("-x² vs x²", n_sq_neg, n_sq_pos),
    ("floor half vs ceil half", n_half_floor, n_half_ceil),
]


@pytest.mark.parametrize("name,f,g", INEQUIV_PAIRS_EXTRA,
                         ids=[t[0] for t in INEQUIV_PAIRS_EXTRA])
def test_z3_inequivalence_extra(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is False, f"{name}: expected INEQUIVALENT, got {r}"
    assert r.method == 'z3', f"{name}: expected method='z3', got '{r.method}'"
    assert r.counterexample is not None


@pytest.mark.parametrize("name,f,g", INEQUIV_PAIRS, ids=[t[0] for t in INEQUIV_PAIRS])
def test_z3_inequivalence(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is False, f"{name}: expected INEQUIVALENT, got {r}"
    assert r.method == 'z3', f"{name}: expected method='z3', got '{r.method}'"
    assert r.counterexample is not None, f"{name}: expected counterexample"
    # Verify the counterexample actually witnesses a difference
    ce = r.counterexample
    import inspect
    params_f = list(inspect.signature(f).parameters.keys())
    params_g = list(inspect.signature(g).parameters.keys())
    args_f = {p: ce[p] for p in params_f if p in ce}
    args_g = {pg: ce[pf] for pf, pg in zip(params_f, params_g) if pf in ce}
    try:
        val_f = f(**args_f)
        val_g = g(**args_g)
        assert val_f != val_g, f"{name}: counterexample {ce} doesn't witness a difference: f={val_f}, g={val_g}"
    except (ZeroDivisionError, OverflowError):
        pass  # partial function — Z3 counterexample may be at a division boundary
