"""
Deppy testing-fallback equivalence/adherence suite.

~30 test cases that exercise the property-based testing path for
types Z3 can't handle, plus cases where Z3 now handles lists/strings.
Uses seeded randomness for deterministic results.
"""
from __future__ import annotations

import random
import pytest
from deppy.equivalence import check_equiv, check_adherence


@pytest.fixture(autouse=True)
def seed_random():
    """Seed randomness for deterministic testing fallback."""
    random.seed(42)
    yield
    random.seed()  # restore


# ═══════════════════════════════════════════════════════════════════
#  LIST EQUIVALENCES (testing path)
# ═══════════════════════════════════════════════════════════════════

def lst_sorted_default(xs: list) -> list:
    return sorted(xs)

def lst_sorted_explicit(xs: list) -> list:
    return sorted(xs, reverse=False)

def lst_rev_rev(xs: list) -> list:
    return list(reversed(list(reversed(xs))))

def lst_identity(xs: list) -> list:
    return list(xs)

def lst_sum_builtin(xs: list) -> int:
    return sum(xs)

def lst_sum_loop(xs: list) -> int:
    total = 0
    for x in xs:
        total += x
    return total

def lst_len_builtin(xs: list) -> int:
    return len(xs)

def lst_len_loop(xs: list) -> int:
    c = 0
    for _ in xs:
        c += 1
    return c

def lst_max_builtin(xs: list) -> int:
    return max(xs) if xs else 0

def lst_max_loop(xs: list) -> int:
    if not xs:
        return 0
    m = xs[0]
    for x in xs[1:]:
        if x > m:
            m = x
    return m

def lst_min_builtin(xs: list) -> int:
    return min(xs) if xs else 0

def lst_min_loop(xs: list) -> int:
    if not xs:
        return 0
    m = xs[0]
    for x in xs[1:]:
        if x < m:
            m = x
    return m


TESTING_EQUIV_PAIRS = [
    ("sorted default vs explicit", lst_sorted_default, lst_sorted_explicit),
    ("reverse twice vs identity", lst_rev_rev, lst_identity),
    ("sum builtin vs loop", lst_sum_builtin, lst_sum_loop),
    ("len builtin vs loop", lst_len_builtin, lst_len_loop),
    ("max builtin vs loop", lst_max_builtin, lst_max_loop),
    ("min builtin vs loop", lst_min_builtin, lst_min_loop),
]


@pytest.mark.parametrize("name,f,g", TESTING_EQUIV_PAIRS,
                         ids=[t[0] for t in TESTING_EQUIV_PAIRS])
def test_testing_equiv(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is True, f"{name}: expected EQUIVALENT, got {r}"
    # Z3 now handles list types via Array theory — accept either method
    assert r.method in ('testing', 'z3'), f"{name}: got unexpected method '{r.method}'"


# ═══════════════════════════════════════════════════════════════════
#  LIST INEQUIVALENCES (testing path)
# ═══════════════════════════════════════════════════════════════════

def lst_head_zero(xs: list) -> int:
    return xs[0] if xs else 0

def lst_head_one(xs: list) -> int:
    return xs[0] if xs else 1

def lst_sorted_asc(xs: list) -> list:
    return sorted(xs)

def lst_sorted_desc(xs: list) -> list:
    return sorted(xs, reverse=True)

def lst_append_0(xs: list) -> list:
    return xs + [0]

def lst_append_1(xs: list) -> list:
    return xs + [1]

def lst_count_pos(xs: list) -> int:
    return sum(1 for x in xs if x > 0)

def lst_count_neg(xs: list) -> int:
    return sum(1 for x in xs if x < 0)


TESTING_INEQUIV_PAIRS = [
    ("head_or_0 vs head_or_1", lst_head_zero, lst_head_one),
    ("sorted asc vs desc", lst_sorted_asc, lst_sorted_desc),
    ("append 0 vs append 1", lst_append_0, lst_append_1),
    ("count pos vs count neg", lst_count_pos, lst_count_neg),
]


@pytest.mark.parametrize("name,f,g", TESTING_INEQUIV_PAIRS,
                         ids=[t[0] for t in TESTING_INEQUIV_PAIRS])
def test_testing_inequiv(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is False, f"{name}: expected INEQUIVALENT, got {r}"
    # Z3 now handles list types — accept either method
    assert r.method in ('testing', 'z3'), f"{name}: got unexpected method '{r.method}'"


# ═══════════════════════════════════════════════════════════════════
#  STRING OPERATIONS (testing path)
# ═══════════════════════════════════════════════════════════════════

def str_upper(s: str) -> str:
    return s.upper()

def str_upper2(s: str) -> str:
    return ''.join(c.upper() for c in s)

def str_len(s: str) -> int:
    return len(s)

def str_count(s: str) -> int:
    c = 0
    for _ in s:
        c += 1
    return c


STRING_EQUIV_PAIRS = [
    ("upper builtin vs join", str_upper, str_upper2),
    ("len vs manual count", str_len, str_count),
]


@pytest.mark.parametrize("name,f,g", STRING_EQUIV_PAIRS,
                         ids=[t[0] for t in STRING_EQUIV_PAIRS])
def test_testing_string_equiv(name, f, g):
    r = check_equiv(f, g)
    assert r.equivalent is True, f"{name}: expected EQUIVALENT, got {r}"


# ═══════════════════════════════════════════════════════════════════
#  METHOD SELECTION TESTS — verify Z3 vs testing is chosen correctly
# ═══════════════════════════════════════════════════════════════════

def method_arith_f(x: int) -> int: return x * 2
def method_arith_g(x: int) -> int: return x + x

def method_list_f(xs: list) -> int: return len(xs)
def method_list_g(xs: list) -> int: return len(list(xs))


def test_method_z3_for_arithmetic():
    r = check_equiv(method_arith_f, method_arith_g)
    assert r.method == 'z3'


def test_method_z3_for_lists():
    """Z3 now handles list types via Array theory."""
    r = check_equiv(method_list_f, method_list_g)
    assert r.method == 'z3'


def test_method_z3_disabled():
    r = check_equiv(method_arith_f, method_arith_g, use_z3=False)
    assert r.method == 'testing'


def test_method_both_disabled():
    r = check_equiv(method_arith_f, method_arith_g, use_z3=False, use_testing=False)
    assert r.method == 'inconclusive'
    assert r.equivalent is None


# ═══════════════════════════════════════════════════════════════════
#  UNSUPPORTED AST / GRACEFUL FALLBACK
# ═══════════════════════════════════════════════════════════════════

def unsup_for_loop(x: int) -> int:
    total = 0
    for i in range(x):
        total += i
    return total

def unsup_sum_range(x: int) -> int:
    return sum(range(x))


def test_unsupported_for_loop_falls_to_testing():
    """for-loop bodies can't be symbolically evaluated; should fall back."""
    r = check_equiv(unsup_for_loop, unsup_sum_range)
    assert r.method == 'testing'


def unsup_listcomp(x: int) -> list:
    return [i * 2 for i in range(x)]

def unsup_listcomp2(x: int) -> list:
    return list(range(0, x * 2, 2))


def test_unsupported_listcomp_falls_to_testing():
    r = check_equiv(unsup_listcomp, unsup_listcomp2)
    assert r.method == 'testing'


# ═══════════════════════════════════════════════════════════════════
#  Z3 COLLECTION TESTS — verify list/dict operations via Z3
# ═══════════════════════════════════════════════════════════════════

def z3_list_len_identity(xs: list) -> int:
    """len(list(xs)) == len(xs)"""
    return len(list(xs))

def z3_list_len_direct(xs: list) -> int:
    return len(xs)


def test_z3_list_len_equiv():
    """Z3 should prove len(list(xs)) == len(xs) via Array theory."""
    r = check_equiv(z3_list_len_identity, z3_list_len_direct)
    assert r.equivalent is True
    assert r.method == 'z3'


def z3_list_head_same_a(xs: list) -> int:
    return xs[0] if xs else 0

def z3_list_head_same_b(xs: list) -> int:
    if xs:
        return xs[0]
    else:
        return 0


def test_z3_list_head_equiv():
    """Z3 should prove xs[0] if xs else 0 ≡ if xs: return xs[0] else 0."""
    r = check_equiv(z3_list_head_same_a, z3_list_head_same_b)
    assert r.equivalent is True
    assert r.method == 'z3'


def z3_list_head_zero(xs: list) -> int:
    return xs[0] if xs else 0

def z3_list_head_one(xs: list) -> int:
    return xs[0] if xs else 1


def test_z3_list_head_inequiv():
    """Z3 should find counterexample for head_or_0 vs head_or_1."""
    r = check_equiv(z3_list_head_zero, z3_list_head_one)
    assert r.equivalent is False
    assert r.method == 'z3'


# ═══════════════════════════════════════════════════════════════════
#  EFFECT Z3 DISCHARGE TESTS
# ═══════════════════════════════════════════════════════════════════

from deppy.effects.effect_types import EffectZ3Discharger, Effect


def test_effect_exception_free_no_raise():
    """Function with no raise → exception-free by absence."""
    src = '''
def safe_add(x: int, y: int) -> int:
    return x + y
'''
    d = EffectZ3Discharger()
    result = d.discharge_exception_freedom(src)
    assert result.verified is True
    assert result.proof_term == "exception_free_by_absence"


def test_effect_exception_guarded_raise():
    """Raise under condition contradicted by precondition → exception-free."""
    src = '''
def safe_div(x: int, y: int) -> int:
    if y == 0:
        raise ValueError("division by zero")
    return x // y
'''
    d = EffectZ3Discharger()
    result = d.discharge_exception_freedom(src, preconditions=["y != 0"])
    assert result.verified is True
    assert result.proof_term == "exception_free_by_z3"


def test_effect_exception_unguarded():
    """Raise without guard → cannot prove exception-free."""
    src = '''
def always_raises(x: int) -> int:
    raise ValueError("always")
'''
    d = EffectZ3Discharger()
    result = d.discharge_exception_freedom(src)
    assert result.verified is False


def test_effect_generator_bounded():
    """Generator with for-loop over finite iterable → bounded."""
    src = '''
def gen(xs):
    for x in xs:
        yield x * 2
'''
    d = EffectZ3Discharger()
    result = d.discharge_generator_safety(src)
    assert result.verified is True


def test_effect_async_bounded():
    """Async function with finite awaits → bounded suspensions."""
    src = '''
async def fetch(url):
    result = await get(url)
    data = await parse(result)
    return data
'''
    d = EffectZ3Discharger()
    result = d.discharge_async_safety(src)
    assert result.verified is True
    assert "2 bounded" in result.message
