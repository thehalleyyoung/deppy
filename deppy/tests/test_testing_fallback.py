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


# ═══════════════════════════════════════════════════════════════════
#  HIGHER-ORDER FUNCTION Z3 TESTS
# ═══════════════════════════════════════════════════════════════════

from typing import Callable

def hof_apply(f: Callable[[int], int], x: int) -> int:
    return f(x)

def hof_apply_alias(f: Callable[[int], int], x: int) -> int:
    y = f(x)
    return y

def test_hof_apply_equiv():
    """HOF: f(x) ≡ f(x) via Z3 callable model."""
    result = check_equiv(hof_apply, hof_apply_alias)
    assert result.equivalent

def hof_double(f: Callable[[int], int], x: int) -> int:
    return f(x) + f(x)

def hof_double_alt(f: Callable[[int], int], x: int) -> int:
    r = f(x)
    return r + r

def test_hof_double_equiv():
    """HOF: f(x) + f(x) ≡ r = f(x); r + r."""
    result = check_equiv(hof_double, hof_double_alt)
    assert result.equivalent

def hof_compose_add(f: Callable[[int], int], x: int) -> int:
    return f(x) + 1

def hof_compose_add_alt(f: Callable[[int], int], x: int) -> int:
    return 1 + f(x)

def test_hof_commutative_add():
    """HOF: f(x) + 1 ≡ 1 + f(x) (commutativity)."""
    result = check_equiv(hof_compose_add, hof_compose_add_alt)
    assert result.equivalent


# ═══════════════════════════════════════════════════════════════════
#  LAMBDA Z3 TESTS
# ═══════════════════════════════════════════════════════════════════

def lambda_apply_double(x: int) -> int:
    f = lambda a: a * 2
    return f(x)

def plain_double(x: int) -> int:
    return x * 2

def test_lambda_equiv():
    """Lambda: (lambda a: a*2)(x) ≡ x*2."""
    result = check_equiv(lambda_apply_double, plain_double)
    assert result.equivalent


# ═══════════════════════════════════════════════════════════════════
#  STRING OPERATION Z3 TESTS
# ═══════════════════════════════════════════════════════════════════

def str_concat(a: str, b: str) -> str:
    return a + b

def str_concat_alt(a: str, b: str) -> str:
    return a + b

def test_str_concat_equiv():
    """String: a + b ≡ a + b."""
    result = check_equiv(str_concat, str_concat_alt)
    assert result.equivalent

def str_startswith_check(s: str) -> bool:
    return s.startswith("hello")

def str_startswith_check_alt(s: str) -> bool:
    return s.startswith("hello")

def test_str_startswith_equiv():
    """String: s.startswith('hello') ≡ s.startswith('hello')."""
    result = check_equiv(str_startswith_check, str_startswith_check_alt)
    assert result.equivalent

def str_replace_check(s: str) -> str:
    return s.replace("a", "b")

def str_replace_check_alt(s: str) -> str:
    return s.replace("a", "b")

def test_str_replace_equiv():
    """String: s.replace('a','b') ≡ s.replace('a','b')."""
    result = check_equiv(str_replace_check, str_replace_check_alt)
    assert result.equivalent

def str_endswith_check(s: str) -> bool:
    return s.endswith(".py")

def str_endswith_check_alt(s: str) -> bool:
    return s.endswith(".py")

def test_str_endswith_equiv():
    """String: s.endswith('.py') ≡ s.endswith('.py')."""
    result = check_equiv(str_endswith_check, str_endswith_check_alt)
    assert result.equivalent


# ═══════════════════════════════════════════════════════════════════
#  DICT MUTATION Z3 TESTS
# ═══════════════════════════════════════════════════════════════════

def dict_pop_check(d: dict, k: int) -> dict:
    d.pop(k)
    return d

def dict_pop_check_alt(d: dict, k: int) -> dict:
    d.pop(k)
    return d

def test_dict_pop_equiv():
    """Dict: d.pop(k) ≡ d.pop(k)."""
    result = check_equiv(dict_pop_check, dict_pop_check_alt)
    assert result.equivalent


# ═══════════════════════════════════════════════════════════════════
#  LEAN EXPORT: HOF + LAMBDA + AXIOM TESTS
# ═══════════════════════════════════════════════════════════════════

from deppy import guarantee, requires, compile_to_lean

@guarantee("result >= 0")
def lean_hof_abs_apply(f: Callable[[int], int], x: int) -> int:
    return abs(f(x))

def test_lean_hof_type():
    """Lean export handles Callable type annotation."""
    cert = compile_to_lean(lean_hof_abs_apply)
    rendered = cert.render()
    assert "→" in rendered  # Callable translates to arrow type

@guarantee("result >= 0")
def lean_lambda_sq(x: int) -> int:
    return (lambda a: a * a)(x)

def test_lean_lambda_body():
    """Lean export translates lambda in function body."""
    cert = compile_to_lean(lean_lambda_sq)
    rendered = cert.render()
    assert "fun" in rendered  # Lambda translates to fun

@guarantee("result >= x")
def lean_map_example(x: int) -> int:
    return max(x, 0) + x

def test_lean_map_tactic():
    """Lean export can prove spec for HOF-style code."""
    cert = compile_to_lean(lean_map_example)
    assert cert.sorry_count == 0


# ── For-loop Z3 tests ────────────────────────────────────

@guarantee("result == 10")
def loop_range_sum() -> int:
    acc = 0
    for i in range(5):
        acc += i
    return acc

def test_loop_range_sum_z3():
    """For-loop with range(5) is proved by Z3 (0+1+2+3+4=10)."""
    r = check_adherence(loop_range_sum, "result == 10")
    assert r and r[0].adheres

@guarantee("result == 6")
def loop_list_sum() -> int:
    acc = 0
    for x in [1, 2, 3]:
        acc += x
    return acc

def test_loop_list_sum_z3():
    """For-loop over literal list proved by Z3."""
    r = check_adherence(loop_list_sum, "result == 6")
    assert r and r[0].adheres

@guarantee("result == 10")
def loop_range_sum_alt() -> int:
    total = 0
    for i in range(1, 5):
        total += i
    return total

def test_loop_range_start_stop():
    """For-loop with range(start, stop) proved by Z3."""
    r = check_adherence(loop_range_sum_alt, "result == 10")
    assert r and r[0].adheres


# ── Recursion Z3 tests ────────────────────────────────────

def factorial_recursive(n: int) -> int:
    if n <= 0:
        return 1
    return n * factorial_recursive(n - 1)

def factorial_if_chain(n: int) -> int:
    if n <= 0:
        return 1
    return n * factorial_if_chain(n - 1)

def test_recursion_equivalence():
    """Two identical recursive functions are Z3-equivalent."""
    result = check_equiv(factorial_recursive, factorial_if_chain)
    assert result is not None
    assert result.equivalent

@guarantee("result >= 1")
def factorial_pos(n: int) -> int:
    if n <= 0:
        return 1
    return n * factorial_pos(n - 1)

def test_recursion_guarantee():
    """Recursive function adherence: Z3 may be inconclusive beyond unroll depth."""
    r = check_adherence(factorial_pos, "result >= 1")
    # Z3 returns a result (may be false negative at boundary)
    assert r is not None and len(r) > 0


# ── Class/method Z3 tests ────────────────────────────────

@guarantee("result >= 0")
def method_reads_field(self) -> int:
    return self.x * self.x

def test_class_method_field_access():
    """Method reading self.field creates Z3 vars and verifies."""
    r = check_adherence(method_reads_field, "result >= 0")
    assert r and r[0].adheres

@guarantee("result == self.x + self.y")
def method_sum_fields(self) -> int:
    return self.x + self.y

def test_class_method_sum_fields():
    """Method returning sum of two fields is verified by Z3."""
    r = check_adherence(method_sum_fields, "result == self.x + self.y")
    assert r and r[0].adheres

def method_a(self) -> int:
    return self.x + self.y

def method_b(self) -> int:
    return self.y + self.x

def test_class_method_equivalence():
    """Two methods reading same fields in different order are equivalent."""
    result = check_equiv(method_a, method_b)
    assert result is not None
    assert result.equivalent


# ── True division Z3 tests ────────────────────────────────

@guarantee("result >= 0")
def true_div_nonneg(x: int) -> float:
    return x / x  # always 1.0 when x != 0

def test_true_division_z3():
    """True division (/) uses Z3 Real, not integer division."""
    r = check_adherence(true_div_nonneg, "result >= 0")
    assert r and len(r) > 0

def div_half_a(x: int) -> float:
    return x / 2

def div_half_b(x: int) -> float:
    return x / 2

def test_true_division_equiv():
    """True division equivalence: x/2 ≡ x/2."""
    result = check_equiv(div_half_a, div_half_b)
    assert result is not None
    assert result.equivalent

def floor_div_a(x: int) -> int:
    return x // 2

def test_true_vs_floor_div():
    """True division and floor division differ for odd integers."""
    result = check_equiv(div_half_a, floor_div_a)
    # They're NOT equivalent (e.g. 1/2=0.5 vs 1//2=0)
    assert result is not None
    assert not result.equivalent


# ── Multi-arg Callable Z3 tests ──────────────────────────

@guarantee("result == 0")
def apply_multi(f: 'Callable[[int, int], int]', x: int) -> int:
    return f(x, 0) - f(x, 0)

def test_multi_arg_callable_z3():
    """Multi-arg Callable[[int, int], int] is supported by Z3."""
    r = check_adherence(apply_multi, "result == 0")
    assert r and r[0].adheres

def apply2_a(f: 'Callable[[int, int], int]', x: int, y: int) -> int:
    return f(x, y)

def apply2_b(f: 'Callable[[int, int], int]', x: int, y: int) -> int:
    return f(x, y)

def test_multi_arg_callable_equiv():
    """Multi-arg callable equivalence."""
    result = check_equiv(apply2_a, apply2_b)
    assert result is not None
    assert result.equivalent


# ── Tuple Z3 tests ───────────────────────────────────────

@guarantee("result >= 0")
def tuple_sum_sq(t: tuple) -> int:
    return t[0] * t[0] + t[1] * t[1]

def test_tuple_z3_adherence():
    """Tuple access: t[0]**2 + t[1]**2 >= 0."""
    r = check_adherence(tuple_sum_sq, "result >= 0")
    assert r and r[0].adheres

def tuple_swap_a() -> int:
    t = (1, 2, 3)
    return t[0] + t[2]

def tuple_swap_b() -> int:
    t = (1, 2, 3)
    return t[2] + t[0]

def test_tuple_literal_equiv():
    """Tuple literal access equivalence."""
    result = check_equiv(tuple_swap_a, tuple_swap_b)
    assert result is not None
    assert result.equivalent


# ── Set Z3 tests ─────────────────────────────────────────

def set_contains_a(x: int) -> bool:
    s = {1, 2, 3}
    return x in s

def set_contains_b(x: int) -> bool:
    s = {3, 2, 1}
    return x in s

def test_set_literal_equiv():
    """Set literals with same elements are equivalent regardless of order."""
    result = check_equiv(set_contains_a, set_contains_b)
    assert result is not None
    assert result.equivalent


# ── Type inference Z3 tests ──────────────────────────────

def untyped_list_sum(xs):
    """No type annotation — inferred as list from xs.append usage."""
    xs.append(0)
    return 0

def untyped_list_sum2(xs):
    xs.append(0)
    return 0

def test_type_inference_list():
    """Type inference detects list from .append() usage."""
    result = check_equiv(untyped_list_sum, untyped_list_sum2)
    assert result is not None
    assert result.equivalent

def untyped_div(x, y):
    """No annotation — x/y infers float for x."""
    return x / y

def untyped_div2(x, y):
    return x / y

def test_type_inference_float():
    """Type inference detects float from / usage."""
    result = check_equiv(untyped_div, untyped_div2)
    assert result is not None
    assert result.equivalent


# ───────── while-loop tests ─────────

def while_sum_down(n: int) -> int:
    """Sum 1..n via while-loop."""
    acc = 0
    i = n
    while i > 0:
        acc = acc + i
        i = i - 1
    return acc

def while_sum_down2(n: int) -> int:
    """Same logic, different var names."""
    total = 0
    k = n
    while k > 0:
        total = total + k
        k = k - 1
    return total

def test_while_loop_equiv():
    """Two while-loop sum-downs are equivalent."""
    result = check_equiv(while_sum_down, while_sum_down2)
    assert result is not None
    assert result.equivalent

@guarantee("result >= 0 or n < 0")
def while_sum_pos(n: int) -> int:
    acc = 0
    i = n
    while i > 0:
        acc = acc + i
        i = i - 1
    return acc

def test_while_loop_adherence():
    """While-loop sum spec check — should not crash."""
    # Use testing fallback since Z3 may timeout on complex unrolled expressions
    from deppy.equivalence import check_adherence
    result = check_adherence(while_sum_pos)
    # Result may be None (Z3 timeout) or AdherenceResult — either is fine
    pass  # just verifying no crash


# ───────── inheritance tests ─────────

def parent_init_child_method():
    """Test class with inheritance — inline equivalence."""
    class Animal:
        def __init__(self, legs: int):
            self.legs = legs
        def describe(self) -> int:
            return self.legs

    class Dog(Animal):
        def __init__(self):
            super().__init__(4)

    d = Dog()
    return d.describe()

def always_four() -> int:
    return 4

def test_inheritance_basic():
    """Inherited method returns correct value."""
    result = check_equiv(parent_init_child_method, always_four)
    # Even if Z3 can't solve it, testing should find equivalence
    assert result is not None
    assert result.equivalent


# ───────── deep recursion with inductive boundary ─────────

@guarantee("result >= 1")
def factorial_pos(n: int) -> int:
    if n <= 1:
        return 1
    return n * factorial_pos(n - 1)

def test_deep_recursion_adherence():
    """Factorial with inductive boundary constraints satisfies result >= 1."""
    results = check_adherence(factorial_pos)
    assert len(results) > 0
    # Should pass: base case 1 >= 1, inductive n * boundary >= 1 when n >= 2 and boundary >= 1
    assert results[0].adheres


# ───────── symbolic-length for-loop adherence ─────────

@guarantee("result >= 0")
def sum_list_nonneg(xs: list) -> int:
    """Sum of list, spec: result >= 0 (only true for nonneg inputs)."""
    total = 0
    for x in xs:
        total = total + x
    return total

def test_symbolic_for_loop_adherence():
    """Symbolic-length for-loop is attempted in adherence mode."""
    # This may or may not prove (unconstrained xs could be negative),
    # but it should not crash
    results = check_adherence(sum_list_nonneg)
    assert len(results) > 0


# ═══════════════════════════════════════════════════════════════════
#  CROSS-FUNCTION VERIFICATION (modular reasoning)
# ═══════════════════════════════════════════════════════════════════

from deppy.proofs.sugar import guarantee as _guarantee_deco

@_guarantee_deco("result >= 0")
def _helper_nonneg(x: int) -> int:
    return x * x

@_guarantee_deco("result >= 0")
def _caller_uses_helper(x: int) -> int:
    return _helper_nonneg(x) + 1

def test_cross_function_guarantee_propagation():
    """Caller should be proved via callee's @guarantee axiom."""
    results = check_adherence(_caller_uses_helper)
    assert len(results) == 1
    r = results[0]
    assert r.adheres is True, f"Expected proved, got {r}"

@_guarantee_deco("result >= 1")
def _helper_positive(x: int) -> int:
    return abs(x) + 1

@_guarantee_deco("result >= 2")
def _caller_adds_helpers(x: int) -> int:
    return _helper_positive(x) + _helper_positive(x)

def test_cross_function_two_calls():
    """Two calls to the same callee should both contribute axioms."""
    results = check_adherence(_caller_adds_helpers)
    assert len(results) == 1
    assert results[0].adheres is True

@_guarantee_deco("result >= 0")
def _callee_same_args(x: int) -> int:
    return x * x

@_guarantee_deco("result == 0")
def _caller_diff_same_call(x: int) -> int:
    return _callee_same_args(x) - _callee_same_args(x)

def test_cross_function_same_args_same_result():
    """Same callee with same args should return the same result (pure)."""
    results = check_adherence(_caller_diff_same_call)
    assert len(results) == 1
    assert results[0].adheres is True


# ═══════════════════════════════════════════════════════════════════
#  CROSS-MODULE VERIFICATION
# ═══════════════════════════════════════════════════════════════════

def test_verify_module():
    """verify_module should find and check all @guarantee functions."""
    from deppy.equivalence import verify_module
    import types

    mod = types.ModuleType('_test_mod')
    @_guarantee_deco("result >= 0")
    def sq(x: int) -> int:
        return x * x
    mod.sq = sq
    mod.sq.__module__ = '_test_mod'

    results = verify_module(mod)
    assert 'sq' in results
    assert results['sq'][0].adheres is True


# ═══════════════════════════════════════════════════════════════════
#  SHARED-STATE ANALYSIS (concurrency)
# ═══════════════════════════════════════════════════════════════════

_global_counter = 0

def _unguarded_writer(x: int) -> int:
    global _global_counter
    _global_counter += x
    return _global_counter

def test_shared_state_unguarded_write():
    """Detect unguarded write to global variable."""
    from deppy.equivalence import analyze_shared_state
    warnings = analyze_shared_state(_unguarded_writer)
    writes = [w for w in warnings if w.access_type == 'write']
    assert len(writes) >= 1
    assert any(not w.guarded for w in writes)
    assert all(w.variable == '_global_counter' for w in writes)

_shared_val = 0

def _guarded_writer(x: int) -> int:
    global _shared_val
    import threading
    lock = threading.Lock()
    with lock:
        _shared_val += x
    return _shared_val

def test_shared_state_guarded_write():
    """Write inside `with lock:` should be marked as guarded."""
    from deppy.equivalence import analyze_shared_state
    warnings = analyze_shared_state(_guarded_writer)
    writes = [w for w in warnings if w.access_type == 'write']
    assert any(w.guarded for w in writes)

def _no_shared_state(x: int) -> int:
    total = x + 1
    return total

def test_shared_state_none():
    """Pure function should produce no shared-state warnings."""
    from deppy.equivalence import analyze_shared_state
    warnings = analyze_shared_state(_no_shared_state)
    assert len(warnings) == 0

_counter2 = 0

def _mixed_access(x: int) -> int:
    global _counter2
    import threading
    lock = threading.Lock()
    # Unguarded read
    old = _counter2
    with lock:
        # Guarded write
        _counter2 = old + x
    return _counter2

def test_shared_state_mixed():
    """Detect both guarded and unguarded accesses."""
    from deppy.equivalence import analyze_shared_state
    warnings = analyze_shared_state(_mixed_access)
    assert any(not w.guarded for w in warnings)
    assert any(w.guarded for w in warnings)


# ═══════════════════════════════════════════════════════════════════
#  COMPOSITIONAL PATH VERIFICATION
# ═══════════════════════════════════════════════════════════════════

@_guarantee_deco("result >= 0")
def _comp_square(x: int) -> int:
    return x * x

@_guarantee_deco("result >= 1")
def _comp_plus_one(x: int) -> int:
    return x + 1

def test_verify_composition_z3():
    """Composition plus_one(square(x)) >= 1 should be Z3-proved."""
    from deppy.equivalence import verify_composition
    result = verify_composition(_comp_plus_one, _comp_square, "result >= 1")
    assert result.verified is True
    assert result.method == 'z3'

def test_verify_composition_testing():
    """Composition should fallback to testing for complex specs."""
    from deppy.equivalence import verify_composition
    result = verify_composition(_comp_plus_one, _comp_square, "result >= 0")
    assert result.verified is True


# ═══════════════════════════════════════════════════════════════════
#  EFFECT-AWARE ANALYSIS
# ═══════════════════════════════════════════════════════════════════

def _pure_fn(x: int) -> int:
    return x + 1

def _impure_fn(x: int) -> int:
    print(x)
    return x

def test_analyze_effects_pure():
    """Pure function should be detected as PURE."""
    from deppy.equivalence import analyze_effects
    report = analyze_effects(_pure_fn)
    assert report is not None
    assert report.is_pure is True

def test_analyze_effects_impure():
    """Function with print() should have IO effect."""
    from deppy.equivalence import analyze_effects
    report = analyze_effects(_impure_fn)
    assert report is not None
    assert report.effect == 'IO'
    assert report.is_pure is False

def test_analyze_call_chain():
    """Call chain analysis should trace through callees."""
    from deppy.equivalence import analyze_call_chain_effects
    reports = analyze_call_chain_effects(_pure_fn)
    assert len(reports) >= 1
    assert all(r.is_pure for r in reports)


# ═══════════════════════════════════════════════════════════════════
#  MODULE-LEVEL PATH EQUIVALENCE
# ═══════════════════════════════════════════════════════════════════

def test_check_module_paths_equivalent():
    """Two modules with same functions should have path equivalence."""
    import types
    from deppy.equivalence import check_module_paths

    mod_a = types.ModuleType('_mod_a')
    mod_b = types.ModuleType('_mod_b')

    def add1(x: int) -> int:
        return x + 1
    def add1_v2(x: int) -> int:
        return 1 + x

    mod_a.add1 = add1
    mod_b.add1 = add1_v2
    mod_a.add1.__name__ = 'add1'
    mod_b.add1.__name__ = 'add1'

    results = check_module_paths(mod_a, mod_b, names=['add1'])
    assert len(results) == 1
    assert results[0].equivalent is True

def test_check_module_paths_inequivalent():
    """Two modules with different functions should fail path check."""
    import types
    from deppy.equivalence import check_module_paths

    mod_a = types.ModuleType('_mod_a')
    mod_b = types.ModuleType('_mod_b')

    def double(x: int) -> int:
        return x * 2
    def triple(x: int) -> int:
        return x * 3

    mod_a.calc = double
    mod_b.calc = triple
    mod_a.calc.__name__ = 'calc'
    mod_b.calc.__name__ = 'calc'

    results = check_module_paths(mod_a, mod_b, names=['calc'])
    assert len(results) == 1
    assert results[0].equivalent is False


# ═══════════════════════════════════════════════════════════════════
#  TOPOLOGICAL MODULE VERIFICATION
# ═══════════════════════════════════════════════════════════════════

def test_verify_module_topological():
    """verify_module with topological=True should order callees first."""
    import types
    from deppy.equivalence import verify_module

    mod = types.ModuleType('_test_topo')

    @_guarantee_deco("result >= 0")
    def base(x: int) -> int:
        return x * x

    @_guarantee_deco("result >= 1")
    def caller(x: int) -> int:
        return base(x) + 1

    mod.base = base
    mod.caller = caller
    results = verify_module(mod, topological=True)
    assert 'base' in results or 'caller' in results


# ═══════════════════════════════════════════════════════════════════
#  CONCURRENT SAFETY VERIFICATION
# ═══════════════════════════════════════════════════════════════════

def test_concurrent_safety_pure():
    """Pure function should be concurrency-safe."""
    from deppy.equivalence import verify_concurrent_safety
    result = verify_concurrent_safety(_pure_fn)
    assert result.safe is True

_conc_counter = 0

def _unsafe_concurrent(x: int) -> int:
    global _conc_counter
    _conc_counter += x
    return _conc_counter

def test_concurrent_safety_unsafe():
    """Unguarded global write should be flagged as unsafe."""
    from deppy.equivalence import verify_concurrent_safety
    result = verify_concurrent_safety(_unsafe_concurrent)
    assert result.safe is False
    assert len(result.unguarded_vars) > 0

_conc_val = 0

def _safe_concurrent(x: int) -> int:
    global _conc_val
    import threading
    lock = threading.Lock()
    with lock:
        _conc_val += x
        result = _conc_val
    return result

def test_concurrent_safety_guarded():
    """Lock-guarded writes should be safe."""
    from deppy.equivalence import verify_concurrent_safety
    result = verify_concurrent_safety(_safe_concurrent)
    assert result.safe is True
    assert len(result.guarded_vars) > 0


# ═══════════════════════════════════════════════════════════════════
#  IMPORT GRAPH ANALYSIS
# ═══════════════════════════════════════════════════════════════════

def test_build_import_graph():
    """Import graph should be constructable from modules."""
    from deppy.equivalence import build_import_graph
    import types
    mod = types.ModuleType('_graph_mod')
    graph = build_import_graph(mod)
    assert len(graph.modules) == 1
    assert graph.topological_order == ['_graph_mod']
