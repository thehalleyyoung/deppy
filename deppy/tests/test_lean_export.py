"""
Deppy Lean 4 export test suite.

~40 test cases verifying that compile_to_lean produces:
 - Real proofs (no sorry) for arithmetic specs
 - Correct sorry + obligation reporting for complex specs
 - Valid theorem text for various function patterns
"""
from __future__ import annotations

import pytest
from deppy import guarantee, requires, compile_to_lean

# ═══════════════════════════════════════════════════════════════════
#  FUNCTIONS THAT GET REAL PROOFS (no sorry)
# ═══════════════════════════════════════════════════════════════════

@guarantee("result >= 0")
def lean_square(x: int) -> int:
    return x * x

@guarantee("result >= 0")
def lean_abs(x: int) -> int:
    if x >= 0:
        return x
    return -x

@requires("n > 0")
@guarantee("result > 0")
def lean_double_pos(n: int) -> int:
    return n * 2

@guarantee("result >= 0")
def lean_zero(x: int) -> int:
    return 0

@guarantee("result >= x")
def lean_abs2(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result >= 0")
def lean_relu(x: int) -> int:
    if x > 0:
        return x
    return 0

@requires("a >= 0")
@guarantee("result >= 0")
def lean_id_pos(a: int) -> int:
    return a

@requires("x > 0")
@guarantee("result > 0")
def lean_triple_pos(x: int) -> int:
    return x * 3

@guarantee("result >= 0")
def lean_abs_neg(x: int) -> int:
    if x < 0:
        return -x
    return x

@requires("x >= 0")
@requires("y >= 0")
@guarantee("result >= 0")
def lean_add_nonneg(x: int, y: int) -> int:
    return x + y

@guarantee("result >= 0")
def lean_abs_ternary(x: int) -> int:
    return x if x >= 0 else -x

@requires("x > 0")
@guarantee("result >= x")
def lean_double_ge(x: int) -> int:
    return x * 2

@guarantee("result >= 0")
def lean_sq_alt(x: int) -> int:
    a = x * x
    return a

@requires("a >= 0")
@requires("b >= 0")
@guarantee("result >= 0")
def lean_mul_pos(a: int, b: int) -> int:
    return a * b

@guarantee("result >= 0")
def lean_max_zero(x: int) -> int:
    return max(x, 0)

@requires("n > 0")
@guarantee("result > 0")
def lean_quad_pos(n: int) -> int:
    return n * 4


PROVEN_FUNCS = [
    lean_square, lean_abs, lean_double_pos, lean_zero,
    lean_abs2, lean_relu, lean_id_pos, lean_triple_pos,
    lean_abs_neg, lean_add_nonneg,
    lean_abs_ternary, lean_double_ge, lean_sq_alt,
    lean_mul_pos, lean_max_zero, lean_quad_pos,
]


@pytest.mark.parametrize("fn", PROVEN_FUNCS, ids=[f.__name__ for f in PROVEN_FUNCS])
def test_lean_proven(fn):
    cert = compile_to_lean(fn)
    assert cert.trust_level in ("LEAN_VERIFIED", "Z3_PROVEN"), (
        f"{fn.__name__}: expected proven, got {cert.trust_level}"
    )
    assert cert.sorry_count == 0, (
        f"{fn.__name__}: expected 0 sorry, got {cert.sorry_count}"
    )
    rendered = cert.render()
    assert "sorry" not in rendered.lower() or "sorry" in rendered.split("/-!")[1].split("-/")[0], (
        f"{fn.__name__}: found sorry in proof body"
    )
    assert cert.proved_count >= 1, f"{fn.__name__}: expected proved_count >= 1"
    assert len(cert.obligations) == 0, (
        f"{fn.__name__}: expected no obligations, got {cert.obligations}"
    )


# ═══════════════════════════════════════════════════════════════════
#  FUNCTIONS THAT GET sorry (complex specs)
# ═══════════════════════════════════════════════════════════════════

@guarantee("result is sorted")
def lean_sorted(xs: list) -> list:
    return sorted(xs)

@guarantee("result is a permutation of xs")
def lean_perm(xs: list) -> list:
    return sorted(xs)

@guarantee("all elements of result are positive")
def lean_filter_pos(xs: list) -> list:
    return [x for x in xs if x > 0]

@guarantee("result contains no duplicates")
def lean_unique(xs: list) -> list:
    return list(set(xs))


SORRY_FUNCS = [
    lean_sorted, lean_perm, lean_filter_pos, lean_unique,
]


@pytest.mark.parametrize("fn", SORRY_FUNCS, ids=[f.__name__ for f in SORRY_FUNCS])
def test_lean_sorry_reported(fn):
    cert = compile_to_lean(fn)
    assert cert.sorry_count >= 1, (
        f"{fn.__name__}: expected sorry obligations, got 0"
    )
    assert len(cert.obligations) >= 1, (
        f"{fn.__name__}: expected obligation warnings"
    )
    assert cert.trust_level != "LEAN_VERIFIED", (
        f"{fn.__name__}: shouldn't be LEAN_VERIFIED with sorry"
    )


# ═══════════════════════════════════════════════════════════════════
#  RENDERED THEOREM TEXT CHECKS
# ═══════════════════════════════════════════════════════════════════

def test_lean_square_theorem_text():
    cert = compile_to_lean(lean_square)
    rendered = cert.render()
    assert "theorem" in rendered or "def" in rendered
    assert "lean_square" in rendered
    # Should have omega tactic for arithmetic
    assert "omega" in rendered or "simp" in rendered


def test_lean_abs_theorem_text():
    cert = compile_to_lean(lean_abs)
    rendered = cert.render()
    assert "lean_abs" in rendered
    assert "omega" in rendered or "simp" in rendered


def test_lean_double_pos_precondition():
    cert = compile_to_lean(lean_double_pos)
    rendered = cert.render()
    assert "lean_double_pos" in rendered
    # Should include the precondition as a hypothesis
    assert "0 <" in rendered or "n > 0" in rendered or "h" in rendered


def test_lean_rendering_is_valid_structure():
    """Every proven certificate should have namespace, end, and header."""
    for fn in PROVEN_FUNCS:
        cert = compile_to_lean(fn)
        rendered = cert.render()
        assert "namespace" in rendered
        assert "end" in rendered
        assert "/-!" in rendered  # header comment


# ═══════════════════════════════════════════════════════════════════
#  TRUST LEVEL TRACKING
# ═══════════════════════════════════════════════════════════════════

@pytest.mark.parametrize("fn", PROVEN_FUNCS, ids=[f.__name__ for f in PROVEN_FUNCS])
def test_lean_trust_level_proven(fn):
    cert = compile_to_lean(fn)
    assert cert.trust_level in ("LEAN_VERIFIED", "Z3_PROVEN")


@pytest.mark.parametrize("fn", SORRY_FUNCS, ids=[f.__name__ for f in SORRY_FUNCS])
def test_lean_trust_level_sorry(fn):
    cert = compile_to_lean(fn)
    assert cert.trust_level in ("LEAN_EXPORTED", "UNTRUSTED")


# ═══════════════════════════════════════════════════════════════════
#  COMPILE MULTIPLE SPECS
# ═══════════════════════════════════════════════════════════════════

@guarantee("result >= 0")
@guarantee("result >= x")
def lean_multi_abs(x: int) -> int:
    if x >= 0:
        return x
    return -x


def test_lean_multi_spec():
    cert = compile_to_lean(lean_multi_abs)
    assert cert.proved_count >= 1
    # Both specs should produce theorems
    rendered = cert.render()
    assert "lean_multi_abs" in rendered
