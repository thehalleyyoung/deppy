"""
Tests for Lean proof script generation in the equivalence checker.
"""
from __future__ import annotations

import pytest
from deppy.equivalence import (
    check_equiv, check_adherence, equiv_to_lean,
    check_spec_equiv, EquivResult, AdherenceResult, SpecEquivResult,
)
from deppy import guarantee, requires


# ═══════════════════════════════════════════════════════════════════
#  Lean proof generation — equivalence
# ═══════════════════════════════════════════════════════════════════

def lean_f1(x: int) -> int: return x * 2
def lean_g1(x: int) -> int: return x + x

def lean_f2(x: int) -> int: return x + 1
def lean_g2(x: int) -> int: return x + 2

def lean_f3(x: int) -> int: return (x + 1) ** 2
def lean_g3(x: int) -> int: return x * x + 2 * x + 1

def lean_f4(x: int, y: int) -> int: return x + y
def lean_g4(x: int, y: int) -> int: return y + x

def lean_f5(x: int) -> int:
    if x >= 0:
        return x
    return -x
def lean_g5(x: int) -> int:
    return x if x >= 0 else -x


class TestLeanEquivGeneration:
    def test_linear_equiv_uses_omega(self):
        r = check_equiv(lean_f1, lean_g1)
        assert r.lean_proof is not None
        assert 'omega' in r.lean_proof
        assert 'theorem lean_f1_eq_lean_g1' in r.lean_proof
        assert 'EQUIVALENT' in r.lean_proof

    def test_inequiv_uses_decide(self):
        r = check_equiv(lean_f2, lean_g2)
        assert r.lean_proof is not None
        assert 'decide' in r.lean_proof
        assert 'lean_f2_neq_lean_g2' in r.lean_proof
        assert 'INEQUIVALENT' in r.lean_proof
        assert '≠' in r.lean_proof

    def test_nonlinear_uses_ring(self):
        r = check_equiv(lean_f3, lean_g3)
        assert r.lean_proof is not None
        assert 'ring' in r.lean_proof
        assert 'theorem lean_f3_eq_lean_g3' in r.lean_proof

    def test_multi_param(self):
        r = check_equiv(lean_f4, lean_g4)
        assert r.lean_proof is not None
        assert '(x : Int)' in r.lean_proof
        assert '(y : Int)' in r.lean_proof

    def test_branching_equiv(self):
        r = check_equiv(lean_f5, lean_g5)
        assert r.lean_proof is not None
        assert 'if' in r.lean_proof

    def test_equiv_to_lean_convenience(self):
        lean = equiv_to_lean(lean_f1, lean_g1)
        assert lean is not None
        assert 'theorem' in lean

    def test_lean_proof_has_import(self):
        r = check_equiv(lean_f1, lean_g1)
        assert 'import Mathlib.Tactic' in r.lean_proof

    def test_lean_proof_has_defs(self):
        r = check_equiv(lean_f1, lean_g1)
        assert 'def lean_f1' in r.lean_proof
        assert 'def lean_g1' in r.lean_proof

    def test_lean_counterexample_in_proof(self):
        r = check_equiv(lean_f2, lean_g2)
        assert r.counterexample is not None
        cex_val = str(r.counterexample.get('x', ''))
        assert cex_val in r.lean_proof


# ═══════════════════════════════════════════════════════════════════
#  Lean proof generation — adherence
# ═══════════════════════════════════════════════════════════════════

@guarantee("result >= 0")
def lean_abs(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result > 0")
def lean_abs_buggy(x: int) -> int:
    if x >= 0:
        return x
    return -x

@guarantee("result >= 0")
def lean_square(x: int) -> int:
    return x * x

@requires("x > 0")
@guarantee("result > 0")
def lean_double_pos(x: int) -> int:
    return x * 2


class TestLeanAdherenceGeneration:
    def test_adherence_correct_lean(self):
        results = check_adherence(lean_abs)
        r = results[0]
        assert r.adheres is True
        assert r.lean_proof is not None
        assert 'theorem lean_abs_adheres' in r.lean_proof
        assert 'ADHERES' in r.lean_proof

    def test_adherence_violated_lean(self):
        results = check_adherence(lean_abs_buggy)
        r = results[0]
        assert r.adheres is False
        assert r.lean_proof is not None
        assert 'VIOLATES' in r.lean_proof

    def test_adherence_nonlinear_lean(self):
        results = check_adherence(lean_square)
        r = results[0]
        assert r.adheres is True
        assert r.lean_proof is not None
        assert 'ring' in r.lean_proof

    def test_adherence_ad_hoc_lean(self):
        def clamp(x: int) -> int:
            if x < 0: return 0
            if x > 100: return 100
            return x
        results = check_adherence(clamp, spec="result >= 0")
        r = results[0]
        assert r.adheres is True
        assert r.lean_proof is not None


# ═══════════════════════════════════════════════════════════════════
#  Spec equivalence
# ═══════════════════════════════════════════════════════════════════

class TestSpecEquiv:
    def test_syntactic_equal(self):
        r = check_spec_equiv("result >= 0", "result >= 0")
        assert r.equivalent is True
        assert r.method == 'syntactic'

    def test_semantic_equiv(self):
        r = check_spec_equiv("result >= 0", "result > -1")
        assert r.equivalent is True
        assert r.implies_forward is True
        assert r.implies_backward is True

    def test_implies_forward_only(self):
        r = check_spec_equiv("result > 0", "result >= 0")
        assert r.equivalent is False
        assert r.implies_forward is True
        assert r.implies_backward is False

    def test_implies_backward_only(self):
        r = check_spec_equiv("result >= 0", "result > 0")
        assert r.equivalent is False
        assert r.implies_forward is False
        assert r.implies_backward is True

    def test_incomparable(self):
        r = check_spec_equiv("result > 5", "result < 10")
        assert r.equivalent is False
        assert r.implies_forward is False
        assert r.implies_backward is False

    def test_with_params(self):
        r = check_spec_equiv("result >= x", "result > x - 1",
                            params=["x"], param_types={"x": int})
        assert r.equivalent is True

    def test_multi_param(self):
        r = check_spec_equiv("result >= x + y", "result >= y + x",
                            params=["x", "y"])
        assert r.equivalent is True


# ═══════════════════════════════════════════════════════════════════
#  Enhanced Z3 — new constructs
# ═══════════════════════════════════════════════════════════════════

def z3_pow_call(x: int) -> int: return pow(x, 2)
def z3_pow_manual(x: int) -> int: return x * x

def z3_bool_coerce(x: int) -> int: return bool(x)
def z3_bool_manual(x: int) -> int:
    if x != 0:
        return 1
    return 0

def z3_int_id(x: int) -> int: return int(x)
def z3_plain_id(x: int) -> int: return x

def z3_min3(a: int, b: int, c: int) -> int: return min(a, b, c)
def z3_min3_nested(a: int, b: int, c: int) -> int: return min(a, min(b, c))

def z3_max3(a: int, b: int, c: int) -> int: return max(a, b, c)
def z3_max3_nested(a: int, b: int, c: int) -> int: return max(a, max(b, c))


class TestEnhancedZ3:
    def test_pow_call(self):
        r = check_equiv(z3_pow_call, z3_pow_manual)
        assert r.equivalent is True
        assert r.method == 'z3'

    def test_bool_coerce(self):
        r = check_equiv(z3_bool_coerce, z3_bool_manual)
        assert r.equivalent is True
        assert r.method == 'z3'

    def test_int_identity(self):
        r = check_equiv(z3_int_id, z3_plain_id)
        assert r.equivalent is True
        assert r.method == 'z3'

    def test_min3(self):
        r = check_equiv(z3_min3, z3_min3_nested)
        assert r.equivalent is True
        assert r.method == 'z3'

    def test_max3(self):
        r = check_equiv(z3_max3, z3_max3_nested)
        assert r.equivalent is True
        assert r.method == 'z3'


# ═══════════════════════════════════════════════════════════════════
#  Spec info enrichment
# ═══════════════════════════════════════════════════════════════════

@guarantee("result >= 0")
def spec_abs_a(x: int) -> int:
    if x >= 0: return x
    return -x

@guarantee("result >= 0")
def spec_abs_b(x: int) -> int:
    return abs(x)


class TestSpecEnrichment:
    def test_spec_info_on_equiv(self):
        r = check_equiv(spec_abs_a, spec_abs_b)
        assert r.equivalent is True
        # spec_info should contain info about matching specs
        assert r.spec_info is not None
        assert 'guarantee' in r.spec_info.lower() or 'spec' in r.spec_info.lower()

    def test_no_spec_info_without_guarantee(self):
        def plain_a(x: int) -> int: return x * 2
        def plain_b(x: int) -> int: return x + x
        r = check_equiv(plain_a, plain_b)
        # No @guarantee → spec_info should be None
        assert r.spec_info is None
