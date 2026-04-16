"""D35: Strength Reduction (Theorem 35.1).

Replace expensive operations with cheaper equivalents.

Mathematical foundation:
  Strength reduction is justified by the ring axioms (for arithmetic
  identities) and the bitwise correspondence theorem (for bit-level
  equivalences over ℤ₂ⁿ).

  In a commutative ring (R, +, ·, 0, 1):
    x · 2 = x + x           (definition of scalar multiplication)
    x · 0 = 0               (absorption)
    x · 1 = x               (unit)
    x² = x · x              (definition of exponentiation)

  For non-negative integers in ℤ₂ⁿ:
    x · 2ᵏ = x << k         (left shift = multiply by power of 2)
    x ÷ 2ᵏ = x >> k         (right shift = integer divide by power of 2)
    x mod 2ᵏ = x & (2ᵏ-1)   (bitwise AND = modular arithmetic)

  Horner's rule: a₀ + a₁x + a₂x² + ... + aₙxⁿ
    = a₀ + x(a₁ + x(a₂ + ... + x·aₙ)...)
  reduces n multiplications to n multiply-add steps.

Covers:
  • x * 2 ↔ x + x ↔ x << 1
  • x ** 2 ↔ x * x
  • x * 0 → 0, x * 1 → x, x + 0 → x
  • x // 2 ↔ x >> 1 (for non-negative x)
  • x % 2 ↔ x & 1
  • abs(x) ** 2 ↔ x ** 2
  • Horner's rule ↔ naive polynomial evaluation
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D35_strength_reduce'
AXIOM_CATEGORY = 'algebraic_simplification'

SOUNDNESS_PROOF = """
Theorem 35.1 (Strength Reduction Identities):
  In a commutative ring (R, +, ·, 0, 1):
    (a) x · 2 = x + x                   [scalar mult definition]
    (b) x · 0 = 0                        [absorption]
    (c) x · 1 = x                        [multiplicative identity]
    (d) x + 0 = x                        [additive identity]
    (e) x² = x · x                       [exponentiation definition]
    (f) |x|² = x²                        [absolute value squared]

Theorem 35.2 (Bitwise Correspondence):
  For non-negative integers in ℤ₂ⁿ:
    (a) x · 2ᵏ = x << k                 [shift-multiply duality]
    (b) ⌊x / 2ᵏ⌋ = x >> k              [shift-divide duality]
    (c) x mod 2ᵏ = x & (2ᵏ - 1)        [mask-modulus duality]
  where << is left shift, >> is arithmetic right shift, & is bitwise AND.

Proof:
  (35.2a): x << k shifts the binary representation of x left by k bits,
  which is equivalent to multiplying by 2ᵏ in positional notation.
  (35.2b): x >> k discards the lowest k bits, which is integer
  division by 2ᵏ (floor division for non-negative x).
  (35.2c): x & (2ᵏ-1) keeps only the lowest k bits, which is the
  remainder when dividing by 2ᵏ.  ∎

Theorem 35.3 (Horner's Rule):
  For polynomial p(x) = Σᵢ aᵢxⁱ,
    p(x) = a₀ + x·(a₁ + x·(a₂ + ... + x·aₙ)...)
  computes the same value with n multiply-adds instead of O(n²) ops.
"""

COMPOSES_WITH = ['D02_beta', 'D36_cse', 'D17_assoc']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'multiply by 2 to add',
        'before': "x * 2",
        'after': "x + x",
        'axiom': 'D35_mul2_to_add',
    },
    {
        'name': 'multiply by 2 to shift',
        'before': "x * 2",
        'after': "x << 1",
        'axiom': 'D35_mul2_to_shift',
    },
    {
        'name': 'square to self-multiply',
        'before': "x ** 2",
        'after': "x * x",
        'axiom': 'D35_pow2_to_mul',
    },
    {
        'name': 'multiply by zero',
        'before': "x * 0",
        'after': "0",
        'axiom': 'D35_mul_zero',
    },
    {
        'name': 'multiply by one',
        'before': "x * 1",
        'after': "x",
        'axiom': 'D35_mul_one',
    },
    {
        'name': 'integer divide by 2 to shift',
        'before': "x // 2",
        'after': "x >> 1",
        'axiom': 'D35_div2_to_rshift',
    },
    {
        'name': 'mod 2 to bitwise and',
        'before': "x % 2",
        'after': "x & 1",
        'axiom': 'D35_mod2_to_and',
    },
    {
        'name': 'abs squared to squared',
        'before': "abs(x) ** 2",
        'after': "x ** 2",
        'axiom': 'D35_abs_sq',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: fiber context
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """All free variable names in *term*."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OCase):
        return (
            _extract_free_vars(term.test)
            | _extract_free_vars(term.true_branch)
            | _extract_free_vars(term.false_branch)
        )
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred)
        return r3
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a)
        return r5
    return set()


def _is_lit(term: OTerm, value: Any) -> bool:
    """Check if term is OLit with given value."""
    return isinstance(term, OLit) and term.value == value


def _is_power_of_2(n: int) -> Optional[int]:
    """Return k if n == 2**k, else None."""
    if n <= 0:
        return None
    k = 0
    while n > 1:
        if n % 2 != 0:
            return None
        n //= 2
        k += 1
    return k


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D35 strength reduction equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    name = term.name
    args = term.args

    # ── Multiplication identities ──
    if name in ('mult', 'mul') and len(args) == 2:
        lhs, rhs = args

        # x * 0 → 0 (absorption, either side)
        if _is_lit(rhs, 0):
            results.append((OLit(0), 'D35_mul_zero'))
        if _is_lit(lhs, 0):
            results.append((OLit(0), 'D35_mul_zero'))

        # x * 1 → x (identity, either side)
        if _is_lit(rhs, 1):
            results.append((lhs, 'D35_mul_one'))
        if _is_lit(lhs, 1):
            results.append((rhs, 'D35_mul_one'))

        # x * -1 → -x (negation)
        if _is_lit(rhs, -1):
            results.append((OOp('u_usub', (lhs,)), 'D35_mul_neg1'))
        if _is_lit(lhs, -1):
            results.append((OOp('u_usub', (rhs,)), 'D35_mul_neg1'))

        # x * 2 → x + x  and  x * 2 → x << 1
        if _is_lit(rhs, 2):
            results.append((OOp('add', (lhs, lhs)), 'D35_mul2_to_add'))
            results.append((OOp('lshift', (lhs, OLit(1))), 'D35_mul2_to_shift'))
        if _is_lit(lhs, 2):
            results.append((OOp('add', (rhs, rhs)), 'D35_mul2_to_add'))
            results.append((OOp('lshift', (rhs, OLit(1))), 'D35_mul2_to_shift'))

        # x * 2^k → x << k (general power-of-2 multiply)
        for side, other in [(rhs, lhs), (lhs, rhs)]:
            if isinstance(side, OLit) and isinstance(side.value, int):
                k = _is_power_of_2(side.value)
                if k is not None and k > 1:
                    results.append((
                        OOp('lshift', (other, OLit(k))),
                        'D35_mul_pow2_to_shift',
                    ))

    # ── Addition identities ──
    if name == 'add' and len(args) == 2:
        lhs, rhs = args
        if _is_lit(rhs, 0):
            results.append((lhs, 'D35_add_zero'))
        if _is_lit(lhs, 0):
            results.append((rhs, 'D35_add_zero'))

        # x + x → x * 2 → x << 1 (reverse of mul2_to_add)
        if lhs.canon() == rhs.canon():
            results.append((OOp('lshift', (lhs, OLit(1))), 'D35_add_self_to_shift'))

    # ── Subtraction identities ──
    if name == 'sub' and len(args) == 2:
        lhs, rhs = args
        if _is_lit(rhs, 0):
            results.append((lhs, 'D35_sub_zero'))
        if lhs.canon() == rhs.canon():
            results.append((OLit(0), 'D35_sub_self'))

    # ── Exponentiation ──
    if name == 'pow' and len(args) == 2:
        base, exp = args
        # x ** 0 → 1
        if _is_lit(exp, 0):
            results.append((OLit(1), 'D35_pow_zero'))
        # x ** 1 → x
        if _is_lit(exp, 1):
            results.append((base, 'D35_pow_one'))
        # x ** 2 → x * x
        if _is_lit(exp, 2):
            results.append((OOp('mult', (base, base)), 'D35_pow2_to_mul'))
        # abs(x) ** 2 → x ** 2
        if (_is_lit(exp, 2) and isinstance(base, OOp)
                and base.name == 'abs' and len(base.args) == 1):
            results.append((
                OOp('pow', (base.args[0], OLit(2))),
                'D35_abs_sq',
            ))

    # ── x * x → x ** 2 (reverse of pow2_to_mul) ──
    if name in ('mult', 'mul') and len(args) == 2:
        lhs, rhs = args
        if lhs.canon() == rhs.canon():
            results.append((OOp('pow', (lhs, OLit(2))), 'D35_self_mul_to_pow2'))

    # ── Integer division by power of 2 → right shift ──
    if name in ('floordiv', 'div') and len(args) == 2:
        lhs, rhs = args
        if isinstance(rhs, OLit) and isinstance(rhs.value, int):
            k = _is_power_of_2(rhs.value)
            if k is not None:
                results.append((
                    OOp('rshift', (lhs, OLit(k))),
                    'D35_div_pow2_to_rshift',
                ))

    # ── Right shift → integer division (reverse) ──
    if name == 'rshift' and len(args) == 2:
        lhs, rhs = args
        if isinstance(rhs, OLit) and isinstance(rhs.value, int):
            k = rhs.value
            results.append((
                OOp('floordiv', (lhs, OLit(2 ** k))),
                'D35_rshift_to_div',
            ))

    # ── Left shift → multiply (reverse) ──
    if name == 'lshift' and len(args) == 2:
        lhs, rhs = args
        if isinstance(rhs, OLit) and isinstance(rhs.value, int):
            k = rhs.value
            results.append((
                OOp('mult', (lhs, OLit(2 ** k))),
                'D35_lshift_to_mul',
            ))

    # ── Modulo by power of 2 → bitwise AND ──
    if name == 'mod' and len(args) == 2:
        lhs, rhs = args
        if isinstance(rhs, OLit) and isinstance(rhs.value, int):
            k = _is_power_of_2(rhs.value)
            if k is not None:
                results.append((
                    OOp('bitand', (lhs, OLit(rhs.value - 1))),
                    'D35_mod_pow2_to_and',
                ))

    # ── Bitwise AND with 2^k-1 → modulo (reverse) ──
    if name == 'bitand' and len(args) == 2:
        lhs, rhs = args
        if isinstance(rhs, OLit) and isinstance(rhs.value, int):
            mask = rhs.value
            if mask > 0 and _is_power_of_2(mask + 1) is not None:
                results.append((
                    OOp('mod', (lhs, OLit(mask + 1))),
                    'D35_and_to_mod',
                ))

    # ── abs(x) ** 2 → x ** 2 (standalone abs detection) ──
    if name == 'abs' and len(args) == 1:
        inner = args[0]
        # Mark for potential absorption with squaring
        results.append((
            OOp('abs_mark', (inner,)),
            'D35_abs_annotate',
        ))

    # ── Horner's rule detection ──
    # Pattern: a0 + a1*x + a2*x**2 + ... → horner(coeffs, x)
    # Simplified: detect a + x*(b + x*c) form
    horner = _detect_horner(term)
    if horner is not None:
        coeffs, var = horner
        results.append((
            OOp('horner', (OSeq(tuple(OLit(c) for c in coeffs)), var)),
            'D35_to_horner',
        ))

    # ── Horner expansion (reverse) ──
    if name == 'horner' and len(args) == 2:
        if isinstance(args[0], OSeq):
            coeffs = args[0].elements
            var = args[1]
            poly = _expand_horner(coeffs, var)
            results.append((poly, 'D35_horner_expand'))

    return results


def _detect_horner(term: OTerm) -> Optional[Tuple[List[Any], OTerm]]:
    """Detect a + x*(b + x*c) Horner form, return (coeffs, x)."""
    # Simple detection: a + x * (b + x * c)
    if not isinstance(term, OOp) or term.name != 'add' or len(term.args) != 2:
        return None
    a_term, mul_term = term.args
    if not isinstance(a_term, OLit):
        return None
    if not isinstance(mul_term, OOp) or mul_term.name not in ('mult', 'mul'):
        return None
    if len(mul_term.args) != 2:
        return None
    x_term, inner = mul_term.args
    # inner could be a literal (2 terms) or another horner step
    if isinstance(inner, OLit):
        return ([a_term.value, inner.value], x_term)
    inner_horner = _detect_horner(inner)
    if inner_horner is not None:
        coeffs, x2 = inner_horner
        if x2.canon() == x_term.canon():
            return ([a_term.value] + coeffs, x_term)
    return None


def _expand_horner(coeffs: Tuple[OTerm, ...], var: OTerm) -> OTerm:
    """Expand Horner form to naive polynomial."""
    if not coeffs:
        return OLit(0)
    result: OTerm = coeffs[-1]
    for c in reversed(coeffs[:-1]):
        result = OOp('add', (c, OOp('mult', (var, result))))
    return result


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D35 in reverse: cheaper ops → original form."""
    results = apply(term, ctx)
    inverse_labels = {
        'D35_lshift_to_mul',
        'D35_rshift_to_div',
        'D35_and_to_mod',
        'D35_self_mul_to_pow2',
        'D35_add_self_to_shift',
        'D35_horner_expand',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D35 is potentially applicable to *term*."""
    if not isinstance(term, OOp):
        return False
    name = term.name
    args = term.args
    if name in ('mult', 'mul') and len(args) == 2:
        return True
    if name == 'add' and len(args) == 2:
        if _is_lit(args[0], 0) or _is_lit(args[1], 0):
            return True
        if args[0].canon() == args[1].canon():
            return True
    if name == 'sub' and len(args) == 2:
        if _is_lit(args[1], 0) or args[0].canon() == args[1].canon():
            return True
    if name == 'pow' and len(args) == 2:
        return True
    if name in ('floordiv', 'div') and len(args) == 2:
        if isinstance(args[1], OLit) and isinstance(args[1].value, int):
            if _is_power_of_2(args[1].value) is not None:
                return True
    if name in ('lshift', 'rshift'):
        return True
    if name == 'mod' and len(args) == 2:
        if isinstance(args[1], OLit) and isinstance(args[1].value, int):
            if _is_power_of_2(args[1].value) is not None:
                return True
    if name == 'bitand' and len(args) == 2:
        if isinstance(args[1], OLit) and isinstance(args[1].value, int):
            mask = args[1].value
            if mask > 0 and _is_power_of_2(mask + 1) is not None:
                return True
    if name == 'abs':
        return True
    if name == 'horner':
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D35 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    arith_kw = ('mult(', 'mul(', 'pow(', 'floordiv(', 'mod(', 'abs(')
    bit_kw = ('lshift(', 'rshift(', 'bitand(', 'bitor(')
    horner_kw = ('horner(',)

    has_arith_s = any(k in sc for k in arith_kw)
    has_arith_t = any(k in tc for k in arith_kw)
    has_bit_s = any(k in sc for k in bit_kw)
    has_bit_t = any(k in tc for k in bit_kw)
    has_horner = any(k in sc or k in tc for k in horner_kw)

    if (has_arith_s and has_bit_t) or (has_bit_s and has_arith_t):
        return 0.95
    if has_horner:
        return 0.90
    if has_arith_s and has_arith_t:
        return 0.70
    if has_bit_s and has_bit_t:
        return 0.60
    if has_arith_s or has_arith_t or has_bit_s or has_bit_t:
        return 0.40
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    ctx = FiberCtx()
    x = OVar('x')

    # ── x * 2 → x + x, x << 1 ──
    print("D35: x * 2 → x + x, x << 1 ...")
    mul2 = OOp('mult', (x, OLit(2)))
    r = apply(mul2, ctx)
    _assert(any(lbl == 'D35_mul2_to_add' for _, lbl in r), "mul2→add")
    _assert(any(lbl == 'D35_mul2_to_shift' for _, lbl in r), "mul2→shift")
    add_results = [t for t, lbl in r if lbl == 'D35_mul2_to_add']
    _assert(len(add_results) >= 1 and isinstance(add_results[0], OOp)
            and add_results[0].name == 'add', "mul2→add yields OOp('add',...)")

    # ── x * 0 → 0 ──
    print("D35: x * 0 → 0 ...")
    mul0 = OOp('mult', (x, OLit(0)))
    r2 = apply(mul0, ctx)
    _assert(any(lbl == 'D35_mul_zero' for _, lbl in r2), "mul_zero")
    zero_results = [t for t, lbl in r2 if lbl == 'D35_mul_zero']
    _assert(len(zero_results) >= 1 and _is_lit(zero_results[0], 0), "mul0→0")

    # ── x * 1 → x ──
    print("D35: x * 1 → x ...")
    mul1 = OOp('mult', (x, OLit(1)))
    r3 = apply(mul1, ctx)
    _assert(any(lbl == 'D35_mul_one' for _, lbl in r3), "mul_one")

    # ── x ** 2 → x * x ──
    print("D35: x ** 2 → x * x ...")
    pow2 = OOp('pow', (x, OLit(2)))
    r4 = apply(pow2, ctx)
    _assert(any(lbl == 'D35_pow2_to_mul' for _, lbl in r4), "pow2→mul")

    # ── x * x → x ** 2 (reverse) ──
    print("D35: x * x → x ** 2 ...")
    self_mul = OOp('mult', (x, x))
    r5 = apply(self_mul, ctx)
    _assert(any(lbl == 'D35_self_mul_to_pow2' for _, lbl in r5), "mul→pow2")

    # ── x // 2 → x >> 1 ──
    print("D35: x // 2 → x >> 1 ...")
    div2 = OOp('floordiv', (x, OLit(2)))
    r6 = apply(div2, ctx)
    _assert(any(lbl == 'D35_div_pow2_to_rshift' for _, lbl in r6), "div2→rshift")

    # ── x >> 1 → x // 2 (reverse) ──
    print("D35: x >> 1 → x // 2 ...")
    rshift1 = OOp('rshift', (x, OLit(1)))
    r7 = apply(rshift1, ctx)
    _assert(any(lbl == 'D35_rshift_to_div' for _, lbl in r7), "rshift→div")

    # ── x % 2 → x & 1 ──
    print("D35: x % 2 → x & 1 ...")
    mod2 = OOp('mod', (x, OLit(2)))
    r8 = apply(mod2, ctx)
    _assert(any(lbl == 'D35_mod_pow2_to_and' for _, lbl in r8), "mod2→and")

    # ── x & 1 → x % 2 (reverse) ──
    print("D35: x & 1 → x % 2 ...")
    and1 = OOp('bitand', (x, OLit(1)))
    r9 = apply(and1, ctx)
    _assert(any(lbl == 'D35_and_to_mod' for _, lbl in r9), "and→mod")

    # ── Roundtrip: x * 2 → x << 1 → x * 2 ──
    print("D35: roundtrip mul2 ↔ shift ...")
    shifted = [t for t, lbl in r if lbl == 'D35_mul2_to_shift']
    _assert(len(shifted) >= 1, "roundtrip step 1")
    back = apply(shifted[0], ctx)
    _assert(any(lbl == 'D35_lshift_to_mul' for _, lbl in back), "roundtrip step 2")

    # ── x + 0 → x ──
    print("D35: x + 0 → x ...")
    add0 = OOp('add', (x, OLit(0)))
    r10 = apply(add0, ctx)
    _assert(any(lbl == 'D35_add_zero' for _, lbl in r10), "add_zero")

    # ── x - 0 → x ──
    print("D35: x - 0 → x ...")
    sub0 = OOp('sub', (x, OLit(0)))
    r11 = apply(sub0, ctx)
    _assert(any(lbl == 'D35_sub_zero' for _, lbl in r11), "sub_zero")

    # ── x - x → 0 ──
    print("D35: x - x → 0 ...")
    sub_self = OOp('sub', (x, x))
    r12 = apply(sub_self, ctx)
    _assert(any(lbl == 'D35_sub_self' for _, lbl in r12), "sub_self")

    # ── x ** 0 → 1 ──
    print("D35: x ** 0 → 1 ...")
    pow0 = OOp('pow', (x, OLit(0)))
    r13 = apply(pow0, ctx)
    _assert(any(lbl == 'D35_pow_zero' for _, lbl in r13), "pow_zero")

    # ── x ** 1 → x ──
    print("D35: x ** 1 → x ...")
    pow1 = OOp('pow', (x, OLit(1)))
    r14 = apply(pow1, ctx)
    _assert(any(lbl == 'D35_pow_one' for _, lbl in r14), "pow_one")

    # ── abs(x) ** 2 → x ** 2 ──
    print("D35: abs(x) ** 2 → x ** 2 ...")
    abs_sq = OOp('pow', (OOp('abs', (x,)), OLit(2)))
    r15 = apply(abs_sq, ctx)
    _assert(any(lbl == 'D35_abs_sq' for _, lbl in r15), "abs_sq")

    # ── x * 8 → x << 3 ──
    print("D35: x * 8 → x << 3 ...")
    mul8 = OOp('mult', (x, OLit(8)))
    r16 = apply(mul8, ctx)
    _assert(any(lbl == 'D35_mul_pow2_to_shift' for _, lbl in r16), "mul8→shift")
    shift_results = [t for t, lbl in r16 if lbl == 'D35_mul_pow2_to_shift']
    _assert(len(shift_results) >= 1, "got shift result for mul8")

    # ── x % 4 → x & 3 ──
    print("D35: x % 4 → x & 3 ...")
    mod4 = OOp('mod', (x, OLit(4)))
    r17 = apply(mod4, ctx)
    _assert(any(lbl == 'D35_mod_pow2_to_and' for _, lbl in r17), "mod4→and3")

    # ── recognizes() ──
    print("D35: recognizes ...")
    _assert(recognizes(mul2), "recognizes mult")
    _assert(recognizes(pow2), "recognizes pow")
    _assert(recognizes(div2), "recognizes floordiv")
    _assert(recognizes(mod2), "recognizes mod")
    _assert(recognizes(rshift1), "recognizes rshift")
    _assert(recognizes(and1), "recognizes bitand")
    _assert(not recognizes(OOp('sorted', (x,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D35: relevance_score ...")
    score = relevance_score(mul2, rshift1)
    _assert(score > 0.8, f"mult↔shift score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (x,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D35: apply_inverse ...")
    inv = apply_inverse(rshift1, ctx)
    _assert(any(lbl == 'D35_rshift_to_div' for _, lbl in inv), "inverse rshift→div")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D35 strength_reduce: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
