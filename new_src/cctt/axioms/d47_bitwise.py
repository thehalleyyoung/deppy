"""D47: Bit Manipulation Equivalences (Theorem 29.5.1).

Bitwise operations correspond to arithmetic operations on
non-negative integers via the binary representation.

Mathematical foundation:
  Non-negative integers are isomorphic to finite bit-strings
  via binary representation:
    n = Σ_{i=0}^{k} b_i · 2^i  where b_i ∈ {0, 1}

  Bitwise operations (AND, OR, XOR, NOT, SHIFT) correspond to
  arithmetic operations through this isomorphism.

  Key correspondences:
  - x & (x-1): clears the lowest set bit (Wegner 1960)
  - x | (x-1): sets all bits below lowest set bit
  - popcount: number of 1-bits = Hamming weight
  - Shifts ↔ multiplication/division by powers of 2
  - XOR is self-inverse: x ⊕ y ⊕ x = y
  - NOT corresponds to two's complement negation minus 1

  IMPORTANT: Most equivalences require x ≥ 0.  For negative
  numbers, Python uses arbitrary-precision two's complement.

Covers:
  • x & (x-1) ↔ clear lowest set bit
  • x | (x-1) ↔ set bits below lowest set bit
  • popcount: bin(x).count('1') ↔ Brian Kernighan's algorithm
  • x & 1 ↔ x % 2 (non-negative)
  • x << n ↔ x * 2**n (non-negative)
  • x >> n ↔ x // 2**n (non-negative)
  • ~x ↔ -(x+1) (two's complement)
  • x ^ y ^ x → y (XOR self-inverse)
  • Power-of-2 test: x & (x-1) == 0
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

AXIOM_NAME = 'D47_bitwise'
AXIOM_CATEGORY = 'logical_bitwise'  # §29

SOUNDNESS_PROOF = """
Theorem 29.5.1 (Bit Shift ↔ Multiplication/Division):
  For non-negative integers x, n:
    x << n  =  x · 2^n
    x >> n  =  ⌊x / 2^n⌋

Proof:
  x = Σ b_i · 2^i.
  x << n = Σ b_i · 2^{i+n} = 2^n · Σ b_i · 2^i = 2^n · x.
  x >> n = Σ_{i≥n} b_i · 2^{i-n} = ⌊x / 2^n⌋.  ∎

Theorem 29.5.2 (Parity: Bit AND ↔ Modulo):
  For non-negative integer x:
    x & 1  =  x mod 2

Proof:
  x & 1 extracts bit b_0.  x mod 2 = b_0 since x = 2·⌊x/2⌋ + b_0.  ∎

Theorem 29.5.3 (Clear Lowest Set Bit):
  x & (x - 1)  clears the lowest set bit of x.

Proof:
  Let x = a·2^k where a is odd and k is the position of the lowest
  set bit.  Then x - 1 = a·2^k - 1, which flips bit k and all bits
  below it.  AND with x clears bit k.  ∎

Theorem 29.5.4 (Popcount Equivalence):
  bin(x).count('1') = popcount_kernighan(x)

Proof:
  Brian Kernighan's algorithm repeatedly clears the lowest set bit
  via x &= x - 1, counting iterations.  Each iteration removes
  exactly one 1-bit.  The total count equals the number of 1-bits,
  which is also bin(x).count('1').  ∎

Theorem 29.5.5 (XOR Self-Inverse):
  x ⊕ y ⊕ x = y

Proof:
  XOR is associative and commutative with identity 0.
  x ⊕ x = 0 (self-inverse).
  Therefore x ⊕ y ⊕ x = (x ⊕ x) ⊕ y = 0 ⊕ y = y.  ∎

Theorem 29.5.6 (Two's Complement NOT):
  ~x = -(x + 1)

Proof:
  In two's complement, ~x inverts all bits.
  x + ~x = -1 (all bits set).  Therefore ~x = -1 - x = -(x+1).  ∎

Theorem 29.5.7 (Power of Two Test):
  x > 0 and (x & (x-1)) == 0  iff  x is a power of 2.

Proof:
  If x = 2^k, then x has exactly one set bit.  x & (x-1) clears it,
  giving 0.  Conversely, if x & (x-1) = 0, then x has at most one
  set bit, so x = 2^k for some k.  ∎
"""

COMPOSES_WITH = ['D48_demorgan', 'D02_beta', 'D17_assoc']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Clear lowest set bit',
        'before': "clear_lowest_bit(x)",
        'after': "x & (x - 1)",
        'axiom': 'D47_clear_lowest_bit',
    },
    {
        'name': 'Popcount: string count to Kernighan',
        'before': "bin(x).count('1')",
        'after': "popcount_kernighan(x)",
        'axiom': 'D47_popcount_str_to_kern',
    },
    {
        'name': 'Parity: bit AND to modulo',
        'before': "x & 1",
        'after': "x % 2",
        'axiom': 'D47_parity_and_to_mod',
        'precondition': 'x >= 0',
    },
    {
        'name': 'Left shift to multiply',
        'before': "x << n",
        'after': "x * (2 ** n)",
        'axiom': 'D47_lshift_to_mult',
        'precondition': 'x >= 0, n >= 0',
    },
    {
        'name': 'Right shift to floor divide',
        'before': "x >> n",
        'after': "x // (2 ** n)",
        'axiom': 'D47_rshift_to_div',
        'precondition': 'x >= 0, n >= 0',
    },
    {
        'name': 'NOT to negation',
        'before': "~x",
        'after': "-(x + 1)",
        'axiom': 'D47_not_to_neg',
    },
    {
        'name': 'XOR self-inverse',
        'before': "x ^ y ^ x",
        'after': "y",
        'axiom': 'D47_xor_self_inverse',
    },
    {
        'name': 'Power of two test',
        'before': "is_power_of_two(x)",
        'after': "x > 0 and (x & (x - 1)) == 0",
        'axiom': 'D47_power_of_two',
    },
]

# ── Known bitwise operation names ──
BITWISE_OPS: FrozenSet[str] = frozenset({
    'bitand', 'bitor', 'bitxor', 'invert',
    'lshift', 'rshift',
    'popcount', 'popcount_kernighan', 'bit_count',
    'clear_lowest_bit', 'set_below_lowest',
    'is_power_of_two', 'highest_bit', 'lowest_bit',
    'u_invert',
})

# ── Arithmetic equivalents ──
ARITHMETIC_EQUIV: FrozenSet[str] = frozenset({
    'mod', 'mult', 'floordiv', 'pow',
    'u_usub',
})


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract all free variable names."""
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


# ═══════════════════════════════════════════════════════════
# Pattern detection
# ═══════════════════════════════════════════════════════════

def _is_clear_lowest_bit(term: OTerm) -> bool:
    """Detect x & (x - 1) pattern."""
    if isinstance(term, OOp) and term.name == 'bitand' and len(term.args) == 2:
        x, sub = term.args
        if isinstance(sub, OOp) and sub.name == 'sub' and len(sub.args) == 2:
            if sub.args[1] == OLit(1) and sub.args[0] == x:
                return True
    if isinstance(term, OOp) and term.name == 'clear_lowest_bit':
        return True
    return False


def _is_set_below_lowest(term: OTerm) -> bool:
    """Detect x | (x - 1) pattern."""
    if isinstance(term, OOp) and term.name == 'bitor' and len(term.args) == 2:
        x, sub = term.args
        if isinstance(sub, OOp) and sub.name == 'sub' and len(sub.args) == 2:
            if sub.args[1] == OLit(1) and sub.args[0] == x:
                return True
    if isinstance(term, OOp) and term.name == 'set_below_lowest':
        return True
    return False


def _is_parity_check(term: OTerm) -> bool:
    """Detect x & 1 or x % 2 patterns."""
    if isinstance(term, OOp) and term.name == 'bitand' and len(term.args) == 2:
        if term.args[1] == OLit(1):
            return True
    if isinstance(term, OOp) and term.name == 'mod' and len(term.args) == 2:
        if term.args[1] == OLit(2):
            return True
    return False


def _is_shift_pattern(term: OTerm) -> bool:
    """Detect left/right shift patterns."""
    if isinstance(term, OOp) and term.name in ('lshift', 'rshift'):
        return True
    return False


def _is_popcount(term: OTerm) -> bool:
    """Detect popcount / bit_count patterns."""
    if isinstance(term, OOp) and term.name in ('popcount', 'popcount_kernighan',
                                                 'bit_count', '.bit_count'):
        return True
    # bin(x).count('1') pattern
    if isinstance(term, OOp) and term.name == '.count':
        if len(term.args) >= 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'bin':
                return True
    return False


def _is_xor_self_inverse(term: OTerm) -> bool:
    """Detect x ^ y ^ x → y pattern."""
    if isinstance(term, OOp) and term.name == 'bitxor' and len(term.args) == 2:
        a, b = term.args
        if isinstance(b, OOp) and b.name == 'bitxor' and len(b.args) == 2:
            if b.args[1] == a:
                return True
        if isinstance(a, OOp) and a.name == 'bitxor' and len(a.args) == 2:
            if a.args[0] == b:
                return True
    return False


def _is_not_pattern(term: OTerm) -> bool:
    """Detect bitwise NOT (~x) or -(x+1) patterns."""
    if isinstance(term, OOp) and term.name in ('u_invert', 'invert'):
        return True
    return False


def _is_power_of_two_test(term: OTerm) -> bool:
    """Detect x & (x-1) == 0 pattern."""
    if isinstance(term, OOp) and term.name in ('eq', 'is_power_of_two'):
        if term.name == 'is_power_of_two':
            return True
        if len(term.args) == 2 and term.args[1] == OLit(0):
            if _is_clear_lowest_bit(term.args[0]):
                return True
    return False


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D47 bitwise ↔ arithmetic equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── x & (x-1) ↔ clear lowest set bit ──
    if _is_clear_lowest_bit(term):
        if isinstance(term, OOp) and term.name == 'bitand':
            x = term.args[0]
            results.append((
                OOp('clear_lowest_bit', (x,)),
                'D47_clear_lowest_bit',
            ))
        elif isinstance(term, OOp) and term.name == 'clear_lowest_bit':
            x = term.args[0] if term.args else OVar('x')
            results.append((
                OOp('bitand', (x, OOp('sub', (x, OLit(1))))),
                'D47_clear_lowest_bit_expand',
            ))

    # ── x | (x-1) ↔ set below lowest ──
    if _is_set_below_lowest(term):
        if isinstance(term, OOp) and term.name == 'bitor':
            x = term.args[0]
            results.append((
                OOp('set_below_lowest', (x,)),
                'D47_set_below_lowest',
            ))
        elif isinstance(term, OOp) and term.name == 'set_below_lowest':
            x = term.args[0] if term.args else OVar('x')
            results.append((
                OOp('bitor', (x, OOp('sub', (x, OLit(1))))),
                'D47_set_below_lowest_expand',
            ))

    # ── Parity: x & 1 ↔ x % 2 ──
    if _is_parity_check(term):
        x = term.args[0]
        if term.name == 'bitand':
            results.append((
                OOp('mod', (x, OLit(2))),
                'D47_parity_and_to_mod',
            ))
        elif term.name == 'mod':
            results.append((
                OOp('bitand', (x, OLit(1))),
                'D47_parity_mod_to_and',
            ))

    # ── Left shift ↔ multiply by power of 2 ──
    if isinstance(term, OOp) and term.name == 'lshift' and len(term.args) == 2:
        x, n = term.args
        results.append((
            OOp('mult', (x, OOp('pow', (OLit(2), n)))),
            'D47_lshift_to_mult',
        ))
    if isinstance(term, OOp) and term.name == 'mult' and len(term.args) == 2:
        x, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'pow' and len(rhs.args) == 2:
            if rhs.args[0] == OLit(2):
                results.append((
                    OOp('lshift', (x, rhs.args[1])),
                    'D47_mult_to_lshift',
                ))

    # ── Right shift ↔ floor divide by power of 2 ──
    if isinstance(term, OOp) and term.name == 'rshift' and len(term.args) == 2:
        x, n = term.args
        results.append((
            OOp('floordiv', (x, OOp('pow', (OLit(2), n)))),
            'D47_rshift_to_div',
        ))
    if isinstance(term, OOp) and term.name == 'floordiv' and len(term.args) == 2:
        x, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'pow' and len(rhs.args) == 2:
            if rhs.args[0] == OLit(2):
                results.append((
                    OOp('rshift', (x, rhs.args[1])),
                    'D47_div_to_rshift',
                ))

    # ── Popcount equivalences ──
    if _is_popcount(term):
        free = sorted(_extract_free_vars(term))
        x_term = OVar(free[0]) if free else OVar('x')
        if isinstance(term, OOp) and term.name in ('popcount', 'bit_count', '.bit_count'):
            results.append((
                OOp('popcount_kernighan', (x_term,)),
                'D47_popcount_to_kern',
            ))
        if isinstance(term, OOp) and term.name == 'popcount_kernighan':
            results.append((
                OOp('popcount', (x_term,)),
                'D47_kern_to_popcount',
            ))
        # bin(x).count('1') → popcount
        if isinstance(term, OOp) and term.name == '.count':
            results.append((
                OOp('popcount', (x_term,)),
                'D47_popcount_str_to_kern',
            ))

    # ── NOT: ~x ↔ -(x+1) ──
    if _is_not_pattern(term):
        x = term.args[0] if term.args else OVar('x')
        results.append((
            OOp('u_usub', (OOp('add', (x, OLit(1))),)),
            'D47_not_to_neg',
        ))
    if isinstance(term, OOp) and term.name == 'u_usub' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'add' and len(inner.args) == 2:
            if inner.args[1] == OLit(1):
                results.append((
                    OOp('u_invert', (inner.args[0],)),
                    'D47_neg_to_not',
                ))

    # ── XOR self-inverse: x ^ y ^ x → y ──
    if _is_xor_self_inverse(term):
        a, b = term.args
        if isinstance(b, OOp) and b.name == 'bitxor':
            y = b.args[0]
        elif isinstance(a, OOp) and a.name == 'bitxor':
            y = a.args[1]
        else:
            y = OVar('y')
        results.append((y, 'D47_xor_self_inverse'))

    # ── Power of two test ──
    if _is_power_of_two_test(term):
        if isinstance(term, OOp) and term.name == 'is_power_of_two':
            x = term.args[0] if term.args else OVar('x')
            results.append((
                OOp('and', (
                    OOp('gt', (x, OLit(0))),
                    OOp('eq', (OOp('bitand', (x, OOp('sub', (x, OLit(1))))), OLit(0))),
                )),
                'D47_power_of_two_expand',
            ))
        else:
            # eq(bitand(x, sub(x, 1)), 0) → is_power_of_two
            if isinstance(term, OOp) and term.name == 'eq':
                clb = term.args[0]
                if isinstance(clb, OOp) and clb.name == 'bitand':
                    x = clb.args[0]
                    results.append((
                        OOp('is_power_of_two', (x,)),
                        'D47_power_of_two',
                    ))

    # ── Abstract specs ──
    if isinstance(term, OAbstract):
        if 'popcount' in term.spec or 'bit_count' in term.spec:
            results.append((OOp('popcount', term.inputs), 'D47_spec_to_popcount'))
            results.append((OOp('popcount_kernighan', term.inputs), 'D47_spec_to_kern'))
        if 'parity' in term.spec:
            x = term.inputs[0] if term.inputs else OVar('x')
            results.append((OOp('bitand', (x, OLit(1))), 'D47_spec_to_parity_and'))
            results.append((OOp('mod', (x, OLit(2))), 'D47_spec_to_parity_mod'))
        if 'power_of_two' in term.spec:
            results.append((OOp('is_power_of_two', term.inputs), 'D47_spec_to_pow2'))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D47 in reverse: arithmetic → bitwise."""
    results = apply(term, ctx)
    inverse_labels = {
        'D47_clear_lowest_bit_expand',
        'D47_set_below_lowest_expand',
        'D47_parity_mod_to_and',
        'D47_mult_to_lshift',
        'D47_div_to_rshift',
        'D47_kern_to_popcount',
        'D47_neg_to_not',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D47 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in BITWISE_OPS:
            return True
        if term.name in ('bitand', 'bitor', 'bitxor'):
            return True
        if term.name in ('is_power_of_two',):
            return True
    if _is_clear_lowest_bit(term):
        return True
    if _is_set_below_lowest(term):
        return True
    if _is_parity_check(term):
        return True
    if _is_shift_pattern(term):
        return True
    if _is_popcount(term):
        return True
    if _is_xor_self_inverse(term):
        return True
    if _is_not_pattern(term):
        return True
    if _is_power_of_two_test(term):
        return True
    if isinstance(term, OAbstract):
        return any(kw in term.spec for kw in ('popcount', 'bit_count', 'parity',
                                               'power_of_two', 'bitwise'))
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D47 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    bit_kw = ['bitand', 'bitor', 'bitxor', 'invert', 'lshift', 'rshift',
              'popcount', 'bit_count', 'clear_lowest', 'set_below']
    arith_kw = ['mod', 'mult', 'floordiv', 'pow', 'u_usub', 'u_invert']

    has_bit_s = any(kw in sc for kw in bit_kw)
    has_bit_t = any(kw in tc for kw in bit_kw)
    has_arith_s = any(kw in sc for kw in arith_kw)
    has_arith_t = any(kw in tc for kw in arith_kw)

    # One bitwise, one arithmetic → high relevance
    if (has_bit_s and has_arith_t) or (has_arith_s and has_bit_t):
        return 0.95
    # Both bitwise
    if has_bit_s and has_bit_t:
        return 0.80
    # Both arithmetic (could be shift-equivalent)
    if has_arith_s and has_arith_t:
        return 0.30
    # One side has bit keyword
    if has_bit_s or has_bit_t:
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
    y = OVar('y')
    n = OVar('n')

    # ── Clear lowest bit: x & (x-1) → clear_lowest_bit ──
    print("D47: clear lowest bit ...")
    clb = OOp('bitand', (x, OOp('sub', (x, OLit(1)))))
    r_clb = apply(clb, ctx)
    _assert(any(lbl == 'D47_clear_lowest_bit' for _, lbl in r_clb),
            "x&(x-1)→clear_lowest_bit")

    # ── Clear lowest bit: clear_lowest_bit → expand ──
    clb_named = OOp('clear_lowest_bit', (x,))
    r_clbn = apply(clb_named, ctx)
    _assert(any(lbl == 'D47_clear_lowest_bit_expand' for _, lbl in r_clbn),
            "clear_lowest_bit→expand")

    # ── Set below lowest ──
    print("D47: set below lowest ...")
    sbl = OOp('bitor', (x, OOp('sub', (x, OLit(1)))))
    r_sbl = apply(sbl, ctx)
    _assert(any(lbl == 'D47_set_below_lowest' for _, lbl in r_sbl),
            "x|(x-1)→set_below_lowest")

    # ── Parity: x & 1 ↔ x % 2 ──
    print("D47: parity ...")
    par_and = OOp('bitand', (x, OLit(1)))
    r_pa = apply(par_and, ctx)
    _assert(any(lbl == 'D47_parity_and_to_mod' for _, lbl in r_pa),
            "x&1→x%2")

    par_mod = OOp('mod', (x, OLit(2)))
    r_pm = apply(par_mod, ctx)
    _assert(any(lbl == 'D47_parity_mod_to_and' for _, lbl in r_pm),
            "x%2→x&1")

    # ── Left shift ↔ multiply ──
    print("D47: left shift ↔ multiply ...")
    lsh = OOp('lshift', (x, n))
    r_ls = apply(lsh, ctx)
    _assert(any(lbl == 'D47_lshift_to_mult' for _, lbl in r_ls),
            "x<<n→x*2^n")

    mul_pow = OOp('mult', (x, OOp('pow', (OLit(2), n))))
    r_mp = apply(mul_pow, ctx)
    _assert(any(lbl == 'D47_mult_to_lshift' for _, lbl in r_mp),
            "x*2^n→x<<n")

    # ── Right shift ↔ floor divide ──
    print("D47: right shift ↔ floor divide ...")
    rsh = OOp('rshift', (x, n))
    r_rs = apply(rsh, ctx)
    _assert(any(lbl == 'D47_rshift_to_div' for _, lbl in r_rs),
            "x>>n→x//2^n")

    div_pow = OOp('floordiv', (x, OOp('pow', (OLit(2), n))))
    r_dp = apply(div_pow, ctx)
    _assert(any(lbl == 'D47_div_to_rshift' for _, lbl in r_dp),
            "x//2^n→x>>n")

    # ── Popcount ──
    print("D47: popcount ...")
    pc = OOp('popcount', (x,))
    r_pc = apply(pc, ctx)
    _assert(any(lbl == 'D47_popcount_to_kern' for _, lbl in r_pc),
            "popcount→kernighan")

    kern = OOp('popcount_kernighan', (x,))
    r_kn = apply(kern, ctx)
    _assert(any(lbl == 'D47_kern_to_popcount' for _, lbl in r_kn),
            "kernighan→popcount")

    # ── NOT ↔ negation ──
    print("D47: NOT ↔ negation ...")
    not_x = OOp('u_invert', (x,))
    r_not = apply(not_x, ctx)
    _assert(any(lbl == 'D47_not_to_neg' for _, lbl in r_not),
            "~x→-(x+1)")

    neg_x = OOp('u_usub', (OOp('add', (x, OLit(1))),))
    r_neg = apply(neg_x, ctx)
    _assert(any(lbl == 'D47_neg_to_not' for _, lbl in r_neg),
            "-(x+1)→~x")

    # ── XOR self-inverse ──
    print("D47: XOR self-inverse ...")
    xor_term = OOp('bitxor', (x, OOp('bitxor', (y, x))))
    r_xor = apply(xor_term, ctx)
    _assert(any(lbl == 'D47_xor_self_inverse' for _, lbl in r_xor),
            "x^y^x→y")

    # ── Power of two test ──
    print("D47: power of two ...")
    p2_test = OOp('is_power_of_two', (x,))
    r_p2 = apply(p2_test, ctx)
    _assert(any(lbl == 'D47_power_of_two_expand' for _, lbl in r_p2),
            "is_power_of_two→expand")

    p2_expand = OOp('eq', (OOp('bitand', (x, OOp('sub', (x, OLit(1))))), OLit(0)))
    r_p2e = apply(p2_expand, ctx)
    _assert(any(lbl == 'D47_power_of_two' for _, lbl in r_p2e),
            "expand→is_power_of_two")

    # ── Abstract spec ──
    print("D47: abstract spec ...")
    spec_pc = OAbstract('popcount_bits', (x,))
    r_spc = apply(spec_pc, ctx)
    _assert(any(lbl == 'D47_spec_to_popcount' for _, lbl in r_spc), "spec→popcount")
    _assert(any(lbl == 'D47_spec_to_kern' for _, lbl in r_spc), "spec→kern")

    # ── recognizes ──
    print("D47: recognizes ...")
    _assert(recognizes(clb), "recognizes clear lowest bit")
    _assert(recognizes(par_and), "recognizes parity AND")
    _assert(recognizes(par_mod), "recognizes parity mod")
    _assert(recognizes(lsh), "recognizes left shift")
    _assert(recognizes(pc), "recognizes popcount")
    _assert(recognizes(not_x), "recognizes NOT")
    _assert(recognizes(xor_term), "recognizes XOR self-inverse")
    _assert(not recognizes(OOp('sorted', (x,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D47: relevance_score ...")
    score = relevance_score(
        OOp('lshift', (x, n)),
        OOp('mult', (x, OOp('pow', (OLit(2), n)))),
    )
    _assert(score > 0.9, f"bit↔arith score={score:.2f} > 0.9")

    low = relevance_score(OOp('sorted', (x,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D47: apply_inverse ...")
    inv_pm = apply_inverse(par_mod, ctx)
    _assert(len(inv_pm) >= 1, "inverse mod→and")

    inv_mp = apply_inverse(mul_pow, ctx)
    _assert(len(inv_mp) >= 1, "inverse mult→lshift")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D47 bitwise: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
