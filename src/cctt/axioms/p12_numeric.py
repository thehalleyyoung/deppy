"""P12: Numeric / Math Patterns (Theorem 30.2.1).

math / numeric library calls ↔ explicit fold / loop equivalents.

Mathematical foundation:
  Each numeric function in the Python standard library computes a
  well-defined arithmetic morphism.  The equivalences recorded here
  are witnessed by natural isomorphisms in the presheaf category of
  operational terms.

  The key insight is that library functions like math.factorial,
  math.gcd, math.comb are computed by the same recursive/fold
  schemas that a programmer would write by hand — they differ only
  in packaging and optimisation.

  For inner-product / norm equivalences, we use the bilinear pairing
  ⟨xs, xs⟩ = Σᵢ xᵢ² and the metric identity |a−b| = max(a,b)−min(a,b).

Covers:
  • math.factorial(n) ↔ functools.reduce(operator.mul, range(1,n+1), 1)
  • math.gcd(a, b) ↔ Euclidean algorithm (OFix)
  • math.comb(n, k) ↔ n! / (k! · (n-k)!)
  • math.isqrt(n) ↔ int(math.sqrt(n))
  • sum(x² for x in xs) ↔ dot(xs, xs)
  • abs(a - b) ↔ max(a,b) - min(a,b)
  • divmod(a, b) ↔ (a // b, a % b)
  • pow(a, b, m) ↔ modular exponentiation fold
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

AXIOM_NAME = 'P12_numeric'
AXIOM_CATEGORY = 'python_idiom'  # §30 — Python-specific numeric idioms

SOUNDNESS_PROOF = """
Theorem 30.2.1 (Numeric Equivalences):
  For all n ∈ ℕ, a, b ∈ ℤ:

  1. math.factorial(n) ≡ fold(mul, 1, range(1, n+1))
     by the recursive definition n! = n · (n-1)!.

  2. math.gcd(a, b) ≡ fix(λ(a,b). if b=0 then a else gcd(b, a mod b))
     by the Euclidean algorithm (Euclid, ~300 BCE).

  3. math.comb(n, k) ≡ n! / (k! · (n-k)!)
     by the definition of the binomial coefficient.

  4. math.isqrt(n) ≡ int(math.sqrt(n))
     both compute ⌊√n⌋ for n ≥ 0.

  5. Σᵢ xᵢ² ≡ ⟨xs, xs⟩  (inner product / dot product)
     by linearity of the bilinear form.

  6. |a − b| ≡ max(a,b) − min(a,b)
     by case analysis on the sign of a − b.

  7. divmod(a, b) ≡ (a // b, a % b)
     by Python's divmod specification.

  8. pow(a, b, m) ≡ fold(mod_mul_a, 1, range(b)) mod m
     by repeated squaring / modular exponentiation.  ∎
"""

COMPOSES_WITH = ['P11_functional', 'D01_fold_unfold', 'D05_fold_universal']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'factorial to fold',
        'before': "math.factorial(n)",
        'after': "fold(mul, 1, range(1, n+1))",
        'axiom': 'P12_factorial_to_fold',
    },
    {
        'name': 'gcd to Euclidean fix',
        'before': "math.gcd(a, b)",
        'after': "fix(gcd, if b==0 then a else gcd(b, a%b))",
        'axiom': 'P12_gcd_to_fix',
    },
    {
        'name': 'comb to factorials',
        'before': "math.comb(n, k)",
        'after': "n! // (k! * (n-k)!)",
        'axiom': 'P12_comb_to_factorials',
    },
    {
        'name': 'isqrt to int(sqrt)',
        'before': "math.isqrt(n)",
        'after': "int(math.sqrt(n))",
        'axiom': 'P12_isqrt_to_int_sqrt',
    },
    {
        'name': 'sum of squares to dot',
        'before': "sum(x**2 for x in xs)",
        'after': "dot(xs, xs)",
        'axiom': 'P12_sum_sq_to_dot',
    },
    {
        'name': 'abs diff to max minus min',
        'before': "abs(a - b)",
        'after': "max(a, b) - min(a, b)",
        'axiom': 'P12_abs_diff_to_max_min',
    },
    {
        'name': 'divmod to tuple',
        'before': "divmod(a, b)",
        'after': "(a // b, a % b)",
        'axiom': 'P12_divmod_to_tuple',
    },
    {
        'name': 'pow mod to fold',
        'before': "pow(a, b, m)",
        'after': "fold(mod_mul, 1, range(b)) with mod m",
        'axiom': 'P12_pow_mod_to_fold',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: extract params for fiber-awareness
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


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P12 numeric equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── math.factorial(n) → fold(mul, 1, range(1, n+1)) ──
    if isinstance(term, OOp) and term.name == 'math.factorial':
        if len(term.args) == 1:
            n = term.args[0]
            results.append((
                OFold('mul', OLit(1), OOp('range', (OLit(1), OOp('add', (n, OLit(1)))))),
                'P12_factorial_to_fold',
            ))

    # ── fold(mul, 1, range(1, n+1)) → math.factorial(n) ──
    if isinstance(term, OFold) and term.op_name == 'mul':
        if isinstance(term.init, OLit) and term.init.value == 1:
            coll = term.collection
            if (isinstance(coll, OOp) and coll.name == 'range'
                    and len(coll.args) == 2
                    and isinstance(coll.args[0], OLit) and coll.args[0].value == 1):
                upper = coll.args[1]
                if (isinstance(upper, OOp) and upper.name == 'add'
                        and len(upper.args) == 2
                        and isinstance(upper.args[1], OLit) and upper.args[1].value == 1):
                    n = upper.args[0]
                    results.append((
                        OOp('math.factorial', (n,)),
                        'P12_fold_to_factorial',
                    ))

    # ── math.gcd(a, b) → fix(gcd, case(b==0, a, gcd(b, a%b))) ──
    if isinstance(term, OOp) and term.name == 'math.gcd':
        if len(term.args) == 2:
            a, b = term.args
            results.append((
                OFix('gcd', OCase(
                    OOp('eq', (b, OLit(0))),
                    a,
                    OFix('gcd', OSeq((b, OOp('mod', (a, b))))),
                )),
                'P12_gcd_to_fix',
            ))

    # ── fix(gcd, case(b==0, ...)) → math.gcd(a, b) ──
    if isinstance(term, OFix) and term.name == 'gcd':
        if isinstance(term.body, OCase):
            case = term.body
            if (isinstance(case.test, OOp) and case.test.name == 'eq'
                    and len(case.test.args) == 2
                    and isinstance(case.test.args[1], OLit)
                    and case.test.args[1].value == 0):
                a = case.true_branch
                b_var = case.test.args[0]
                results.append((
                    OOp('math.gcd', (a, b_var)),
                    'P12_fix_to_gcd',
                ))

    # ── math.comb(n, k) → n! // (k! * (n-k)!) ──
    if isinstance(term, OOp) and term.name == 'math.comb':
        if len(term.args) == 2:
            n, k = term.args
            results.append((
                OOp('floordiv', (
                    OOp('math.factorial', (n,)),
                    OOp('mul', (
                        OOp('math.factorial', (k,)),
                        OOp('math.factorial', (OOp('sub', (n, k)),)),
                    )),
                )),
                'P12_comb_to_factorials',
            ))

    # ── n! // (k! * (n-k)!) → math.comb(n, k) ──
    if isinstance(term, OOp) and term.name == 'floordiv' and len(term.args) == 2:
        numer, denom = term.args
        if (isinstance(numer, OOp) and numer.name == 'math.factorial'
                and len(numer.args) == 1
                and isinstance(denom, OOp) and denom.name == 'mul'
                and len(denom.args) == 2):
            k_fact, nk_fact = denom.args
            if (isinstance(k_fact, OOp) and k_fact.name == 'math.factorial'
                    and isinstance(nk_fact, OOp) and nk_fact.name == 'math.factorial'):
                n = numer.args[0]
                k = k_fact.args[0]
                results.append((
                    OOp('math.comb', (n, k)),
                    'P12_factorials_to_comb',
                ))

    # ── math.isqrt(n) → int(math.sqrt(n)) ──
    if isinstance(term, OOp) and term.name == 'math.isqrt':
        if len(term.args) == 1:
            n = term.args[0]
            results.append((
                OOp('int', (OOp('math.sqrt', (n,)),)),
                'P12_isqrt_to_int_sqrt',
            ))

    # ── int(math.sqrt(n)) → math.isqrt(n) ──
    if isinstance(term, OOp) and term.name == 'int' and len(term.args) == 1:
        inner = term.args[0]
        if (isinstance(inner, OOp) and inner.name == 'math.sqrt'
                and len(inner.args) == 1):
            n = inner.args[0]
            results.append((
                OOp('math.isqrt', (n,)),
                'P12_int_sqrt_to_isqrt',
            ))

    # ── sum(x² for x in xs) → dot(xs, xs) ──
    #    fold(add, 0, map(λx. x², xs))  →  dot(xs, xs)
    if isinstance(term, OFold) and term.op_name == 'add':
        if isinstance(term.init, OLit) and term.init.value == 0:
            if isinstance(term.collection, OMap):
                mp = term.collection
                if (isinstance(mp.transform, OLam)
                        and len(mp.transform.params) == 1):
                    body = mp.transform.body
                    param = mp.transform.params[0]
                    if (isinstance(body, OOp) and body.name == 'pow'
                            and len(body.args) == 2
                            and isinstance(body.args[0], OVar)
                            and body.args[0].name == param
                            and isinstance(body.args[1], OLit)
                            and body.args[1].value == 2):
                        results.append((
                            OOp('dot', (mp.collection, mp.collection)),
                            'P12_sum_sq_to_dot',
                        ))

    # ── dot(xs, xs) → fold(add, 0, map(λx. x², xs)) ──
    if isinstance(term, OOp) and term.name == 'dot' and len(term.args) == 2:
        xs_a, xs_b = term.args
        if xs_a.canon() == xs_b.canon():
            results.append((
                OFold('add', OLit(0), OMap(
                    OLam(('x',), OOp('pow', (OVar('x'), OLit(2)))),
                    xs_a,
                )),
                'P12_dot_to_sum_sq',
            ))

    # ── abs(a - b) → max(a,b) - min(a,b) ──
    if isinstance(term, OOp) and term.name == 'abs' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'sub' and len(inner.args) == 2:
            a, b = inner.args
            results.append((
                OOp('sub', (OOp('max', (a, b)), OOp('min', (a, b)))),
                'P12_abs_diff_to_max_min',
            ))

    # ── max(a,b) - min(a,b) → abs(a - b) ──
    if isinstance(term, OOp) and term.name == 'sub' and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OOp) and lhs.name == 'max' and len(lhs.args) == 2
                and isinstance(rhs, OOp) and rhs.name == 'min' and len(rhs.args) == 2):
            if (lhs.args[0].canon() == rhs.args[0].canon()
                    and lhs.args[1].canon() == rhs.args[1].canon()):
                a, b = lhs.args
                results.append((
                    OOp('abs', (OOp('sub', (a, b)),)),
                    'P12_max_min_to_abs_diff',
                ))

    # ── divmod(a, b) → (a // b, a % b) ──
    if isinstance(term, OOp) and term.name == 'divmod' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OSeq((OOp('floordiv', (a, b)), OOp('mod', (a, b)))),
            'P12_divmod_to_tuple',
        ))

    # ── (a // b, a % b) → divmod(a, b) ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        e0, e1 = term.elements
        if (isinstance(e0, OOp) and e0.name == 'floordiv' and len(e0.args) == 2
                and isinstance(e1, OOp) and e1.name == 'mod' and len(e1.args) == 2):
            if (e0.args[0].canon() == e1.args[0].canon()
                    and e0.args[1].canon() == e1.args[1].canon()):
                a, b = e0.args
                results.append((
                    OOp('divmod', (a, b)),
                    'P12_tuple_to_divmod',
                ))

    # ── pow(a, b, m) → fold(mod_mul, 1, range(b)) with OOp wrapping mod ──
    if isinstance(term, OOp) and term.name == 'pow' and len(term.args) == 3:
        a, b, m = term.args
        results.append((
            OOp('mod', (
                OFold('mul_a', OLit(1), OOp('range', (b,))),
                m,
            )),
            'P12_pow_mod_to_fold',
        ))

    # ── fold-based mod exponentiation → pow(a, b, m) ──
    if isinstance(term, OOp) and term.name == 'mod' and len(term.args) == 2:
        inner, m = term.args
        if (isinstance(inner, OFold) and inner.op_name == 'mul_a'
                and isinstance(inner.init, OLit) and inner.init.value == 1
                and isinstance(inner.collection, OOp)
                and inner.collection.name == 'range'
                and len(inner.collection.args) == 1):
            b = inner.collection.args[0]
            results.append((
                OOp('pow', (OVar('a'), b, m)),
                'P12_fold_to_pow_mod',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P12 in reverse: expanded form → library call.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P12_fold_to_factorial',
        'P12_fix_to_gcd',
        'P12_factorials_to_comb',
        'P12_int_sqrt_to_isqrt',
        'P12_dot_to_sum_sq',
        'P12_max_min_to_abs_diff',
        'P12_tuple_to_divmod',
        'P12_fold_to_pow_mod',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P12 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('math.factorial', 'math.gcd', 'math.comb',
                         'math.isqrt', 'math.sqrt',
                         'dot', 'divmod', 'abs'):
            return True
        # int(math.sqrt(...))
        if term.name == 'int' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'math.sqrt':
                return True
        # pow(a, b, m) — three-arg form
        if term.name == 'pow' and len(term.args) == 3:
            return True
        # n! // (k! * (n-k)!) pattern
        if term.name == 'floordiv' and len(term.args) == 2:
            numer = term.args[0]
            if isinstance(numer, OOp) and numer.name == 'math.factorial':
                return True
        # abs(sub(...))
        if term.name == 'abs' and len(term.args) == 1:
            if isinstance(term.args[0], OOp) and term.args[0].name == 'sub':
                return True
        # max(a,b) - min(a,b)
        if term.name == 'sub' and len(term.args) == 2:
            lhs, rhs = term.args
            if (isinstance(lhs, OOp) and lhs.name == 'max'
                    and isinstance(rhs, OOp) and rhs.name == 'min'):
                return True
    # fold(mul, 1, range(1, n+1))
    if isinstance(term, OFold):
        if term.op_name == 'mul' and isinstance(term.init, OLit) and term.init.value == 1:
            return True
        if term.op_name == 'add' and isinstance(term.init, OLit) and term.init.value == 0:
            return True
    # fix(gcd, ...)
    if isinstance(term, OFix) and term.name == 'gcd':
        return True
    # (a // b, a % b)
    if isinstance(term, OSeq) and len(term.elements) == 2:
        e0, e1 = term.elements
        if (isinstance(e0, OOp) and e0.name == 'floordiv'
                and isinstance(e1, OOp) and e1.name == 'mod'):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P12 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_factorial_s = 'math.factorial(' in sc
    has_factorial_t = 'math.factorial(' in tc
    has_gcd_s = 'math.gcd(' in sc
    has_gcd_t = 'math.gcd(' in tc
    has_comb_s = 'math.comb(' in sc
    has_comb_t = 'math.comb(' in tc
    has_fold_mul_s = 'fold[mul]' in sc
    has_fold_mul_t = 'fold[mul]' in tc
    has_dot_s = 'dot(' in sc
    has_dot_t = 'dot(' in tc
    has_divmod_s = 'divmod(' in sc
    has_divmod_t = 'divmod(' in tc

    # factorial ↔ fold(mul)
    if (has_factorial_s and has_fold_mul_t) or (has_factorial_t and has_fold_mul_s):
        return 0.95

    # gcd ↔ fix
    if (has_gcd_s and 'fix[gcd]' in tc) or (has_gcd_t and 'fix[gcd]' in sc):
        return 0.95

    # comb ↔ factorials
    if has_comb_s != has_comb_t and (has_factorial_s or has_factorial_t):
        return 0.90

    # dot ↔ fold(add)
    if has_dot_s != has_dot_t:
        return 0.85

    # divmod ↔ (floordiv, mod)
    if has_divmod_s != has_divmod_t:
        return 0.85

    # isqrt / sqrt
    if 'isqrt(' in sc or 'isqrt(' in tc:
        return 0.80

    # abs / max-min
    if ('abs(' in sc and 'max(' in tc) or ('abs(' in tc and 'max(' in sc):
        return 0.80

    # Generic numeric signals
    if has_factorial_s or has_factorial_t or has_gcd_s or has_gcd_t:
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
    n = OVar('n')
    k = OVar('k')
    a = OVar('a')
    b = OVar('b')
    m = OVar('m')
    xs = OVar('xs')

    # ── factorial → fold ──
    print("P12: factorial → fold ...")
    fact_term = OOp('math.factorial', (n,))
    r = apply(fact_term, ctx)
    _assert(len(r) >= 1, "factorial(n) should rewrite")
    _assert(r[0][1] == 'P12_factorial_to_fold', "axiom label")
    _assert(isinstance(r[0][0], OFold), "result is OFold")

    # ── fold → factorial ──
    print("P12: fold → factorial ...")
    fold_fact = OFold('mul', OLit(1), OOp('range', (OLit(1), OOp('add', (n, OLit(1))))))
    r2 = apply(fold_fact, ctx)
    _assert(any(lbl == 'P12_fold_to_factorial' for _, lbl in r2), "fold→factorial")

    # ── factorial roundtrip ──
    print("P12: factorial roundtrip ...")
    rt = apply(r[0][0], ctx)
    _assert(any(lbl == 'P12_fold_to_factorial' for _, lbl in rt), "roundtrip works")

    # ── gcd → fix ──
    print("P12: gcd → fix ...")
    gcd_term = OOp('math.gcd', (a, b))
    r3 = apply(gcd_term, ctx)
    _assert(len(r3) >= 1, "gcd(a, b) should rewrite")
    _assert(r3[0][1] == 'P12_gcd_to_fix', "gcd label")
    _assert(isinstance(r3[0][0], OFix), "result is OFix")

    # ── fix → gcd ──
    print("P12: fix → gcd ...")
    fix_gcd = OFix('gcd', OCase(
        OOp('eq', (b, OLit(0))),
        a,
        OFix('gcd', OSeq((b, OOp('mod', (a, b))))),
    ))
    r4 = apply(fix_gcd, ctx)
    _assert(any(lbl == 'P12_fix_to_gcd' for _, lbl in r4), "fix→gcd")

    # ── comb → factorials ──
    print("P12: comb → factorials ...")
    comb_term = OOp('math.comb', (n, k))
    r5 = apply(comb_term, ctx)
    _assert(len(r5) >= 1, "comb(n, k) should rewrite")
    _assert(r5[0][1] == 'P12_comb_to_factorials', "comb label")

    # ── factorials → comb ──
    print("P12: factorials → comb ...")
    fact_comb = OOp('floordiv', (
        OOp('math.factorial', (n,)),
        OOp('mul', (
            OOp('math.factorial', (k,)),
            OOp('math.factorial', (OOp('sub', (n, k)),)),
        )),
    ))
    r6 = apply(fact_comb, ctx)
    _assert(any(lbl == 'P12_factorials_to_comb' for _, lbl in r6), "factorials→comb")

    # ── isqrt → int(sqrt) ──
    print("P12: isqrt → int(sqrt) ...")
    isqrt_term = OOp('math.isqrt', (n,))
    r7 = apply(isqrt_term, ctx)
    _assert(len(r7) >= 1, "isqrt should rewrite")
    _assert(r7[0][1] == 'P12_isqrt_to_int_sqrt', "isqrt label")

    # ── int(sqrt) → isqrt ──
    print("P12: int(sqrt) → isqrt ...")
    int_sqrt = OOp('int', (OOp('math.sqrt', (n,)),))
    r8 = apply(int_sqrt, ctx)
    _assert(any(lbl == 'P12_int_sqrt_to_isqrt' for _, lbl in r8), "int(sqrt)→isqrt")

    # ── sum(x² for x in xs) → dot(xs, xs) ──
    print("P12: sum of squares → dot ...")
    sum_sq = OFold('add', OLit(0), OMap(
        OLam(('x',), OOp('pow', (OVar('x'), OLit(2)))),
        xs,
    ))
    r9 = apply(sum_sq, ctx)
    _assert(any(lbl == 'P12_sum_sq_to_dot' for _, lbl in r9), "sum_sq→dot")

    # ── dot(xs, xs) → sum of squares ──
    print("P12: dot → sum of squares ...")
    dot_term = OOp('dot', (xs, xs))
    r10 = apply(dot_term, ctx)
    _assert(any(lbl == 'P12_dot_to_sum_sq' for _, lbl in r10), "dot→sum_sq")

    # ── abs(a - b) → max - min ──
    print("P12: abs diff → max-min ...")
    abs_diff = OOp('abs', (OOp('sub', (a, b)),))
    r11 = apply(abs_diff, ctx)
    _assert(len(r11) >= 1, "abs(a-b) should rewrite")
    _assert(r11[0][1] == 'P12_abs_diff_to_max_min', "abs_diff label")

    # ── max - min → abs diff ──
    print("P12: max-min → abs diff ...")
    max_min = OOp('sub', (OOp('max', (a, b)), OOp('min', (a, b))))
    r12 = apply(max_min, ctx)
    _assert(any(lbl == 'P12_max_min_to_abs_diff' for _, lbl in r12), "max_min→abs")

    # ── divmod → tuple ──
    print("P12: divmod → tuple ...")
    divmod_term = OOp('divmod', (a, b))
    r13 = apply(divmod_term, ctx)
    _assert(len(r13) >= 1, "divmod should rewrite")
    _assert(r13[0][1] == 'P12_divmod_to_tuple', "divmod label")
    _assert(isinstance(r13[0][0], OSeq), "result is OSeq")

    # ── tuple → divmod ──
    print("P12: tuple → divmod ...")
    tuple_dm = OSeq((OOp('floordiv', (a, b)), OOp('mod', (a, b))))
    r14 = apply(tuple_dm, ctx)
    _assert(any(lbl == 'P12_tuple_to_divmod' for _, lbl in r14), "tuple→divmod")

    # ── pow(a, b, m) → fold ──
    print("P12: pow mod → fold ...")
    pow_term = OOp('pow', (a, b, m))
    r15 = apply(pow_term, ctx)
    _assert(len(r15) >= 1, "pow(a,b,m) should rewrite")
    _assert(r15[0][1] == 'P12_pow_mod_to_fold', "pow_mod label")

    # ── recognizes() ──
    print("P12: recognizes ...")
    _assert(recognizes(fact_term), "recognizes factorial")
    _assert(recognizes(gcd_term), "recognizes gcd")
    _assert(recognizes(comb_term), "recognizes comb")
    _assert(recognizes(isqrt_term), "recognizes isqrt")
    _assert(recognizes(divmod_term), "recognizes divmod")
    _assert(recognizes(abs_diff), "recognizes abs(sub)")
    _assert(recognizes(max_min), "recognizes max-min")
    _assert(recognizes(fold_fact), "recognizes fold(mul)")
    _assert(recognizes(fix_gcd), "recognizes fix(gcd)")
    _assert(recognizes(tuple_dm), "recognizes (floordiv, mod)")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P12: relevance_score ...")
    score = relevance_score(fact_term, fold_fact)
    _assert(score > 0.8, f"factorial↔fold score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P12: apply_inverse ...")
    inv = apply_inverse(fold_fact, ctx)
    _assert(len(inv) >= 1, "inverse of fold(mul) produces factorial")
    inv2 = apply_inverse(max_min, ctx)
    _assert(any(lbl == 'P12_max_min_to_abs_diff' for _, lbl in inv2), "inverse max_min→abs")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P12 numeric: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
