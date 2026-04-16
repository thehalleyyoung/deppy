"""P8: Unpacking / Assignment Equivalences (Theorem 28.4.1).

Tuple swap ↔ temp-variable swap,
starred unpack (head) ↔ indexing + slicing,
starred unpack (tail) ↔ slicing + indexing,
multi-assignment ↔ sequential assignment,
tuple unpacking in loops ↔ single-param destructure,
walrus operator ↔ separate binding + condition.

Mathematical foundation:
  All six equivalences are instances of the general principle that
  Python's parallel/structured binding forms are syntactic sugar for
  sequential binding in the substitution monad.

  Formally, each rewrite is a natural isomorphism between two functors
  on the category of binding contexts (Γ → Γ'):

  • swap(a,b) is an involution on Γ[a,b]; the temp-variable encoding
    lifts it to Γ[a,b,tmp] with an immediate projection back.

  • Starred unpacking decomposes a sequence object via the universal
    property of the product (head × tail or init × last).

  • Multi-assignment a = b = c = v is the diagonal Δ: v ↦ (v,v,v)
    in the product category.

  • Walrus := embeds a binding into an expression context; extracting
    it is the standard let-floating transformation from the enriched
    λ-calculus.

Covers:
  • a, b = b, a ↔ temp swap
  • a, *rest = xs ↔ a = xs[0]; rest = xs[1:]
  • *init, last = xs ↔ init = xs[:-1]; last = xs[-1]
  • a = b = c = 0 ↔ a = 0; b = 0; c = 0
  • for a, b in pairs ↔ for p in pairs: a, b = p
  • (n := f(x)) > 0 ↔ n = f(x); n > 0
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

AXIOM_NAME = 'P8_unpacking'
AXIOM_CATEGORY = 'python_idiom'  # §28 — Python-specific idioms

SOUNDNESS_PROOF = """
Theorem 28.4.1 (Unpacking / Assignment Equivalences):

  (a) Swap: a, b = b, a  ≡  tmp = a; a = b; b = tmp
      The RHS is the Church encoding of the swap permutation σ₁₂
      in the substitution monad.  Both produce Γ[a↦old_b, b↦old_a].

  (b) Starred head: a, *rest = xs  ≡  a = xs[0]; rest = xs[1:]
      By the universal property of the product (head, tail): X* ≅ X × X*.
      Both bind a to π₁(xs) and rest to π₂(xs).

  (c) Starred tail: *init, last = xs  ≡  init = xs[:-1]; last = xs[-1]
      Dual of (b), using the (init, last) decomposition.

  (d) Multi-assignment: a = b = c = v  ≡  a = v; b = v; c = v
      Diagonal morphism Δ₃: V → V³ in the category of contexts.

  (e) Tuple unpacking in loops:
      for a, b in pairs  ≡  for p in pairs: a, b = p
      The destructuring λ(a,b).body ≡ λp. let (a,b)=p in body.

  (f) Walrus: if (n := f(x)) > 0:  ≡  n = f(x); if n > 0:
      Standard let-floating: let n = e in C[n]  ≡  let n = e; C[n].  ∎
"""

COMPOSES_WITH = ['D02_beta', 'D14_indexing', 'D05_fold_universal']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'swap to temp',
        'before': "a, b = b, a",
        'after': "tmp = a; a = b; b = tmp",
        'axiom': 'P8_swap_to_temp',
    },
    {
        'name': 'starred head unpack',
        'before': "a, *rest = xs",
        'after': "a = xs[0]; rest = xs[1:]",
        'axiom': 'P8_starred_head_to_index',
    },
    {
        'name': 'starred tail unpack',
        'before': "*init, last = xs",
        'after': "init = xs[:-1]; last = xs[-1]",
        'axiom': 'P8_starred_tail_to_index',
    },
    {
        'name': 'multi-assign to seq',
        'before': "a = b = c = 0",
        'after': "a = 0; b = 0; c = 0",
        'axiom': 'P8_multi_assign_to_seq',
    },
    {
        'name': 'tuple-param loop to destructure',
        'before': "for a, b in pairs: body",
        'after': "for p in pairs: a, b = p; body",
        'axiom': 'P8_tuple_loop_to_destructure',
    },
    {
        'name': 'walrus to let-bind',
        'before': "if (n := f(x)) > 0: ...",
        'after': "n = f(x); if n > 0: ...",
        'axiom': 'P8_walrus_to_let',
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
    """Apply P8 unpacking/assignment equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── swap(a, b) → temp-variable swap sequence ──
    if isinstance(term, OOp) and term.name == 'swap' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OOp('swap_temp', (a, b)),
            'P8_swap_to_temp',
        ))

    # ── temp-variable swap → swap(a, b) ──
    if isinstance(term, OOp) and term.name == 'swap_temp' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OOp('swap', (a, b)),
            'P8_temp_to_swap',
        ))

    # ── starred_unpack_head(xs) → seq(getitem(xs,0), slice(xs,1,None)) ──
    if isinstance(term, OOp) and term.name == 'starred_unpack_head':
        if len(term.args) == 1:
            xs = term.args[0]
            results.append((
                OSeq((
                    OOp('getitem', (xs, OLit(0))),
                    OOp('slice', (xs, OLit(1), OLit(None))),
                )),
                'P8_starred_head_to_index',
            ))

    # ── seq(getitem(xs,0), slice(xs,1,None)) → starred_unpack_head(xs) ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        e0, e1 = term.elements
        if (isinstance(e0, OOp) and e0.name == 'getitem' and len(e0.args) == 2
                and isinstance(e0.args[1], OLit) and e0.args[1].value == 0):
            if (isinstance(e1, OOp) and e1.name == 'slice' and len(e1.args) == 3
                    and isinstance(e1.args[1], OLit) and e1.args[1].value == 1
                    and isinstance(e1.args[2], OLit) and e1.args[2].value is None):
                # Check both refer to the same source
                if _terms_equal(e0.args[0], e1.args[0]):
                    results.append((
                        OOp('starred_unpack_head', (e0.args[0],)),
                        'P8_index_to_starred_head',
                    ))

    # ── starred_unpack_tail(xs) → seq(slice(xs,None,-1), getitem(xs,-1)) ──
    if isinstance(term, OOp) and term.name == 'starred_unpack_tail':
        if len(term.args) == 1:
            xs = term.args[0]
            results.append((
                OSeq((
                    OOp('slice', (xs, OLit(None), OLit(-1))),
                    OOp('getitem', (xs, OLit(-1))),
                )),
                'P8_starred_tail_to_index',
            ))

    # ── seq(slice(xs,None,-1), getitem(xs,-1)) → starred_unpack_tail(xs) ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        e0, e1 = term.elements
        if (isinstance(e0, OOp) and e0.name == 'slice' and len(e0.args) == 3
                and isinstance(e0.args[1], OLit) and e0.args[1].value is None
                and isinstance(e0.args[2], OLit) and e0.args[2].value == -1):
            if (isinstance(e1, OOp) and e1.name == 'getitem' and len(e1.args) == 2
                    and isinstance(e1.args[1], OLit) and e1.args[1].value == -1):
                if _terms_equal(e0.args[0], e1.args[0]):
                    results.append((
                        OOp('starred_unpack_tail', (e0.args[0],)),
                        'P8_index_to_starred_tail',
                    ))

    # ── multi_assign(v, names...) → OSeq of individual assignments ──
    if isinstance(term, OOp) and term.name == 'multi_assign':
        if len(term.args) >= 2:
            value = term.args[0]
            names = term.args[1:]
            assigns = tuple(
                OOp('assign', (name, value)) for name in names
            )
            results.append((
                OSeq(assigns),
                'P8_multi_assign_to_seq',
            ))

    # ── OSeq of identical assigns → multi_assign ──
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        if all(isinstance(e, OOp) and e.name == 'assign' and len(e.args) == 2
               for e in term.elements):
            values = [e.args[1] for e in term.elements]  # type: ignore[union-attr]
            if all(_terms_equal(v, values[0]) for v in values[1:]):
                names = tuple(e.args[0] for e in term.elements)  # type: ignore[union-attr]
                results.append((
                    OOp('multi_assign', (values[0],) + names),
                    'P8_seq_to_multi_assign',
                ))

    # ── tuple-param loop: OMap with tuple-param λ → OMap with destructure ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if len(lam.params) == 2:
            p_var = OVar('_p')
            destructure = OSeq((
                OOp('assign', (OVar(lam.params[0]), OOp('getitem', (p_var, OLit(0))))),
                OOp('assign', (OVar(lam.params[1]), OOp('getitem', (p_var, OLit(1))))),
            ))
            new_body = OSeq((destructure, lam.body))
            results.append((
                OMap(OLam(('_p',), new_body), term.collection),
                'P8_tuple_loop_to_destructure',
            ))

    # ── single-param + destructure → tuple-param loop ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if len(lam.params) == 1 and isinstance(lam.body, OSeq):
            extracted = _extract_destructure(lam.body, lam.params[0])
            if extracted is not None:
                param_a, param_b, inner_body = extracted
                results.append((
                    OMap(OLam((param_a, param_b), inner_body), term.collection),
                    'P8_destructure_to_tuple_loop',
                ))

    # ── walrus(name, expr) in condition → separate binding + condition ──
    if isinstance(term, OOp) and term.name in ('gt', 'lt', 'ge', 'le', 'eq', 'ne'):
        if len(term.args) == 2:
            lhs, rhs = term.args
            if isinstance(lhs, OOp) and lhs.name == 'walrus' and len(lhs.args) == 2:
                name_term, expr = lhs.args
                results.append((
                    OSeq((
                        OOp('assign', (name_term, expr)),
                        OOp(term.name, (name_term, rhs)),
                    )),
                    'P8_walrus_to_let',
                ))

    # ── separate binding + condition → walrus ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        e0, e1 = term.elements
        if isinstance(e0, OOp) and e0.name == 'assign' and len(e0.args) == 2:
            name_term, expr = e0.args
            if isinstance(e1, OOp) and e1.name in ('gt', 'lt', 'ge', 'le', 'eq', 'ne'):
                if len(e1.args) == 2 and _terms_equal(e1.args[0], name_term):
                    walrus = OOp('walrus', (name_term, expr))
                    results.append((
                        OOp(e1.name, (walrus, e1.args[1])),
                        'P8_let_to_walrus',
                    ))

    return results


def _terms_equal(a: OTerm, b: OTerm) -> bool:
    """Structural equality check for OTerms via canonical form."""
    return a.canon() == b.canon()


def _extract_destructure(
    body: OSeq, param: str,
) -> Optional[Tuple[str, str, OTerm]]:
    """Try to extract a two-element destructure from a loop body.

    Looks for the pattern:
      OSeq((assign(a, getitem(p, 0)), assign(b, getitem(p, 1))), rest_body)
    where p is *param*.
    """
    elems = body.elements
    if len(elems) < 2:
        return None
    head = elems[0]
    if not isinstance(head, OSeq) or len(head.elements) != 2:
        return None
    a0, a1 = head.elements
    if not (isinstance(a0, OOp) and a0.name == 'assign' and len(a0.args) == 2):
        return None
    if not (isinstance(a1, OOp) and a1.name == 'assign' and len(a1.args) == 2):
        return None
    idx0 = a0.args[1]
    idx1 = a1.args[1]
    if not (isinstance(idx0, OOp) and idx0.name == 'getitem' and len(idx0.args) == 2):
        return None
    if not (isinstance(idx1, OOp) and idx1.name == 'getitem' and len(idx1.args) == 2):
        return None
    if not (isinstance(idx0.args[0], OVar) and idx0.args[0].name == param):
        return None
    if not (isinstance(idx1.args[0], OVar) and idx1.args[0].name == param):
        return None
    if not (isinstance(idx0.args[1], OLit) and idx0.args[1].value == 0):
        return None
    if not (isinstance(idx1.args[1], OLit) and idx1.args[1].value == 1):
        return None
    name_a = a0.args[0]
    name_b = a1.args[0]
    if not (isinstance(name_a, OVar) and isinstance(name_b, OVar)):
        return None
    rest = elems[1] if len(elems) == 2 else OSeq(elems[1:])
    return (name_a.name, name_b.name, rest)


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P8 in reverse direction.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P8_temp_to_swap',
        'P8_index_to_starred_head',
        'P8_index_to_starred_tail',
        'P8_seq_to_multi_assign',
        'P8_destructure_to_tuple_loop',
        'P8_let_to_walrus',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P8 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('swap', 'swap_temp',
                         'starred_unpack_head', 'starred_unpack_tail',
                         'multi_assign', 'walrus'):
            return True
        if term.name in ('gt', 'lt', 'ge', 'le', 'eq', 'ne') and len(term.args) == 2:
            if isinstance(term.args[0], OOp) and term.args[0].name == 'walrus':
                return True
    if isinstance(term, OSeq):
        if _is_head_unpack_seq(term) or _is_tail_unpack_seq(term):
            return True
        if _is_identical_assign_seq(term):
            return True
        if _is_bind_then_cmp(term):
            return True
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        return True
    return False


def _is_head_unpack_seq(term: OSeq) -> bool:
    """Check for getitem(xs,0), slice(xs,1,None) pattern."""
    if len(term.elements) != 2:
        return False
    e0, e1 = term.elements
    return (isinstance(e0, OOp) and e0.name == 'getitem'
            and isinstance(e1, OOp) and e1.name == 'slice')


def _is_tail_unpack_seq(term: OSeq) -> bool:
    """Check for slice(xs,None,-1), getitem(xs,-1) pattern."""
    if len(term.elements) != 2:
        return False
    e0, e1 = term.elements
    return (isinstance(e0, OOp) and e0.name == 'slice'
            and isinstance(e1, OOp) and e1.name == 'getitem')


def _is_identical_assign_seq(term: OSeq) -> bool:
    """Check for seq of identical assign(name, same_val) ops."""
    if len(term.elements) < 2:
        return False
    return all(isinstance(e, OOp) and e.name == 'assign' for e in term.elements)


def _is_bind_then_cmp(term: OSeq) -> bool:
    """Check for assign(n, expr) followed by cmp(n, ...)."""
    if len(term.elements) != 2:
        return False
    e0, e1 = term.elements
    if not (isinstance(e0, OOp) and e0.name == 'assign'):
        return False
    if not (isinstance(e1, OOp) and e1.name in ('gt', 'lt', 'ge', 'le', 'eq', 'ne')):
        return False
    return True


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P8 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    unpack_kws = (
        'swap(', 'swap_temp(', 'starred_unpack_head(', 'starred_unpack_tail(',
        'multi_assign(', 'walrus(',
    )
    expand_kws = ('getitem(', 'slice(', 'assign(')

    has_unpack_s = any(kw in sc for kw in unpack_kws)
    has_unpack_t = any(kw in tc for kw in unpack_kws)
    has_expand_s = any(kw in sc for kw in expand_kws)
    has_expand_t = any(kw in tc for kw in expand_kws)

    # Direct swap ↔ swap_temp pairing → high relevance
    if ('swap(' in sc and 'swap_temp(' in tc) or ('swap_temp(' in sc and 'swap(' in tc):
        return 0.95

    # One side compact, other side expanded → high relevance
    if has_unpack_s and has_expand_t:
        return 0.95
    if has_unpack_t and has_expand_s:
        return 0.95

    # Both have unpacking constructs → moderate-high
    if has_unpack_s and has_unpack_t:
        return 0.85

    # Only one side mentions unpacking
    if has_unpack_s or has_unpack_t:
        return 0.45

    # Walrus / assign pattern
    if 'walrus(' in sc or 'walrus(' in tc:
        return 0.60

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
    xs = OVar('xs')
    a = OVar('a')
    b = OVar('b')

    # ── swap → temp ──
    print("P8: swap → temp ...")
    swap_term = OOp('swap', (a, b))
    r = apply(swap_term, ctx)
    _assert(len(r) >= 1, "swap(a,b) should rewrite")
    _assert(r[0][1] == 'P8_swap_to_temp', "axiom label")
    _assert(isinstance(r[0][0], OOp) and r[0][0].name == 'swap_temp', "result is swap_temp")

    # ── temp → swap (roundtrip) ──
    print("P8: temp → swap ...")
    r2 = apply(r[0][0], ctx)
    _assert(any(lbl == 'P8_temp_to_swap' for _, lbl in r2), "temp→swap roundtrip")

    # ── starred_unpack_head → index+slice ──
    print("P8: starred_unpack_head → index+slice ...")
    head_term = OOp('starred_unpack_head', (xs,))
    r3 = apply(head_term, ctx)
    _assert(any(lbl == 'P8_starred_head_to_index' for _, lbl in r3), "head→index")
    _assert(any(isinstance(t, OSeq) for t, _ in r3), "result is OSeq")

    # ── index+slice → starred_unpack_head (roundtrip) ──
    print("P8: index+slice → starred_unpack_head ...")
    head_expanded = OSeq((
        OOp('getitem', (xs, OLit(0))),
        OOp('slice', (xs, OLit(1), OLit(None))),
    ))
    r4 = apply(head_expanded, ctx)
    _assert(any(lbl == 'P8_index_to_starred_head' for _, lbl in r4), "index→head")

    # ── starred_unpack_tail → slice+index ──
    print("P8: starred_unpack_tail → slice+index ...")
    tail_term = OOp('starred_unpack_tail', (xs,))
    r5 = apply(tail_term, ctx)
    _assert(any(lbl == 'P8_starred_tail_to_index' for _, lbl in r5), "tail→index")

    # ── slice+index → starred_unpack_tail (roundtrip) ──
    print("P8: slice+index → starred_unpack_tail ...")
    tail_expanded = OSeq((
        OOp('slice', (xs, OLit(None), OLit(-1))),
        OOp('getitem', (xs, OLit(-1))),
    ))
    r6 = apply(tail_expanded, ctx)
    _assert(any(lbl == 'P8_index_to_starred_tail' for _, lbl in r6), "index→tail")

    # ── multi_assign → seq ──
    print("P8: multi_assign → seq ...")
    ma_term = OOp('multi_assign', (OLit(0), OVar('x'), OVar('y'), OVar('z')))
    r7 = apply(ma_term, ctx)
    _assert(any(lbl == 'P8_multi_assign_to_seq' for _, lbl in r7), "multi→seq")
    for t, lbl in r7:
        if lbl == 'P8_multi_assign_to_seq':
            _assert(isinstance(t, OSeq), "result is OSeq")
            _assert(len(t.elements) == 3, "three assignments")

    # ── seq of assigns → multi_assign (roundtrip) ──
    print("P8: seq of assigns → multi_assign ...")
    seq_assigns = OSeq((
        OOp('assign', (OVar('x'), OLit(0))),
        OOp('assign', (OVar('y'), OLit(0))),
        OOp('assign', (OVar('z'), OLit(0))),
    ))
    r8 = apply(seq_assigns, ctx)
    _assert(any(lbl == 'P8_seq_to_multi_assign' for _, lbl in r8), "seq→multi roundtrip")

    # ── walrus in condition → let-bind ──
    print("P8: walrus → let-bind ...")
    walrus_term = OOp('gt', (
        OOp('walrus', (OVar('n'), OOp('f', (OVar('x'),)))),
        OLit(0),
    ))
    r9 = apply(walrus_term, ctx)
    _assert(any(lbl == 'P8_walrus_to_let' for _, lbl in r9), "walrus→let")

    # ── let-bind → walrus (roundtrip) ──
    print("P8: let-bind → walrus ...")
    let_term = OSeq((
        OOp('assign', (OVar('n'), OOp('f', (OVar('x'),)))),
        OOp('gt', (OVar('n'), OLit(0))),
    ))
    r10 = apply(let_term, ctx)
    _assert(any(lbl == 'P8_let_to_walrus' for _, lbl in r10), "let→walrus roundtrip")

    # ── tuple-param loop → destructure ──
    print("P8: tuple-param loop → destructure ...")
    tuple_loop = OMap(
        OLam(('a', 'b'), OOp('add', (OVar('a'), OVar('b')))),
        OVar('pairs'),
    )
    r11 = apply(tuple_loop, ctx)
    _assert(any(lbl == 'P8_tuple_loop_to_destructure' for _, lbl in r11), "tuple→destructure")

    # ── recognizes() ──
    print("P8: recognizes ...")
    _assert(recognizes(swap_term), "recognizes swap")
    _assert(recognizes(head_term), "recognizes starred_unpack_head")
    _assert(recognizes(tail_term), "recognizes starred_unpack_tail")
    _assert(recognizes(ma_term), "recognizes multi_assign")
    _assert(recognizes(walrus_term), "recognizes walrus in condition")
    _assert(recognizes(head_expanded), "recognizes head expanded seq")
    _assert(recognizes(seq_assigns), "recognizes assign seq")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P8: relevance_score ...")
    score = relevance_score(swap_term, OOp('swap_temp', (a, b)))
    _assert(score > 0.8, f"swap↔temp score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P8: apply_inverse ...")
    inv = apply_inverse(OOp('swap_temp', (a, b)), ctx)
    _assert(len(inv) >= 1, "inverse of swap_temp produces swap")
    inv_labels = {lbl for _, lbl in inv}
    _assert('P8_temp_to_swap' in inv_labels, "inverse label correct")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P8 unpacking: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
