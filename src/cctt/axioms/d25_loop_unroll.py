"""D25: Loop Unrolling/Rolling — Bounded Iteration ↔ Explicit Sequence.

§25.1 of the CCTT monograph.  Theorem 25.1.1:
A fold over a literal (bounded) collection is isomorphic to the
sequential application of the fold operation.

Key rewrites:
  • OFold(op, base, [a,b,c]) → op(op(op(base, a), b), c)   [unroll]
  • op(op(op(base, a), b), c) → OFold(op, base, [a,b,c])   [roll]
  • Peel first iteration: fold(op, b, [h|t]) → fold(op, op(b,h), t)
  • Peel last iteration:  fold(op, b, [init|l]) → op(fold(op,b,init), l)
  • OMap over literal list → explicit sequence of applications
  • Detect sequential pattern and roll into fold
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D25_loop_unroll"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.1.1 (Loop Unrolling).
Let op : A × B → A, base : A, xs = [x₁, ..., xₙ] : [B].
Then:
    fold[op](base, [x₁, ..., xₙ]) = op(... op(op(base, x₁), x₂) ..., xₙ)

Proof by induction on n:
  Base (n=0):  fold[op](base, []) = base  ✓
  Step (n→n+1):
    fold[op](base, [x₁,...,xₙ,xₙ₊₁])
      = fold[op](op(base, x₁), [x₂,...,xₙ₊₁])   (unfold)
      = op(... op(op(base,x₁), x₂) ..., xₙ₊₁)    (IH)
      = op(fold[op](base, [x₁,...,xₙ]), xₙ₊₁)     (refold)  □

Rolling soundness: the reverse direction holds by the same induction.

Peel-first:  fold(op, b, [h|t]) = fold(op, op(b,h), t)
  — directly from the definition of left fold.

Peel-last:   fold(op, b, xs++[l]) = op(fold(op, b, xs), l)
  — by induction, the last application of op uses the last element.
"""

COMPOSES_WITH = ["D1_fold_unfold", "D5_fold_universal", "D7_tailrec", "D28_loop_fusion"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "fold_unroll_3",
        "before": "fold[add](0, [1, 2, 3])",
        "after": "add(add(add(0, 1), 2), 3)",
        "benchmark": None,
    },
    {
        "name": "fold_roll_chain",
        "before": "mul(mul(mul(1, a), b), c)",
        "after": "fold[mul](1, [a, b, c])",
        "benchmark": None,
    },
    {
        "name": "peel_first",
        "before": "fold[add](0, [1, 2, 3])",
        "after": "fold[add](add(0, 1), [2, 3])",
        "benchmark": None,
    },
    {
        "name": "map_unroll",
        "before": "map(λ(x)f(x), [a, b, c])",
        "after": "[f(a), f(b), f(c)]",
        "benchmark": None,
    },
]


# ═══════════════════════════════════════════════════════════
# OTerm helpers
# ═══════════════════════════════════════════════════════════

def _is_literal_seq(term: OTerm) -> bool:
    """Check if term is an OSeq (literal list)."""
    return isinstance(term, OSeq)


def _extract_free_vars(term: OTerm, bound: Optional[Set[str]] = None) -> Set[str]:
    """Extract free variables from a term."""
    if bound is None:
        bound = set()
    if isinstance(term, OVar):
        return {term.name} - bound
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a, bound)
        return r
    if isinstance(term, OLam):
        return _extract_free_vars(term.body, bound | set(term.params))
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test, bound)
                | _extract_free_vars(term.true_branch, bound)
                | _extract_free_vars(term.false_branch, bound))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init, bound) | _extract_free_vars(term.collection, bound)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body, bound)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e, bound)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform, bound) | _extract_free_vars(term.collection, bound)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred, bound)
        return r3
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner, bound)
    if isinstance(term, OAbstract):
        return set().union(*(_extract_free_vars(a, bound) for a in term.inputs))
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k, bound) | _extract_free_vars(v, bound)
        return r5
    return set()


def _subst_var(term: OTerm, name: str, replacement: OTerm) -> OTerm:
    """Substitute variable *name* with *replacement* in *term*."""
    if isinstance(term, OVar):
        return replacement if term.name == name else term
    if isinstance(term, (OLit, OUnknown)):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_var(a, name, replacement) for a in term.args))
    if isinstance(term, OLam):
        if name in term.params:
            return term
        return OLam(term.params, _subst_var(term.body, name, replacement))
    if isinstance(term, OCase):
        return OCase(
            _subst_var(term.test, name, replacement),
            _subst_var(term.true_branch, name, replacement),
            _subst_var(term.false_branch, name, replacement),
        )
    if isinstance(term, OFold):
        return OFold(term.op_name, _subst_var(term.init, name, replacement),
                     _subst_var(term.collection, name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_var(e, name, replacement) for e in term.elements))
    if isinstance(term, OMap):
        filt = term.filter_pred
        if filt is not None:
            filt = _subst_var(filt, name, replacement)
        return OMap(_subst_var(term.transform, name, replacement),
                    _subst_var(term.collection, name, replacement), filt)
    if isinstance(term, OCatch):
        return OCatch(_subst_var(term.body, name, replacement),
                      _subst_var(term.default, name, replacement))
    return term


def _try_detect_repeated_op(term: OTerm) -> Optional[Tuple[str, OTerm, List[OTerm]]]:
    """Detect nested left-associative op pattern: op(op(op(base, a), b), c).

    Returns (op_name, base, [a, b, c]) if pattern matches.
    """
    elements: List[OTerm] = []
    current = term
    op_name: Optional[str] = None

    while isinstance(current, OOp) and len(current.args) == 2:
        if op_name is None:
            op_name = current.name
        elif current.name != op_name:
            return None
        elements.append(current.args[1])
        current = current.args[0]

    if op_name is None or not elements:
        return None

    elements.reverse()
    return (op_name, current, elements)


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


MAX_UNROLL = 16  # safety limit


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D25 loop unrolling/rolling rewrites to *term*.

    Handles:
      1. OFold over literal OSeq → unrolled chain of op applications
      2. OMap over literal OSeq → explicit sequence of applications
      3. Peel first iteration from fold over OSeq
      4. Peel last iteration from fold over OSeq
      5. Roll: nested op(op(op(base, a), b), c) → OFold
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Full unrolling: fold(op, base, [a,b,c]) → op(op(op(base,a),b),c) ──
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        elts = term.collection.elements
        if 0 < len(elts) <= MAX_UNROLL:
            acc: OTerm = term.init
            for e in elts:
                acc = OOp(term.op_name, (acc, e))
            results.append((acc, 'D25_fold_unroll'))

    # ── 2. Peel first: fold(op, base, [h, ...t]) → fold(op, op(base,h), t) ──
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        elts = term.collection.elements
        if len(elts) >= 2:
            head = elts[0]
            tail = OSeq(elts[1:])
            new_init = OOp(term.op_name, (term.init, head))
            results.append((
                OFold(term.op_name, new_init, tail),
                'D25_peel_first',
            ))

    # ── 3. Peel last: fold(op, base, [init..., l]) → op(fold(op, base, init), l) ──
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        elts = term.collection.elements
        if len(elts) >= 2:
            init_elts = OSeq(elts[:-1])
            last = elts[-1]
            results.append((
                OOp(term.op_name, (OFold(term.op_name, term.init, init_elts), last)),
                'D25_peel_last',
            ))

    # ── 4. Map unrolling: map(f, [a,b,c]) → [f(a), f(b), f(c)] ──
    if isinstance(term, OMap) and isinstance(term.collection, OSeq):
        elts = term.collection.elements
        if 0 < len(elts) <= MAX_UNROLL and term.filter_pred is None:
            if isinstance(term.transform, OLam) and len(term.transform.params) == 1:
                param = term.transform.params[0]
                mapped = tuple(
                    _subst_var(term.transform.body, param, e) for e in elts
                )
                results.append((OSeq(mapped), 'D25_map_unroll'))
            else:
                mapped_op = tuple(
                    OOp('__call__', (term.transform, e)) for e in elts
                )
                results.append((OSeq(mapped_op), 'D25_map_unroll_opaque'))

    # ── 5. Rolling: op(op(op(base, a), b), c) → fold(op, base, [a,b,c]) ──
    if isinstance(term, OOp) and len(term.args) == 2:
        detected = _try_detect_repeated_op(term)
        if detected is not None:
            op_name, base, elements = detected
            if len(elements) >= 2:
                results.append((
                    OFold(op_name, base, OSeq(tuple(elements))),
                    'D25_roll_to_fold',
                ))

    # ── 6. Fold over empty → init ──
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        if len(term.collection.elements) == 0:
            results.append((term.init, 'D25_fold_empty'))

    # ── 7. Fold over singleton → single application ──
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        if len(term.collection.elements) == 1:
            results.append((
                OOp(term.op_name, (term.init, term.collection.elements[0])),
                'D25_fold_singleton',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D25 apply to this term?"""
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        return True
    if isinstance(term, OMap) and isinstance(term.collection, OSeq):
        return True
    if isinstance(term, OOp) and len(term.args) == 2:
        detected = _try_detect_repeated_op(term)
        return detected is not None and len(detected[2]) >= 2
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D25 helps bridge source → target."""
    sc = source.canon()
    tc = target.canon()

    s_fold_lit = isinstance(source, OFold) and isinstance(source.collection, OSeq)
    t_fold_lit = isinstance(target, OFold) and isinstance(target.collection, OSeq)

    # One is fold-over-literal, other is expanded chain → high
    if s_fold_lit and 'fold[' not in tc:
        return 0.9
    if t_fold_lit and 'fold[' not in sc:
        return 0.9
    # Both fold-over-literal with different element counts
    if s_fold_lit and t_fold_lit:
        return 0.5
    # Map over literal
    if isinstance(source, OMap) and isinstance(source.collection, OSeq):
        return 0.7
    if isinstance(target, OMap) and isinstance(target.collection, OSeq):
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D25: roll expanded chains into folds, expand folds into chains."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # Unrolled chain → fold (rolling)
    if isinstance(term, OOp) and len(term.args) == 2:
        detected = _try_detect_repeated_op(term)
        if detected is not None:
            op_name, base, elements = detected
            if len(elements) >= 2:
                results.append((
                    OFold(op_name, base, OSeq(tuple(elements))),
                    'D25_inv_roll',
                ))

    # Fold over literal → unrolled chain
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        elts = term.collection.elements
        if 0 < len(elts) <= MAX_UNROLL:
            acc: OTerm = term.init
            for e in elts:
                acc = OOp(term.op_name, (acc, e))
            results.append((acc, 'D25_inv_unroll'))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    _pass = 0
    _fail = 0

    def _assert(cond: bool, msg: str) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL: {msg}")

    ctx = FiberCtx()
    a, b, c = OVar('a'), OVar('b'), OVar('c')
    x = OVar('x')

    # 1. Fold unroll: fold[add](0, [1,2,3]) → add(add(add(0,1),2),3)
    t1 = OFold('add', OLit(0), OSeq((OLit(1), OLit(2), OLit(3))))
    r1 = apply(t1, ctx)
    _assert(any(lbl == 'D25_fold_unroll' for _, lbl in r1), "fold unroll")
    unrolled = [t for t, lbl in r1 if lbl == 'D25_fold_unroll'][0]
    _assert(isinstance(unrolled, OOp) and unrolled.name == 'add', "unrolled is add")

    # 2. Peel first: fold(add, 0, [1,2,3]) → fold(add, add(0,1), [2,3])
    _assert(any(lbl == 'D25_peel_first' for _, lbl in r1), "peel first")
    peeled = [t for t, lbl in r1 if lbl == 'D25_peel_first'][0]
    _assert(isinstance(peeled, OFold) and isinstance(peeled.init, OOp), "peeled init is op")

    # 3. Peel last: fold(add, 0, [1,2,3]) → add(fold(add, 0, [1,2]), 3)
    _assert(any(lbl == 'D25_peel_last' for _, lbl in r1), "peel last")
    peeled_last = [t for t, lbl in r1 if lbl == 'D25_peel_last'][0]
    _assert(isinstance(peeled_last, OOp) and peeled_last.name == 'add', "peeled last is op")

    # 4. Rolling: add(add(add(0, a), b), c) → fold[add](0, [a,b,c])
    chain = OOp('add', (OOp('add', (OOp('add', (OLit(0), a)), b)), c))
    r4 = apply(chain, ctx)
    _assert(any(lbl == 'D25_roll_to_fold' for _, lbl in r4), "roll to fold")
    rolled = [t for t, lbl in r4 if lbl == 'D25_roll_to_fold'][0]
    _assert(isinstance(rolled, OFold) and rolled.op_name == 'add', "rolled is fold[add]")

    # 5. Map unroll: map(λx.f(x), [a,b,c]) → [f(a), f(b), f(c)]
    t5 = OMap(OLam(('x',), OOp('f', (OVar('x'),))), OSeq((a, b, c)))
    r5 = apply(t5, ctx)
    _assert(any(lbl == 'D25_map_unroll' for _, lbl in r5), "map unroll")
    map_result = [t for t, lbl in r5 if lbl == 'D25_map_unroll'][0]
    _assert(isinstance(map_result, OSeq) and len(map_result.elements) == 3, "map unroll produces 3 elts")

    # 6. Fold over empty → init
    t6 = OFold('add', OLit(0), OSeq(()))
    r6 = apply(t6, ctx)
    _assert(any(lbl == 'D25_fold_empty' for _, lbl in r6), "fold empty")

    # 7. Fold over singleton → single op
    t7 = OFold('add', OLit(0), OSeq((OLit(42),)))
    r7 = apply(t7, ctx)
    _assert(any(lbl == 'D25_fold_singleton' for _, lbl in r7), "fold singleton")

    # 8. Recognizes
    _assert(recognizes(t1), "recognizes fold over seq")
    _assert(recognizes(chain), "recognizes chain")
    _assert(recognizes(t5), "recognizes map over seq")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 9. Relevance
    _assert(relevance_score(t1, chain) > 0.5, "high relevance fold↔chain")

    # 10. Inverse: fold → chain
    r10 = apply_inverse(t1, ctx)
    _assert(any(lbl == 'D25_inv_unroll' for _, lbl in r10), "inverse unroll")

    # 11. Inverse: chain → fold
    r11 = apply_inverse(chain, ctx)
    _assert(any(lbl == 'D25_inv_roll' for _, lbl in r11), "inverse roll")

    # 12. Mixed ops don't roll
    mixed = OOp('add', (OOp('mul', (OLit(1), a)), b))
    r12 = apply(mixed, ctx)
    _assert(not any(lbl == 'D25_roll_to_fold' for _, lbl in r12), "mixed ops no roll")

    print(f"D25 loop-unroll: {_pass} passed, {_fail} failed")
