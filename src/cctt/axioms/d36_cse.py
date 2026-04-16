"""D36: Common Subexpression Elimination (Theorem 36.1).

Detect and factor out repeated subterms in OTerm trees.

Mathematical foundation:
  In a language with referential transparency (no side effects),
  any expression e that appears multiple times in a term t can be
  replaced by a single binding:

    C[e, e]  ≡  let x = e in C[x, x]

  provided e is pure (no effects).  This is justified by the
  substitution lemma of the simply-typed lambda calculus:

    If Γ ⊢ e : τ  and  Γ, x:τ ⊢ t : σ,
    then  Γ ⊢ t[x↦e] : σ.

  The inverse (inlining) is D2 (beta reduction):
    let x = e in C[x] ≡ C[e].

Covers:
  • f(a*b) + g(a*b) ↔ let t = a*b in f(t) + g(t)
  • Detect repeated subterms in OTerm trees
  • OOp(+, OOp(*, a, b), OOp(*, a, b)) → introduce sharing
  • Inverse: inline let bindings (connect to D2 beta)
  • len(xs) + len(xs) ↔ 2 * len(xs)
  • Multiple uses of same function call → bind once
"""
from __future__ import annotations

import hashlib
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D36_cse'
AXIOM_CATEGORY = 'algebraic_simplification'

SOUNDNESS_PROOF = """
Theorem 36.1 (Common Subexpression Elimination):
  For a pure expression e and term t containing e at positions p₁, p₂, ...,
    t  ≡  let x = e in t[p₁↦x, p₂↦x, ...]
  by the substitution lemma and referential transparency.

Proof:
  1. Since e is pure, evaluating e twice produces the same result.
  2. Introducing let x = e binds x to the value of e.
  3. Replacing each occurrence of e with x preserves the value of t
     because x and e denote the same value.
  4. Formally: by the β-equivalence of the lambda calculus,
       (λx.t[p₁↦x,p₂↦x,...]) e  ≡  t[p₁↦e,p₂↦e,...]  = t.  ∎

Corollary 36.1.1 (Repeated Call Folding):
  f(e) + f(e) ≡ 2 * f(e)  ≡  let t = f(e) in t + t  ≡  let t = f(e) in 2*t
  by CSE + arithmetic identity (D35).

Corollary 36.1.2 (Inlining is the Inverse):
  let x = e in C[x]  ≡  C[e]   (D2 β-reduction)
  CSE and inlining form a section-retraction pair.
"""

COMPOSES_WITH = ['D02_beta', 'D35_strength_reduce', 'D17_assoc']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'CSE binary op',
        'before': "f(a*b) + g(a*b)",
        'after': "let t = a*b in f(t) + g(t)",
        'axiom': 'D36_cse_extract',
    },
    {
        'name': 'inline let',
        'before': "let t = e in C[t]",
        'after': "C[e]",
        'axiom': 'D36_inline_let',
    },
    {
        'name': 'duplicate add to multiply',
        'before': "len(xs) + len(xs)",
        'after': "2 * len(xs)",
        'axiom': 'D36_dup_add_to_mul',
    },
    {
        'name': 'factor common subexpr in args',
        'before': "h(f(x), g(f(x)))",
        'after': "let t = f(x) in h(t, g(t))",
        'axiom': 'D36_cse_extract',
    },
    {
        'name': 'shared subterm in conditional',
        'before': "if c then f(e) + e else g(e) + e",
        'after': "let t = e in (if c then f(t) + t else g(t) + t)",
        'axiom': 'D36_cse_hoist',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: fiber context + subterm utilities
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


def _collect_subterms(term: OTerm) -> List[OTerm]:
    """Collect all non-trivial subterms of *term* (depth-first)."""
    result: List[OTerm] = []
    if isinstance(term, (OVar, OLit, OUnknown)):
        return result  # trivial — don't factor these out
    result.append(term)
    for child in _children(term):
        result.extend(_collect_subterms(child))
    return result


def _children(term: OTerm) -> List[OTerm]:
    """Direct children of *term*."""
    if isinstance(term, OOp):
        return list(term.args)
    if isinstance(term, OFold):
        return [term.init, term.collection]
    if isinstance(term, OCase):
        return [term.test, term.true_branch, term.false_branch]
    if isinstance(term, OFix):
        return [term.body]
    if isinstance(term, OLam):
        return [term.body]
    if isinstance(term, OSeq):
        return list(term.elements)
    if isinstance(term, OMap):
        kids = [term.transform, term.collection]
        if term.filter_pred:
            kids.append(term.filter_pred)
        return kids
    if isinstance(term, OQuotient):
        return [term.inner]
    if isinstance(term, ODict):
        kids: List[OTerm] = []
        for k, v in term.pairs:
            kids.extend([k, v])
        return kids
    if isinstance(term, OCatch):
        return [term.body, term.default]
    if isinstance(term, OAbstract):
        return list(term.inputs)
    return []


def _subst_term(term: OTerm, old_canon: str, replacement: OTerm) -> OTerm:
    """Replace all subterms whose canon() == old_canon with *replacement*."""
    if term.canon() == old_canon:
        return replacement
    if isinstance(term, (OVar, OLit, OUnknown)):
        return term
    if isinstance(term, OOp):
        new_args = tuple(_subst_term(a, old_canon, replacement) for a in term.args)
        return OOp(term.name, new_args)
    if isinstance(term, OFold):
        return OFold(
            term.op_name,
            _subst_term(term.init, old_canon, replacement),
            _subst_term(term.collection, old_canon, replacement),
        )
    if isinstance(term, OCase):
        return OCase(
            _subst_term(term.test, old_canon, replacement),
            _subst_term(term.true_branch, old_canon, replacement),
            _subst_term(term.false_branch, old_canon, replacement),
        )
    if isinstance(term, OFix):
        return OFix(term.name, _subst_term(term.body, old_canon, replacement))
    if isinstance(term, OLam):
        return OLam(term.params, _subst_term(term.body, old_canon, replacement))
    if isinstance(term, OSeq):
        new_elts = tuple(_subst_term(e, old_canon, replacement) for e in term.elements)
        return OSeq(new_elts)
    if isinstance(term, OMap):
        fp = None
        if term.filter_pred is not None:
            fp = _subst_term(term.filter_pred, old_canon, replacement)
        return OMap(
            _subst_term(term.transform, old_canon, replacement),
            _subst_term(term.collection, old_canon, replacement),
            fp,
        )
    if isinstance(term, OQuotient):
        return OQuotient(_subst_term(term.inner, old_canon, replacement), term.equiv_class)
    if isinstance(term, ODict):
        new_pairs = tuple(
            (_subst_term(k, old_canon, replacement), _subst_term(v, old_canon, replacement))
            for k, v in term.pairs
        )
        return ODict(new_pairs)
    if isinstance(term, OCatch):
        return OCatch(
            _subst_term(term.body, old_canon, replacement),
            _subst_term(term.default, old_canon, replacement),
        )
    if isinstance(term, OAbstract):
        new_inputs = tuple(_subst_term(a, old_canon, replacement) for a in term.inputs)
        return OAbstract(term.spec, new_inputs)
    return term


def _term_size(term: OTerm) -> int:
    """Approximate size of an OTerm tree (node count)."""
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 1
    return 1 + sum(_term_size(c) for c in _children(term))


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

_CSE_COUNTER = 0

def _fresh_cse_var() -> str:
    global _CSE_COUNTER
    _CSE_COUNTER += 1
    return f'_cse{_CSE_COUNTER}'


def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D36 common subexpression elimination to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Detect repeated subterms → CSE extraction ──
    subterms = _collect_subterms(term)
    canon_counts: Counter = Counter()
    canon_to_term: Dict[str, OTerm] = {}
    for st in subterms:
        c = st.canon()
        canon_counts[c] += 1
        if c not in canon_to_term:
            canon_to_term[c] = st

    # Find the largest repeated subterm (by size) that appears ≥ 2 times
    repeated = [
        (c, canon_to_term[c])
        for c, count in canon_counts.items()
        if count >= 2 and _term_size(canon_to_term[c]) >= 2
    ]
    # Sort by size descending — extract the biggest repeated subexpr first
    repeated.sort(key=lambda pair: _term_size(pair[1]), reverse=True)

    for canon, subterm in repeated:
        var_name = _fresh_cse_var()
        var = OVar(var_name)
        new_body = _subst_term(term, canon, var)
        # Represent as: OOp('let', (OLit(var_name), subterm, new_body))
        let_term = OOp('let', (OLit(var_name), subterm, new_body))
        results.append((let_term, 'D36_cse_extract'))
        break  # only extract the largest one per application

    # ── e + e → 2 * e (duplicate addition) ──
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        lhs, rhs = term.args
        if lhs.canon() == rhs.canon() and _term_size(lhs) >= 2:
            results.append((
                OOp('mult', (OLit(2), lhs)),
                'D36_dup_add_to_mul',
            ))

    # ── 2 * e → e + e (reverse) ──
    if isinstance(term, OOp) and term.name in ('mult', 'mul') and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(lhs, OLit) and lhs.value == 2:
            results.append((OOp('add', (rhs, rhs)), 'D36_mul2_to_dup_add'))
        if isinstance(rhs, OLit) and rhs.value == 2:
            results.append((OOp('add', (lhs, lhs)), 'D36_mul2_to_dup_add'))

    # ── Inline let binding: OOp('let', (name, val, body)) → body[name↦val] ──
    if isinstance(term, OOp) and term.name == 'let' and len(term.args) == 3:
        name_lit, val, body = term.args
        if isinstance(name_lit, OLit) and isinstance(name_lit.value, str):
            var_name = name_lit.value
            # Inline: substitute var back into body
            inlined = _subst_term(body, OVar(var_name).canon(), val)
            results.append((inlined, 'D36_inline_let'))

    # ── CSE across OCase branches (hoist common subterm) ──
    if isinstance(term, OCase):
        t_subs = _collect_subterms(term.true_branch)
        f_subs_canon = {st.canon() for st in _collect_subterms(term.false_branch)}
        for st in t_subs:
            c = st.canon()
            if c in f_subs_canon and _term_size(st) >= 2:
                var_name = _fresh_cse_var()
                var = OVar(var_name)
                new_true = _subst_term(term.true_branch, c, var)
                new_false = _subst_term(term.false_branch, c, var)
                hoisted = OOp('let', (
                    OLit(var_name),
                    st,
                    OCase(term.test, new_true, new_false),
                ))
                results.append((hoisted, 'D36_cse_hoist'))
                break  # one per application

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D36 in reverse: inline let bindings, expand duplicates."""
    results = apply(term, ctx)
    inverse_labels = {
        'D36_inline_let',
        'D36_mul2_to_dup_add',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D36 is potentially applicable to *term*."""
    # Check for let bindings (inlining opportunity)
    if isinstance(term, OOp) and term.name == 'let' and len(term.args) == 3:
        return True

    # Check for repeated subterms
    subterms = _collect_subterms(term)
    canon_counts: Counter = Counter()
    for st in subterms:
        c = st.canon()
        canon_counts[c] += 1
        if canon_counts[c] >= 2 and _term_size(st) >= 2:
            return True

    # Check for e + e pattern
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            return True

    # Check for 2 * e pattern
    if isinstance(term, OOp) and term.name in ('mult', 'mul') and len(term.args) == 2:
        if isinstance(term.args[0], OLit) and term.args[0].value == 2:
            return True
        if isinstance(term.args[1], OLit) and term.args[1].value == 2:
            return True

    # Check for shared subterms across OCase branches
    if isinstance(term, OCase):
        t_canons = {st.canon() for st in _collect_subterms(term.true_branch)
                    if _term_size(st) >= 2}
        f_canons = {st.canon() for st in _collect_subterms(term.false_branch)
                    if _term_size(st) >= 2}
        if t_canons & f_canons:
            return True

    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D36 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    has_let_s = 'let(' in sc
    has_let_t = 'let(' in tc

    # One has let, other doesn't → high relevance (inline/extract)
    if has_let_s != has_let_t:
        return 0.90

    # Check for repeated subterms in source
    src_subs = _collect_subterms(source)
    src_canon_counts: Counter = Counter()
    for st in src_subs:
        src_canon_counts[st.canon()] += 1
    max_dup = max(src_canon_counts.values()) if src_canon_counts else 0
    if max_dup >= 2:
        return 0.85

    # Both have let → moderate (possible restructuring)
    if has_let_s and has_let_t:
        return 0.50

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
    a = OVar('a')
    b = OVar('b')
    x = OVar('x')

    # ── CSE extraction: f(a*b) + g(a*b) ──
    print("D36: CSE extraction ...")
    ab = OOp('mult', (a, b))
    term = OOp('add', (OOp('f', (ab,)), OOp('g', (ab,))))
    r = apply(term, ctx)
    _assert(any(lbl == 'D36_cse_extract' for _, lbl in r), "CSE extract")
    cse_results = [t for t, lbl in r if lbl == 'D36_cse_extract']
    _assert(len(cse_results) >= 1, "got CSE result")
    _assert(isinstance(cse_results[0], OOp) and cse_results[0].name == 'let',
            "CSE result is let-binding")

    # ── Inline let binding ──
    print("D36: inline let ...")
    let_term = OOp('let', (OLit('t'), OOp('mult', (a, b)),
                           OOp('add', (OOp('f', (OVar('t'),)),
                                       OOp('g', (OVar('t'),))))))
    r2 = apply(let_term, ctx)
    _assert(any(lbl == 'D36_inline_let' for _, lbl in r2), "inline let")
    inlined = [t for t, lbl in r2 if lbl == 'D36_inline_let']
    _assert(len(inlined) >= 1, "got inlined result")
    # After inlining, t should be replaced with mult(a,b)
    _assert('let(' not in inlined[0].canon(), "no let in inlined result")

    # ── Roundtrip: CSE → inline → original ──
    print("D36: roundtrip CSE ↔ inline ...")
    cse_term = cse_results[0]
    back = apply(cse_term, ctx)
    _assert(any(lbl == 'D36_inline_let' for _, lbl in back), "roundtrip inline")

    # ── Duplicate addition: len(xs) + len(xs) → 2 * len(xs) ──
    print("D36: duplicate add → multiply ...")
    xs = OVar('xs')
    len_xs = OOp('len', (xs,))
    dup_add = OOp('add', (len_xs, len_xs))
    r3 = apply(dup_add, ctx)
    _assert(any(lbl == 'D36_dup_add_to_mul' for _, lbl in r3), "dup_add→mul")
    mul_results = [t for t, lbl in r3 if lbl == 'D36_dup_add_to_mul']
    _assert(len(mul_results) >= 1, "got mul result")
    _assert(isinstance(mul_results[0], OOp) and mul_results[0].name == 'mult',
            "dup add yields mult")

    # ── 2 * len(xs) → len(xs) + len(xs) (reverse) ──
    print("D36: 2 * e → e + e ...")
    mul2 = OOp('mult', (OLit(2), len_xs))
    r4 = apply(mul2, ctx)
    _assert(any(lbl == 'D36_mul2_to_dup_add' for _, lbl in r4), "mul2→dup_add")

    # ── CSE across OCase branches ──
    print("D36: CSE hoist across branches ...")
    shared = OOp('expensive', (a, b))
    case_term = OCase(
        OVar('cond'),
        OOp('add', (shared, OLit(1))),
        OOp('sub', (shared, OLit(2))),
    )
    r5 = apply(case_term, ctx)
    _assert(any(lbl == 'D36_cse_hoist' for _, lbl in r5), "CSE hoist")
    hoist_results = [t for t, lbl in r5 if lbl == 'D36_cse_hoist']
    _assert(len(hoist_results) >= 1 and isinstance(hoist_results[0], OOp)
            and hoist_results[0].name == 'let', "hoisted is let-binding")

    # ── No CSE for trivial terms ──
    print("D36: no CSE for trivial ...")
    trivial = OOp('add', (OLit(1), OLit(1)))
    r6 = apply(trivial, ctx)
    # OLit(1) has size 1, so it won't be CSE'd (only dup_add might fire,
    # but size < 2)
    _assert(not any(lbl == 'D36_cse_extract' for _, lbl in r6), "no CSE for literals")

    # ── recognizes() ──
    print("D36: recognizes ...")
    _assert(recognizes(term), "recognizes repeated subterms")
    _assert(recognizes(let_term), "recognizes let binding")
    _assert(recognizes(dup_add), "recognizes dup add")
    _assert(recognizes(case_term), "recognizes shared in branches")
    _assert(not recognizes(OOp('sorted', (OVar('xs'),))), "does not recognise sorted")

    # ── relevance_score ──
    print("D36: relevance_score ...")
    score = relevance_score(term, let_term)
    _assert(score > 0.8, f"cse↔let score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (OVar('xs'),)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D36: apply_inverse ...")
    inv = apply_inverse(let_term, ctx)
    _assert(any(lbl == 'D36_inline_let' for _, lbl in inv), "inverse inline let")
    inv2 = apply_inverse(mul2, ctx)
    _assert(any(lbl == 'D36_mul2_to_dup_add' for _, lbl in inv2), "inverse mul2→add")

    # ── Nested repeated subterms ──
    print("D36: nested repeated subterms ...")
    deep = OOp('add', (
        OOp('mult', (OOp('f', (a,)), OOp('g', (b,)))),
        OOp('mult', (OOp('f', (a,)), OOp('g', (b,)))),
    ))
    r7 = apply(deep, ctx)
    _assert(any(lbl == 'D36_cse_extract' for _, lbl in r7), "deep CSE")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D36 cse: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
