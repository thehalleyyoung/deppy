"""D33: Church/Scott Encoding (Theorem 33.1).

Data-as-functions ↔ data-as-values with external dispatch.

Mathematical foundation:
  Church encoding maps data types to their eliminators in System F:
    Nat ≅ ∀α. (α → α) → α → α        (Church numerals)
    Bool ≅ ∀α. α → α → α              (Church booleans)
  Scott encoding maps inductive types to case-dispatch functions:
    T ≅ ∀α. (case₁ → α) → ... → (caseₙ → α) → α

  The encoding-decoding round-trip witnesses a definable isomorphism
  in the presheaf topos: encode ∘ decode = id, decode ∘ encode = id.

  In Python, this manifests as:
    • isinstance dispatch ↔ method dispatch (Scott eliminator)
    • Data-as-functions (visitor pattern) ↔ data-as-values (tagged union)
    • Church booleans (λt.λf.t) ↔ True/False with if/else

Covers:
  • Church numerals: λf.λx.f(f(...(x))) ↔ n
  • Church booleans: λt.λf.t ↔ True, λt.λf.f ↔ False
  • Church pairs: λf.f(a)(b) ↔ (a, b)
  • Scott encoding: tagged unions as case-dispatch functions
  • isinstance dispatch ↔ method dispatch ↔ Scott eliminator
  • Visitor pattern ↔ match/case ↔ if/elif chain
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

AXIOM_NAME = 'D33_encoding'
AXIOM_CATEGORY = 'data_representation'

SOUNDNESS_PROOF = """
Theorem 33.1 (Encoding Round-Trip):
  For a data type T with Church (or Scott) encoding enc_T:
    decode_T(encode_T(x)) = x   for all x : T
    encode_T(decode_T(f)) = f   for all f : enc_T

Proof sketch:
  1. Church booleans:
     encode(True)  = λt.λf.t  →  decode: apply(enc, True, False) = True  ✓
     encode(False) = λt.λf.f  →  decode: apply(enc, True, False) = False ✓

  2. Church numerals:
     encode(n) = λf.λx.f^n(x)  →  decode: apply(enc, (+1), 0) = n  ✓
     by induction on n.

  3. Church pairs:
     encode((a,b)) = λf.f(a)(b)  →  decode: apply(enc, λa.λb.(a,b)) = (a,b)  ✓

  4. Scott encoding for tagged union A + B:
     encode(Left(a))  = λl.λr.l(a)
     encode(Right(b)) = λl.λr.r(b)
     Decode: apply to case handlers.  Round-trip by β-reduction.

  5. isinstance dispatch ↔ method dispatch:
     isinstance(x, T) then f(x)  ≡  x.f()  when f is a method of T.
     This is exactly the Scott eliminator: the object "knows" its case.  ∎
"""

COMPOSES_WITH = ['D02_beta', 'D24_eta', 'D21_dispatch']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Church True to boolean',
        'before': "λt.λf.t",
        'after': "True",
        'axiom': 'D33_church_bool_true',
    },
    {
        'name': 'Church False to boolean',
        'before': "λt.λf.f",
        'after': "False",
        'axiom': 'D33_church_bool_false',
    },
    {
        'name': 'Boolean to Church True',
        'before': "True",
        'after': "λt.λf.t",
        'axiom': 'D33_bool_to_church_true',
    },
    {
        'name': 'Church pair to tuple',
        'before': "λf.f(a)(b)",
        'after': "(a, b)",
        'axiom': 'D33_church_pair_decode',
    },
    {
        'name': 'isinstance to method dispatch',
        'before': "isinstance(x, T) → f(x)",
        'after': "x.f()",
        'axiom': 'D33_isinstance_to_method',
    },
    {
        'name': 'if/elif chain to match/visitor',
        'before': "if isinstance(x, A): ... elif isinstance(x, B): ...",
        'after': "match x: case A: ... case B: ...",
        'axiom': 'D33_isinstance_chain_to_match',
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


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D33 Church/Scott encoding equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Church boolean True: λt.λf.t → True ──
    if isinstance(term, OLam) and len(term.params) == 2:
        t_param, f_param = term.params
        body = term.body
        if isinstance(body, OVar) and body.name == t_param:
            results.append((OLit(True), 'D33_church_bool_true'))
        elif isinstance(body, OVar) and body.name == f_param:
            results.append((OLit(False), 'D33_church_bool_false'))

    # ── True/False → Church booleans ──
    if isinstance(term, OLit) and term.value is True:
        results.append((
            OLam(('_t', '_f'), OVar('_t')),
            'D33_bool_to_church_true',
        ))
    if isinstance(term, OLit) and term.value is False:
        results.append((
            OLam(('_t', '_f'), OVar('_f')),
            'D33_bool_to_church_false',
        ))

    # ── Church pair: λf.f(a)(b) → (a, b) ──
    # Detect: OLam(('f',), OOp('call', (OOp('call', (OVar('f'), a)), b)))
    # or simplified: OLam(('f',), OOp('apply', (OVar('f'), a, b)))
    if isinstance(term, OLam) and len(term.params) == 1:
        f_param = term.params[0]
        body = term.body
        pair_elems = _extract_church_pair(body, f_param)
        if pair_elems is not None:
            a, b = pair_elems
            results.append((OSeq((a, b)), 'D33_church_pair_decode'))

    # ── (a, b) → Church pair λf.f(a)(b) ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        a, b = term.elements
        fv = _extract_free_vars(a) | _extract_free_vars(b)
        fp = '_cp'
        while fp in fv:
            fp = fp + '_'
        church_pair = OLam(
            (fp,),
            OOp('call', (OOp('call', (OVar(fp), a)), b)),
        )
        results.append((church_pair, 'D33_tuple_to_church_pair'))

    # ── isinstance chain → Scott dispatch / OCase chain ──
    # Pattern: OCase(isinstance(x, T1), body1, OCase(isinstance(x, T2), body2, ...))
    if isinstance(term, OCase):
        chain = _extract_isinstance_chain(term)
        if chain is not None and len(chain) >= 2:
            # Convert to Scott-style dispatch: OOp('scott_dispatch', (x, ...handlers))
            x_term = chain[0][0]  # the dispatched object
            handlers = tuple(
                OSeq((OLit(type_name), handler))
                for x_term_, type_name, handler in chain
            )
            results.append((
                OOp('scott_dispatch', (x_term,) + handlers),
                'D33_isinstance_chain_to_scott',
            ))

    # ── isinstance(x, T) test → type_tag check ──
    if isinstance(term, OOp) and term.name == 'isinstance' and len(term.args) == 2:
        x, t = term.args
        results.append((
            OOp('eq', (OOp('.type_tag', (x,)), t)),
            'D33_isinstance_to_tag',
        ))

    # ── Scott dispatch → isinstance chain (reverse) ──
    if isinstance(term, OOp) and term.name == 'scott_dispatch':
        if len(term.args) >= 2:
            x = term.args[0]
            handlers = term.args[1:]
            # Build nested OCase from handlers
            case_tree = _build_isinstance_chain(x, handlers)
            if case_tree is not None:
                results.append((case_tree, 'D33_scott_to_isinstance_chain'))

    # ── Method dispatch ↔ isinstance dispatch ──
    # x.method() where x has known type → isinstance(x, T) then T.method(x)
    if isinstance(term, OOp) and term.name.startswith('.') and len(term.args) == 1:
        method_name = term.name[1:]
        x = term.args[0]
        results.append((
            OOp('dispatch_call', (x, OLit(method_name))),
            'D33_method_to_dispatch',
        ))

    # ── Church numeral detection: λf.λx.f(f(...(x)...)) → n ──
    if isinstance(term, OLam) and len(term.params) == 2:
        f_param, x_param = term.params
        n = _count_church_applications(term.body, f_param, x_param)
        if n is not None:
            results.append((OLit(n), 'D33_church_numeral_decode'))

    # ── Integer → Church numeral ──
    if isinstance(term, OLit) and isinstance(term.value, int) and term.value >= 0:
        n = term.value
        if n <= 10:  # only encode small numerals
            body = _build_church_numeral_body(n, '_cf', '_cx')
            results.append((
                OLam(('_cf', '_cx'), body),
                'D33_int_to_church_numeral',
            ))

    # ── if/else with boolean → Church boolean application ──
    if isinstance(term, OCase):
        test = term.test
        t_branch = term.true_branch
        f_branch = term.false_branch
        if isinstance(test, OLit) and test.value in (True, False):
            if test.value is True:
                results.append((t_branch, 'D33_church_bool_elim_true'))
            else:
                results.append((f_branch, 'D33_church_bool_elim_false'))

    return results


def _extract_church_pair(body: OTerm, f_param: str) -> Optional[Tuple[OTerm, OTerm]]:
    """Extract (a, b) from Church pair body f(a)(b)."""
    # Pattern: OOp('call', (OOp('call', (OVar(f), a)), b))
    if isinstance(body, OOp) and body.name == 'call' and len(body.args) == 2:
        inner, b = body.args
        if isinstance(inner, OOp) and inner.name == 'call' and len(inner.args) == 2:
            f_var, a = inner.args
            if isinstance(f_var, OVar) and f_var.name == f_param:
                return (a, b)
    # Alternate: OOp('apply', (OVar(f), a, b))
    if isinstance(body, OOp) and body.name == 'apply' and len(body.args) == 3:
        f_var, a, b = body.args
        if isinstance(f_var, OVar) and f_var.name == f_param:
            return (a, b)
    return None


def _count_church_applications(body: OTerm, f: str, x: str) -> Optional[int]:
    """Count how many times f is applied in f(f(...(x)...))."""
    if isinstance(body, OVar) and body.name == x:
        return 0
    if isinstance(body, OOp) and body.name in ('call', f) and len(body.args) >= 1:
        if isinstance(body, OOp) and body.name == 'call' and len(body.args) == 2:
            func, arg = body.args
            if isinstance(func, OVar) and func.name == f:
                inner = _count_church_applications(arg, f, x)
                if inner is not None:
                    return inner + 1
        elif isinstance(body, OOp) and body.name == f and len(body.args) == 1:
            inner = _count_church_applications(body.args[0], f, x)
            if inner is not None:
                return inner + 1
    return None


def _build_church_numeral_body(n: int, f: str, x: str) -> OTerm:
    """Build f^n(x) as an OTerm."""
    result: OTerm = OVar(x)
    for _ in range(n):
        result = OOp('call', (OVar(f), result))
    return result


def _extract_isinstance_chain(
    term: OTerm,
) -> Optional[List[Tuple[OTerm, str, OTerm]]]:
    """Extract [(x, type_name, handler), ...] from nested isinstance OCase."""
    chain: List[Tuple[OTerm, str, OTerm]] = []
    current = term
    while isinstance(current, OCase):
        test = current.test
        if isinstance(test, OOp) and test.name == 'isinstance' and len(test.args) == 2:
            x = test.args[0]
            t = test.args[1]
            type_name = t.canon() if not isinstance(t, OLit) else str(t.value)
            chain.append((x, type_name, current.true_branch))
            current = current.false_branch
        else:
            break
    if len(chain) >= 2:
        return chain
    return None


def _build_isinstance_chain(
    x: OTerm, handlers: Tuple[OTerm, ...],
) -> Optional[OTerm]:
    """Build nested OCase from Scott dispatch handlers."""
    if not handlers:
        return OUnknown('no_match')
    # Each handler is OSeq((OLit(type_name), body))
    parts: List[Tuple[str, OTerm]] = []
    for h in handlers:
        if isinstance(h, OSeq) and len(h.elements) == 2:
            type_lit, body = h.elements
            if isinstance(type_lit, OLit):
                parts.append((str(type_lit.value), body))
            else:
                return None
        else:
            return None
    if not parts:
        return None
    # Build from last to first
    result: OTerm = OUnknown('no_match')
    for type_name, body in reversed(parts):
        test = OOp('isinstance', (x, OLit(type_name)))
        result = OCase(test, body, result)
    return result


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D33 in reverse: decoded values → encodings."""
    results = apply(term, ctx)
    inverse_labels = {
        'D33_bool_to_church_true',
        'D33_bool_to_church_false',
        'D33_tuple_to_church_pair',
        'D33_int_to_church_numeral',
        'D33_scott_to_isinstance_chain',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D33 is potentially applicable to *term*."""
    if isinstance(term, OLam):
        if len(term.params) == 2:
            # Could be Church boolean or numeral
            return True
        if len(term.params) == 1:
            # Could be Church pair
            body = term.body
            if isinstance(body, OOp) and body.name in ('call', 'apply'):
                return True
    if isinstance(term, OLit):
        if term.value is True or term.value is False:
            return True
        if isinstance(term.value, int) and 0 <= term.value <= 10:
            return True
    if isinstance(term, OSeq) and len(term.elements) == 2:
        return True
    if isinstance(term, OOp):
        if term.name in ('isinstance', 'scott_dispatch', 'dispatch_call'):
            return True
        if term.name.startswith('.') and len(term.args) == 1:
            return True
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'isinstance':
            return True
        if isinstance(term.test, OLit) and term.test.value in (True, False):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D33 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    church_kw = ('λ(', 'call(', 'church', 'scott_dispatch(')
    data_kw = ('True', 'False', 'isinstance(', 'dispatch_call(')

    has_church_s = any(k in sc for k in church_kw)
    has_church_t = any(k in tc for k in church_kw)
    has_data_s = any(k in sc for k in data_kw)
    has_data_t = any(k in tc for k in data_kw)

    if (has_church_s and has_data_t) or (has_data_s and has_church_t):
        return 0.95
    if has_church_s != has_church_t:
        return 0.85
    if 'isinstance(' in sc or 'isinstance(' in tc:
        return 0.75
    if has_church_s or has_church_t:
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

    # ── Church boolean True: λt.λf.t → True ──
    print("D33: Church boolean True ...")
    church_true = OLam(('t', 'f'), OVar('t'))
    r = apply(church_true, ctx)
    _assert(any(lbl == 'D33_church_bool_true' for _, lbl in r), "church True")
    true_results = [t for t, lbl in r if lbl == 'D33_church_bool_true']
    _assert(len(true_results) >= 1 and isinstance(true_results[0], OLit)
            and true_results[0].value is True, "church True → True")

    # ── Church boolean False: λt.λf.f → False ──
    print("D33: Church boolean False ...")
    church_false = OLam(('t', 'f'), OVar('f'))
    r2 = apply(church_false, ctx)
    _assert(any(lbl == 'D33_church_bool_false' for _, lbl in r2), "church False")

    # ── True → Church True ──
    print("D33: True → Church True ...")
    r3 = apply(OLit(True), ctx)
    _assert(any(lbl == 'D33_bool_to_church_true' for _, lbl in r3), "True→church")

    # ── False → Church False ──
    print("D33: False → Church False ...")
    r4 = apply(OLit(False), ctx)
    _assert(any(lbl == 'D33_bool_to_church_false' for _, lbl in r4), "False→church")

    # ── Roundtrip: True → Church → True ──
    print("D33: roundtrip True ...")
    encoded = [t for t, lbl in r3 if lbl == 'D33_bool_to_church_true']
    _assert(len(encoded) >= 1, "roundtrip step 1")
    decoded = apply(encoded[0], ctx)
    _assert(any(lbl == 'D33_church_bool_true' for _, lbl in decoded), "roundtrip step 2")

    # ── Church numeral: λf.λx.f(f(x)) → 2 ──
    print("D33: Church numeral ...")
    church_2 = OLam(
        ('f', 'x'),
        OOp('call', (OVar('f'), OOp('call', (OVar('f'), OVar('x'))))),
    )
    r5 = apply(church_2, ctx)
    _assert(any(lbl == 'D33_church_numeral_decode' for _, lbl in r5), "church numeral 2")
    num_results = [t for t, lbl in r5 if lbl == 'D33_church_numeral_decode']
    _assert(len(num_results) >= 1 and isinstance(num_results[0], OLit)
            and num_results[0].value == 2, "church 2 → 2")

    # ── Church numeral zero: λf.λx.x → 0 ──
    print("D33: Church numeral zero ...")
    church_0 = OLam(('f', 'x'), OVar('x'))
    r6 = apply(church_0, ctx)
    _assert(any(lbl == 'D33_church_numeral_decode' for _, lbl in r6), "church numeral 0")

    # ── Integer → Church numeral ──
    print("D33: Integer → Church numeral ...")
    r7 = apply(OLit(3), ctx)
    _assert(any(lbl == 'D33_int_to_church_numeral' for _, lbl in r7), "3→church")

    # ── Church pair: λf.f(a)(b) → (a, b) ──
    print("D33: Church pair ...")
    a, b = OVar('a'), OVar('b')
    church_pair = OLam(
        ('f',),
        OOp('call', (OOp('call', (OVar('f'), a)), b)),
    )
    r8 = apply(church_pair, ctx)
    _assert(any(lbl == 'D33_church_pair_decode' for _, lbl in r8), "church pair decode")

    # ── Tuple → Church pair ──
    print("D33: Tuple → Church pair ...")
    pair = OSeq((a, b))
    r9 = apply(pair, ctx)
    _assert(any(lbl == 'D33_tuple_to_church_pair' for _, lbl in r9), "tuple→church pair")

    # ── isinstance chain → Scott dispatch ──
    print("D33: isinstance chain → Scott dispatch ...")
    chain = OCase(
        OOp('isinstance', (OVar('x'), OLit('Circle'))),
        OOp('area_circle', (OVar('x'),)),
        OCase(
            OOp('isinstance', (OVar('x'), OLit('Square'))),
            OOp('area_square', (OVar('x'),)),
            OUnknown('no_match'),
        ),
    )
    r10 = apply(chain, ctx)
    _assert(any(lbl == 'D33_isinstance_chain_to_scott' for _, lbl in r10),
            "isinstance→scott")

    # ── isinstance → tag check ──
    print("D33: isinstance → tag check ...")
    isinst = OOp('isinstance', (OVar('x'), OLit('int')))
    r11 = apply(isinst, ctx)
    _assert(any(lbl == 'D33_isinstance_to_tag' for _, lbl in r11), "isinstance→tag")

    # ── recognizes() ──
    print("D33: recognizes ...")
    _assert(recognizes(church_true), "recognizes church True")
    _assert(recognizes(OLit(True)), "recognizes True literal")
    _assert(recognizes(isinst), "recognizes isinstance")
    _assert(recognizes(pair), "recognizes pair/tuple")
    _assert(not recognizes(OOp('sorted', (OVar('xs'),))), "does not recognise sorted")

    # ── relevance_score ──
    print("D33: relevance_score ...")
    score = relevance_score(church_true, OLit(True))
    _assert(score > 0.8, f"church↔bool score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (OVar('xs'),)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D33: apply_inverse ...")
    inv = apply_inverse(OLit(True), ctx)
    _assert(any(lbl == 'D33_bool_to_church_true' for _, lbl in inv), "inverse True→church")

    # ── if/else with literal boolean → branch elimination ──
    print("D33: boolean elimination ...")
    cond_true = OCase(OLit(True), OVar('a'), OVar('b'))
    r12 = apply(cond_true, ctx)
    _assert(any(lbl == 'D33_church_bool_elim_true' for _, lbl in r12), "if True → a")
    elim_results = [t for t, lbl in r12 if lbl == 'D33_church_bool_elim_true']
    _assert(len(elim_results) >= 1 and isinstance(elim_results[0], OVar)
            and elim_results[0].name == 'a', "if True a b → a")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D33 encoding: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
