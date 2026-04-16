"""P9: Exception Pattern Equivalences (Theorem 31.2.1).

EAFP ↔ LBYL ↔ context-manager ↔ suppress — canonical exception idioms.

Mathematical foundation:
  Exception handling defines a partial-function algebra with a monad
  T_E(A) = A + E for exception type E.  The ``try/except`` construct is
  the bind of this monad, while ``dict.get`` and conditional guards are
  total-function representations of the same partial map.

  The equivalence is witnessed by a natural isomorphism in the Kleisli
  category of the exception monad:

    OCatch(f, default)  ≅  OCase(guard, f, default)

  when the guard exactly characterises the domain where f does not
  raise.

Covers:
  • EAFP dict lookup:    try: d[k] except KeyError: default  ↔  d.get(k, default)
  • Safe cast:           try: int(s) except ValueError: None  ↔  int(s) if s.isdigit() else None
  • Context manager:     with open(f) as fh: body  ↔  try/finally with explicit close
  • suppress(Error):     suppress(body, Error)  ↔  try: body except Error: pass
  • Merged except:       except (A, B): handler  ↔  except A: handler; except B: handler
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

AXIOM_NAME = 'P9_exceptions'
AXIOM_CATEGORY = 'python_idiom'  # §31 — Pythonic exception patterns

SOUNDNESS_PROOF = """
Theorem 31.2.1 (EAFP–LBYL Equivalence):
  For a dict d and key k,
    try: d[k] except KeyError: default  ≡  d.get(k, default)
  as morphisms  (Dict × Key) → Value  in the Kleisli category of T_E.

Proof sketch:
  1. d[k] raises KeyError iff k ∉ dom(d).
  2. d.get(k, default) returns default iff k ∉ dom(d).
  3. In both cases the observable result is the same value.  ∎

Corollary (Safe Cast):
  try: int(s) except ValueError: None  ≡  int(s) if s.isdigit() else None
  when s contains no leading/trailing whitespace or sign characters
  (the guard isdigit() is a conservative approximation of the domain).

Context-Manager Equivalence:
  with open(f) as fh: body(fh)
  ≡  fh = open(f); try: body(fh); finally: fh.close()
  by the context-manager protocol (__enter__/__exit__).

Suppress Equivalence:
  contextlib.suppress(E)(body)  ≡  try: body except E: pass
  by definition of suppress.
"""

COMPOSES_WITH = ['D22_effect_elim', 'P10_class_patterns']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'EAFP dict get',
        'before': "try: d[k] except KeyError: default",
        'after': "d.get(k, default)",
        'axiom': 'P9_eafp_dict_to_get',
    },
    {
        'name': 'LBYL dict get (inverse)',
        'before': "d.get(k, default)",
        'after': "try: d[k] except KeyError: default",
        'axiom': 'P9_get_to_eafp_dict',
    },
    {
        'name': 'Safe int cast',
        'before': "try: int(s) except ValueError: None",
        'after': "int(s) if s.isdigit() else None",
        'axiom': 'P9_safe_cast_to_guard',
    },
    {
        'name': 'Context manager to try/finally',
        'before': "with open(f) as fh: fh.read()",
        'after': "fh = open(f); try: fh.read(); finally: fh.close()",
        'axiom': 'P9_context_manager_to_try_finally',
    },
    {
        'name': 'Suppress to try/except pass',
        'before': "suppress(body, Error)",
        'after': "try: body except Error: pass",
        'axiom': 'P9_suppress_to_catch',
    },
    {
        'name': 'Merged except clauses',
        'before': "except (A, B): handler",
        'after': "except A: handler; except B: handler",
        'axiom': 'P9_merged_except_to_nested',
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
    """Apply P9 exception-pattern equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── EAFP dict: OCatch(getitem(d, k), default) → d.get(k, default) ──
    if isinstance(term, OCatch):
        body = term.body
        default = term.default
        if isinstance(body, OOp) and body.name == 'getitem' and len(body.args) == 2:
            d, k = body.args
            results.append((
                OOp('.get', (d, k, default)),
                'P9_eafp_dict_to_get',
            ))

    # ── d.get(k, default) → OCatch(getitem(d, k), default) ──
    if isinstance(term, OOp) and term.name == '.get' and len(term.args) == 3:
        d, k, default = term.args
        results.append((
            OCatch(OOp('getitem', (d, k)), default),
            'P9_get_to_eafp_dict',
        ))

    # ── Safe cast: OCatch(int(s), None) → OCase(isdigit, int(s), None) ──
    if isinstance(term, OCatch):
        body = term.body
        default = term.default
        if (isinstance(body, OOp) and body.name == 'int'
                and len(body.args) == 1
                and isinstance(default, OLit) and default.value is None):
            s = body.args[0]
            guard = OOp('.isdigit', (s,))
            results.append((
                OCase(guard, OOp('int', (s,)), OLit(None)),
                'P9_safe_cast_to_guard',
            ))

    # ── Guard-based cast → OCatch: OCase(isdigit(s), int(s), None) → OCatch ──
    if isinstance(term, OCase):
        if (isinstance(term.test, OOp) and term.test.name == '.isdigit'
                and len(term.test.args) == 1
                and isinstance(term.true_branch, OOp)
                and term.true_branch.name == 'int'
                and isinstance(term.false_branch, OLit)
                and term.false_branch.value is None):
            s = term.test.args[0]
            results.append((
                OCatch(OOp('int', (s,)), OLit(None)),
                'P9_guard_to_safe_cast',
            ))

    # ── Context manager: with_context(open(f), body) → try/finally ──
    if isinstance(term, OOp) and term.name == 'with_context' and len(term.args) == 2:
        resource_expr, body = term.args
        if isinstance(resource_expr, OOp) and resource_expr.name == 'open':
            fh = OVar('_fh')
            cleanup = OOp('.close', (fh,))
            try_finally = OSeq((
                OOp('assign', (fh, resource_expr)),
                OCatch(
                    OOp('apply_with', (body, fh)),
                    OOp('raise_after', (cleanup,)),
                ),
                cleanup,
            ))
            results.append((try_finally, 'P9_context_manager_to_try_finally'))

    # ── try/finally with assign+close → with_context (inverse) ──
    if isinstance(term, OSeq) and len(term.elements) >= 3:
        elems = term.elements
        if (isinstance(elems[0], OOp) and elems[0].name == 'assign'
                and len(elems[0].args) == 2
                and isinstance(elems[0].args[1], OOp)
                and elems[0].args[1].name == 'open'):
            resource_expr = elems[0].args[1]
            if isinstance(elems[-1], OOp) and elems[-1].name == '.close':
                body = elems[1] if len(elems) == 3 else OSeq(tuple(elems[1:-1]))
                results.append((
                    OOp('with_context', (resource_expr, body)),
                    'P9_try_finally_to_context_manager',
                ))

    # ── suppress(body, error_type) → OCatch(body, None) ──
    if isinstance(term, OOp) and term.name == 'suppress' and len(term.args) == 2:
        body, error_type = term.args
        results.append((
            OCatch(body, OLit(None)),
            'P9_suppress_to_catch',
        ))

    # ── OCatch(body, None) → suppress(body, Exception) (inverse) ──
    if isinstance(term, OCatch):
        if isinstance(term.default, OLit) and term.default.value is None:
            body = term.body
            if not (isinstance(body, OOp) and body.name in ('getitem', 'int')):
                results.append((
                    OOp('suppress', (body, OVar('Exception'))),
                    'P9_catch_to_suppress',
                ))

    # ── Merged except: OCatch with tuple error → nested OCatch ──
    if isinstance(term, OOp) and term.name == 'catch_multi' and len(term.args) == 3:
        body, error_tuple, handler = term.args
        if isinstance(error_tuple, OSeq) and len(error_tuple.elements) >= 2:
            inner = handler
            for exc_type in reversed(error_tuple.elements):
                inner = OCatch(body, inner)
            results.append((inner, 'P9_merged_except_to_nested'))

    # ── Nested OCatch with same handler → merged except (inverse) ──
    if isinstance(term, OCatch) and isinstance(term.body, OTerm):
        if isinstance(term.default, OCatch):
            outer_body = term.body
            inner = term.default
            if (isinstance(inner, OCatch)
                    and _terms_structurally_equal(outer_body, inner.body)):
                error_types = [OVar('E1'), OVar('E2')]
                results.append((
                    OOp('catch_multi', (
                        outer_body,
                        OSeq(tuple(error_types)),
                        inner.default,
                    )),
                    'P9_nested_to_merged_except',
                ))

    return results


def _terms_structurally_equal(a: OTerm, b: OTerm) -> bool:
    """Shallow structural equality check for OTerms."""
    return a.canon() == b.canon()


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P9 in reverse direction.

    Inverse rewrites select the complementary direction from apply().
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P9_get_to_eafp_dict',
        'P9_guard_to_safe_cast',
        'P9_try_finally_to_context_manager',
        'P9_catch_to_suppress',
        'P9_nested_to_merged_except',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P9 is potentially applicable to *term*."""
    if isinstance(term, OCatch):
        return True
    if isinstance(term, OOp):
        if term.name in ('.get', 'suppress', 'with_context', 'catch_multi'):
            return True
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == '.isdigit':
            return True
    if isinstance(term, OSeq) and len(term.elements) >= 3:
        elems = term.elements
        if (isinstance(elems[0], OOp) and elems[0].name == 'assign'
                and isinstance(elems[-1], OOp) and elems[-1].name == '.close'):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P9 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_catch_s = 'OCatch(' in sc or 'catch' in sc.lower()
    has_catch_t = 'OCatch(' in tc or 'catch' in tc.lower()
    has_get_s = '.get(' in sc
    has_get_t = '.get(' in tc
    has_with_s = 'with_context(' in sc
    has_with_t = 'with_context(' in tc
    has_suppress_s = 'suppress(' in sc
    has_suppress_t = 'suppress(' in tc

    # EAFP ↔ LBYL crossover → high relevance
    if has_catch_s and has_get_t:
        return 0.95
    if has_get_s and has_catch_t:
        return 0.95

    # Context manager ↔ try/finally
    if has_with_s != has_with_t:
        return 0.90

    # suppress ↔ catch
    if has_suppress_s != has_suppress_t:
        return 0.85

    # Any exception-related term on either side
    if has_catch_s or has_catch_t:
        return 0.50

    if has_suppress_s or has_suppress_t:
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
    d = OVar('d')
    k = OVar('k')
    s = OVar('s')
    f = OVar('f')
    default = OVar('default')

    # ── EAFP dict → .get ──
    print("P9: EAFP dict → .get ...")
    eafp_term = OCatch(OOp('getitem', (d, k)), default)
    r = apply(eafp_term, ctx)
    _assert(any(lbl == 'P9_eafp_dict_to_get' for _, lbl in r), "EAFP→get")
    get_result = [t for t, lbl in r if lbl == 'P9_eafp_dict_to_get'][0]
    _assert(isinstance(get_result, OOp) and get_result.name == '.get', "result is .get")

    # ── .get → EAFP dict ──
    print("P9: .get → EAFP dict ...")
    get_term = OOp('.get', (d, k, default))
    r2 = apply(get_term, ctx)
    _assert(any(lbl == 'P9_get_to_eafp_dict' for _, lbl in r2), "get→EAFP")
    catch_result = [t for t, lbl in r2 if lbl == 'P9_get_to_eafp_dict'][0]
    _assert(isinstance(catch_result, OCatch), "result is OCatch")

    # ── Roundtrip EAFP ↔ .get ──
    print("P9: roundtrip EAFP ↔ .get ...")
    rt = apply(get_result, ctx)
    _assert(any(lbl == 'P9_get_to_eafp_dict' for _, lbl in rt), "roundtrip works")

    # ── Safe cast → guard ──
    print("P9: safe cast → guard ...")
    cast_term = OCatch(OOp('int', (s,)), OLit(None))
    r3 = apply(cast_term, ctx)
    _assert(any(lbl == 'P9_safe_cast_to_guard' for _, lbl in r3), "cast→guard")
    guard_result = [t for t, lbl in r3 if lbl == 'P9_safe_cast_to_guard'][0]
    _assert(isinstance(guard_result, OCase), "result is OCase")

    # ── Guard → safe cast ──
    print("P9: guard → safe cast ...")
    guard_term = OCase(OOp('.isdigit', (s,)), OOp('int', (s,)), OLit(None))
    r4 = apply(guard_term, ctx)
    _assert(any(lbl == 'P9_guard_to_safe_cast' for _, lbl in r4), "guard→cast")

    # ── Context manager → try/finally ──
    print("P9: context manager → try/finally ...")
    with_term = OOp('with_context', (OOp('open', (f,)), OVar('body')))
    r5 = apply(with_term, ctx)
    _assert(any(lbl == 'P9_context_manager_to_try_finally' for _, lbl in r5),
            "with→try/finally")

    # ── suppress → catch ──
    print("P9: suppress → catch ...")
    suppress_term = OOp('suppress', (OVar('body'), OVar('KeyError')))
    r6 = apply(suppress_term, ctx)
    _assert(any(lbl == 'P9_suppress_to_catch' for _, lbl in r6), "suppress→catch")
    catch_r = [t for t, lbl in r6 if lbl == 'P9_suppress_to_catch'][0]
    _assert(isinstance(catch_r, OCatch), "suppress result is OCatch")

    # ── Merged except → nested ──
    print("P9: merged except → nested ...")
    merged = OOp('catch_multi', (
        OVar('body'),
        OSeq((OVar('A'), OVar('B'))),
        OVar('handler'),
    ))
    r7 = apply(merged, ctx)
    _assert(any(lbl == 'P9_merged_except_to_nested' for _, lbl in r7), "merged→nested")

    # ── recognizes() ──
    print("P9: recognizes ...")
    _assert(recognizes(eafp_term), "recognizes OCatch")
    _assert(recognizes(get_term), "recognizes .get")
    _assert(recognizes(suppress_term), "recognizes suppress")
    _assert(recognizes(guard_term), "recognizes guard/isdigit")
    _assert(not recognizes(OOp('sorted', (OVar('xs'),))), "does not recognise sorted")

    # ── relevance_score ──
    print("P9: relevance_score ...")
    score = relevance_score(eafp_term, get_term)
    _assert(score > 0.8, f"EAFP↔get score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (OVar('xs'),)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P9: apply_inverse ...")
    inv = apply_inverse(get_term, ctx)
    _assert(len(inv) >= 1, "inverse of .get produces OCatch")
    _assert(all(lbl in (
        'P9_get_to_eafp_dict', 'P9_guard_to_safe_cast',
        'P9_try_finally_to_context_manager', 'P9_catch_to_suppress',
        'P9_nested_to_merged_except',
    ) for _, lbl in inv), "inverse labels correct")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P9 exceptions: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
