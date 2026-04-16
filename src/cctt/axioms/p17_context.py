"""P17 Axiom: Context Manager / Resource Pattern Equivalences.

Establishes equivalences between Python context manager patterns
and their manual resource-management counterparts.

Mathematical basis: Context managers implement the bracket pattern
from effect systems:
    bracket(acquire, use, release) ≡ with acquire() as r: use(r)
This is a monoidal operation in the effect category — the resource
is acquired, used, and released regardless of exception outcome.

Key rewrites:
  • with open(f) as fh: fh.read()  ↔  open(f).read()  (read-only)
  • contextlib.suppress(E)          ↔  try: ... except E: pass
  • with lock: body                 ↔  lock.acquire(); try: body; finally: lock.release()
  • tempfile patterns

(§P17, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P17_context"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D22_effect_elim", "D24_eta"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P17 Context Manager Equivalence).

1. with open(f) as fh: return fh.read()
   ≡ open(f).read()
   When used for read-only with no exception handling, the
   context manager's __exit__ calls fh.close(), which also
   happens when fh is garbage collected.  For correctness,
   the context manager form is preferred, but the semantics
   of the return value are identical.

2. contextlib.suppress(E): body
   ≡ try: body; except E: pass
   suppress(E) catches and discards exceptions of type E.

3. with lock: body
   ≡ lock.acquire(); try: body; finally: lock.release()
   The lock context manager is syntactic sugar for
   acquire/release with guaranteed release via finally.

4. @contextmanager def cm(): yield resource
   The generator-based context manager protocol:
   code before yield = __enter__,
   code after yield = __exit__.
"""

EXAMPLES = [
    ("with_open_read($f)", "open_read($f)", "P17_with_open_to_read"),
    ("suppress($e, $body)", "catch($body, noop)", "P17_suppress_to_catch"),
    ("with_lock($lock, $body)", "bracket(acquire($lock), $body, release($lock))",
     "P17_lock_bracket"),
]

# Context manager operation names
_CONTEXT_OPS = frozenset({
    'with_open', 'with_open_read', 'with_open_write',
    'with_lock', 'with_suppress', 'with_tempfile',
    'with_redirect', 'with_context',
})


def _is_with_open_read(term: OTerm) -> Optional[Tuple[OTerm, OTerm]]:
    """Detect with_open(f, mode, λfh.fh.read()) → (f, read_body)."""
    if isinstance(term, OOp) and term.name in ('with_open', 'with_open_read'):
        if len(term.args) >= 2:
            f = term.args[0]
            body = term.args[-1]
            if isinstance(body, OLam) and len(body.params) == 1:
                if (isinstance(body.body, OOp)
                        and body.body.name == '.read'
                        and len(body.body.args) == 1
                        and isinstance(body.body.args[0], OVar)
                        and body.body.args[0].name == body.params[0]):
                    return (f, body.body)
            return (f, body)
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P17: Context manager rewrites.

    Handles:
      1. with_open_read(f, λfh.fh.read()) → open_read(f)
      2. with_suppress(E, body) → catch(body, noop)
      3. with_lock(lock, body) → bracket(acquire, body, release)
      4. bracket(acquire, body, release) → with_context(...)
      5. catch(body, noop) → suppress(E, body)
      6. with_tempfile patterns
      7. with_redirect(stdout, f, body)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. with_open_read(f, λfh.fh.read()) → open_read(f) ──
    match = _is_with_open_read(term)
    if match is not None:
        f, body = match
        if isinstance(body, OOp) and body.name == '.read':
            results.append((
                OOp('.read', (OOp('open', (f,)),)),
                'P17_with_open_read_to_direct',
            ))
        # General: with_open(f, body) → bracket(open(f), body, close)
        if isinstance(term, OOp) and len(term.args) >= 2:
            body_term = term.args[-1]
            results.append((
                OOp('bracket', (OOp('open', (f,)), body_term,
                                OOp('close', ()))),
                'P17_with_open_to_bracket',
            ))

    # ── 2. with_suppress(E, body) ↔ catch(body, noop) ──
    if isinstance(term, OOp) and term.name == 'with_suppress' and len(term.args) == 2:
        exc_type, body = term.args
        results.append((
            OCatch(body, OLit(None)),
            'P17_suppress_to_catch',
        ))

    if isinstance(term, OCatch) and isinstance(term.default, OLit) and term.default.value is None:
        results.append((
            OOp('with_suppress', (OOp('Exception', ()), term.body)),
            'P17_catch_noop_to_suppress',
        ))

    # ── 3. with_lock(lock, body) → bracket(acquire, body, release) ──
    if isinstance(term, OOp) and term.name == 'with_lock' and len(term.args) == 2:
        lock, body = term.args
        results.append((
            OOp('bracket', (
                OOp('.acquire', (lock,)),
                body,
                OOp('.release', (lock,)),
            )),
            'P17_lock_to_bracket',
        ))

    # ── 4. bracket(acquire(lock), body, release(lock)) → with_lock ──
    if isinstance(term, OOp) and term.name == 'bracket' and len(term.args) == 3:
        acquire, body, release = term.args
        if (isinstance(acquire, OOp) and acquire.name == '.acquire'
                and isinstance(release, OOp) and release.name == '.release'):
            if len(acquire.args) == 1 and len(release.args) == 1:
                if acquire.args[0].canon() == release.args[0].canon():
                    results.append((
                        OOp('with_lock', (acquire.args[0], body)),
                        'P17_bracket_to_with_lock',
                    ))

    # ── 5. with_redirect(stdout, file, body) ──
    if isinstance(term, OOp) and term.name == 'with_redirect' and len(term.args) == 3:
        stream, target, body = term.args
        results.append((
            OOp('bracket', (
                OOp('redirect_set', (stream, target)),
                body,
                OOp('redirect_restore', (stream,)),
            )),
            'P17_redirect_to_bracket',
        ))

    # ── 6. with_tempfile(body) → bracket(mktemp, body, unlink) ──
    if isinstance(term, OOp) and term.name == 'with_tempfile' and len(term.args) >= 1:
        body = term.args[-1]
        results.append((
            OOp('bracket', (
                OOp('mktemp', ()),
                body,
                OOp('unlink', ()),
            )),
            'P17_tempfile_to_bracket',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _CONTEXT_OPS:
        return True
    if isinstance(term, OOp) and term.name == 'bracket':
        return True
    if isinstance(term, OCatch):
        if isinstance(term.default, OLit) and term.default.value is None:
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('with_', 'bracket', 'suppress', 'catch', 'open'):
        if kw in sc and kw in tc:
            return 0.8
    if 'bracket' in sc or 'bracket' in tc:
        return 0.6
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand bracket back to with statement."""
    results: List[Tuple[OTerm, str]] = []

    # open_read(f) → with_open_read(f, λfh.fh.read())
    if isinstance(term, OOp) and term.name == '.read' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'open' and len(inner.args) == 1:
            f = inner.args[0]
            lam = OLam(('_fh',), OOp('.read', (OVar('_fh'),)))
            results.append((
                OOp('with_open_read', (f, lam)),
                'P17_inv_direct_to_with_open',
            ))

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

    # 1. with_open_read → direct read
    lam1 = OLam(('fh',), OOp('.read', (OVar('fh'),)))
    t1 = OOp('with_open_read', (OVar('f'), lam1))
    r1 = apply(t1)
    _assert(any(a == 'P17_with_open_read_to_direct' for _, a in r1), "with_open → direct")

    # 2. with_suppress → catch
    t2 = OOp('with_suppress', (OVar('ValueError'), OVar('body')))
    r2 = apply(t2)
    _assert(any(a == 'P17_suppress_to_catch' for _, a in r2), "suppress → catch")

    # 3. catch(body, None) → suppress
    t3 = OCatch(OVar('body'), OLit(None))
    r3 = apply(t3)
    _assert(any(a == 'P17_catch_noop_to_suppress' for _, a in r3), "catch → suppress")

    # 4. with_lock → bracket
    t4 = OOp('with_lock', (OVar('lock'), OVar('body')))
    r4 = apply(t4)
    _assert(any(a == 'P17_lock_to_bracket' for _, a in r4), "lock → bracket")

    # 5. bracket(acquire, body, release) → with_lock
    t5 = OOp('bracket', (
        OOp('.acquire', (OVar('lock'),)),
        OVar('body'),
        OOp('.release', (OVar('lock'),)),
    ))
    r5 = apply(t5)
    _assert(any(a == 'P17_bracket_to_with_lock' for _, a in r5), "bracket → with_lock")

    # 6. with_redirect → bracket
    t6 = OOp('with_redirect', (OVar('stdout'), OVar('file'), OVar('body')))
    r6 = apply(t6)
    _assert(any(a == 'P17_redirect_to_bracket' for _, a in r6), "redirect → bracket")

    # 7. with_tempfile → bracket
    t7 = OOp('with_tempfile', (OVar('body'),))
    r7 = apply(t7)
    _assert(any(a == 'P17_tempfile_to_bracket' for _, a in r7), "tempfile → bracket")

    # 8. recognizes
    _assert(recognizes(t1), "recognizes with_open_read")
    _assert(recognizes(t4), "recognizes with_lock")
    _assert(recognizes(t5), "recognizes bracket")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 9. relevance
    _assert(relevance_score(t4, t5) > 0.5, "lock-bracket relevance")

    # 10. inverse
    t10 = OOp('.read', (OOp('open', (OVar('f'),)),))
    r10 = apply_inverse(t10)
    _assert(any(a == 'P17_inv_direct_to_with_open' for _, a in r10), "inv direct → with_open")

    # 11. with_open bracket form
    _assert(any(a == 'P17_with_open_to_bracket' for _, a in r1), "with_open → bracket")

    print(f"P17 context: {_pass} passed, {_fail} failed")
