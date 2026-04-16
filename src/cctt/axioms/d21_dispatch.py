"""D21: Dynamic Dispatch Equivalence — isinstance ↔ Dict Dispatch.

§23.1 of the CCTT monograph.  Theorem 23.1.1:
A chain of isinstance checks compiles to the same OCase chain as
a dictionary dispatch table.  Both are equivalent when the type
universe is closed (all branches covered).

Key rewrites:
  • isinstance chain → OCase chain (normalisation)
  • dict dispatch table → OCase chain
  • OCase chain → dict dispatch (when guards are type tests)
  • Visitor pattern → dispatch table
  • Method resolution → vtable lookup
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D21_dispatch"
AXIOM_CATEGORY = "language_feature"

SOUNDNESS_PROOF = """
Theorem 23.1.1 (Dispatch Equivalence).
isinstance(x, T₁) → f₁(x), isinstance(x, T₂) → f₂(x), ...
is equivalent to {T₁: f₁, T₂: f₂, ...}[type(x)](x) when
{T₁, T₂, ...} partitions the type universe.  Both compile to
the same OCase chain in the denotation, hence are equal in PyComp.

The vtable form is also equivalent: looking up a method in a class
hierarchy (MRO) is isomorphic to a type-indexed dispatch table.
"""

COMPOSES_WITH = ["CASE", "ALG", "D24_eta"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("case(isinstance(x,int), f(x), case(isinstance(x,str), g(x), h(x)))",
     "dispatch({int: f, str: g, _: h}, x)",
     "D21_isinstance_to_dispatch"),
    ("getitem(dispatch_table, type(x))(x)",
     "case(isinstance(x,T1), f1(x), ...)",
     "D21_dict_dispatch_to_case"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _is_isinstance_guard(test: OTerm) -> bool:
    """Check if test is an isinstance-style type check."""
    if isinstance(test, OOp):
        if test.name in ('isinstance', 'type_check', 'is_type'):
            return True
        if test.name == 'eq' and len(test.args) == 2:
            if isinstance(test.args[0], OOp) and test.args[0].name == 'type':
                return True
    return False


def _extract_type_from_guard(test: OTerm) -> Optional[OTerm]:
    """Extract the type being tested from an isinstance guard."""
    if isinstance(test, OOp):
        if test.name in ('isinstance', 'type_check', 'is_type') and len(test.args) == 2:
            return test.args[1]
        if test.name == 'eq' and len(test.args) == 2:
            if isinstance(test.args[0], OOp) and test.args[0].name == 'type':
                return test.args[1]
    return None


def _extract_dispatch_obj(test: OTerm) -> Optional[OTerm]:
    """Extract the object being dispatched on."""
    if isinstance(test, OOp):
        if test.name in ('isinstance', 'type_check', 'is_type') and len(test.args) == 2:
            return test.args[0]
        if test.name == 'eq' and len(test.args) == 2:
            if isinstance(test.args[0], OOp) and test.args[0].name == 'type':
                return test.args[0].args[0] if test.args[0].args else None
    return None


def _collect_isinstance_chain(term: OTerm) -> List[Tuple[OTerm, OTerm]]:
    """Collect (type, handler) pairs from a nested isinstance OCase chain."""
    pairs: List[Tuple[OTerm, OTerm]] = []
    current = term
    while isinstance(current, OCase):
        typ = _extract_type_from_guard(current.test)
        if typ is None:
            break
        pairs.append((typ, current.true_branch))
        current = current.false_branch
    if pairs:
        pairs.append((OUnknown('_default'), current))
    return pairs


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D21 dispatch-equivalence rewrites."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. isinstance chain → dispatch table ──
    if isinstance(term, OCase) and _is_isinstance_guard(term.test):
        chain = _collect_isinstance_chain(term)
        if len(chain) >= 2:
            dispatch_obj = _extract_dispatch_obj(term.test)
            if dispatch_obj is not None:
                dispatch_pairs = tuple(
                    (typ, handler) for typ, handler in chain
                )
                dispatch_dict = ODict(dispatch_pairs)
                results.append((
                    OOp('dispatch', (dispatch_dict, dispatch_obj)),
                    'D21_isinstance_to_dispatch',
                ))

    # ── 2. dispatch(table, x) → OCase chain ──
    if isinstance(term, OOp) and term.name == 'dispatch':
        if len(term.args) == 2 and isinstance(term.args[0], ODict):
            table = term.args[0]
            obj = term.args[1]
            if len(table.pairs) >= 1:
                # Build OCase chain from bottom
                case_chain = table.pairs[-1][1]  # default/last
                for typ, handler in reversed(table.pairs[:-1]):
                    guard = OOp('isinstance', (obj, typ))
                    case_chain = OCase(guard, handler, case_chain)
                results.append((case_chain, 'D21_dispatch_to_isinstance'))

    # ── 3. getitem(vtable, type(x)) → dispatch ──
    if isinstance(term, OOp) and term.name == 'getitem':
        if len(term.args) == 2:
            table, key = term.args
            if isinstance(key, OOp) and key.name == 'type' and len(key.args) == 1:
                results.append((
                    OOp('dispatch', (table, key.args[0])),
                    'D21_vtable_to_dispatch',
                ))

    # ── 4. Method call on known type → direct call ──
    if isinstance(term, OOp) and term.name.startswith('.') and len(term.args) >= 1:
        method_name = term.name[1:]
        obj = term.args[0]
        if isinstance(obj, OOp) and obj.name == 'dispatch':
            results.append((
                OOp(f'dispatch_method_{method_name}', term.args),
                'D21_method_dispatch_normalise',
            ))

    # ── 5. match/case → dispatch (Python 3.10+ structural pattern) ──
    if isinstance(term, OOp) and term.name == 'match':
        if len(term.args) >= 2:
            subject = term.args[0]
            cases = term.args[1:]
            if all(isinstance(c, OCase) for c in cases):
                results.append((
                    OOp('dispatch', (OSeq(cases), subject)),
                    'D21_match_to_dispatch',
                ))

    # ── 6. Visitor pattern: accept(visitor) → dispatch(visitor.methods, self) ──
    if isinstance(term, OOp) and term.name == '.accept':
        if len(term.args) == 2:
            obj, visitor = term.args
            results.append((
                OOp('dispatch', (OOp('.methods', (visitor,)), obj)),
                'D21_visitor_to_dispatch',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D21 can potentially rewrite *term*."""
    if isinstance(term, OCase) and _is_isinstance_guard(term.test):
        return True
    if isinstance(term, OOp) and term.name in ('dispatch', 'match', '.accept'):
        return True
    if isinstance(term, OOp) and term.name == 'getitem':
        if len(term.args) == 2 and isinstance(term.args[1], OOp):
            if term.args[1].name == 'type':
                return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D21's relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()
    has_isinstance = 'isinstance(' in sc or 'isinstance(' in tc
    has_dispatch = 'dispatch(' in sc or 'dispatch(' in tc
    has_type = 'type(' in sc or 'type(' in tc
    if has_isinstance and has_dispatch:
        return 0.9
    if has_isinstance or has_dispatch:
        return 0.5
    if has_type:
        return 0.3
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: dispatch table → isinstance chain."""
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OOp) and term.name == 'dispatch':
        if len(term.args) == 2 and isinstance(term.args[0], ODict):
            table, obj = term.args[0], term.args[1]
            if len(table.pairs) >= 1:
                case_chain = table.pairs[-1][1]
                for typ, handler in reversed(table.pairs[:-1]):
                    guard = OOp('isinstance', (obj, typ))
                    case_chain = OCase(guard, handler, case_chain)
                results.append((case_chain, 'D21_dispatch_to_isinstance_inv'))

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
    x = OVar('x')

    # isinstance chain → dispatch
    chain = OCase(
        OOp('isinstance', (x, OLit('int'))),
        OOp('f', (x,)),
        OCase(
            OOp('isinstance', (x, OLit('str'))),
            OOp('g', (x,)),
            OOp('h', (x,)),
        ),
    )
    r1 = apply(chain, ctx)
    _assert(any(a == 'D21_isinstance_to_dispatch' for _, a in r1),
            "isinstance chain → dispatch")

    # dispatch → isinstance chain
    table = ODict(((OLit('int'), OOp('f', ())), (OLit('str'), OOp('g', ())),
                   (OUnknown('_default'), OOp('h', ()))))
    dispatch = OOp('dispatch', (table, x))
    r2 = apply(dispatch, ctx)
    _assert(any(a == 'D21_dispatch_to_isinstance' for _, a in r2),
            "dispatch → isinstance chain")

    # vtable → dispatch
    vtable = OOp('getitem', (OVar('vtable'), OOp('type', (x,))))
    r3 = apply(vtable, ctx)
    _assert(any(a == 'D21_vtable_to_dispatch' for _, a in r3),
            "vtable → dispatch")

    # visitor → dispatch
    visitor = OOp('.accept', (x, OVar('visitor')))
    r4 = apply(visitor, ctx)
    _assert(any(a == 'D21_visitor_to_dispatch' for _, a in r4),
            "visitor → dispatch")

    # recognizes
    _assert(recognizes(chain), "recognizes isinstance chain")
    _assert(recognizes(dispatch), "recognizes dispatch call")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # relevance
    _assert(relevance_score(chain, dispatch) > 0.5,
            "high relevance for isinstance↔dispatch")

    # inverse
    r5 = apply_inverse(dispatch, ctx)
    _assert(len(r5) >= 1, "inverse dispatch → isinstance chain")
    _assert(isinstance(r5[0][0], OCase), "inverse produces OCase")

    print(f"D21 dispatch: {_pass} passed, {_fail} failed")
