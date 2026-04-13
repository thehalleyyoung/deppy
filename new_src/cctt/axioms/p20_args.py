"""P20 Axiom: Argument Pattern Equivalences.

Establishes equivalences between Python function argument patterns:
mutable defaults, *args/**kwargs, keyword-only, positional-only.

Mathematical basis: Python function signatures define a
product type with optional, keyword, and variadic components.
The argument pattern determines the morphism interface:
    f : A × B? × C* → R
where B? is an optional argument and C* is a variadic argument.

The key insight: mutable default arguments are a common Python
pitfall.  `def f(b=[])` shares one list across calls (aliasing),
while `def f(b=None): if b is None: b = []` creates a fresh list
each time.  These have different denotational semantics.

Key rewrites:
  • def f(a, b=None): if b is None: b = []  ↔  def f(a, b=()): b = list(b)
  • *args ↔ explicit positional
  • **kwargs ↔ explicit keyword arguments
  • keyword-only (*, key=None) ↔ regular keyword
  • positional-only (x, /) ↔ regular positional

(§P20, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P20_args"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D24_eta", "D2_beta", "P18_decorators"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P20 Argument Pattern Equivalence).

1. def f(a, b=None):
       if b is None: b = []
       ...
   ≡ def f(a, b=()):
       b = list(b)
       ...
   Both create a fresh mutable container each call.
   The tuple default is immutable (safe) and converted to list.

2. def f(*args): body using args[0], args[1]
   ≡ def f(a, b): body using a, b
   When the function always expects exactly N positional args,
   *args is equivalent to explicit positionals.

3. def f(**kwargs): body using kwargs['key']
   ≡ def f(key=None): body using key
   When the function only uses known keyword names.

4. def f(*, key=None): body
   ≡ def f(key=None): body
   Keyword-only is a calling convention difference, not a
   semantic one for the function body.

5. def f(x, /): body
   ≡ def f(x): body
   Positional-only is also a calling convention constraint.
"""

EXAMPLES = [
    ("none_guard($x, [])", "tuple_default($x, list)", "P20_mutable_default"),
    ("args_index($args, 0)", "param($a)", "P20_args_to_positional"),
    ("kwargs_get($kw, 'key')", "param($key)", "P20_kwargs_to_keyword"),
]


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P20: Argument pattern rewrites.

    Handles:
      1. none_guard(x, []) → tuple_default(x, list)
      2. none_guard(x, {}) → tuple_default(x, dict)
      3. args_unpack(*args) → explicit positional
      4. kwargs_unpack(**kwargs) → explicit keyword
      5. keyword_only(x) ↔ keyword(x)
      6. positional_only(x) ↔ positional(x)
      7. getitem(args, i) → param_i
      8. kwargs.get(key, default) → param with default
      9. args + kwargs merge patterns
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. none_guard(x, mutable_default) → immutable_default ──
    if isinstance(term, OOp) and term.name == 'none_guard' and len(term.args) == 2:
        x, default = term.args
        # none_guard(x, []) → tuple_default(x, list)
        if isinstance(default, OSeq) and len(default.elements) == 0:
            results.append((
                OOp('tuple_default', (x, OOp('list', ()))),
                'P20_none_guard_list',
            ))
        # none_guard(x, {}) → immutable default dict
        if isinstance(default, ODict) and len(default.pairs) == 0:
            results.append((
                OOp('tuple_default', (x, OOp('dict', ()))),
                'P20_none_guard_dict',
            ))
        # General: none_guard is case(is_none(x), default, x)
        results.append((
            OCase(OOp('is', (x, OLit(None))), default, x),
            'P20_none_guard_to_case',
        ))

    # ── Inverse: case(is_none(x), default, x) → none_guard ──
    if isinstance(term, OCase):
        if (isinstance(term.test, OOp) and term.test.name == 'is'
                and len(term.test.args) == 2
                and isinstance(term.test.args[1], OLit)
                and term.test.args[1].value is None):
            x = term.test.args[0]
            if term.false_branch.canon() == x.canon():
                results.append((
                    OOp('none_guard', (x, term.true_branch)),
                    'P20_case_to_none_guard',
                ))

    # ── 2. args_index(args, i) → positional param ──
    if isinstance(term, OOp) and term.name == 'args_index' and len(term.args) == 2:
        args, idx = term.args
        if isinstance(idx, OLit) and isinstance(idx.value, int):
            results.append((
                OVar(f'_param{idx.value}'),
                f'P20_args_index_{idx.value}',
            ))

    # ── 3. kwargs_get(kw, key, default) → param with default ──
    if isinstance(term, OOp) and term.name == 'kwargs_get' and len(term.args) >= 2:
        kw, key = term.args[0], term.args[1]
        if isinstance(key, OLit) and isinstance(key.value, str):
            default_val = term.args[2] if len(term.args) > 2 else OLit(None)
            results.append((
                OOp('param_default', (OVar(key.value), default_val)),
                'P20_kwargs_get_to_param',
            ))

    # ── 4. keyword_only(x) ↔ keyword(x) ──
    if isinstance(term, OOp) and term.name == 'keyword_only' and len(term.args) >= 1:
        results.append((
            OOp('keyword', term.args),
            'P20_keyword_only_to_keyword',
        ))

    if isinstance(term, OOp) and term.name == 'keyword' and len(term.args) >= 1:
        results.append((
            OOp('keyword_only', term.args),
            'P20_keyword_to_keyword_only',
        ))

    # ── 5. positional_only(x) ↔ positional(x) ──
    if isinstance(term, OOp) and term.name == 'positional_only' and len(term.args) >= 1:
        results.append((
            OOp('positional', term.args),
            'P20_positional_only_to_positional',
        ))

    if isinstance(term, OOp) and term.name == 'positional' and len(term.args) >= 1:
        results.append((
            OOp('positional_only', term.args),
            'P20_positional_to_positional_only',
        ))

    # ── 6. tuple_default → none_guard (inverse) ──
    if isinstance(term, OOp) and term.name == 'tuple_default' and len(term.args) == 2:
        x, factory = term.args
        if isinstance(factory, OOp) and factory.name == 'list' and len(factory.args) == 0:
            results.append((
                OOp('none_guard', (x, OSeq(()))),
                'P20_tuple_default_to_none_guard_list',
            ))
        if isinstance(factory, OOp) and factory.name == 'dict' and len(factory.args) == 0:
            results.append((
                OOp('none_guard', (x, ODict(()))),
                'P20_tuple_default_to_none_guard_dict',
            ))

    # ── 7. args_len(args) → known arity ──
    if isinstance(term, OOp) and term.name == 'args_len' and len(term.args) == 1:
        results.append((
            OOp('known_arity', term.args),
            'P20_args_len_to_arity',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in ('none_guard', 'tuple_default', 'args_index',
                         'kwargs_get', 'keyword_only', 'keyword',
                         'positional_only', 'positional', 'args_len'):
            return True
    if isinstance(term, OCase):
        if (isinstance(term.test, OOp) and term.test.name == 'is'
                and len(term.test.args) == 2
                and isinstance(term.test.args[1], OLit)
                and term.test.args[1].value is None):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('none_guard', 'tuple_default', 'args_index', 'kwargs',
               'keyword_only', 'positional_only'):
        if kw in sc or kw in tc:
            return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: introduce verbose argument patterns."""
    results: List[Tuple[OTerm, str]] = []

    # param_i → args_index(args, i)
    if isinstance(term, OVar) and term.name.startswith('_param'):
        try:
            idx = int(term.name[6:])
            results.append((
                OOp('args_index', (OVar('args'), OLit(idx))),
                f'P20_inv_param_to_args_index',
            ))
        except ValueError:
            pass

    # param_default(key, default) → kwargs_get(kwargs, key, default)
    if isinstance(term, OOp) and term.name == 'param_default' and len(term.args) == 2:
        key, default = term.args
        if isinstance(key, OVar):
            results.append((
                OOp('kwargs_get', (OVar('kwargs'), OLit(key.name), default)),
                'P20_inv_param_to_kwargs_get',
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

    # 1. none_guard(x, []) → tuple_default
    t1 = OOp('none_guard', (OVar('b'), OSeq(())))
    r1 = apply(t1)
    _assert(any(a == 'P20_none_guard_list' for _, a in r1), "none_guard list")

    # 2. none_guard(x, {}) → tuple_default
    t2 = OOp('none_guard', (OVar('b'), ODict(())))
    r2 = apply(t2)
    _assert(any(a == 'P20_none_guard_dict' for _, a in r2), "none_guard dict")

    # 3. none_guard → case
    _assert(any(a == 'P20_none_guard_to_case' for _, a in r1), "none_guard → case")

    # 4. case(is_none) → none_guard
    t4 = OCase(
        OOp('is', (OVar('x'), OLit(None))),
        OSeq(()),
        OVar('x'),
    )
    r4 = apply(t4)
    _assert(any(a == 'P20_case_to_none_guard' for _, a in r4), "case → none_guard")

    # 5. args_index → param
    t5 = OOp('args_index', (OVar('args'), OLit(0)))
    r5 = apply(t5)
    _assert(any('P20_args_index' in a for _, a in r5), "args_index → param")

    # 6. kwargs_get → param
    t6 = OOp('kwargs_get', (OVar('kw'), OLit('key'), OLit(None)))
    r6 = apply(t6)
    _assert(any(a == 'P20_kwargs_get_to_param' for _, a in r6), "kwargs_get → param")

    # 7. keyword_only ↔ keyword
    t7 = OOp('keyword_only', (OVar('x'),))
    r7 = apply(t7)
    _assert(any(a == 'P20_keyword_only_to_keyword' for _, a in r7), "kw_only → kw")

    t7b = OOp('keyword', (OVar('x'),))
    r7b = apply(t7b)
    _assert(any(a == 'P20_keyword_to_keyword_only' for _, a in r7b), "kw → kw_only")

    # 8. positional_only ↔ positional
    t8 = OOp('positional_only', (OVar('x'),))
    r8 = apply(t8)
    _assert(any(a == 'P20_positional_only_to_positional' for _, a in r8), "pos_only → pos")

    # 9. tuple_default → none_guard
    t9 = OOp('tuple_default', (OVar('b'), OOp('list', ())))
    r9 = apply(t9)
    _assert(any(a == 'P20_tuple_default_to_none_guard_list' for _, a in r9), "tuple → none_guard")

    # 10. recognizes
    _assert(recognizes(t1), "recognizes none_guard")
    _assert(recognizes(t5), "recognizes args_index")
    _assert(recognizes(t4), "recognizes case is_none")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 11. relevance
    _assert(relevance_score(t1, t9) > 0.5, "relevance none_guard/tuple_default")

    # 12. inverse: param → args_index
    t12 = OVar('_param0')
    r12 = apply_inverse(t12)
    _assert(any(a == 'P20_inv_param_to_args_index' for _, a in r12), "inv param → args")

    # 13. inverse: param_default → kwargs_get
    t13 = OOp('param_default', (OVar('key'), OLit(None)))
    r13 = apply_inverse(t13)
    _assert(any(a == 'P20_inv_param_to_kwargs_get' for _, a in r13), "inv param → kwargs")

    print(f"P20 args: {_pass} passed, {_fail} failed")
