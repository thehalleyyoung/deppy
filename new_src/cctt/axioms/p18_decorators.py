"""P18 Axiom: Decorator Pattern Equivalences.

Establishes equivalences between Python decorator syntax and
their functional / explicit counterparts.

Mathematical basis: A decorator is a higher-order function
    d : (A → B) → (A → B)
The decorator syntax @d is syntactic sugar for function composition:
    @d def f: body  ≡  f = d(λ args. body)

This is the Yoneda lemma in the function category:
    Nat(Hom(–, A→B), F) ≅ F(A→B)
A decorator is a natural transformation on the function space.

Key rewrites:
  • @decorator def f: ...        ↔ f = decorator(f)
  • @functools.wraps identity    ↔ f  (identity wrapper)
  • @staticmethod                ↔ module-level function
  • @classmethod def create(...) ↔ factory function
  • @property                    ↔ explicit getter/setter
  • @lru_cache                   ↔ manual cache dict

(§P18, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P18_decorators"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D24_eta", "D16_memo_dp", "D21_dispatch"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P18 Decorator Equivalence).

1. @d def f(x): body  ≡  f = d(λx. body)
   By Python decorator semantics: the decorator is applied to
   the function object after definition.

2. @functools.wraps(f)
   def wrapper(*a, **k): return f(*a, **k)
   ≡ f
   The identity wrapper: wrapper is η-equivalent to f,
   functools.wraps preserves metadata.  This is η-reduction (D24).

3. @staticmethod def f(x): body  ≡  def f(x): body  (module level)
   A static method has no cls/self parameter; it is functionally
   identical to a module-level function.

4. @classmethod def create(cls, x): return cls(x)
   ≡ def create(x): return ClassName(x)
   When cls is only used as a constructor call, the classmethod
   is equivalent to a factory function with the class name.

5. @property def x(self): return self._x
   ≡ getter: x.fget = λself. self._x

6. @lru_cache def f(x): expensive(x)
   ≡ _cache = {}
     def f(x):
       if x not in _cache: _cache[x] = expensive(x)
       return _cache[x]
   Memoization: lru_cache wraps f with a dictionary cache.
"""

EXAMPLES = [
    ("decorated($d, $f)", "apply($d, $f)", "P18_decorator_desugar"),
    ("identity_wrapper($f)", "$f", "P18_identity_wrapper"),
    ("staticmethod($f)", "$f", "P18_staticmethod"),
    ("lru_cache($f)", "memoize($f)", "P18_lru_cache"),
]

# Decorator-related operation names
_DECORATOR_OPS = frozenset({
    'decorated', 'decorator_apply',
    'staticmethod', 'classmethod', 'property',
    'lru_cache', 'cache', 'cached_property',
    'identity_wrapper', 'wraps_wrapper',
})


def _is_identity_wrapper(term: OTerm) -> Optional[OTerm]:
    """Detect identity wrapper: λ(*a,**k). f(*a,**k) → f."""
    if isinstance(term, OOp) and term.name == 'identity_wrapper':
        if len(term.args) == 1:
            return term.args[0]
    if isinstance(term, OOp) and term.name == 'wraps_wrapper':
        if len(term.args) == 1:
            return term.args[0]
    # Lambda form: λ(args). f(args) is handled by D24 η
    if isinstance(term, OLam) and len(term.params) >= 1:
        body = term.body
        if isinstance(body, OOp) and len(body.args) == len(term.params):
            if all(isinstance(a, OVar) and a.name == p
                   for a, p in zip(body.args, term.params)):
                return OOp(body.name, ())
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P18: Decorator pattern rewrites.

    Handles:
      1. decorated(d, f) → apply(d, f)  (desugar @)
      2. identity_wrapper(f) → f
      3. staticmethod(f) → f
      4. classmethod(f) → factory(f)
      5. property(getter) → getter
      6. lru_cache(f) → memoize(f)
      7. cache(f) → memoize(f)
      8. decorated(decorator, decorated(d2, f)) → decorated(compose(d,d2), f)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. decorated(d, f) → apply(d, f) ──
    if isinstance(term, OOp) and term.name == 'decorated' and len(term.args) == 2:
        d, f = term.args
        results.append((
            OOp('apply', (d, f)),
            'P18_decorator_desugar',
        ))

    # ── 2. identity_wrapper / wraps_wrapper → unwrap ──
    unwrapped = _is_identity_wrapper(term)
    if unwrapped is not None:
        results.append((
            unwrapped,
            'P18_identity_wrapper_elim',
        ))

    # ── 3. staticmethod(f) → f ──
    if isinstance(term, OOp) and term.name == 'staticmethod' and len(term.args) == 1:
        results.append((
            term.args[0],
            'P18_staticmethod_elim',
        ))

    # ── 4. classmethod(f) → factory pattern ──
    if isinstance(term, OOp) and term.name == 'classmethod' and len(term.args) == 1:
        f = term.args[0]
        results.append((
            OOp('factory', (f,)),
            'P18_classmethod_to_factory',
        ))

    # ── 5. property(getter) → getter ──
    if isinstance(term, OOp) and term.name == 'property' and len(term.args) >= 1:
        getter = term.args[0]
        results.append((
            OOp('getter', (getter,)),
            'P18_property_to_getter',
        ))
        if len(term.args) >= 2:
            setter = term.args[1]
            results.append((
                OOp('getter_setter', (getter, setter)),
                'P18_property_to_getter_setter',
            ))

    # ── 6. lru_cache(f) → memoize(f) ──
    if isinstance(term, OOp) and term.name in ('lru_cache', 'cache', 'cached_property'):
        if len(term.args) == 1:
            f = term.args[0]
            results.append((
                OOp('memoize', (f,)),
                'P18_lru_cache_to_memoize',
            ))

    # ── 7. memoize(f) → lru_cache(f) ──
    if isinstance(term, OOp) and term.name == 'memoize' and len(term.args) == 1:
        f = term.args[0]
        results.append((
            OOp('lru_cache', (f,)),
            'P18_memoize_to_lru_cache',
        ))

    # ── 8. Stacked decorators: decorated(d1, decorated(d2, f)) ──
    if isinstance(term, OOp) and term.name == 'decorated' and len(term.args) == 2:
        d1, inner = term.args
        if isinstance(inner, OOp) and inner.name == 'decorated' and len(inner.args) == 2:
            d2, f = inner.args
            results.append((
                OOp('decorated', (OOp('compose', (d1, d2)), f)),
                'P18_stacked_decorators',
            ))

    # ── 9. apply(d, f) → decorated(d, f) (re-sugar) ──
    if isinstance(term, OOp) and term.name == 'apply' and len(term.args) == 2:
        d, f = term.args
        results.append((
            OOp('decorated', (d, f)),
            'P18_apply_to_decorator',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _DECORATOR_OPS:
        return True
    if isinstance(term, OOp) and term.name in ('apply', 'memoize'):
        return True
    identity = _is_identity_wrapper(term)
    if identity is not None:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('decorated', 'staticmethod', 'classmethod', 'property',
               'lru_cache', 'memoize', 'wrapper'):
        if kw in sc or kw in tc:
            return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: re-introduce decorator patterns."""
    results: List[Tuple[OTerm, str]] = []

    # f → identity_wrapper(f)
    if isinstance(term, OOp) and len(term.args) == 0:
        results.append((
            OOp('identity_wrapper', (term,)),
            'P18_inv_add_identity_wrapper',
        ))

    # memoize(f) → manual cache dict pattern
    if isinstance(term, OOp) and term.name == 'memoize' and len(term.args) == 1:
        f = term.args[0]
        results.append((
            OOp('cache_dict_pattern', (f,)),
            'P18_inv_memoize_to_cache_dict',
        ))

    # factory(f) → classmethod(f)
    if isinstance(term, OOp) and term.name == 'factory' and len(term.args) == 1:
        results.append((
            OOp('classmethod', (term.args[0],)),
            'P18_inv_factory_to_classmethod',
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

    # 1. decorated → apply
    t1 = OOp('decorated', (OVar('d'), OVar('f')))
    r1 = apply(t1)
    _assert(any(a == 'P18_decorator_desugar' for _, a in r1), "decorator desugar")

    # 2. identity_wrapper → f
    t2 = OOp('identity_wrapper', (OVar('f'),))
    r2 = apply(t2)
    _assert(any(a == 'P18_identity_wrapper_elim' for _, a in r2), "identity wrapper elim")

    # 3. staticmethod → f
    t3 = OOp('staticmethod', (OVar('f'),))
    r3 = apply(t3)
    _assert(any(a == 'P18_staticmethod_elim' for _, a in r3), "staticmethod elim")

    # 4. classmethod → factory
    t4 = OOp('classmethod', (OVar('f'),))
    r4 = apply(t4)
    _assert(any(a == 'P18_classmethod_to_factory' for _, a in r4), "classmethod → factory")

    # 5. property → getter
    t5 = OOp('property', (OVar('getter'),))
    r5 = apply(t5)
    _assert(any(a == 'P18_property_to_getter' for _, a in r5), "property → getter")

    # 6. property(getter, setter) → getter_setter
    t6 = OOp('property', (OVar('getter'), OVar('setter')))
    r6 = apply(t6)
    _assert(any(a == 'P18_property_to_getter_setter' for _, a in r6), "property → g/s")

    # 7. lru_cache → memoize
    t7 = OOp('lru_cache', (OVar('f'),))
    r7 = apply(t7)
    _assert(any(a == 'P18_lru_cache_to_memoize' for _, a in r7), "lru_cache → memoize")

    # 8. memoize → lru_cache
    t8 = OOp('memoize', (OVar('f'),))
    r8 = apply(t8)
    _assert(any(a == 'P18_memoize_to_lru_cache' for _, a in r8), "memoize → lru_cache")

    # 9. stacked decorators
    t9 = OOp('decorated', (OVar('d1'),
             OOp('decorated', (OVar('d2'), OVar('f')))))
    r9 = apply(t9)
    _assert(any(a == 'P18_stacked_decorators' for _, a in r9), "stacked decorators")

    # 10. apply → decorated
    t10 = OOp('apply', (OVar('d'), OVar('f')))
    r10 = apply(t10)
    _assert(any(a == 'P18_apply_to_decorator' for _, a in r10), "apply → decorated")

    # 11. lambda identity wrapper detection
    t11 = OLam(('x',), OOp('f', (OVar('x'),)))
    r11 = apply(t11)
    _assert(any(a == 'P18_identity_wrapper_elim' for _, a in r11), "lambda identity wrapper")

    # 12. recognizes
    _assert(recognizes(t1), "recognizes decorated")
    _assert(recognizes(t7), "recognizes lru_cache")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 13. inverse: factory → classmethod
    t13 = OOp('factory', (OVar('f'),))
    r13 = apply_inverse(t13)
    _assert(any(a == 'P18_inv_factory_to_classmethod' for _, a in r13), "inv factory → cm")

    # 14. inverse: memoize → cache_dict
    r14 = apply_inverse(t8)
    _assert(any(a == 'P18_inv_memoize_to_cache_dict' for _, a in r14), "inv memo → cache")

    print(f"P18 decorators: {_pass} passed, {_fail} failed")
