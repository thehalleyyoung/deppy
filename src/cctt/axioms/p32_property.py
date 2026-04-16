"""P32 Axiom: Property / Descriptor Equivalences.

Establishes equivalences between @property decorator syntax,
manual getter/setter methods, the property() built-in, raw
descriptor protocol (__get__/__set__), @cached_property, and
__slots__-vs-__dict__ access patterns.

Mathematical basis: Properties form a lens (in the sense of
bidirectional programming) between an object's external interface
and its internal representation:
    get : Obj → Val          (the getter / projection)
    set : Obj × Val → Obj    (the setter / coalgebra map)
satisfying the lens laws:
    get(set(o, v)) ≡ v           (PutGet)
    set(o, get(o)) ≡ o           (GetPut)

@property and the descriptor protocol are two representations of
the same lens; they are naturally isomorphic as morphisms in the
category of Python attribute-access protocols.

@cached_property is a comonad on the lens: it memoises the getter
so repeated extraction does not recompute.

Key rewrites:
  • @property getter ↔ manual def get_x(self) method
  • @property setter ↔ manual def set_x(self, v) method
  • property(fget, fset) ↔ @property decorator syntax
  • __get__/__set__ descriptor ↔ property()
  • @cached_property ↔ manual cache-in-__dict__ pattern
  • __slots__ attribute access ↔ __dict__ attribute access
  • @property deleter ↔ manual def del_x(self) method
  • class_property (classmethod + property) pattern

(§P32, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P32_property"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P10_class_patterns", "P18_decorators", "P27_dataclasses"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P32 Property / Descriptor Equivalences).

1. property_getter(obj, attr) ≡ manual_getter(obj, attr)
   @property decorates a method so that attribute access calls
   the method; a manual getter method is called explicitly.
   The return value is identical: both apply fget to obj.

2. property_setter(obj, attr, val) ≡ manual_setter(obj, attr, val)
   @x.setter invokes fset(obj, val); manual set_x(self, v) does
   the same through explicit call.

3. property_fn(fget, fset) ≡ property_decorator(fget, fset)
   property(fget, fset) is the built-in constructor; the decorator
   syntax is syntactic sugar for the same call.

4. descriptor_get(desc, obj) ≡ property_getter(obj, attr)
   A descriptor's __get__ is the generalisation of @property's
   getter; for simple data descriptors the two coincide.

5. descriptor_set(desc, obj, val) ≡ property_setter(obj, attr, val)
   A descriptor's __set__ is the generalisation of @property's
   setter.

6. cached_property(obj, attr) ≡ manual_cache(obj, attr)
   @cached_property stores the result in obj.__dict__ on first
   access; the manual pattern does the same with an explicit
   if-check.

7. slots_access(obj, attr) ≡ dict_access(obj, attr)
   __slots__-based attribute access and __dict__-based access
   yield the same value; they differ only in storage strategy.

8. property_deleter(obj, attr) ≡ manual_deleter(obj, attr)
   @x.deleter invokes fdel(obj); manual del_x() is equivalent.
"""

EXAMPLES = [
    ("property_getter($obj, $attr)", "manual_getter($obj, $attr)",
     "P32_prop_getter_to_manual"),
    ("property_setter($obj, $a, $v)", "manual_setter($obj, $a, $v)",
     "P32_prop_setter_to_manual"),
    ("property_fn($fget, $fset)", "property_decorator($fget, $fset)",
     "P32_fn_to_decorator"),
    ("cached_property($obj, $a)", "manual_cache($obj, $a)",
     "P32_cached_to_manual"),
    ("slots_access($obj, $a)", "dict_access($obj, $a)",
     "P32_slots_to_dict"),
]

_PROPERTY_OPS = frozenset({
    'property_getter', 'manual_getter', 'property_setter', 'manual_setter',
    'property_fn', 'property_decorator', 'descriptor_get', 'descriptor_set',
    'cached_property', 'manual_cache', 'slots_access', 'dict_access',
    'property_deleter', 'manual_deleter', 'class_property', 'static_property',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P32: Property / descriptor equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. property_getter ↔ manual_getter ──
    if term.name == 'property_getter' and len(term.args) == 2:
        results.append((
            OOp('manual_getter', term.args),
            'P32_prop_getter_to_manual',
        ))

    if term.name == 'manual_getter' and len(term.args) == 2:
        results.append((
            OOp('property_getter', term.args),
            'P32_manual_to_prop_getter',
        ))

    # ── 2. property_setter ↔ manual_setter ──
    if term.name == 'property_setter' and len(term.args) == 3:
        results.append((
            OOp('manual_setter', term.args),
            'P32_prop_setter_to_manual',
        ))

    if term.name == 'manual_setter' and len(term.args) == 3:
        results.append((
            OOp('property_setter', term.args),
            'P32_manual_to_prop_setter',
        ))

    # ── 3. property_fn(fget, fset) ↔ property_decorator(fget, fset) ──
    if term.name == 'property_fn' and len(term.args) >= 2:
        results.append((
            OOp('property_decorator', term.args),
            'P32_fn_to_decorator',
        ))

    if term.name == 'property_decorator' and len(term.args) >= 2:
        results.append((
            OOp('property_fn', term.args),
            'P32_decorator_to_fn',
        ))

    # ── 4. descriptor_get ↔ property_getter ──
    if term.name == 'descriptor_get' and len(term.args) == 2:
        results.append((
            OOp('property_getter', term.args),
            'P32_descriptor_get_to_prop',
        ))

    if term.name == 'property_getter' and len(term.args) == 2:
        results.append((
            OOp('descriptor_get', term.args),
            'P32_prop_to_descriptor_get',
        ))

    # ── 5. descriptor_set ↔ property_setter ──
    if term.name == 'descriptor_set' and len(term.args) == 3:
        results.append((
            OOp('property_setter', term.args),
            'P32_descriptor_set_to_prop',
        ))

    if term.name == 'property_setter' and len(term.args) == 3:
        results.append((
            OOp('descriptor_set', term.args),
            'P32_prop_to_descriptor_set',
        ))

    # ── 6. cached_property ↔ manual_cache ──
    if term.name == 'cached_property' and len(term.args) == 2:
        results.append((
            OOp('manual_cache', term.args),
            'P32_cached_to_manual',
        ))

    if term.name == 'manual_cache' and len(term.args) == 2:
        results.append((
            OOp('cached_property', term.args),
            'P32_manual_to_cached',
        ))

    # ── 7. slots_access ↔ dict_access ──
    if term.name == 'slots_access' and len(term.args) == 2:
        results.append((
            OOp('dict_access', term.args),
            'P32_slots_to_dict',
        ))

    if term.name == 'dict_access' and len(term.args) == 2:
        results.append((
            OOp('slots_access', term.args),
            'P32_dict_to_slots',
        ))

    # ── 8. property_deleter ↔ manual_deleter ──
    if term.name == 'property_deleter' and len(term.args) == 2:
        results.append((
            OOp('manual_deleter', term.args),
            'P32_prop_deleter_to_manual',
        ))

    if term.name == 'manual_deleter' and len(term.args) == 2:
        results.append((
            OOp('property_deleter', term.args),
            'P32_manual_to_prop_deleter',
        ))

    # ── 9. class_property ↔ static_property ──
    if term.name == 'class_property' and len(term.args) >= 1:
        results.append((
            OOp('static_property', term.args),
            'P32_class_prop_to_static',
        ))

    if term.name == 'static_property' and len(term.args) >= 1:
        results.append((
            OOp('class_property', term.args),
            'P32_static_to_class_prop',
        ))

    # ── 10. descriptor_get ↔ manual_getter (transitive) ──
    if term.name == 'descriptor_get' and len(term.args) == 2:
        results.append((
            OOp('manual_getter', term.args),
            'P32_descriptor_get_to_manual',
        ))

    if term.name == 'descriptor_set' and len(term.args) == 3:
        results.append((
            OOp('manual_setter', term.args),
            'P32_descriptor_set_to_manual',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual form → property/descriptor form)."""
    inverse_labels = {
        'P32_manual_to_prop_getter', 'P32_manual_to_prop_setter',
        'P32_decorator_to_fn', 'P32_descriptor_get_to_prop',
        'P32_descriptor_set_to_prop', 'P32_manual_to_cached',
        'P32_dict_to_slots', 'P32_manual_to_prop_deleter',
        'P32_static_to_class_prop',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a property/descriptor op."""
    if isinstance(term, OOp) and term.name in _PROPERTY_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('property', 'getter', 'setter', 'descriptor',
               'cached', 'slots', 'deleter'):
        if kw in sc and kw in tc:
            return 0.9
    if ('property' in sc and 'manual' in tc) or \
       ('manual' in sc and 'property' in tc):
        return 0.85
    if ('descriptor' in sc and 'property' in tc) or \
       ('property' in sc and 'descriptor' in tc):
        return 0.85
    if ('slots' in sc and 'dict' in tc) or ('dict' in sc and 'slots' in tc):
        return 0.8
    if any(k in sc for k in ('property', 'descriptor', 'cached', 'slots')):
        return 0.3
    return 0.05


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

    # 1. property_getter → manual_getter
    t = OOp('property_getter', (OVar('obj'), OLit('x')))
    r = apply(t)
    _assert(any(l == 'P32_prop_getter_to_manual' for _, l in r),
            "prop_getter → manual")

    # 2. manual_getter → property_getter
    t2 = OOp('manual_getter', (OVar('obj'), OLit('x')))
    r2 = apply(t2)
    _assert(any(l == 'P32_manual_to_prop_getter' for _, l in r2),
            "manual → prop_getter")

    # 3. property_setter → manual_setter
    t3 = OOp('property_setter', (OVar('obj'), OLit('x'), OVar('v')))
    r3 = apply(t3)
    _assert(any(l == 'P32_prop_setter_to_manual' for _, l in r3),
            "prop_setter → manual")

    # 4. manual_setter → property_setter
    t4 = OOp('manual_setter', (OVar('obj'), OLit('x'), OVar('v')))
    r4 = apply(t4)
    _assert(any(l == 'P32_manual_to_prop_setter' for _, l in r4),
            "manual → prop_setter")

    # 5. property_fn → property_decorator
    t5 = OOp('property_fn', (OVar('fget'), OVar('fset')))
    r5 = apply(t5)
    _assert(any(l == 'P32_fn_to_decorator' for _, l in r5), "fn → decorator")

    # 6. property_decorator → property_fn
    t6 = OOp('property_decorator', (OVar('fget'), OVar('fset')))
    r6 = apply(t6)
    _assert(any(l == 'P32_decorator_to_fn' for _, l in r6), "decorator → fn")

    # 7. descriptor_get → property_getter
    t7 = OOp('descriptor_get', (OVar('desc'), OVar('obj')))
    r7 = apply(t7)
    _assert(any(l == 'P32_descriptor_get_to_prop' for _, l in r7),
            "desc_get → prop")

    # 8. descriptor_set → property_setter
    t8 = OOp('descriptor_set', (OVar('desc'), OVar('obj'), OVar('v')))
    r8 = apply(t8)
    _assert(any(l == 'P32_descriptor_set_to_prop' for _, l in r8),
            "desc_set → prop")

    # 9. cached_property → manual_cache
    t9 = OOp('cached_property', (OVar('obj'), OLit('x')))
    r9 = apply(t9)
    _assert(any(l == 'P32_cached_to_manual' for _, l in r9),
            "cached → manual")

    # 10. manual_cache → cached_property
    t10 = OOp('manual_cache', (OVar('obj'), OLit('x')))
    r10 = apply(t10)
    _assert(any(l == 'P32_manual_to_cached' for _, l in r10),
            "manual → cached")

    # 11. slots_access → dict_access
    t11 = OOp('slots_access', (OVar('obj'), OLit('x')))
    r11 = apply(t11)
    _assert(any(l == 'P32_slots_to_dict' for _, l in r11), "slots → dict")

    # 12. dict_access → slots_access
    t12 = OOp('dict_access', (OVar('obj'), OLit('x')))
    r12 = apply(t12)
    _assert(any(l == 'P32_dict_to_slots' for _, l in r12), "dict → slots")

    # 13. property_deleter → manual_deleter
    t13 = OOp('property_deleter', (OVar('obj'), OLit('x')))
    r13 = apply(t13)
    _assert(any(l == 'P32_prop_deleter_to_manual' for _, l in r13),
            "prop_del → manual")

    # 14. class_property → static_property
    t14 = OOp('class_property', (OVar('cls'), OVar('fn')))
    r14 = apply(t14)
    _assert(any(l == 'P32_class_prop_to_static' for _, l in r14),
            "class_prop → static")

    # 15. descriptor_get → manual_getter (transitive)
    _assert(any(l == 'P32_descriptor_get_to_manual' for _, l in r7),
            "desc_get → manual (transitive)")

    # 16. inverse: manual_getter → property_getter
    r16_inv = apply_inverse(OOp('manual_getter', (OVar('o'), OLit('a'))))
    _assert(any(l == 'P32_manual_to_prop_getter' for _, l in r16_inv),
            "inv: manual → prop")

    # 17. recognizes property ops
    _assert(recognizes(OOp('property_getter', (OVar('o'), OLit('x')))),
            "recognizes prop_getter")
    _assert(recognizes(OOp('cached_property', (OVar('o'), OLit('x')))),
            "recognizes cached_property")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 18. relevance: property ↔ manual high
    _assert(relevance_score(
        OOp('property_getter', (OVar('o'), OLit('x'))),
        OOp('manual_getter', (OVar('o'), OLit('x'))),
    ) > 0.7, "property/manual relevance high")

    # 19. relevance: descriptor ↔ property high
    _assert(relevance_score(
        OOp('descriptor_get', (OVar('d'), OVar('o'))),
        OOp('property_getter', (OVar('o'), OLit('x'))),
    ) > 0.7, "descriptor/property relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2, "unrelated relevance low")

    print(f"P32 property: {_pass} passed, {_fail} failed")
