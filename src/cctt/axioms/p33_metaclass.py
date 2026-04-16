"""P33 Axiom: Metaclass / ABC Equivalences.

Establishes equivalences between different Python mechanisms for
defining abstract interfaces and metaclass-controlled class
creation: ABCMeta, ABC, @abstractmethod, Protocol, __init_subclass__,
and related patterns.

Mathematical basis: Abstract base classes define a *signature*
in universal algebra — a set of operation names and arities that
concrete implementations must realise.  Two mechanisms for
specifying the same signature are naturally isomorphic:

   ABCMeta('T', (), {'f': abstractmethod(f)})
     ≅  class T(ABC): @abstractmethod def f ...

In the category of Python types, metaclass __init__ hooks and
__init_subclass__ hooks are dual:
   - metaclass.__init__  fires at class-object creation (top-down)
   - __init_subclass__   fires in the parent when subclassed (bottom-up)
Both observe the same event (new subclass) and can enforce the
same invariants, making them extensionally equivalent for
validation / registration purposes.

Protocol (structural subtyping) and ABC (nominal subtyping) define
the same morphism sets when restricted to classes that explicitly
implement all required methods — they are two presentations of
the same sketch in the sense of categorical logic.

Key rewrites:
  • ABCMeta ↔ ABC (base class shorthand)
  • @abstractmethod ↔ raise NotImplementedError
  • __init_subclass__ ↔ metaclass __init__
  • register ↔ direct subclassing
  • __subclasshook__ ↔ isinstance override
  • Protocol ↔ ABC (structural ↔ nominal)
  • metaclass __new__ ↔ __init_subclass__ __new__
  • virtual subclass ↔ concrete subclass

(§P33, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P33_metaclass"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P10_class_patterns", "P18_decorators", "P28_typing"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P33 Metaclass / ABC Equivalences).

1. abc_meta(cls) ≡ abc_class(cls)
   class T(metaclass=ABCMeta) is equivalent to class T(ABC);
   ABC is simply a convenience base whose metaclass is ABCMeta.

2. abstractmethod(fn) ≡ raise_not_implemented(fn)
   @abstractmethod marks a method as requiring override; a method
   body that raises NotImplementedError has the same contract
   (though only @abstractmethod prevents instantiation).

3. init_subclass(cls, **kw) ≡ metaclass_init(meta, name, bases, ns)
   Both fire when a subclass is created; __init_subclass__ receives
   the child class, metaclass.__init__ receives all creation args.
   For validation / registration they are extensionally equivalent.

4. abc_register(base, sub) ≡ direct_subclass(base, sub)
   base.register(sub) makes isinstance/issubclass true for sub
   without inheritance.  Direct subclassing achieves the same
   via MRO.

5. subclasshook(cls, sub) ≡ isinstance_check(cls, sub)
   __subclasshook__ customises isinstance checks; an explicit
   isinstance test with manual logic is equivalent.

6. protocol_class(cls) ≡ abc_class_alt(cls)
   typing.Protocol and ABC both define interface contracts;
   Protocol checks structurally, ABC nominally.  When a class
   explicitly implements all methods, both accept it.

7. metaclass_new(meta, name, bases, ns) ≡ init_subclass_new(cls)
   metaclass.__new__ and __init_subclass__ with __new__ override
   both intercept class creation.

8. virtual_subclass(base, sub) ≡ concrete_subclass(base, sub)
   A virtual subclass (registered) and a concrete subclass
   (inheriting) both satisfy isinstance checks.
"""

EXAMPLES = [
    ("abc_meta($cls)", "abc_class($cls)", "P33_meta_to_abc"),
    ("abstractmethod($fn)", "raise_not_implemented($fn)",
     "P33_abstract_to_raise"),
    ("init_subclass($cls)", "metaclass_init($cls)",
     "P33_init_sub_to_meta"),
    ("abc_register($base, $sub)", "direct_subclass($base, $sub)",
     "P33_register_to_direct"),
    ("protocol_class($cls)", "abc_class_alt($cls)",
     "P33_protocol_to_abc"),
]

_METACLASS_OPS = frozenset({
    'abc_meta', 'abc_class', 'abstractmethod', 'raise_not_implemented',
    'init_subclass', 'metaclass_init', 'abc_register', 'direct_subclass',
    'subclasshook', 'isinstance_check', 'protocol_class', 'abc_class_alt',
    'metaclass_new', 'init_subclass_new', 'virtual_subclass',
    'concrete_subclass',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P33: Metaclass / ABC equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. abc_meta ↔ abc_class ──
    if term.name == 'abc_meta' and len(term.args) >= 1:
        results.append((
            OOp('abc_class', term.args),
            'P33_meta_to_abc',
        ))

    if term.name == 'abc_class' and len(term.args) >= 1:
        results.append((
            OOp('abc_meta', term.args),
            'P33_abc_to_meta',
        ))

    # ── 2. abstractmethod ↔ raise_not_implemented ──
    if term.name == 'abstractmethod' and len(term.args) >= 1:
        results.append((
            OOp('raise_not_implemented', term.args),
            'P33_abstract_to_raise',
        ))

    if term.name == 'raise_not_implemented' and len(term.args) >= 1:
        results.append((
            OOp('abstractmethod', term.args),
            'P33_raise_to_abstract',
        ))

    # ── 3. init_subclass ↔ metaclass_init ──
    if term.name == 'init_subclass' and len(term.args) >= 1:
        results.append((
            OOp('metaclass_init', term.args),
            'P33_init_sub_to_meta_init',
        ))

    if term.name == 'metaclass_init' and len(term.args) >= 1:
        results.append((
            OOp('init_subclass', term.args),
            'P33_meta_init_to_init_sub',
        ))

    # ── 4. abc_register ↔ direct_subclass ──
    if term.name == 'abc_register' and len(term.args) == 2:
        results.append((
            OOp('direct_subclass', term.args),
            'P33_register_to_direct',
        ))

    if term.name == 'direct_subclass' and len(term.args) == 2:
        results.append((
            OOp('abc_register', term.args),
            'P33_direct_to_register',
        ))

    # ── 5. subclasshook ↔ isinstance_check ──
    if term.name == 'subclasshook' and len(term.args) == 2:
        results.append((
            OOp('isinstance_check', term.args),
            'P33_hook_to_isinstance',
        ))

    if term.name == 'isinstance_check' and len(term.args) == 2:
        results.append((
            OOp('subclasshook', term.args),
            'P33_isinstance_to_hook',
        ))

    # ── 6. protocol_class ↔ abc_class_alt ──
    if term.name == 'protocol_class' and len(term.args) >= 1:
        results.append((
            OOp('abc_class_alt', term.args),
            'P33_protocol_to_abc',
        ))

    if term.name == 'abc_class_alt' and len(term.args) >= 1:
        results.append((
            OOp('protocol_class', term.args),
            'P33_abc_to_protocol',
        ))

    # ── 7. metaclass_new ↔ init_subclass_new ──
    if term.name == 'metaclass_new' and len(term.args) >= 1:
        results.append((
            OOp('init_subclass_new', term.args),
            'P33_meta_new_to_init_sub',
        ))

    if term.name == 'init_subclass_new' and len(term.args) >= 1:
        results.append((
            OOp('metaclass_new', term.args),
            'P33_init_sub_to_meta_new',
        ))

    # ── 8. virtual_subclass ↔ concrete_subclass ──
    if term.name == 'virtual_subclass' and len(term.args) == 2:
        results.append((
            OOp('concrete_subclass', term.args),
            'P33_virtual_to_concrete',
        ))

    if term.name == 'concrete_subclass' and len(term.args) == 2:
        results.append((
            OOp('virtual_subclass', term.args),
            'P33_concrete_to_virtual',
        ))

    # ── 9. abc_register → virtual_subclass (transitive) ──
    if term.name == 'abc_register' and len(term.args) == 2:
        results.append((
            OOp('virtual_subclass', term.args),
            'P33_register_to_virtual',
        ))

    # ── 10. protocol_class → abc_class (transitive via abc_class_alt) ──
    if term.name == 'protocol_class' and len(term.args) >= 1:
        results.append((
            OOp('abc_class', term.args),
            'P33_protocol_to_abc_direct',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual form → ABC/metaclass form)."""
    inverse_labels = {
        'P33_abc_to_meta', 'P33_raise_to_abstract',
        'P33_meta_init_to_init_sub', 'P33_direct_to_register',
        'P33_isinstance_to_hook', 'P33_abc_to_protocol',
        'P33_init_sub_to_meta_new', 'P33_concrete_to_virtual',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a metaclass/ABC op."""
    if isinstance(term, OOp) and term.name in _METACLASS_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('abc', 'metaclass', 'abstract', 'protocol',
               'subclass', 'descriptor', 'register'):
        if kw in sc and kw in tc:
            return 0.9
    if ('abc' in sc and 'protocol' in tc) or \
       ('protocol' in sc and 'abc' in tc):
        return 0.85
    if ('metaclass' in sc and 'init_subclass' in tc) or \
       ('init_subclass' in sc and 'metaclass' in tc):
        return 0.85
    if ('abstract' in sc and 'raise' in tc) or \
       ('raise' in sc and 'abstract' in tc):
        return 0.8
    if any(k in sc for k in ('abc', 'metaclass', 'protocol', 'abstract')):
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

    # 1. abc_meta → abc_class
    t = OOp('abc_meta', (OVar('T'),))
    r = apply(t)
    _assert(any(l == 'P33_meta_to_abc' for _, l in r), "meta → abc")

    # 2. abc_class → abc_meta
    t2 = OOp('abc_class', (OVar('T'),))
    r2 = apply(t2)
    _assert(any(l == 'P33_abc_to_meta' for _, l in r2), "abc → meta")

    # 3. abstractmethod → raise_not_implemented
    t3 = OOp('abstractmethod', (OVar('fn'),))
    r3 = apply(t3)
    _assert(any(l == 'P33_abstract_to_raise' for _, l in r3),
            "abstract → raise")

    # 4. raise_not_implemented → abstractmethod
    t4 = OOp('raise_not_implemented', (OVar('fn'),))
    r4 = apply(t4)
    _assert(any(l == 'P33_raise_to_abstract' for _, l in r4),
            "raise → abstract")

    # 5. init_subclass → metaclass_init
    t5 = OOp('init_subclass', (OVar('cls'),))
    r5 = apply(t5)
    _assert(any(l == 'P33_init_sub_to_meta_init' for _, l in r5),
            "init_sub → meta_init")

    # 6. metaclass_init → init_subclass
    t6 = OOp('metaclass_init', (OVar('cls'),))
    r6 = apply(t6)
    _assert(any(l == 'P33_meta_init_to_init_sub' for _, l in r6),
            "meta_init → init_sub")

    # 7. abc_register → direct_subclass
    t7 = OOp('abc_register', (OVar('Base'), OVar('Sub')))
    r7 = apply(t7)
    _assert(any(l == 'P33_register_to_direct' for _, l in r7),
            "register → direct")

    # 8. direct_subclass → abc_register
    t8 = OOp('direct_subclass', (OVar('Base'), OVar('Sub')))
    r8 = apply(t8)
    _assert(any(l == 'P33_direct_to_register' for _, l in r8),
            "direct → register")

    # 9. subclasshook → isinstance_check
    t9 = OOp('subclasshook', (OVar('cls'), OVar('sub')))
    r9 = apply(t9)
    _assert(any(l == 'P33_hook_to_isinstance' for _, l in r9),
            "hook → isinstance")

    # 10. protocol_class → abc_class_alt
    t10 = OOp('protocol_class', (OVar('T'),))
    r10 = apply(t10)
    _assert(any(l == 'P33_protocol_to_abc' for _, l in r10),
            "protocol → abc")

    # 11. abc_class_alt → protocol_class
    t11 = OOp('abc_class_alt', (OVar('T'),))
    r11 = apply(t11)
    _assert(any(l == 'P33_abc_to_protocol' for _, l in r11),
            "abc_alt → protocol")

    # 12. metaclass_new → init_subclass_new
    t12 = OOp('metaclass_new', (OVar('meta'), OVar('name')))
    r12 = apply(t12)
    _assert(any(l == 'P33_meta_new_to_init_sub' for _, l in r12),
            "meta_new → init_sub_new")

    # 13. virtual_subclass → concrete_subclass
    t13 = OOp('virtual_subclass', (OVar('Base'), OVar('Sub')))
    r13 = apply(t13)
    _assert(any(l == 'P33_virtual_to_concrete' for _, l in r13),
            "virtual → concrete")

    # 14. concrete_subclass → virtual_subclass
    t14 = OOp('concrete_subclass', (OVar('Base'), OVar('Sub')))
    r14 = apply(t14)
    _assert(any(l == 'P33_concrete_to_virtual' for _, l in r14),
            "concrete → virtual")

    # 15. abc_register → virtual_subclass (transitive)
    _assert(any(l == 'P33_register_to_virtual' for _, l in r7),
            "register → virtual (transitive)")

    # 16. protocol_class → abc_class (transitive)
    _assert(any(l == 'P33_protocol_to_abc_direct' for _, l in r10),
            "protocol → abc_class (transitive)")

    # 17. inverse: raise → abstract
    r17_inv = apply_inverse(OOp('raise_not_implemented', (OVar('fn'),)))
    _assert(any(l == 'P33_raise_to_abstract' for _, l in r17_inv),
            "inv: raise → abstract")

    # 18. recognizes metaclass ops
    _assert(recognizes(OOp('abc_meta', (OVar('T'),))),
            "recognizes abc_meta")
    _assert(recognizes(OOp('protocol_class', (OVar('T'),))),
            "recognizes protocol_class")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance: abc ↔ protocol high
    _assert(relevance_score(
        OOp('abc_class', (OVar('T'),)),
        OOp('protocol_class', (OVar('T'),)),
    ) > 0.7, "abc/protocol relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P33 metaclass: {_pass} passed, {_fail} failed")
