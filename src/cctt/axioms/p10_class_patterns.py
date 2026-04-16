"""P10: Class / OOP Pattern Equivalences (Theorem 32.1.1).

Property ↔ attribute ↔ dataclass ↔ manual class ↔ factory patterns.

Mathematical foundation:
  A Python class is a record type with methods as named projections.
  ``@dataclass`` auto-generates the canonical projections (__init__,
  __repr__, __eq__) from the field signature, while a manual class
  defines them explicitly.  The equivalence is witnessed by a natural
  isomorphism in the category of record types:

    OOp('dataclass', fields)  ≅  OAbstract('class_with_init_repr_eq', fields)

  @property accessors are trivial when the getter returns ``self._x``
  without side-effects.  Static methods factor through the forgetful
  functor that drops the ``cls``/``self`` parameter.

Covers:
  • Property getter:     @property → direct attribute (trivial getter)
  • Dataclass:           @dataclass ↔ manual __init__ + __repr__ + __eq__
  • Classmethod factory: cls.from_x(args) ↔ Cls(transform(args))
  • Static method:       Cls.static(args) ↔ module_fn(args)
  • __slots__ class:     slots class ↔ regular class (same interface)
  • ABC abstractmethod:  isinstance(obj, ABC) ↔ hasattr-based duck typing
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

AXIOM_NAME = 'P10_class_patterns'
AXIOM_CATEGORY = 'python_idiom'  # §32 — OOP pattern equivalences

SOUNDNESS_PROOF = """
Theorem 32.1.1 (Dataclass–Manual Class Equivalence):
  For a field signature F = (f₁:T₁, …, fₙ:Tₙ),
    @dataclass(F)  ≡  class with __init__(self,f₁,…,fₙ), __repr__, __eq__
  as objects in the category of record types with projection morphisms.

Proof sketch:
  1. @dataclass generates __init__ that assigns self.fᵢ = fᵢ for all i.
  2. The manual class performs the same assignments.
  3. __repr__ and __eq__ are determined by the field values alone.
  4. Hence both define the same functor  F ↦ Record(F).  ∎

Property Triviality Lemma:
  If ``@property def x(self): return self._x`` and no setter is
  defined, then ``obj.x ≡ obj._x`` as morphisms Obj → T.

Classmethod Factorisation:
  ``cls.from_x(args) ≡ cls(transform(args))``  when from_x is a
  simple constructor adapter with no side effects.

Static/Module Equivalence:
  ``Cls.static_method(args) ≡ module_fn(args)``  since the static
  method does not depend on cls or self.

ABC–Duck Equivalence:
  ``isinstance(obj, ABC)`` where ABC requires methods m₁,…,mₖ
  ≡ ``hasattr(obj, m₁) and … and hasattr(obj, mₖ)``
  in the structural subtyping discipline.
"""

COMPOSES_WITH = ['P9_exceptions', 'D21_dispatch', 'D24_eta']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Property to attribute',
        'before': "@property def x(self): return self._x",
        'after': "obj._x  (direct access)",
        'axiom': 'P10_property_to_attr',
    },
    {
        'name': 'Dataclass to manual class',
        'before': "@dataclass class C: x: int; y: str",
        'after': "class C: def __init__(self, x, y): ...",
        'axiom': 'P10_dataclass_to_manual',
    },
    {
        'name': 'Manual class to dataclass',
        'before': "class C: def __init__(self, x, y): ...; __repr__; __eq__",
        'after': "@dataclass class C: x: int; y: str",
        'axiom': 'P10_manual_to_dataclass',
    },
    {
        'name': 'Classmethod factory to constructor',
        'before': "Cls.from_dict(d)",
        'after': "Cls(d['x'], d['y'])",
        'axiom': 'P10_classmethod_to_constructor',
    },
    {
        'name': 'Static method to module function',
        'before': "Cls.validate(x)",
        'after': "validate(x)",
        'axiom': 'P10_static_to_module',
    },
    {
        'name': 'ABC isinstance to duck typing',
        'before': "isinstance(obj, Iterable)",
        'after': "hasattr(obj, '__iter__')",
        'axiom': 'P10_abc_to_duck',
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
    """Apply P10 class-pattern equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Property getter → direct attribute ──
    # OOp('.property_get', (obj, 'x')) → OOp('.x', (obj,))
    if isinstance(term, OOp) and term.name == '.property_get' and len(term.args) == 2:
        obj, attr = term.args
        if isinstance(attr, OLit) and isinstance(attr.value, str):
            attr_name = '.' + attr.value
            results.append((
                OOp(attr_name, (obj,)),
                'P10_property_to_attr',
            ))

    # ── Direct attribute → property getter (inverse) ──
    if isinstance(term, OOp) and term.name.startswith('.') and len(term.args) == 1:
        attr_name = term.name[1:]  # strip leading dot
        if attr_name.startswith('_') and not attr_name.startswith('__'):
            obj = term.args[0]
            public_name = attr_name[1:]  # strip underscore prefix
            results.append((
                OOp('.property_get', (obj, OLit(public_name))),
                'P10_attr_to_property',
            ))

    # ── Dataclass → manual class ──
    # OOp('dataclass', (fields...)) → OAbstract('class_with_init_repr_eq', fields...)
    if isinstance(term, OOp) and term.name == 'dataclass':
        fields = term.args
        results.append((
            OAbstract('class_with_init_repr_eq', fields),
            'P10_dataclass_to_manual',
        ))

    # ── Manual class → dataclass (inverse) ──
    if isinstance(term, OAbstract) and term.spec == 'class_with_init_repr_eq':
        fields = term.inputs
        results.append((
            OOp('dataclass', tuple(fields)),
            'P10_manual_to_dataclass',
        ))

    # ── Classmethod factory → constructor call ──
    # OOp('classmethod_call', (cls, method, args)) → OOp('apply', (constructor, args'))
    if isinstance(term, OOp) and term.name == 'classmethod_call' and len(term.args) == 3:
        cls, method, args = term.args
        results.append((
            OOp('apply', (OOp('constructor', (cls,)), args)),
            'P10_classmethod_to_constructor',
        ))

    # ── Constructor call → classmethod factory (inverse) ──
    if isinstance(term, OOp) and term.name == 'apply' and len(term.args) == 2:
        fn, args = term.args
        if isinstance(fn, OOp) and fn.name == 'constructor' and len(fn.args) == 1:
            cls = fn.args[0]
            results.append((
                OOp('classmethod_call', (cls, OLit('from_args'), args)),
                'P10_constructor_to_classmethod',
            ))

    # ── Static method → module-level function ──
    # OOp('staticmethod_call', (cls, method, args)) → OOp('apply', (OVar(method), args))
    if isinstance(term, OOp) and term.name == 'staticmethod_call' and len(term.args) == 3:
        cls, method, args = term.args
        if isinstance(method, OLit) and isinstance(method.value, str):
            results.append((
                OOp('apply', (OVar(method.value), args)),
                'P10_static_to_module',
            ))
        elif isinstance(method, OVar):
            results.append((
                OOp('apply', (method, args)),
                'P10_static_to_module',
            ))

    # ── Module function → static method (inverse) ──
    if isinstance(term, OOp) and term.name == 'apply' and len(term.args) == 2:
        fn, args = term.args
        if isinstance(fn, OVar):
            duck = ctx.param_duck_types.get(fn.name, '')
            if duck == 'staticmethod':
                results.append((
                    OOp('staticmethod_call', (OVar('Cls'), OLit(fn.name), args)),
                    'P10_module_to_static',
                ))

    # ── __slots__ class ↔ regular class ──
    if isinstance(term, OAbstract) and term.spec == 'slots_class':
        results.append((
            OAbstract('regular_class', term.inputs),
            'P10_slots_to_regular',
        ))

    if isinstance(term, OAbstract) and term.spec == 'regular_class':
        results.append((
            OAbstract('slots_class', term.inputs),
            'P10_regular_to_slots',
        ))

    # ── ABC isinstance → duck typing (hasattr checks) ──
    # OOp('isinstance_check', (obj, abc)) → OOp('and', (hasattr(obj,m1), ...))
    if isinstance(term, OOp) and term.name == 'isinstance_check' and len(term.args) == 2:
        obj, abc = term.args
        methods = _abc_required_methods(abc)
        if methods:
            checks = tuple(
                OOp('hasattr', (obj, OLit(m))) for m in methods
            )
            if len(checks) == 1:
                results.append((checks[0], 'P10_abc_to_duck'))
            else:
                results.append((OOp('and', checks), 'P10_abc_to_duck'))

    # ── Duck typing (and of hasattr) → isinstance check (inverse) ──
    if isinstance(term, OOp) and term.name == 'and':
        all_hasattr = all(
            isinstance(a, OOp) and a.name == 'hasattr' and len(a.args) == 2
            for a in term.args
        )
        if all_hasattr and len(term.args) >= 2:
            obj = term.args[0].args[0]
            methods = [a.args[1] for a in term.args
                       if isinstance(a.args[1], OLit)]
            if methods:
                abc_name = _infer_abc_from_methods(
                    [m.value for m in methods if isinstance(m.value, str)]
                )
                results.append((
                    OOp('isinstance_check', (obj, OVar(abc_name))),
                    'P10_duck_to_abc',
                ))

    return results


def _abc_required_methods(abc: OTerm) -> List[str]:
    """Return the abstract methods implied by an ABC term."""
    if isinstance(abc, OVar):
        abc_methods = {
            'Iterable': ['__iter__'],
            'Iterator': ['__iter__', '__next__'],
            'Sized': ['__len__'],
            'Container': ['__contains__'],
            'Hashable': ['__hash__'],
            'Callable': ['__call__'],
            'Mapping': ['__getitem__', '__len__', '__iter__'],
            'Sequence': ['__getitem__', '__len__'],
            'MutableSequence': ['__getitem__', '__setitem__', '__delitem__',
                                '__len__', 'insert'],
            'Set': ['__contains__', '__iter__', '__len__'],
        }
        return abc_methods.get(abc.name, [])
    return []


def _infer_abc_from_methods(methods: List[str]) -> str:
    """Heuristically infer an ABC name from a set of required methods."""
    ms = set(methods)
    if ms == {'__iter__'}:
        return 'Iterable'
    if ms == {'__iter__', '__next__'}:
        return 'Iterator'
    if ms == {'__len__'}:
        return 'Sized'
    if ms == {'__contains__'}:
        return 'Container'
    if ms == {'__hash__'}:
        return 'Hashable'
    if ms == {'__call__'}:
        return 'Callable'
    if '__getitem__' in ms and '__len__' in ms and '__iter__' in ms:
        return 'Mapping'
    if '__getitem__' in ms and '__len__' in ms:
        return 'Sequence'
    if '__contains__' in ms and '__iter__' in ms and '__len__' in ms:
        return 'Set'
    return 'ABC'


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P10 in reverse direction.

    Inverse rewrites select the complementary direction from apply().
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P10_attr_to_property',
        'P10_manual_to_dataclass',
        'P10_constructor_to_classmethod',
        'P10_module_to_static',
        'P10_regular_to_slots',
        'P10_duck_to_abc',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P10 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('.property_get', 'dataclass', 'classmethod_call',
                         'staticmethod_call', 'isinstance_check'):
            return True
        if term.name == 'and' and all(
            isinstance(a, OOp) and a.name == 'hasattr'
            for a in term.args
        ):
            return True
        if term.name.startswith('.') and len(term.args) == 1:
            attr = term.name[1:]
            if attr.startswith('_') and not attr.startswith('__'):
                return True
    if isinstance(term, OAbstract):
        if term.spec in ('class_with_init_repr_eq', 'slots_class', 'regular_class'):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P10 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_dataclass_s = 'dataclass(' in sc
    has_dataclass_t = 'dataclass(' in tc
    has_manual_s = 'class_with_init_repr_eq' in sc
    has_manual_t = 'class_with_init_repr_eq' in tc
    has_property_s = '.property_get(' in sc
    has_property_t = '.property_get(' in tc
    has_isinstance_s = 'isinstance_check(' in sc
    has_isinstance_t = 'isinstance_check(' in tc
    has_hasattr_s = 'hasattr(' in sc
    has_hasattr_t = 'hasattr(' in tc

    # Dataclass ↔ manual class → high relevance
    if has_dataclass_s and has_manual_t:
        return 0.95
    if has_manual_s and has_dataclass_t:
        return 0.95

    # Property ↔ attribute crossover
    if has_property_s != has_property_t:
        return 0.90

    # ABC ↔ duck typing crossover
    if has_isinstance_s and has_hasattr_t:
        return 0.85
    if has_hasattr_s and has_isinstance_t:
        return 0.85

    # Any class-pattern signal
    if has_dataclass_s or has_dataclass_t:
        return 0.50
    if has_isinstance_s or has_isinstance_t:
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
    obj = OVar('obj')

    # ── Property → attribute ──
    print("P10: property → attribute ...")
    prop_term = OOp('.property_get', (obj, OLit('x')))
    r = apply(prop_term, ctx)
    _assert(any(lbl == 'P10_property_to_attr' for _, lbl in r), "property→attr")
    attr_result = [t for t, lbl in r if lbl == 'P10_property_to_attr'][0]
    _assert(isinstance(attr_result, OOp) and attr_result.name == '.x', "result is .x")

    # ── Attribute → property (inverse) ──
    print("P10: attribute → property ...")
    attr_term = OOp('._x', (obj,))
    r2 = apply(attr_term, ctx)
    _assert(any(lbl == 'P10_attr_to_property' for _, lbl in r2), "attr→property")

    # ── Dataclass → manual class ──
    print("P10: dataclass → manual ...")
    dc_term = OOp('dataclass', (OLit('x'), OLit('y')))
    r3 = apply(dc_term, ctx)
    _assert(any(lbl == 'P10_dataclass_to_manual' for _, lbl in r3), "dataclass→manual")
    manual_result = [t for t, lbl in r3 if lbl == 'P10_dataclass_to_manual'][0]
    _assert(isinstance(manual_result, OAbstract), "result is OAbstract")
    _assert(manual_result.spec == 'class_with_init_repr_eq', "correct spec")

    # ── Manual class → dataclass (inverse) ──
    print("P10: manual → dataclass ...")
    manual_term = OAbstract('class_with_init_repr_eq', (OLit('x'), OLit('y')))
    r4 = apply(manual_term, ctx)
    _assert(any(lbl == 'P10_manual_to_dataclass' for _, lbl in r4), "manual→dataclass")

    # ── Roundtrip dataclass ↔ manual ──
    print("P10: roundtrip dataclass ↔ manual ...")
    rt = apply(manual_result, ctx)
    _assert(any(lbl == 'P10_manual_to_dataclass' for _, lbl in rt), "roundtrip works")

    # ── Classmethod → constructor ──
    print("P10: classmethod → constructor ...")
    cm_term = OOp('classmethod_call', (OVar('Cls'), OLit('from_dict'), OVar('args')))
    r5 = apply(cm_term, ctx)
    _assert(any(lbl == 'P10_classmethod_to_constructor' for _, lbl in r5),
            "classmethod→constructor")

    # ── Static method → module function ──
    print("P10: static → module ...")
    static_term = OOp('staticmethod_call', (OVar('Cls'), OLit('validate'), OVar('x')))
    r6 = apply(static_term, ctx)
    _assert(any(lbl == 'P10_static_to_module' for _, lbl in r6), "static→module")
    mod_result = [t for t, lbl in r6 if lbl == 'P10_static_to_module'][0]
    _assert(isinstance(mod_result, OOp) and mod_result.name == 'apply', "result is apply")

    # ── __slots__ ↔ regular class ──
    print("P10: slots ↔ regular ...")
    slots_term = OAbstract('slots_class', (OLit('x'), OLit('y')))
    r7 = apply(slots_term, ctx)
    _assert(any(lbl == 'P10_slots_to_regular' for _, lbl in r7), "slots→regular")
    reg_result = [t for t, lbl in r7 if lbl == 'P10_slots_to_regular'][0]
    _assert(isinstance(reg_result, OAbstract) and reg_result.spec == 'regular_class',
            "result is regular_class")

    reg_term = OAbstract('regular_class', (OLit('x'), OLit('y')))
    r8 = apply(reg_term, ctx)
    _assert(any(lbl == 'P10_regular_to_slots' for _, lbl in r8), "regular→slots")

    # ── ABC isinstance → duck typing ──
    print("P10: ABC → duck typing ...")
    abc_term = OOp('isinstance_check', (obj, OVar('Iterable')))
    r9 = apply(abc_term, ctx)
    _assert(any(lbl == 'P10_abc_to_duck' for _, lbl in r9), "ABC→duck")
    duck_result = [t for t, lbl in r9 if lbl == 'P10_abc_to_duck'][0]
    _assert(isinstance(duck_result, OOp) and duck_result.name == 'hasattr',
            "result is hasattr")

    # ── Duck typing → ABC (inverse) ──
    print("P10: duck typing → ABC ...")
    duck_term = OOp('and', (
        OOp('hasattr', (obj, OLit('__iter__'))),
        OOp('hasattr', (obj, OLit('__next__'))),
    ))
    r10 = apply(duck_term, ctx)
    _assert(any(lbl == 'P10_duck_to_abc' for _, lbl in r10), "duck→ABC")

    # ── recognizes() ──
    print("P10: recognizes ...")
    _assert(recognizes(prop_term), "recognizes property_get")
    _assert(recognizes(dc_term), "recognizes dataclass")
    _assert(recognizes(cm_term), "recognizes classmethod_call")
    _assert(recognizes(abc_term), "recognizes isinstance_check")
    _assert(recognizes(slots_term), "recognizes slots_class")
    _assert(recognizes(duck_term), "recognizes hasattr duck typing")
    _assert(not recognizes(OOp('sorted', (OVar('xs'),))), "does not recognise sorted")

    # ── relevance_score ──
    print("P10: relevance_score ...")
    score = relevance_score(dc_term, manual_term)
    _assert(score > 0.8, f"dataclass↔manual score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (OVar('xs'),)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P10: apply_inverse ...")
    inv = apply_inverse(manual_term, ctx)
    _assert(len(inv) >= 1, "inverse of manual produces dataclass")
    _assert(all(lbl in (
        'P10_attr_to_property', 'P10_manual_to_dataclass',
        'P10_constructor_to_classmethod', 'P10_module_to_static',
        'P10_regular_to_slots', 'P10_duck_to_abc',
    ) for _, lbl in inv), "inverse labels correct")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P10 class_patterns: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
