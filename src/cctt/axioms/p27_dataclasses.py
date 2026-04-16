"""P27 Axiom: Dataclass Equivalences.

Establishes equivalences between @dataclass-generated methods and
their manual counterparts, plus namedtuple interconversions.

Mathematical basis: A dataclass is a product type Π_i F_i equipped
with canonical projections, equality via pointwise comparison, and
ordering via lexicographic extension.  The generated methods are
the unique morphisms making the requisite diagrams commute:
    @dataclass  ≅  manual __init__ + __repr__ + __eq__
    namedtuple  ≅  @dataclass(frozen=True)
    asdict(obj) ≅  {f.name: getattr(obj, f.name) for f in fields(obj)}

Key rewrites:
  • @dataclass init ↔ manual __init__
  • @dataclass repr ↔ manual __repr__
  • @dataclass eq ↔ manual __eq__
  • namedtuple ↔ frozen dataclass
  • field(default_factory=list) ↔ manual init default
  • asdict(obj) ↔ manual dict construction
  • @dataclass(order=True) ↔ manual __lt__/__le__/__gt__/__ge__

(§P27, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P27_dataclasses"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P10_class_patterns", "P3_dict_ops"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P27 Dataclass Equivalences).

1. dataclass_init(cls, fields) ≡ manual_init(cls, fields)
   @dataclass generates __init__ that assigns each field to self.
   A manual __init__ doing the same assignments is extensionally equal.

2. dataclass_repr(cls, fields) ≡ manual_repr(cls, fields)
   @dataclass generates __repr__ as "ClassName(f1=v1, ...)".
   A manual __repr__ producing the same string is extensionally equal.

3. dataclass_eq(cls, fields) ≡ manual_eq(cls, fields)
   @dataclass generates __eq__ comparing all fields pairwise.
   A manual __eq__ with the same comparisons is extensionally equal.

4. namedtuple(name, fields) ≡ frozen_dataclass(name, fields)
   Both create immutable product types with the same field access,
   equality, hashing, and iteration semantics.

5. field_factory(f, factory) ≡ manual_field_init(f, factory)
   field(default_factory=list) defers list creation per-instance,
   identical to manual "if arg is None: arg = []" pattern.

6. asdict(obj) ≡ manual_to_dict(obj)
   dataclasses.asdict recursively converts to dict; a manual
   dict comprehension over fields produces the same result.

7. dataclass_order(cls, fields) ≡ manual_lt(cls, fields)
   @dataclass(order=True) generates lexicographic comparison;
   manual __lt__ with tuple comparison is equivalent.
"""

EXAMPLES = [
    ("dataclass_init($cls, $fields)", "manual_init($cls, $fields)", "P27_init_equiv"),
    ("dataclass_repr($cls, $fields)", "manual_repr($cls, $fields)", "P27_repr_equiv"),
    ("dataclass_eq($cls, $fields)", "manual_eq($cls, $fields)", "P27_eq_equiv"),
    ("namedtuple($name, $fields)", "frozen_dataclass($name, $fields)", "P27_nt_to_frozen"),
    ("asdict($obj)", "manual_to_dict($obj)", "P27_asdict_equiv"),
]

_DC_OPS = frozenset({
    'dataclass_init', 'manual_init', 'namedtuple', 'frozen_dataclass',
    'field_factory', 'manual_field_init', 'asdict', 'manual_to_dict',
    'dataclass_order', 'manual_lt', 'dataclass_repr', 'manual_repr',
    'dataclass_eq', 'manual_eq', 'dataclass_hash', 'manual_hash',
    'dataclass_frozen_set', 'namedtuple_replace', 'dataclass_replace',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P27: Dataclass equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── dataclass_init ↔ manual_init ──
    if isinstance(term, OOp) and term.name == 'dataclass_init' and len(term.args) >= 2:
        results.append((
            OOp('manual_init', term.args),
            'P27_dataclass_init_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_init' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_init', term.args),
            'P27_manual_init_to_dataclass',
        ))

    # ── dataclass_repr ↔ manual_repr ──
    if isinstance(term, OOp) and term.name == 'dataclass_repr' and len(term.args) >= 2:
        results.append((
            OOp('manual_repr', term.args),
            'P27_dataclass_repr_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_repr' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_repr', term.args),
            'P27_manual_repr_to_dataclass',
        ))

    # ── dataclass_eq ↔ manual_eq ──
    if isinstance(term, OOp) and term.name == 'dataclass_eq' and len(term.args) >= 2:
        results.append((
            OOp('manual_eq', term.args),
            'P27_dataclass_eq_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_eq' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_eq', term.args),
            'P27_manual_eq_to_dataclass',
        ))

    # ── namedtuple ↔ frozen_dataclass ──
    if isinstance(term, OOp) and term.name == 'namedtuple' and len(term.args) >= 2:
        results.append((
            OOp('frozen_dataclass', term.args),
            'P27_namedtuple_to_frozen_dataclass',
        ))

    if isinstance(term, OOp) and term.name == 'frozen_dataclass' and len(term.args) >= 2:
        results.append((
            OOp('namedtuple', term.args),
            'P27_frozen_dataclass_to_namedtuple',
        ))

    # ── field_factory ↔ manual_field_init ──
    if isinstance(term, OOp) and term.name == 'field_factory' and len(term.args) >= 2:
        results.append((
            OOp('manual_field_init', term.args),
            'P27_field_factory_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_field_init' and len(term.args) >= 2:
        results.append((
            OOp('field_factory', term.args),
            'P27_manual_field_init_to_factory',
        ))

    # ── asdict ↔ manual_to_dict ──
    if isinstance(term, OOp) and term.name == 'asdict' and len(term.args) >= 1:
        results.append((
            OOp('manual_to_dict', term.args),
            'P27_asdict_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_to_dict' and len(term.args) >= 1:
        results.append((
            OOp('asdict', term.args),
            'P27_manual_to_dict_to_asdict',
        ))

    # ── dataclass_order ↔ manual_lt ──
    if isinstance(term, OOp) and term.name == 'dataclass_order' and len(term.args) >= 2:
        results.append((
            OOp('manual_lt', term.args),
            'P27_dataclass_order_to_manual_lt',
        ))

    if isinstance(term, OOp) and term.name == 'manual_lt' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_order', term.args),
            'P27_manual_lt_to_dataclass_order',
        ))

    # ── dataclass_hash ↔ manual_hash ──
    if isinstance(term, OOp) and term.name == 'dataclass_hash' and len(term.args) >= 2:
        results.append((
            OOp('manual_hash', term.args),
            'P27_dataclass_hash_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_hash' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_hash', term.args),
            'P27_manual_hash_to_dataclass',
        ))

    # ── namedtuple_replace ↔ dataclass_replace ──
    if isinstance(term, OOp) and term.name == 'namedtuple_replace' and len(term.args) >= 1:
        results.append((
            OOp('dataclass_replace', term.args),
            'P27_nt_replace_to_dc_replace',
        ))

    if isinstance(term, OOp) and term.name == 'dataclass_replace' and len(term.args) >= 1:
        results.append((
            OOp('namedtuple_replace', term.args),
            'P27_dc_replace_to_nt_replace',
        ))

    # ── dataclass_frozen_set ↔ manual error on setattr ──
    if isinstance(term, OOp) and term.name == 'dataclass_frozen_set' and len(term.args) >= 2:
        results.append((
            OOp('manual_frozen_setattr', term.args),
            'P27_frozen_set_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_frozen_setattr' and len(term.args) >= 2:
        results.append((
            OOp('dataclass_frozen_set', term.args),
            'P27_manual_to_frozen_set',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {l for _, l in results if 'manual' in l and 'to_dataclass' in l
           or 'to_factory' in l or 'to_asdict' in l
           or 'to_dataclass_order' in l or 'to_frozen_set' in l
           or 'nt_replace' in l or 'frozen_dataclass_to' in l}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _DC_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('dataclass', 'namedtuple', 'asdict', 'field_factory',
               'manual_init', 'manual_repr', 'manual_eq'):
        if kw in sc and kw in tc:
            return 0.85
    if ('dataclass' in sc and 'manual' in tc) or ('manual' in sc and 'dataclass' in tc):
        return 0.9
    if ('namedtuple' in sc and 'frozen' in tc) or ('frozen' in sc and 'namedtuple' in tc):
        return 0.9
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

    # 1. dataclass_init → manual_init
    t = OOp('dataclass_init', (OVar('cls'), OSeq((OVar('x'), OVar('y')))))
    r = apply(t)
    _assert(any(a == 'P27_dataclass_init_to_manual' for _, a in r), "dc_init → manual")

    # 2. manual_init → dataclass_init
    t2 = OOp('manual_init', (OVar('cls'), OSeq((OVar('x'), OVar('y')))))
    r2 = apply(t2)
    _assert(any(a == 'P27_manual_init_to_dataclass' for _, a in r2), "manual → dc_init")

    # 3. dataclass_repr → manual_repr
    t3 = OOp('dataclass_repr', (OVar('cls'), OSeq((OVar('x'),))))
    r3 = apply(t3)
    _assert(any(a == 'P27_dataclass_repr_to_manual' for _, a in r3), "dc_repr → manual")

    # 4. manual_repr → dataclass_repr
    t4 = OOp('manual_repr', (OVar('cls'), OSeq((OVar('x'),))))
    r4 = apply(t4)
    _assert(any(a == 'P27_manual_repr_to_dataclass' for _, a in r4), "manual → dc_repr")

    # 5. dataclass_eq → manual_eq
    t5 = OOp('dataclass_eq', (OVar('cls'), OSeq((OVar('x'),))))
    r5 = apply(t5)
    _assert(any(a == 'P27_dataclass_eq_to_manual' for _, a in r5), "dc_eq → manual")

    # 6. manual_eq → dataclass_eq
    t6 = OOp('manual_eq', (OVar('cls'), OSeq((OVar('x'),))))
    r6 = apply(t6)
    _assert(any(a == 'P27_manual_eq_to_dataclass' for _, a in r6), "manual → dc_eq")

    # 7. namedtuple → frozen_dataclass
    t7 = OOp('namedtuple', (OLit('Point'), OSeq((OLit('x'), OLit('y')))))
    r7 = apply(t7)
    _assert(any(a == 'P27_namedtuple_to_frozen_dataclass' for _, a in r7), "nt → frozen_dc")

    # 8. frozen_dataclass → namedtuple
    t8 = OOp('frozen_dataclass', (OLit('Point'), OSeq((OLit('x'), OLit('y')))))
    r8 = apply(t8)
    _assert(any(a == 'P27_frozen_dataclass_to_namedtuple' for _, a in r8), "frozen_dc → nt")

    # 9. field_factory → manual_field_init
    t9 = OOp('field_factory', (OVar('items'), OLit('list')))
    r9 = apply(t9)
    _assert(any(a == 'P27_field_factory_to_manual' for _, a in r9), "factory → manual")

    # 10. manual_field_init → field_factory
    t10 = OOp('manual_field_init', (OVar('items'), OLit('list')))
    r10 = apply(t10)
    _assert(any(a == 'P27_manual_field_init_to_factory' for _, a in r10), "manual → factory")

    # 11. asdict → manual_to_dict
    t11 = OOp('asdict', (OVar('obj'),))
    r11 = apply(t11)
    _assert(any(a == 'P27_asdict_to_manual' for _, a in r11), "asdict → manual")

    # 12. manual_to_dict → asdict
    t12 = OOp('manual_to_dict', (OVar('obj'),))
    r12 = apply(t12)
    _assert(any(a == 'P27_manual_to_dict_to_asdict' for _, a in r12), "manual → asdict")

    # 13. dataclass_order → manual_lt
    t13 = OOp('dataclass_order', (OVar('cls'), OSeq((OVar('x'), OVar('y')))))
    r13 = apply(t13)
    _assert(any(a == 'P27_dataclass_order_to_manual_lt' for _, a in r13), "dc_order → manual_lt")

    # 14. manual_lt → dataclass_order
    t14 = OOp('manual_lt', (OVar('cls'), OSeq((OVar('x'), OVar('y')))))
    r14 = apply(t14)
    _assert(any(a == 'P27_manual_lt_to_dataclass_order' for _, a in r14), "manual_lt → dc_order")

    # 15. dataclass_hash → manual_hash
    t15 = OOp('dataclass_hash', (OVar('cls'), OSeq((OVar('x'),))))
    r15 = apply(t15)
    _assert(any(a == 'P27_dataclass_hash_to_manual' for _, a in r15), "dc_hash → manual")

    # 16. manual_hash → dataclass_hash
    t16 = OOp('manual_hash', (OVar('cls'), OSeq((OVar('x'),))))
    r16 = apply(t16)
    _assert(any(a == 'P27_manual_hash_to_dataclass' for _, a in r16), "manual → dc_hash")

    # 17. namedtuple_replace → dataclass_replace
    t17 = OOp('namedtuple_replace', (OVar('obj'), OVar('kwargs')))
    r17 = apply(t17)
    _assert(any(a == 'P27_nt_replace_to_dc_replace' for _, a in r17), "nt_replace → dc_replace")

    # 18. recognizes dataclass ops
    _assert(recognizes(t), "recognizes dataclass_init")
    _assert(recognizes(OOp('asdict', (OVar('x'),))), "recognizes asdict")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance: dataclass ↔ manual
    _assert(relevance_score(t, t2) > 0.5, "dc/manual relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2, "unrelated relevance low")

    print(f"P27 dataclasses: {_pass} passed, {_fail} failed")
