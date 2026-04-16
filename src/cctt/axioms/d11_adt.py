"""D11 Axiom: Algebraic Data Type Equivalences.

Establishes equivalence between different representations of
algebraic data types: class hierarchies, tagged tuples/dicts,
enum+match patterns, and structural decompositions.

Mathematical basis: An ADT is a sum-of-products type:
    T = Σᵢ (tag_i × Πⱼ field_ij)

Different concrete representations — named classes, tagged
tuples, dictionaries with a 'type' key — all implement the
same initial algebra.  By Lambek's lemma, the initial algebra
is unique up to isomorphism, so all correct implementations
compute the same catamorphism (fold) results.

In OTerm terms, the representation-independence manifests as:
  case(isinstance(x, Foo), process_foo(x),
       case(isinstance(x, Bar), process_bar(x), default))
  ≡
  case(eq(getattr(x,'tag'), 'foo'), process_foo(x),
       case(eq(getattr(x,'tag'), 'bar'), process_bar(x), default))

Both compile to the same OCase chain over the type discriminant;
D11 normalizes the discriminant to a canonical form.

For container equivalences (OrderedDict ↔ list-of-pairs,
namedtuple ↔ dict, dataclass ↔ dict, etc.), the isomorphism
is the natural bijection between the record type and its
dictionary representation (§21.3, Theorem 21.3.1).
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = "D11_adt"
AXIOM_CATEGORY = "data_structure"

COMPOSES_WITH = ["D8_section_merge", "D10_priority_queue", "D12_map_construct", "D21_dispatch"]
REQUIRES: List[str] = []

# Ordered container synonyms
_ORDERED_CONTAINERS = frozenset({
    'OrderedDict', 'collections.OrderedDict',
    'odict', 'ordered_dict',
})

_LIST_OF_PAIRS_OPS = frozenset({
    'list_of_pairs', 'items', 'zip',
})

# Record-like container synonyms
_RECORD_TYPES = frozenset({
    'namedtuple', 'collections.namedtuple',
    'dataclass', 'attrs', 'TypedDict',
    'SimpleNamespace', 'types.SimpleNamespace',
})

_DICT_RECORD_OPS = frozenset({
    'dict', 'fromkeys', 'dict_from_pairs',
})

# isinstance / type dispatch patterns
_TYPE_CHECK_OPS = frozenset({
    'isinstance', 'type', 'issubclass',
    'getattr_type', '__class__',
})

SOUNDNESS_PROOF = r"""
Theorem (D11 ADT Representation Independence).

Let T = Σᵢ (tagᵢ × Aᵢ₁ × ... × Aᵢₙ) be an algebraic data type.

Let R₁ (class hierarchy) and R₂ (tagged tuple) be two representations.
Let φ : R₁ → T and ψ : R₂ → T be the encoding isomorphisms.

Claim: For any catamorphism f : T → B,
       f ∘ φ ≡ f ∘ ψ  (as functions on encoded values).

Proof:
  1. Both φ and ψ are injections into T with the same image.
  2. By the universal property of the initial algebra,
     there is a unique f : T → B satisfying the fold equations.
  3. f ∘ φ and f ∘ ψ both compute f on T-values.
  4. Since φ, ψ are bijections on valid inputs, the results agree.
  □

Corollary: isinstance(x, Foo) ↔ eq(x.tag, 'foo') ↔ eq(x[0], 'foo')
when the tag field correctly discriminates the variant.

Container equivalences:
  - OrderedDict(pairs) ≡ list(pairs) when only key-order and
    lookup are used (same interface).
  - namedtuple._asdict() establishes the natural isomorphism
    between records and dicts.
  - dataclass → dict via dataclasses.asdict() is the same iso.
"""

EXAMPLES = [
    {
        "name": "isinstance_vs_tag_check",
        "before": "case(isinstance(x, Foo), process_foo(x), case(isinstance(x, Bar), process_bar(x), default))",
        "after": "case(eq(tag(x), 'foo'), process_foo(x), case(eq(tag(x), 'bar'), process_bar(x), default))",
        "benchmark": None,
    },
    {
        "name": "ordered_dict_vs_list_pairs",
        "before": "OrderedDict(pairs)",
        "after": "list(pairs)",
        "benchmark": None,
    },
    {
        "name": "namedtuple_vs_dict",
        "before": "Point(x=1, y=2)",
        "after": "{'x': 1, 'y': 2}",
        "benchmark": None,
    },
    {
        "name": "enum_match_vs_if_chain",
        "before": "case(eq(shape.kind, CIRCLE), area_circle(shape), case(eq(shape.kind, RECT), area_rect(shape), 0))",
        "after": "dispatch_table[shape.kind](shape)",
        "benchmark": None,
    },
]


# ═══════════════════════════════════════════════════════════
# Pattern recognition helpers
# ═══════════════════════════════════════════════════════════

def _is_isinstance_guard(test: OTerm) -> bool:
    """Check if a guard is an isinstance check."""
    if isinstance(test, OOp) and test.name in ('isinstance', 'issubclass'):
        return True
    if isinstance(test, OOp) and test.name == 'eq':
        if len(test.args) == 2:
            for a in test.args:
                if isinstance(a, OOp) and a.name in ('type', '__class__', 'getattr_type'):
                    return True
    return False


def _is_tag_guard(test: OTerm) -> bool:
    """Check if a guard is a tag/discriminant check."""
    if isinstance(test, OOp) and test.name == 'eq':
        if len(test.args) == 2:
            for a in test.args:
                if isinstance(a, OOp) and a.name in ('getattr', 'getitem', 'tag'):
                    return True
                if isinstance(a, OOp) and a.name == '.kind':
                    return True
    return False


def _extract_type_info(guard: OTerm) -> Optional[Tuple[OTerm, str]]:
    """Extract (object, type_name) from a type-check guard."""
    if isinstance(guard, OOp) and guard.name == 'isinstance' and len(guard.args) == 2:
        obj, typ = guard.args
        if isinstance(typ, OVar):
            return (obj, typ.name)
        if isinstance(typ, OLit):
            return (obj, str(typ.value))
    if isinstance(guard, OOp) and guard.name == 'eq' and len(guard.args) == 2:
        lhs, rhs = guard.args
        if isinstance(lhs, OOp) and lhs.name in ('type', '__class__', 'getattr_type'):
            if len(lhs.args) >= 1:
                obj = lhs.args[0]
                if isinstance(rhs, OVar):
                    return (obj, rhs.name)
                if isinstance(rhs, OLit):
                    return (obj, str(rhs.value))
    return None


def _isinstance_to_tag(guard: OTerm) -> Optional[OTerm]:
    """Convert isinstance(x, Foo) → eq(tag(x), 'foo')."""
    info = _extract_type_info(guard)
    if info is None:
        return None
    obj, type_name = info
    tag_check = OOp('eq', (
        OOp('tag', (obj,)),
        OLit(type_name.lower()),
    ))
    return tag_check


def _tag_to_isinstance(guard: OTerm) -> Optional[OTerm]:
    """Convert eq(tag(x), 'foo') → isinstance(x, Foo)."""
    if not isinstance(guard, OOp) or guard.name != 'eq' or len(guard.args) != 2:
        return None
    lhs, rhs = guard.args
    if isinstance(lhs, OOp) and lhs.name == 'tag' and len(lhs.args) == 1:
        obj = lhs.args[0]
        if isinstance(rhs, OLit) and isinstance(rhs.value, str):
            type_var = OVar(rhs.value.capitalize())
            return OOp('isinstance', (obj, type_var))
    return None


def _collect_case_chain(term: OTerm) -> List[Tuple[OTerm, OTerm]]:
    """Flatten right-nested OCase chain into (guard, value) pairs."""
    chain: List[Tuple[OTerm, OTerm]] = []
    cur = term
    while isinstance(cur, OCase):
        chain.append((cur.test, cur.true_branch))
        cur = cur.false_branch
    chain.append((OLit(True), cur))
    return chain


def _build_case_chain(chain: List[Tuple[OTerm, OTerm]]) -> OTerm:
    """Reconstruct right-nested OCase from a chain list."""
    if len(chain) == 1:
        return chain[0][1]
    guard, val = chain[0]
    rest = _build_case_chain(chain[1:])
    return OCase(guard, val, rest)


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D11: Algebraic data type equivalences.

    Handles:
      1. isinstance chain → tag-based case chain (and reverse)
      2. OrderedDict(pairs) ↔ list(pairs) (ordered container iso)
      3. namedtuple/dataclass ↔ dict representation
      4. isinstance chain → dispatch table (ODict lookup)
      5. Tuple-based ADT → record-based ADT
      6. Enum match normalization
    """
    results: List[Tuple[OTerm, str]] = []

    # ── isinstance → tag normalization in case chains ──
    if isinstance(term, OCase):
        chain = _collect_case_chain(term)
        guards = [g for g, _ in chain[:-1]]

        # Check if all guards are isinstance checks
        all_isinstance = all(_is_isinstance_guard(g) for g in guards)
        if all_isinstance and len(guards) >= 1:
            new_chain: List[Tuple[OTerm, OTerm]] = []
            changed = False
            for guard, val in chain[:-1]:
                tag_guard = _isinstance_to_tag(guard)
                if tag_guard is not None:
                    new_chain.append((tag_guard, val))
                    changed = True
                else:
                    new_chain.append((guard, val))
            new_chain.append(chain[-1])
            if changed:
                rebuilt = _build_case_chain(new_chain)
                results.append((rebuilt, 'D11_isinstance_to_tag'))

        # Check if all guards are tag checks → can convert to isinstance
        all_tag = all(_is_tag_guard(g) for g in guards)
        if all_tag and len(guards) >= 1:
            new_chain2: List[Tuple[OTerm, OTerm]] = []
            changed2 = False
            for guard, val in chain[:-1]:
                inst_guard = _tag_to_isinstance(guard)
                if inst_guard is not None:
                    new_chain2.append((inst_guard, val))
                    changed2 = True
                else:
                    new_chain2.append((guard, val))
            new_chain2.append(chain[-1])
            if changed2:
                rebuilt2 = _build_case_chain(new_chain2)
                results.append((rebuilt2, 'D11_tag_to_isinstance'))

        # isinstance/tag chain → dispatch table (ODict)
        if (all_isinstance or all_tag) and len(guards) >= 2:
            dispatch_pairs: List[Tuple[OTerm, OTerm]] = []
            valid = True
            for guard, val in chain[:-1]:
                info = _extract_type_info(guard)
                if info is not None:
                    _, type_name = info
                    dispatch_pairs.append((OLit(type_name.lower()), val))
                else:
                    if _is_tag_guard(guard) and isinstance(guard, OOp) and guard.name == 'eq':
                        if isinstance(guard.args[1], OLit):
                            dispatch_pairs.append((guard.args[1], val))
                        else:
                            valid = False
                    else:
                        valid = False
            if valid and dispatch_pairs:
                _, default_val = chain[-1]
                obj = None
                for guard, _ in chain[:-1]:
                    info = _extract_type_info(guard)
                    if info:
                        obj = info[0]
                        break
                if obj is not None:
                    dispatch = OOp('dispatch_get', (
                        ODict(tuple(dispatch_pairs)),
                        OOp('tag', (obj,)),
                        default_val,
                    ))
                    results.append((dispatch, 'D11_case_to_dispatch'))

    # ── OrderedDict ↔ list-of-pairs ──
    if isinstance(term, OOp):
        if term.name in _ORDERED_CONTAINERS and len(term.args) >= 1:
            results.append((
                OOp('list', (term.args[0],)),
                'D11_ordered_dict_to_list',
            ))
        if term.name == 'list' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'items':
                # list(d.items()) → OrderedDict view
                results.append((
                    OOp('OrderedDict', (inner,)),
                    'D11_list_items_to_ordered_dict',
                ))

    # ── namedtuple / dataclass ↔ dict ──
    if isinstance(term, OOp):
        if term.name == '_asdict' and len(term.args) == 1:
            # nt._asdict() → dict(nt_fields)
            results.append((
                OOp('dict', (OOp('fields', (term.args[0],)),)),
                'D11_namedtuple_to_dict',
            ))
        if term.name == 'asdict' and len(term.args) == 1:
            # dataclasses.asdict(dc) → dict
            results.append((
                OOp('dict', (OOp('fields', (term.args[0],)),)),
                'D11_dataclass_to_dict',
            ))
        if term.name == 'vars' and len(term.args) == 1:
            results.append((
                OOp('dict', (OOp('fields', (term.args[0],)),)),
                'D11_vars_to_dict',
            ))

    # ── Tuple-based ADT normalization ──
    if isinstance(term, OOp) and term.name == 'getitem':
        if len(term.args) == 2 and isinstance(term.args[1], OLit):
            idx = term.args[1].value
            if isinstance(idx, int):
                results.append((
                    OOp('field', (term.args[0], OLit(f'_{idx}'))),
                    'D11_tuple_index_to_field',
                ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D11 apply to this term?"""
    if isinstance(term, OCase):
        chain = _collect_case_chain(term)
        guards = [g for g, _ in chain[:-1]]
        if len(guards) >= 1:
            if all(_is_isinstance_guard(g) for g in guards):
                return True
            if all(_is_tag_guard(g) for g in guards):
                return True
    if isinstance(term, OOp):
        if term.name in _ORDERED_CONTAINERS | _RECORD_TYPES:
            return True
        if term.name in ('_asdict', 'asdict', 'vars'):
            return True
        if term.name == 'getitem' and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and isinstance(term.args[1].value, int):
                return True
        if term.name == 'list' and len(term.args) == 1:
            if isinstance(term.args[0], OOp) and term.args[0].name == 'items':
                return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D11 helps bridge term→other."""
    score = 0.0

    # isinstance chain ↔ tag chain
    if isinstance(term, OCase) and isinstance(other, OCase):
        t_chain = _collect_case_chain(term)
        o_chain = _collect_case_chain(other)
        t_guards = [g for g, _ in t_chain[:-1]]
        o_guards = [g for g, _ in o_chain[:-1]]
        t_isinstance = all(_is_isinstance_guard(g) for g in t_guards) if t_guards else False
        o_isinstance = all(_is_isinstance_guard(g) for g in o_guards) if o_guards else False
        t_tag = all(_is_tag_guard(g) for g in t_guards) if t_guards else False
        o_tag = all(_is_tag_guard(g) for g in o_guards) if o_guards else False
        if t_isinstance and o_tag:
            score = max(score, 0.95)
        if t_tag and o_isinstance:
            score = max(score, 0.95)
        if (t_isinstance or t_tag) and isinstance(other, OOp):
            score = max(score, 0.7)

    # Ordered container conversions
    if isinstance(term, OOp) and isinstance(other, OOp):
        if term.name in _ORDERED_CONTAINERS and other.name == 'list':
            score = max(score, 0.9)
        if term.name == 'list' and other.name in _ORDERED_CONTAINERS:
            score = max(score, 0.9)

    # Record ↔ dict
    if isinstance(term, OOp) and term.name in ('_asdict', 'asdict', 'vars'):
        score = max(score, 0.8)

    return min(score, 1.0)


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Reverse D11: expand canonical ADT forms back to concrete.

    tag-based chain → isinstance chain
    dispatch table → case chain
    dict → namedtuple/dataclass
    """
    results: List[Tuple[OTerm, str]] = []

    # dispatch table → case chain
    if isinstance(term, OOp) and term.name == 'dispatch_get':
        if len(term.args) == 3:
            table, key_expr, default = term.args
            if isinstance(table, ODict):
                chain: List[Tuple[OTerm, OTerm]] = []
                for k, v in table.pairs:
                    guard = OOp('eq', (key_expr, k))
                    chain.append((guard, v))
                chain.append((OLit(True), default))
                rebuilt = _build_case_chain(chain)
                results.append((rebuilt, 'D11_inv_dispatch_to_case'))

    # dict → OrderedDict
    if isinstance(term, OOp) and term.name == 'dict':
        if len(term.args) >= 1:
            results.append((
                OOp('OrderedDict', term.args),
                'D11_inv_dict_to_ordered_dict',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    ctx = FiberCtx(param_duck_types={})

    # Test 1: isinstance chain → tag chain
    isinstance_chain = OCase(
        OOp('isinstance', (OVar('x'), OVar('Circle'))),
        OOp('area_circle', (OVar('x'),)),
        OCase(
            OOp('isinstance', (OVar('x'), OVar('Rect'))),
            OOp('area_rect', (OVar('x'),)),
            OLit(0),
        ),
    )
    rewrites = apply(isinstance_chain, ctx)
    assert any('D11_isinstance_to_tag' in ax for _, ax in rewrites), \
        f"Expected isinstance→tag, got {[ax for _, ax in rewrites]}"
    print("✓ isinstance chain → tag chain")

    # Test 2: isinstance chain → dispatch table
    assert any('D11_case_to_dispatch' in ax for _, ax in rewrites)
    print("✓ isinstance chain → dispatch table")

    # Test 3: OrderedDict → list
    odict = OOp('OrderedDict', (OVar('pairs'),))
    rewrites = apply(odict, ctx)
    assert any('D11_ordered_dict_to_list' in ax for _, ax in rewrites)
    print("✓ OrderedDict → list")

    # Test 4: _asdict → dict
    asdict = OOp('_asdict', (OVar('nt'),))
    rewrites = apply(asdict, ctx)
    assert any('D11_namedtuple_to_dict' in ax for _, ax in rewrites)
    print("✓ _asdict → dict")

    # Test 5: tuple index → field
    tup_idx = OOp('getitem', (OVar('point'), OLit(0)))
    rewrites = apply(tup_idx, ctx)
    assert any('D11_tuple_index_to_field' in ax for _, ax in rewrites)
    print("✓ tuple index → field")

    # Test 6: recognizes
    assert recognizes(isinstance_chain)
    assert recognizes(odict)
    assert recognizes(asdict)
    assert not recognizes(OVar('x'))
    print("✓ recognizes()")

    # Test 7: relevance_score
    tag_chain = OCase(
        OOp('eq', (OOp('tag', (OVar('x'),)), OLit('circle'))),
        OOp('area_circle', (OVar('x'),)),
        OLit(0),
    )
    score = relevance_score(isinstance_chain, tag_chain)
    assert score >= 0.8, f"Expected high relevance, got {score}"
    print(f"✓ relevance_score(isinstance, tag) = {score:.2f}")

    # Test 8: inverse dispatch → case
    dispatch = OOp('dispatch_get', (
        ODict((
            (OLit('circle'), OOp('area_circle', (OVar('x'),))),
            (OLit('rect'), OOp('area_rect', (OVar('x'),))),
        )),
        OOp('tag', (OVar('x'),)),
        OLit(0),
    ))
    inv = apply_inverse(dispatch, ctx)
    assert any('D11_inv_dispatch_to_case' in ax for _, ax in inv)
    print("✓ apply_inverse(dispatch) → case chain")

    # Test 9: list(d.items()) → OrderedDict
    list_items = OOp('list', (OOp('items', (OVar('d'),)),))
    rewrites = apply(list_items, ctx)
    assert any('D11_list_items_to_ordered_dict' in ax for _, ax in rewrites)
    print("✓ list(d.items()) → OrderedDict")

    print("\nAll D11 self-tests passed ✓")
