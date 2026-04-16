"""P28 Axiom: Typing Pattern Equivalences.

Establishes equivalences between legacy typing module generics and
modern built-in generic syntax introduced in Python 3.9/3.10.

Mathematical basis: Type annotations are objects in the category
**Typ** of Python types.  The typing module generics and built-in
generics denote the same objects:
    typing.Optional[X]  ≅  X | None        (coproduct with unit)
    typing.Union[A, B]  ≅  A | B           (coproduct)
    typing.List[X]      ≅  list[X]         (free monoid functor)
    typing.Dict[K, V]   ≅  dict[K, V]     (Map functor)
    typing.Callable[[A], B] ≅ A → B        (exponential object)

Key rewrites:
  • Optional[X] ↔ X | None
  • Union[A, B] ↔ A | B
  • List[X] ↔ list[X]
  • Dict[K, V] ↔ dict[K, V]
  • Tuple[X, ...] ↔ tuple[X, ...]
  • Set[X] ↔ set[X]
  • FrozenSet[X] ↔ frozenset[X]
  • Callable[[A], B] ↔ (A) -> B annotation
  • cast(T, x) ↔ assert isinstance then use
  • TYPE_CHECKING guard ↔ runtime import

(§P28, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P28_typing"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P10_class_patterns", "P16_type_convert"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P28 Typing Pattern Equivalences).

1. typing.Optional[X] ≡ X | None
   Optional[X] is defined as Union[X, None]; PEP 604 union syntax
   A | B is semantically identical.

2. typing.Union[A, B] ≡ A | B
   PEP 604 introduced | as syntactic sugar for Union at the type level.

3. typing.List[X] ≡ list[X]
   PEP 585 made built-in list subscriptable; typing.List is an alias.

4. typing.Dict[K, V] ≡ dict[K, V]
   PEP 585 made built-in dict subscriptable; typing.Dict is an alias.

5. typing.Tuple[X, ...] ≡ tuple[X, ...]
   PEP 585 made built-in tuple subscriptable.

6. typing.Set[X] ≡ set[X]
   PEP 585 made built-in set subscriptable.

7. typing.FrozenSet[X] ≡ frozenset[X]
   PEP 585 made built-in frozenset subscriptable.

8. typing.Callable[[A], B] ≡ (A) -> B function annotation
   Both denote the exponential object B^A in the type category.

9. typing.cast(T, x) ≡ (assert isinstance(x, T), x)[-1]
   cast is a no-op at runtime; the assertion form adds a runtime check.

10. TYPE_CHECKING import guard ≡ runtime import
    Under TYPE_CHECKING, imports exist only for type checkers;
    moving them to runtime makes them always available.
"""

EXAMPLES = [
    ("typing_optional($x)", "union_none($x)", "P28_optional_to_union_none"),
    ("typing_union($a, $b)", "pipe_union($a, $b)", "P28_union_to_pipe"),
    ("typing_list($x)", "builtin_list($x)", "P28_list_alias"),
    ("typing_dict($k, $v)", "builtin_dict($k, $v)", "P28_dict_alias"),
    ("typing_callable($a, $b)", "func_annotation($a, $b)", "P28_callable_to_annotation"),
]

_TYPING_OPS = frozenset({
    'typing_optional', 'union_none', 'typing_union', 'pipe_union',
    'typing_list', 'builtin_list', 'typing_dict', 'builtin_dict',
    'typing_callable', 'func_annotation', 'typing_cast', 'assert_type',
    'type_checking_guard', 'runtime_import',
    'typing_tuple', 'builtin_tuple',
    'typing_set', 'builtin_set',
    'typing_frozenset', 'builtin_frozenset',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P28: Typing pattern equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── Optional[X] ↔ X | None ──
    if isinstance(term, OOp) and term.name == 'typing_optional' and len(term.args) >= 1:
        results.append((
            OOp('union_none', term.args),
            'P28_optional_to_union_none',
        ))

    if isinstance(term, OOp) and term.name == 'union_none' and len(term.args) >= 1:
        results.append((
            OOp('typing_optional', term.args),
            'P28_union_none_to_optional',
        ))

    # ── Union[A, B] ↔ A | B ──
    if isinstance(term, OOp) and term.name == 'typing_union' and len(term.args) >= 2:
        results.append((
            OOp('pipe_union', term.args),
            'P28_union_to_pipe',
        ))

    if isinstance(term, OOp) and term.name == 'pipe_union' and len(term.args) >= 2:
        results.append((
            OOp('typing_union', term.args),
            'P28_pipe_to_union',
        ))

    # ── List[X] ↔ list[X] ──
    if isinstance(term, OOp) and term.name == 'typing_list' and len(term.args) >= 1:
        results.append((
            OOp('builtin_list', term.args),
            'P28_typing_list_to_builtin',
        ))

    if isinstance(term, OOp) and term.name == 'builtin_list' and len(term.args) >= 1:
        results.append((
            OOp('typing_list', term.args),
            'P28_builtin_list_to_typing',
        ))

    # ── Dict[K, V] ↔ dict[K, V] ──
    if isinstance(term, OOp) and term.name == 'typing_dict' and len(term.args) >= 2:
        results.append((
            OOp('builtin_dict', term.args),
            'P28_typing_dict_to_builtin',
        ))

    if isinstance(term, OOp) and term.name == 'builtin_dict' and len(term.args) >= 2:
        results.append((
            OOp('typing_dict', term.args),
            'P28_builtin_dict_to_typing',
        ))

    # ── Tuple[X, ...] ↔ tuple[X, ...] ──
    if isinstance(term, OOp) and term.name == 'typing_tuple' and len(term.args) >= 1:
        results.append((
            OOp('builtin_tuple', term.args),
            'P28_typing_tuple_to_builtin',
        ))

    if isinstance(term, OOp) and term.name == 'builtin_tuple' and len(term.args) >= 1:
        results.append((
            OOp('typing_tuple', term.args),
            'P28_builtin_tuple_to_typing',
        ))

    # ── Set[X] ↔ set[X] ──
    if isinstance(term, OOp) and term.name == 'typing_set' and len(term.args) >= 1:
        results.append((
            OOp('builtin_set', term.args),
            'P28_typing_set_to_builtin',
        ))

    if isinstance(term, OOp) and term.name == 'builtin_set' and len(term.args) >= 1:
        results.append((
            OOp('typing_set', term.args),
            'P28_builtin_set_to_typing',
        ))

    # ── FrozenSet[X] ↔ frozenset[X] ──
    if isinstance(term, OOp) and term.name == 'typing_frozenset' and len(term.args) >= 1:
        results.append((
            OOp('builtin_frozenset', term.args),
            'P28_typing_frozenset_to_builtin',
        ))

    if isinstance(term, OOp) and term.name == 'builtin_frozenset' and len(term.args) >= 1:
        results.append((
            OOp('typing_frozenset', term.args),
            'P28_builtin_frozenset_to_typing',
        ))

    # ── Callable[[A], B] ↔ func_annotation(A, B) ──
    if isinstance(term, OOp) and term.name == 'typing_callable' and len(term.args) >= 2:
        results.append((
            OOp('func_annotation', term.args),
            'P28_callable_to_func_annotation',
        ))

    if isinstance(term, OOp) and term.name == 'func_annotation' and len(term.args) >= 2:
        results.append((
            OOp('typing_callable', term.args),
            'P28_func_annotation_to_callable',
        ))

    # ── cast(T, x) ↔ assert isinstance then use ──
    if isinstance(term, OOp) and term.name == 'typing_cast' and len(term.args) == 2:
        ty, val = term.args
        results.append((
            OOp('assert_type', (ty, val)),
            'P28_cast_to_assert',
        ))

    if isinstance(term, OOp) and term.name == 'assert_type' and len(term.args) == 2:
        ty, val = term.args
        results.append((
            OOp('typing_cast', (ty, val)),
            'P28_assert_to_cast',
        ))

    # ── TYPE_CHECKING guard ↔ runtime import ──
    if isinstance(term, OOp) and term.name == 'type_checking_guard' and len(term.args) >= 1:
        results.append((
            OOp('runtime_import', term.args),
            'P28_type_checking_to_runtime',
        ))

    if isinstance(term, OOp) and term.name == 'runtime_import' and len(term.args) >= 1:
        results.append((
            OOp('type_checking_guard', term.args),
            'P28_runtime_to_type_checking',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {l for _, l in results if '_to_typing' in l or '_to_optional' in l
           or '_to_union' in l or '_to_callable' in l or '_to_cast' in l
           or '_to_type_checking' in l}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _TYPING_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('typing_', 'builtin_', 'union', 'optional', 'callable',
               'pipe_union', 'func_annotation'):
        if kw in sc and kw in tc:
            return 0.85
    if ('typing_' in sc and 'builtin_' in tc) or ('builtin_' in sc and 'typing_' in tc):
        return 0.9
    if ('optional' in sc and 'union_none' in tc) or ('union_none' in sc and 'optional' in tc):
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

    # 1. Optional → union_none
    t = OOp('typing_optional', (OVar('X'),))
    r = apply(t)
    _assert(any(a == 'P28_optional_to_union_none' for _, a in r), "Optional → union_none")

    # 2. union_none → Optional
    t2 = OOp('union_none', (OVar('X'),))
    r2 = apply(t2)
    _assert(any(a == 'P28_union_none_to_optional' for _, a in r2), "union_none → Optional")

    # 3. Union → pipe
    t3 = OOp('typing_union', (OVar('A'), OVar('B')))
    r3 = apply(t3)
    _assert(any(a == 'P28_union_to_pipe' for _, a in r3), "Union → pipe")

    # 4. pipe → Union
    t4 = OOp('pipe_union', (OVar('A'), OVar('B')))
    r4 = apply(t4)
    _assert(any(a == 'P28_pipe_to_union' for _, a in r4), "pipe → Union")

    # 5. List → list
    t5 = OOp('typing_list', (OVar('X'),))
    r5 = apply(t5)
    _assert(any(a == 'P28_typing_list_to_builtin' for _, a in r5), "List → list")

    # 6. list → List
    t6 = OOp('builtin_list', (OVar('X'),))
    r6 = apply(t6)
    _assert(any(a == 'P28_builtin_list_to_typing' for _, a in r6), "list → List")

    # 7. Dict → dict
    t7 = OOp('typing_dict', (OVar('K'), OVar('V')))
    r7 = apply(t7)
    _assert(any(a == 'P28_typing_dict_to_builtin' for _, a in r7), "Dict → dict")

    # 8. dict → Dict
    t8 = OOp('builtin_dict', (OVar('K'), OVar('V')))
    r8 = apply(t8)
    _assert(any(a == 'P28_builtin_dict_to_typing' for _, a in r8), "dict → Dict")

    # 9. Tuple → tuple
    t9 = OOp('typing_tuple', (OVar('X'),))
    r9 = apply(t9)
    _assert(any(a == 'P28_typing_tuple_to_builtin' for _, a in r9), "Tuple → tuple")

    # 10. tuple → Tuple
    t10 = OOp('builtin_tuple', (OVar('X'),))
    r10 = apply(t10)
    _assert(any(a == 'P28_builtin_tuple_to_typing' for _, a in r10), "tuple → Tuple")

    # 11. Set → set
    t11 = OOp('typing_set', (OVar('X'),))
    r11 = apply(t11)
    _assert(any(a == 'P28_typing_set_to_builtin' for _, a in r11), "Set → set")

    # 12. set → Set
    t12 = OOp('builtin_set', (OVar('X'),))
    r12 = apply(t12)
    _assert(any(a == 'P28_builtin_set_to_typing' for _, a in r12), "set → Set")

    # 13. FrozenSet → frozenset
    t13 = OOp('typing_frozenset', (OVar('X'),))
    r13 = apply(t13)
    _assert(any(a == 'P28_typing_frozenset_to_builtin' for _, a in r13), "FrozenSet → frozenset")

    # 14. Callable → func_annotation
    t14 = OOp('typing_callable', (OVar('A'), OVar('B')))
    r14 = apply(t14)
    _assert(any(a == 'P28_callable_to_func_annotation' for _, a in r14), "Callable → annotation")

    # 15. cast → assert_type
    t15 = OOp('typing_cast', (OVar('T'), OVar('x')))
    r15 = apply(t15)
    _assert(any(a == 'P28_cast_to_assert' for _, a in r15), "cast → assert")

    # 16. assert_type → cast
    t16 = OOp('assert_type', (OVar('T'), OVar('x')))
    r16 = apply(t16)
    _assert(any(a == 'P28_assert_to_cast' for _, a in r16), "assert → cast")

    # 17. type_checking_guard → runtime_import
    t17 = OOp('type_checking_guard', (OVar('mod'),))
    r17 = apply(t17)
    _assert(any(a == 'P28_type_checking_to_runtime' for _, a in r17), "TYPE_CHECKING → runtime")

    # 18. runtime_import → type_checking_guard
    t18 = OOp('runtime_import', (OVar('mod'),))
    r18 = apply(t18)
    _assert(any(a == 'P28_runtime_to_type_checking' for _, a in r18), "runtime → TYPE_CHECKING")

    # 19. recognizes
    _assert(recognizes(t), "recognizes typing_optional")
    _assert(recognizes(OOp('builtin_dict', (OVar('K'), OVar('V')))), "recognizes builtin_dict")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 20. relevance: typing ↔ builtin high
    _assert(relevance_score(t5, t6) > 0.5, "typing/builtin relevance high")

    print(f"P28 typing: {_pass} passed, {_fail} failed")
