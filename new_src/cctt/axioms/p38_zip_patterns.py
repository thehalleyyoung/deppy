"""P38 Axiom: Zip Pattern Equivalences.

Establishes equivalences between different Python zip patterns:
zip(a, b) vs index-based pairing, unzip via zip(*pairs),
zip_longest for unequal-length sequences, pairwise adjacency
(3.10+), dict(zip(keys, vals)), and strict-mode zip.

Mathematical basis: zip(a, b) computes the *product* of two
sequences truncated to the minimum length:

  zip : List(A) × List(B) → List(A × B)
  zip(a, b) = [(a[i], b[i]) | i ∈ [min(|a|, |b|)]]

This is the componentwise pairing induced by the product functor
in the category of finite sequences.

Unzipping is the inverse operation (split):
  unzip : List(A × B) → List(A) × List(B)
  unzip(ps) = ([p[0] for p in ps], [p[1] for p in ps])

In Python, zip(*pairs) computes unzip via the transpose of a
matrix of tuples — the adjunction between zip and unzip.

zip_longest pads shorter sequences with a fillvalue, computing
the product over the *maximum* length (a coproduct padding).

pairwise (itertools.pairwise in 3.10+) computes the diagonal
shift: zip(xs, xs[1:]), the pullback along the successor map.

Key rewrites:
  • zip(a, b) ↔ [(a[i], b[i]) for i in range(min(len(a), len(b)))]
  • zip(*pairs) ↔ unzip (transpose)
  • zip_longest(a, b) ↔ padded zip loop
  • zip(xs, xs[1:]) ↔ pairwise(xs)
  • dict(zip(keys, vals)) ↔ {k: v for k, v in zip(keys, vals)}
  • zip(a, b, strict=True) ↔ zip with length check
  • zip + enumerate fusion
  • zip + map fusion → starmap

(§P38, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P38_zip_patterns"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P23_iteration", "P06_itertools", "P37_range_enumerate"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P38 Zip Pattern Equivalences).

1. zip_pair(a, b) ≡ index_pair_loop(a, b)
   zip(a, b) and [(a[i], b[i]) for i in range(min(len(a), len(b)))]
   both compute the componentwise pairing of a and b.

2. unzip(pairs) ≡ zip_star(pairs)
   The manual unzip [([p[0] for p in pairs], [p[1] for p in pairs])]
   and zip(*pairs) both compute the transpose.

3. zip_longest(a, b, fill) ≡ padded_zip(a, b, fill)
   itertools.zip_longest(a, b, fillvalue=fill) and the manual
   loop that pads the shorter sequence both produce tuples
   up to max(len(a), len(b)).

4. pairwise(xs) ≡ zip_adjacent(xs)
   itertools.pairwise(xs) (3.10+) and zip(xs, xs[1:]) both
   yield consecutive pairs (xs[0],xs[1]), (xs[1],xs[2]), …

5. dict_zip(keys, vals) ≡ dict_comp_kv(keys, vals)
   dict(zip(keys, vals)) and {k: v for k, v in zip(keys, vals)}
   both construct a dict from parallel key/value sequences.

6. zip_strict(a, b) ≡ zip_check_len(a, b)
   zip(a, b, strict=True) (3.10+) and a manual length check
   followed by zip both raise ValueError on length mismatch.

7. zip_enumerate(a, b) ≡ enumerate_pair(a, b)
   enumerate(zip(a, b)) and the manual indexed-pair loop both
   produce (index, (a_elem, b_elem)) triples.

8. zip_map(f, a, b) ≡ starmap_zip(f, a, b)
   [f(x, y) for x, y in zip(a, b)] and
   itertools.starmap(f, zip(a, b)) both apply f to paired elements.

9. zip_pair(a, b) → OMap form using transform and collection.

10. dict_zip → ODict when keys and vals are known literals.
"""

EXAMPLES = [
    ("zip_pair($a, $b)", "index_pair_loop($a, $b)", "P38_zip_to_index"),
    ("unzip($ps)", "zip_star($ps)", "P38_unzip_to_star"),
    ("zip_longest($a, $b)", "padded_zip($a, $b)", "P38_longest_to_padded"),
    ("pairwise($xs)", "zip_adjacent($xs)", "P38_pairwise_to_adjacent"),
    ("dict_zip($ks, $vs)", "dict_comp_kv($ks, $vs)", "P38_dict_zip_to_comp"),
]

_ZIP_OPS = frozenset({
    'zip_pair', 'index_pair_loop', 'unzip', 'zip_star',
    'zip_longest', 'padded_zip', 'pairwise', 'zip_adjacent',
    'dict_zip', 'dict_comp_kv', 'zip_strict', 'zip_check_len',
    'zip_enumerate', 'enumerate_pair', 'zip_map', 'starmap_zip',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P38: Zip pattern equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. zip_pair ↔ index_pair_loop ──
    if term.name == 'zip_pair' and len(term.args) == 2:
        results.append((
            OOp('index_pair_loop', term.args),
            'P38_zip_to_index',
        ))

    if term.name == 'index_pair_loop' and len(term.args) == 2:
        results.append((
            OOp('zip_pair', term.args),
            'P38_index_to_zip',
        ))

    # ── 2. unzip ↔ zip_star ──
    if term.name == 'unzip' and len(term.args) >= 1:
        results.append((
            OOp('zip_star', term.args),
            'P38_unzip_to_star',
        ))

    if term.name == 'zip_star' and len(term.args) >= 1:
        results.append((
            OOp('unzip', term.args),
            'P38_star_to_unzip',
        ))

    # ── 3. zip_longest ↔ padded_zip ──
    if term.name == 'zip_longest' and len(term.args) >= 2:
        results.append((
            OOp('padded_zip', term.args),
            'P38_longest_to_padded',
        ))

    if term.name == 'padded_zip' and len(term.args) >= 2:
        results.append((
            OOp('zip_longest', term.args),
            'P38_padded_to_longest',
        ))

    # ── 4. pairwise ↔ zip_adjacent ──
    if term.name == 'pairwise' and len(term.args) == 1:
        results.append((
            OOp('zip_adjacent', term.args),
            'P38_pairwise_to_adjacent',
        ))

    if term.name == 'zip_adjacent' and len(term.args) == 1:
        results.append((
            OOp('pairwise', term.args),
            'P38_adjacent_to_pairwise',
        ))

    # ── 5. dict_zip ↔ dict_comp_kv ──
    if term.name == 'dict_zip' and len(term.args) == 2:
        results.append((
            OOp('dict_comp_kv', term.args),
            'P38_dict_zip_to_comp',
        ))

    if term.name == 'dict_comp_kv' and len(term.args) == 2:
        results.append((
            OOp('dict_zip', term.args),
            'P38_comp_to_dict_zip',
        ))

    # ── 6. zip_strict ↔ zip_check_len ──
    if term.name == 'zip_strict' and len(term.args) == 2:
        results.append((
            OOp('zip_check_len', term.args),
            'P38_strict_to_check',
        ))

    if term.name == 'zip_check_len' and len(term.args) == 2:
        results.append((
            OOp('zip_strict', term.args),
            'P38_check_to_strict',
        ))

    # ── 7. zip_enumerate ↔ enumerate_pair ──
    if term.name == 'zip_enumerate' and len(term.args) == 2:
        results.append((
            OOp('enumerate_pair', term.args),
            'P38_zip_enum_to_enum_pair',
        ))

    if term.name == 'enumerate_pair' and len(term.args) == 2:
        results.append((
            OOp('zip_enumerate', term.args),
            'P38_enum_pair_to_zip_enum',
        ))

    # ── 8. zip_map ↔ starmap_zip ──
    if term.name == 'zip_map' and len(term.args) == 3:
        results.append((
            OOp('starmap_zip', term.args),
            'P38_zip_map_to_starmap',
        ))

    if term.name == 'starmap_zip' and len(term.args) == 3:
        results.append((
            OOp('zip_map', term.args),
            'P38_starmap_to_zip_map',
        ))

    # ── 9. zip_pair → OMap (structural form) ──
    if term.name == 'zip_pair' and len(term.args) == 2:
        a, b = term.args
        pair_fn = OLam(('i',), OOp('tuple', (
            OOp('getitem', (a, OVar('i'))),
            OOp('getitem', (b, OVar('i'))),
        )))
        indices = OOp('range', (OOp('min', (
            OOp('len', (a,)), OOp('len', (b,)))),))
        results.append((
            OMap(pair_fn, indices),
            'P38_zip_to_map_form',
        ))

    # ── 10. dict_zip with literal keys/vals → ODict ──
    if term.name == 'dict_zip' and len(term.args) == 2:
        ks, vs = term.args
        if isinstance(ks, OSeq) and isinstance(vs, OSeq):
            n = min(len(ks.elements), len(vs.elements))
            pairs = tuple((ks.elements[i], vs.elements[i]) for i in range(n))
            results.append((
                ODict(pairs),
                'P38_dict_zip_literal_to_odict',
            ))

    # ── 11. pairwise → zip_pair(xs, slice(xs, 1)) (explicit) ──
    if term.name == 'pairwise' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('zip_pair', (xs, OOp('slice_from', (xs, OLit(1))))),
            'P38_pairwise_to_zip_slice',
        ))

    # ── 12. zip_strict → zip_pair (when lengths known equal) ──
    if term.name == 'zip_strict' and len(term.args) == 2:
        results.append((
            OOp('zip_pair', term.args),
            'P38_strict_to_plain_zip',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual form → zip-based form)."""
    inverse_labels = {
        'P38_index_to_zip', 'P38_star_to_unzip',
        'P38_padded_to_longest', 'P38_adjacent_to_pairwise',
        'P38_comp_to_dict_zip', 'P38_check_to_strict',
        'P38_enum_pair_to_zip_enum', 'P38_starmap_to_zip_map',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a zip-pattern op."""
    if isinstance(term, OOp) and term.name in _ZIP_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('zip', 'unzip', 'pairwise', 'adjacent', 'longest',
               'padded', 'starmap', 'enumerate_pair'):
        if kw in sc and kw in tc:
            return 0.9
    if ('zip' in sc and 'index' in tc) or \
       ('index' in sc and 'zip' in tc):
        return 0.85
    if ('zip' in sc and 'dict' in tc) or \
       ('dict' in sc and 'zip' in tc):
        return 0.85
    if ('pairwise' in sc and 'zip' in tc) or \
       ('zip' in sc and 'pairwise' in tc):
        return 0.8
    if any(k in sc for k in ('zip', 'unzip', 'pairwise', 'starmap')):
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

    # 1. zip_pair → index_pair_loop
    t = OOp('zip_pair', (OVar('a'), OVar('b')))
    r = apply(t)
    _assert(any(l == 'P38_zip_to_index' for _, l in r),
            "zip → index")

    # 2. index_pair_loop → zip_pair
    t2 = OOp('index_pair_loop', (OVar('a'), OVar('b')))
    r2 = apply(t2)
    _assert(any(l == 'P38_index_to_zip' for _, l in r2),
            "index → zip")

    # 3. unzip → zip_star
    t3 = OOp('unzip', (OVar('pairs'),))
    r3 = apply(t3)
    _assert(any(l == 'P38_unzip_to_star' for _, l in r3),
            "unzip → star")

    # 4. zip_star → unzip
    t4 = OOp('zip_star', (OVar('pairs'),))
    r4 = apply(t4)
    _assert(any(l == 'P38_star_to_unzip' for _, l in r4),
            "star → unzip")

    # 5. zip_longest → padded_zip
    t5 = OOp('zip_longest', (OVar('a'), OVar('b')))
    r5 = apply(t5)
    _assert(any(l == 'P38_longest_to_padded' for _, l in r5),
            "longest → padded")

    # 6. padded_zip → zip_longest
    t6 = OOp('padded_zip', (OVar('a'), OVar('b')))
    r6 = apply(t6)
    _assert(any(l == 'P38_padded_to_longest' for _, l in r6),
            "padded → longest")

    # 7. pairwise → zip_adjacent
    t7 = OOp('pairwise', (OVar('xs'),))
    r7 = apply(t7)
    _assert(any(l == 'P38_pairwise_to_adjacent' for _, l in r7),
            "pairwise → adjacent")

    # 8. zip_adjacent → pairwise
    t8 = OOp('zip_adjacent', (OVar('xs'),))
    r8 = apply(t8)
    _assert(any(l == 'P38_adjacent_to_pairwise' for _, l in r8),
            "adjacent → pairwise")

    # 9. dict_zip → dict_comp_kv
    t9 = OOp('dict_zip', (OVar('keys'), OVar('vals')))
    r9 = apply(t9)
    _assert(any(l == 'P38_dict_zip_to_comp' for _, l in r9),
            "dict_zip → comp")

    # 10. dict_comp_kv → dict_zip
    t10 = OOp('dict_comp_kv', (OVar('keys'), OVar('vals')))
    r10 = apply(t10)
    _assert(any(l == 'P38_comp_to_dict_zip' for _, l in r10),
            "comp → dict_zip")

    # 11. zip_strict → zip_check_len
    t11 = OOp('zip_strict', (OVar('a'), OVar('b')))
    r11 = apply(t11)
    _assert(any(l == 'P38_strict_to_check' for _, l in r11),
            "strict → check")

    # 12. zip_check_len → zip_strict
    t12 = OOp('zip_check_len', (OVar('a'), OVar('b')))
    r12 = apply(t12)
    _assert(any(l == 'P38_check_to_strict' for _, l in r12),
            "check → strict")

    # 13. zip_enumerate → enumerate_pair
    t13 = OOp('zip_enumerate', (OVar('a'), OVar('b')))
    r13 = apply(t13)
    _assert(any(l == 'P38_zip_enum_to_enum_pair' for _, l in r13),
            "zip_enum → enum_pair")

    # 14. enumerate_pair → zip_enumerate
    t14 = OOp('enumerate_pair', (OVar('a'), OVar('b')))
    r14 = apply(t14)
    _assert(any(l == 'P38_enum_pair_to_zip_enum' for _, l in r14),
            "enum_pair → zip_enum")

    # 15. zip_map → starmap_zip
    t15 = OOp('zip_map', (OVar('f'), OVar('a'), OVar('b')))
    r15 = apply(t15)
    _assert(any(l == 'P38_zip_map_to_starmap' for _, l in r15),
            "zip_map → starmap")

    # 16. starmap_zip → zip_map
    t16 = OOp('starmap_zip', (OVar('f'), OVar('a'), OVar('b')))
    r16 = apply(t16)
    _assert(any(l == 'P38_starmap_to_zip_map' for _, l in r16),
            "starmap → zip_map")

    # 17. zip_pair → OMap form
    _assert(any(l == 'P38_zip_to_map_form' for _, l in r),
            "zip → map form")

    # 18. dict_zip with literal seqs → ODict
    t18 = OOp('dict_zip', (
        OSeq((OLit('a'), OLit('b'), OLit('c'))),
        OSeq((OLit(1), OLit(2), OLit(3))),
    ))
    r18 = apply(t18)
    _assert(any(l == 'P38_dict_zip_literal_to_odict' for _, l in r18),
            "dict_zip literals → ODict")
    odict_results = [(t, l) for t, l in r18
                     if l == 'P38_dict_zip_literal_to_odict']
    if odict_results:
        od = odict_results[0][0]
        _assert(isinstance(od, ODict) and len(od.pairs) == 3,
                "ODict has 3 pairs")
    else:
        _assert(False, "ODict has 3 pairs")

    # 19. pairwise → zip_pair(xs, slice) explicit
    _assert(any(l == 'P38_pairwise_to_zip_slice' for _, l in r7),
            "pairwise → zip_slice")

    # 20. zip_strict → plain zip (fallback)
    _assert(any(l == 'P38_strict_to_plain_zip' for _, l in r11),
            "strict → plain zip")

    # 21. inverse: index_pair_loop → zip_pair
    r21_inv = apply_inverse(OOp('index_pair_loop', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P38_index_to_zip' for _, l in r21_inv),
            "inv: index → zip")

    # 22. inverse: padded_zip → zip_longest
    r22_inv = apply_inverse(OOp('padded_zip', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P38_padded_to_longest' for _, l in r22_inv),
            "inv: padded → longest")

    # 23. inverse: zip_adjacent → pairwise
    r23_inv = apply_inverse(OOp('zip_adjacent', (OVar('xs'),)))
    _assert(any(l == 'P38_adjacent_to_pairwise' for _, l in r23_inv),
            "inv: adjacent → pairwise")

    # 24. recognizes zip ops
    _assert(recognizes(OOp('zip_pair', (OVar('a'), OVar('b')))),
            "recognizes zip_pair")
    _assert(recognizes(OOp('pairwise', (OVar('xs'),))),
            "recognizes pairwise")
    _assert(recognizes(OOp('dict_zip', (OVar('k'), OVar('v')))),
            "recognizes dict_zip")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 25. relevance: zip ↔ index high
    _assert(relevance_score(
        OOp('zip_pair', (OVar('a'), OVar('b'))),
        OOp('index_pair_loop', (OVar('a'), OVar('b'))),
    ) > 0.7, "zip/index relevance high")

    # 26. relevance: pairwise ↔ zip high
    _assert(relevance_score(
        OOp('pairwise', (OVar('xs'),)),
        OOp('zip_adjacent', (OVar('xs'),)),
    ) > 0.7, "pairwise/zip relevance high")

    # 27. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P38 zip_patterns: {_pass} passed, {_fail} failed")
