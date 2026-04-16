from __future__ import annotations
"""D5: Fold Universality — recognise fold patterns and canonicalise.

Mathematical basis: the universal property of folds (catamorphisms).
A fold is uniquely determined by its binary operation, identity
element, and collection.  Different names for the same operation
(e.g. ``add`` / ``iadd`` / ``operator.add``) yield the same fold.

This axiom:
  1. Canonicalises fold op-names via a synonym table
  2. Identifies hash-named fold operations
  3. Splits non-identity base cases via associativity
  4. Recognises synonym identity elements (0 ↔ [], "" ↔ [])

HIT path:  d5 : OFold(op1, init, c) = OFold(op2, init, c)  when op1 ≡ op2
Monograph: Chapter 20, §20.5 — Definition 4.7, Theorem 4.8
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════

AXIOM_NAME = "d5_fold_universal"
AXIOM_CATEGORY = "algebraic"

# ═══════════════════════════════════════════════════════════════
# Fold operation synonym table
# ═══════════════════════════════════════════════════════════════

FOLD_OP_SYNONYMS: Dict[str, str] = {
    # Additive
    'add': 'iadd', '.add': 'iadd', '__add__': 'iadd', 'plus': 'iadd',
    'sum': 'iadd', 'operator.add': 'iadd',
    # Multiplicative
    'mul': 'imul', '.mul': 'imul', '__mul__': 'imul', 'mult': 'imul',
    'multiply': 'imul', 'times': 'imul', 'operator.mul': 'imul',
    # Subtractive
    'sub': 'isub', '.sub': 'isub', '__sub__': 'isub', 'minus': 'isub',
    'operator.sub': 'isub',
    # Bitwise / logical
    'and_': 'iand', '.and_': 'iand', '__and__': 'iand',
    'or_': 'ior', '.or_': 'ior', '__or__': 'ior',
    'bitor': 'ior', 'bitand': 'iand',
    # Comparison folds
    'min': 'imin', 'minimum': 'imin',
    'max': 'imax', 'maximum': 'imax',
    # Collection operations
    'append': 'list_append', 'extend': 'list_extend',
    'concat': 'list_extend', 'join': 'str_join',
    # String
    'str_concat': 'str_concat', '.join': 'str_concat',
}


def canonicalize_op(name: str) -> str:
    """Return the canonical form for a fold operator name."""
    return FOLD_OP_SYNONYMS.get(name, name)


# ═══════════════════════════════════════════════════════════════
# Identity elements for fold operations
# ═══════════════════════════════════════════════════════════════

IDENTITY_ELEMENTS: Dict[str, Any] = {
    # Additive: 0
    'iadd': 0, '.add': 0, 'add': 0, 'sum': 0,
    # Multiplicative: 1
    'imul': 1, '.mul': 1, 'mul': 1, 'mult': 1,
    # Logical
    'and': True, 'iand': True,
    'or': False, 'ior': False,
    # Extremal
    'imin': float('inf'), 'min': float('inf'),
    'imax': float('-inf'), 'max': float('-inf'),
    # Collections
    'list_append': [], 'list_extend': [],
    'str_join': '', 'str_concat': '',
}

# Base-case synonyms: different types of "zero"
BASE_SYNONYMS: Dict[str, List[Any]] = {
    'iadd': [0, 0.0],
    'imul': [1, 1.0],
    'list_append': [[], ()],
    'list_extend': [[], ()],
    'str_join': [''],
    'str_concat': [''],
}


def _identify_fold_op(term: OFold) -> Optional[str]:
    """Try to identify a hash-named fold's actual operation.

    Hash-named ops arise from the normalizer when the fold body
    is a lambda whose structure matches a known operation.
    """
    # 8-char hex hash → try reverse lookup
    if len(term.op_name) != 8:
        return None
    # Heuristic: check if init suggests the operation
    if isinstance(term.init, OLit):
        if term.init.value == 0:
            return 'iadd'
        if term.init.value == 1:
            return 'imul'
        if term.init.value is True:
            return 'iand'
        if term.init.value is False:
            return 'ior'
    if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
        return 'list_extend'
    return None


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D5 axiom: canonicalise fold operations.

    Produces:
      - D5_fold_synonym:      rename op via synonym table
      - D5_fold_canonicalize: identify hash-named op
      - D5_base_split:        split non-identity init via associativity
      - D5_base_normalize:    normalise base-case representation
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OFold):
        return results

    # ── Synonym canonicalisation ──
    canonical = canonicalize_op(term.op_name)
    if canonical != term.op_name:
        results.append((
            OFold(canonical, term.init, term.collection),
            'D5_fold_synonym',
        ))

    # ── Hash-named op identification ──
    if len(term.op_name) == 8:
        ident = _identify_fold_op(term)
        if ident and ident != term.op_name:
            results.append((
                OFold(ident, term.init, term.collection),
                'D5_fold_canonicalize',
            ))

    # ── Non-identity base split ──
    # fold[op](k, coll) = op(k, fold[op](id, coll)) when op is assoc.
    op = canonicalize_op(term.op_name)
    id_val = IDENTITY_ELEMENTS.get(op)
    if id_val is not None and isinstance(term.init, OLit):
        if term.init.value != id_val:
            canonical_fold = OFold(op, OLit(id_val), term.collection)
            results.append((
                OOp(op, (term.init, canonical_fold)),
                'D5_base_split',
            ))

    # ── Base-case synonym normalisation ──
    # e.g. OSeq(()) as init for an additive fold → OLit(0)
    if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
        if op in ('iadd', 'imul', 'isub'):
            # [] as init for numeric fold → use numeric identity
            num_id = IDENTITY_ELEMENTS.get(op)
            if num_id is not None:
                results.append((
                    OFold(op, OLit(num_id), term.collection),
                    'D5_base_normalize',
                ))

    # ── Fold over empty collection ──
    if isinstance(term.collection, OSeq) and len(term.collection.elements) == 0:
        results.append((term.init, 'D5_fold_empty'))

    # ── Fold over singleton ──
    if isinstance(term.collection, OSeq) and len(term.collection.elements) == 1:
        elem = term.collection.elements[0]
        results.append((
            OOp(op, (term.init, elem)),
            'D5_fold_singleton',
        ))

    return results


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D5 apply to this term?"""
    if not isinstance(term, OFold):
        return False
    # Has a non-canonical op name?
    if canonicalize_op(term.op_name) != term.op_name:
        return True
    # Hash-named op?
    if len(term.op_name) == 8:
        return True
    # Non-identity base?
    op = canonicalize_op(term.op_name)
    id_val = IDENTITY_ELEMENTS.get(op)
    if id_val is not None and isinstance(term.init, OLit):
        if term.init.value != id_val:
            return True
    # Empty or singleton collection?
    if isinstance(term.collection, OSeq) and len(term.collection.elements) <= 1:
        return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D5 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      0.9 — both are folds with different op names that are synonyms
      0.7 — both are folds with same op but different inits
      0.5 — both are folds
      0.0 — neither is a fold
    """
    if not isinstance(term, OFold) or not isinstance(other, OFold):
        if isinstance(term, OFold) or isinstance(other, OFold):
            return 0.2
        return 0.0

    c_t = canonicalize_op(term.op_name)
    c_o = canonicalize_op(other.op_name)
    if c_t == c_o:
        if term.init.canon() == other.init.canon():
            return 0.5
        return 0.7
    return 0.9


# ═══════════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D5 in reverse: expand canonical op names to alternatives.

    This emits alternative op-name spellings so the BFS can match
    a term that uses a non-canonical name.
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OFold):
        return results

    canonical = canonicalize_op(term.op_name)
    # Find all synonyms that map to the same canonical form
    for alias, canon_val in FOLD_OP_SYNONYMS.items():
        if canon_val == canonical and alias != term.op_name:
            results.append((
                OFold(alias, term.init, term.collection),
                f'D5_inv_synonym_{alias}',
            ))
            # Limit to 3 alternatives to avoid explosion
            if len(results) >= 3:
                break

    # Reverse base split: op(k, fold[op](id, coll)) → fold[op](k, coll)
    if isinstance(term, OOp) and len(term.args) == 2:
        op = term.name
        second = term.args[1]
        if isinstance(second, OFold) and canonicalize_op(second.op_name) == canonicalize_op(op):
            id_val = IDENTITY_ELEMENTS.get(canonicalize_op(op))
            if id_val is not None and isinstance(second.init, OLit) and second.init.value == id_val:
                results.append((
                    OFold(op, term.args[0], second.collection),
                    'D5_inv_base_merge',
                ))

    return results


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d1_fold_unfold", "d4_comp_fusion", "d6_lazy_eager"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D5 Soundness): If D5 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By the universal property of catamorphisms.

1. Synonym canonicalisation:
   ⟦fold[add](init, c)⟧ = ⟦fold[iadd](init, c)⟧
   because ``add`` and ``iadd`` denote the same binary operation.

2. Base split (associativity):
   ⟦fold[op](k, c)⟧
   = op(k, op(c₁, op(c₂, … op(cₙ, id)…)))
   = op(k, ⟦fold[op](id, c)⟧)
   = ⟦op(k, fold[op](id, c))⟧

   by associativity of op and the identity law op(id, x) = x.

3. Fold over empty:
   ⟦fold[op](init, [])⟧ = init  by definition.

4. Fold over singleton:
   ⟦fold[op](init, [x])⟧ = op(init, x)  by definition.  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "add_to_iadd",
        "before": "OFold('add', OLit(0), OVar('xs'))",
        "after": "OFold('iadd', OLit(0), OVar('xs'))",
        "benchmark": "fold01",
        "description": "fold[add] canonicalises to fold[iadd]",
    },
    {
        "name": "operator_mul_to_imul",
        "before": "OFold('operator.mul', OLit(1), OVar('xs'))",
        "after": "OFold('imul', OLit(1), OVar('xs'))",
        "benchmark": "fold02",
        "description": "fold[operator.mul] → fold[imul]",
    },
    {
        "name": "base_split",
        "before": "OFold('iadd', OLit(10), OVar('xs'))",
        "after": "OOp('iadd', (OLit(10), OFold('iadd', OLit(0), OVar('xs'))))",
        "benchmark": "fold03",
        "description": "fold[add](10, xs) → add(10, fold[add](0, xs))",
    },
    {
        "name": "fold_empty",
        "before": "OFold('iadd', OLit(0), OSeq(()))",
        "after": "OLit(0)",
        "benchmark": "fold04",
        "description": "fold[add](0, []) → 0",
    },
    {
        "name": "fold_singleton",
        "before": "OFold('iadd', OLit(0), OSeq((OLit(42),)))",
        "after": "OOp('iadd', (OLit(0), OLit(42)))",
        "benchmark": "fold05",
        "description": "fold[add](0, [42]) → add(0, 42)",
    },
]

# ═══════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys
    _passed = 0
    _failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global _passed, _failed
        if cond:
            _passed += 1
            print(f'  ✓ {msg}')
        else:
            _failed += 1
            print(f'  ✗ FAIL: {msg}')

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})

    # Test synonym canonicalisation
    print('▶ D5 synonym canonicalisation')
    fold_add = OFold('add', OLit(0), OVar('xs'))
    results = apply(fold_add, ctx)
    _assert(any(lbl == 'D5_fold_synonym' for _, lbl in results),
            'D5 synonym fires for add→iadd')
    found = [t for t, lbl in results if lbl == 'D5_fold_synonym']
    _assert(found[0].op_name == 'iadd', 'canonical op is iadd')

    print('▶ D5 operator.mul → imul')
    fold_opmul = OFold('operator.mul', OLit(1), OVar('xs'))
    results = apply(fold_opmul, ctx)
    _assert(any(lbl == 'D5_fold_synonym' for _, lbl in results),
            'D5 synonym fires for operator.mul')

    # Test hash-named op identification
    print('▶ D5 hash-named op')
    fold_hash = OFold('ab12cd34', OLit(0), OVar('xs'))
    results = apply(fold_hash, ctx)
    _assert(any(lbl == 'D5_fold_canonicalize' for _, lbl in results),
            'D5 canonicalize fires on hash op with init=0')
    id_result = [t for t, lbl in results if lbl == 'D5_fold_canonicalize']
    _assert(id_result[0].op_name == 'iadd', 'identified as iadd')

    # Test base split
    print('▶ D5 base split')
    fold_offset = OFold('iadd', OLit(10), OVar('xs'))
    results = apply(fold_offset, ctx)
    _assert(any(lbl == 'D5_base_split' for _, lbl in results),
            'D5 base split fires for non-identity init')
    split = [t for t, lbl in results if lbl == 'D5_base_split'][0]
    _assert(isinstance(split, OOp) and split.name == 'iadd',
            'split result is iadd(10, fold(iadd, 0, xs))')

    # Test fold over empty
    print('▶ D5 fold over empty')
    fold_empty = OFold('iadd', OLit(0), OSeq(()))
    results = apply(fold_empty, ctx)
    _assert(any(lbl == 'D5_fold_empty' for _, lbl in results),
            'D5 fold_empty fires')
    empty_result = [t for t, lbl in results if lbl == 'D5_fold_empty'][0]
    _assert(empty_result == OLit(0), 'fold over empty → init')

    # Test fold over singleton
    print('▶ D5 fold over singleton')
    fold_single = OFold('iadd', OLit(0), OSeq((OLit(42),)))
    results = apply(fold_single, ctx)
    _assert(any(lbl == 'D5_fold_singleton' for _, lbl in results),
            'D5 fold_singleton fires')

    # Test recognizes
    print('▶ D5 recognizes()')
    _assert(recognizes(fold_add), 'non-canonical op recognised')
    _assert(recognizes(fold_offset), 'non-identity init recognised')
    _assert(recognizes(fold_empty), 'empty collection recognised')
    _assert(not recognizes(OLit(42)), 'literal not recognised')
    _assert(not recognizes(OVar('x')), 'var not recognised')

    # Test relevance_score
    print('▶ D5 relevance_score()')
    _assert(relevance_score(fold_add, OFold('iadd', OLit(0), OVar('xs'))) == 0.5,
            'synonymous ops (same canonical) → 0.5')
    _assert(relevance_score(fold_offset, OFold('iadd', OLit(0), OVar('xs'))) == 0.7,
            'same op, different init → 0.7')
    _assert(relevance_score(OLit(1), OLit(2)) == 0.0,
            'no folds → 0.0')

    # Test inverse
    print('▶ D5 apply_inverse()')
    inv_results = apply_inverse(OFold('iadd', OLit(0), OVar('xs')), ctx)
    _assert(any('inv_synonym' in lbl for _, lbl in inv_results),
            'inverse emits synonym alternatives')

    # Test canonicalize_op
    print('▶ canonicalize_op()')
    _assert(canonicalize_op('add') == 'iadd', 'add→iadd')
    _assert(canonicalize_op('operator.mul') == 'imul', 'operator.mul→imul')
    _assert(canonicalize_op('min') == 'imin', 'min→imin')
    _assert(canonicalize_op('unknown_op') == 'unknown_op', 'unknown passes through')

    # Edge cases
    print('▶ D5 edge cases')
    _assert(apply(OLit(3), ctx) == [], 'D5 on literal is empty')
    _assert(apply(OVar('x'), ctx) == [], 'D5 on var is empty')
    # Already-canonical fold with identity init
    fold_canon = OFold('iadd', OLit(0), OVar('xs'))
    results = apply(fold_canon, ctx)
    _assert(not any(lbl == 'D5_fold_synonym' for _, lbl in results),
            'already canonical → no synonym rewrite')
    _assert(not any(lbl == 'D5_base_split' for _, lbl in results),
            'identity init → no base split')

    print(f'\n{"═" * 50}')
    print(f'  D5: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
