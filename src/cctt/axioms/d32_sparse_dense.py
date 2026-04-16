"""D32: Sparse ↔ Dense Representation (Theorem 32.1).

Sparse containers (defaultdict, Counter, filtered dicts) are isomorphic
to their dense counterparts (full arrays, complete dicts) when viewed as
mathematical maps  K → V  with a distinguished zero element.

Mathematical foundation:
  Let (V, 0_V) be a pointed set.  A map  f: K → V  can be represented:
    • Dense:   an array/dict that stores f(k) for every k ∈ K.
    • Sparse:  a dict that stores only {k : f(k) | f(k) ≠ 0_V}.

  The isomorphism is witnessed by:
    dense_to_sparse(d) = {k: v for k, v in d.items() if v != 0}
    sparse_to_dense(s, keys) = {k: s.get(k, 0) for k in keys}

  These form a retraction pair (section-retraction) in Set:
    sparse_to_dense ∘ dense_to_sparse = id  (on the image).

Covers:
  • defaultdict(int) ↔ full array with zeros
  • {k: v for k,v in items if v != 0} ↔ full dict
  • dict.get(k, 0) ↔ array[k] (with bounds)
  • Counter (sparse) ↔ histogram array (dense)
  • Sparse matrix operations ↔ dense matrix operations
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

AXIOM_NAME = 'D32_sparse_dense'
AXIOM_CATEGORY = 'data_representation'

SOUNDNESS_PROOF = """
Theorem 32.1 (Sparse-Dense Isomorphism):
  For a pointed set (V, 0_V) and key set K, the maps
    dense_to_sparse: V^K → V^K_nz  (filter out zero entries)
    sparse_to_dense: V^K_nz → V^K   (fill missing keys with 0_V)
  form an isomorphism of the underlying mathematical functions K → V.

Proof sketch:
  1. For any f : K → V and its sparse representation s = {k: f(k) | f(k) ≠ 0}:
       sparse_to_dense(s)(k) = s.get(k, 0) = f(k)  for all k ∈ K.
     This is because:
       - If f(k) ≠ 0: k ∈ dom(s), so s.get(k, 0) = s[k] = f(k).  ✓
       - If f(k) = 0: k ∉ dom(s), so s.get(k, 0) = 0 = f(k).  ✓
  2. dense_to_sparse(sparse_to_dense(s)) = s
     because filtering out zeros from a map that only differs on zeros
     recovers exactly the original sparse representation.  ∎

  dict.get(k, 0) ≡ array[k] follows directly: both compute f(k).
"""

COMPOSES_WITH = ['D13_histogram', 'D14_indexing', 'D12_map_construct']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'defaultdict to full array',
        'before': "defaultdict(int, sparse_data)",
        'after': "[sparse_data.get(i, 0) for i in range(n)]",
        'axiom': 'D32_sparse_to_dense_array',
    },
    {
        'name': 'filter zeros (dense to sparse)',
        'before': "{k: v for k, v in d.items() if v != 0}",
        'after': "sparse_dict(d)",
        'axiom': 'D32_dense_to_sparse',
    },
    {
        'name': 'dict.get with default',
        'before': "d.get(k, 0)",
        'after': "d[k]  # when k guaranteed in d",
        'axiom': 'D32_get_default_to_index',
    },
    {
        'name': 'Counter to histogram array',
        'before': "Counter(xs)",
        'after': "[xs.count(i) for i in range(max_val)]",
        'axiom': 'D32_counter_to_histogram',
    },
    {
        'name': 'fill missing keys',
        'before': "{k: d.get(k, 0) for k in all_keys}",
        'after': "dense_from_sparse(d, all_keys)",
        'axiom': 'D32_fill_missing',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: fiber context
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
    """Apply D32 sparse ↔ dense equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── defaultdict(int) → dense representation ──
    if isinstance(term, OOp) and term.name == 'defaultdict':
        if len(term.args) >= 1 and isinstance(term.args[0], OLit):
            if term.args[0].value in (0, 'int'):
                results.append((
                    OOp('dense_zeros', term.args[1:] if len(term.args) > 1 else ()),
                    'D32_defaultdict_to_dense',
                ))

    # ── dict.get(k, 0) → getitem(d, k) (dense indexing) ──
    if isinstance(term, OOp) and term.name == '.get' and len(term.args) == 3:
        d, k, default = term.args
        if isinstance(default, OLit) and default.value == 0:
            results.append((
                OOp('getitem', (d, k)),
                'D32_get_default_to_index',
            ))

    # ── OOp('get', (d, k, OLit(0))) alternate form ──
    if isinstance(term, OOp) and term.name == 'get' and len(term.args) == 3:
        d, k, default = term.args
        if isinstance(default, OLit) and default.value == 0:
            results.append((
                OOp('getitem', (d, k)),
                'D32_get_default_to_index',
            ))

    # ── getitem(d, k) → d.get(k, 0) (sparse-safe indexing) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        d, k = term.args
        results.append((
            OOp('.get', (d, k, OLit(0))),
            'D32_index_to_get_default',
        ))

    # ── filter-map removing zeros: dense → sparse ──
    if isinstance(term, OMap) and term.filter_pred is not None:
        pred = term.filter_pred
        if isinstance(pred, OLam) and len(pred.params) == 1:
            body = pred.body
            # λx. x != 0  or  λ(k,v). v != 0
            if _is_nonzero_filter(body, pred.params[0]):
                results.append((
                    OOp('sparse_filter', (term.collection,)),
                    'D32_dense_to_sparse',
                ))

    # ── {k: v for k,v in d.items() if v != 0} pattern via OMap ──
    # Also detect comprehension that filters items
    if isinstance(term, OMap) and term.filter_pred is not None:
        if isinstance(term.collection, OOp) and term.collection.name == '.items':
            results.append((
                OOp('sparse_from_items', (term.collection.args[0] if term.collection.args else OUnknown('d'),)),
                'D32_items_filter_to_sparse',
            ))

    # ── Counter(xs) ↔ histogram array ──
    if isinstance(term, OOp) and term.name == 'Counter' and len(term.args) == 1:
        xs = term.args[0]
        # Counter is sparse; histogram array is dense
        results.append((
            OOp('histogram_array', (xs,)),
            'D32_counter_to_histogram',
        ))

    if isinstance(term, OOp) and term.name == 'histogram_array' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('Counter', (xs,)),
            'D32_histogram_to_counter',
        ))

    # ── sparse_matrix operations → dense_matrix ──
    if isinstance(term, OOp) and term.name in ('csr_matrix', 'csc_matrix', 'coo_matrix'):
        results.append((
            OOp('dense_matrix', term.args),
            'D32_sparse_matrix_to_dense',
        ))

    if isinstance(term, OOp) and term.name == 'dense_matrix':
        results.append((
            OOp('csr_matrix', term.args),
            'D32_dense_matrix_to_sparse',
        ))

    # ── {k: d.get(k, 0) for k in all_keys} → dense_from_sparse ──
    if isinstance(term, OMap):
        tf = term.transform
        if isinstance(tf, OLam) and len(tf.params) == 1:
            body = tf.body
            param = tf.params[0]
            if (isinstance(body, OOp) and body.name in ('.get', 'get')
                    and len(body.args) == 3):
                _, key_arg, default = body.args
                if (isinstance(key_arg, OVar) and key_arg.name == param
                        and isinstance(default, OLit) and default.value == 0):
                    results.append((
                        OOp('dense_from_sparse', (body.args[0], term.collection)),
                        'D32_fill_missing',
                    ))

    return results


def _is_nonzero_filter(body: OTerm, param: str) -> bool:
    """Check if body represents `param != 0` or similar nonzero test."""
    if isinstance(body, OOp) and body.name in ('noteq', 'ne') and len(body.args) == 2:
        lhs, rhs = body.args
        if isinstance(lhs, OVar) and lhs.name == param and isinstance(rhs, OLit) and rhs.value == 0:
            return True
        if isinstance(rhs, OVar) and rhs.name == param and isinstance(lhs, OLit) and lhs.value == 0:
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D32 in reverse: dense → sparse conversions."""
    results = apply(term, ctx)
    inverse_labels = {
        'D32_index_to_get_default',
        'D32_histogram_to_counter',
        'D32_dense_matrix_to_sparse',
        'D32_dense_to_sparse',
        'D32_items_filter_to_sparse',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D32 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('defaultdict', 'Counter', 'histogram_array',
                         'csr_matrix', 'csc_matrix', 'coo_matrix',
                         'dense_matrix', 'dense_zeros', 'sparse_filter',
                         'dense_from_sparse', 'sparse_from_items'):
            return True
        if term.name in ('.get', 'get') and len(term.args) == 3:
            if isinstance(term.args[2], OLit) and term.args[2].value == 0:
                return True
        if term.name == 'getitem' and len(term.args) == 2:
            return True
    if isinstance(term, OMap) and term.filter_pred is not None:
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D32 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    sparse_kw = ('defaultdict(', 'Counter(', '.get(', 'sparse', 'csr_matrix(', 'coo_matrix(')
    dense_kw = ('histogram_array(', 'dense_matrix(', 'dense_zeros(', 'dense_from_sparse(')

    has_sparse_s = any(k in sc for k in sparse_kw)
    has_sparse_t = any(k in tc for k in sparse_kw)
    has_dense_s = any(k in sc for k in dense_kw)
    has_dense_t = any(k in tc for k in dense_kw)

    if (has_sparse_s and has_dense_t) or (has_dense_s and has_sparse_t):
        return 0.95
    if has_sparse_s != has_sparse_t:
        return 0.80
    if has_dense_s != has_dense_t:
        return 0.80
    if has_sparse_s or has_dense_s or has_sparse_t or has_dense_t:
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
    d = OVar('d')
    k = OVar('k')
    xs = OVar('xs')

    # ── defaultdict(int) → dense ──
    print("D32: defaultdict(int) → dense ...")
    dd_term = OOp('defaultdict', (OLit(0),))
    r = apply(dd_term, ctx)
    _assert(any(lbl == 'D32_defaultdict_to_dense' for _, lbl in r), "defaultdict→dense")

    # ── dict.get(k, 0) → getitem ──
    print("D32: dict.get(k, 0) → getitem ...")
    get_term = OOp('.get', (d, k, OLit(0)))
    r2 = apply(get_term, ctx)
    _assert(any(lbl == 'D32_get_default_to_index' for _, lbl in r2), "get→getitem")

    # ── getitem → dict.get(k, 0) (reverse) ──
    print("D32: getitem → dict.get(k, 0) ...")
    gi_term = OOp('getitem', (d, k))
    r3 = apply(gi_term, ctx)
    _assert(any(lbl == 'D32_index_to_get_default' for _, lbl in r3), "getitem→get")

    # ── Counter → histogram_array ──
    print("D32: Counter → histogram_array ...")
    counter_term = OOp('Counter', (xs,))
    r4 = apply(counter_term, ctx)
    _assert(any(lbl == 'D32_counter_to_histogram' for _, lbl in r4), "Counter→histogram")

    # ── histogram_array → Counter (reverse) ──
    print("D32: histogram_array → Counter ...")
    hist_term = OOp('histogram_array', (xs,))
    r5 = apply(hist_term, ctx)
    _assert(any(lbl == 'D32_histogram_to_counter' for _, lbl in r5), "histogram→Counter")

    # ── sparse_matrix → dense_matrix ──
    print("D32: sparse_matrix → dense_matrix ...")
    sparse_mat = OOp('csr_matrix', (OVar('data'),))
    r6 = apply(sparse_mat, ctx)
    _assert(any(lbl == 'D32_sparse_matrix_to_dense' for _, lbl in r6), "sparse→dense matrix")

    # ── dense_matrix → sparse_matrix ──
    print("D32: dense_matrix → sparse_matrix ...")
    dense_mat = OOp('dense_matrix', (OVar('data'),))
    r7 = apply(dense_mat, ctx)
    _assert(any(lbl == 'D32_dense_matrix_to_sparse' for _, lbl in r7), "dense→sparse matrix")

    # ── Roundtrip: defaultdict → dense → getitem → get ──
    print("D32: roundtrip ...")
    # get(k,0) → getitem, then getitem → get(k,0)
    rewritten = [t for t, lbl in r2 if lbl == 'D32_get_default_to_index']
    _assert(len(rewritten) >= 1, "roundtrip step 1")
    r_back = apply(rewritten[0], ctx)
    _assert(any(lbl == 'D32_index_to_get_default' for _, lbl in r_back), "roundtrip step 2")

    # ── fill_missing pattern ──
    print("D32: fill missing keys ...")
    fill_term = OMap(
        OLam(('k',), OOp('.get', (d, OVar('k'), OLit(0)))),
        OVar('all_keys'),
    )
    r8 = apply(fill_term, ctx)
    _assert(any(lbl == 'D32_fill_missing' for _, lbl in r8), "fill missing")

    # ── recognizes() ──
    print("D32: recognizes ...")
    _assert(recognizes(dd_term), "recognizes defaultdict")
    _assert(recognizes(get_term), "recognizes .get")
    _assert(recognizes(counter_term), "recognizes Counter")
    _assert(recognizes(sparse_mat), "recognizes csr_matrix")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D32: relevance_score ...")
    score = relevance_score(counter_term, hist_term)
    _assert(score > 0.8, f"Counter↔histogram score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D32: apply_inverse ...")
    inv = apply_inverse(hist_term, ctx)
    _assert(len(inv) >= 1, "inverse produces Counter")
    inv2 = apply_inverse(gi_term, ctx)
    _assert(any(lbl == 'D32_index_to_get_default' for _, lbl in inv2), "inverse getitem→get")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D32 sparse_dense: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
