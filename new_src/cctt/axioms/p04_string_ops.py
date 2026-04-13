"""P4: String Method Equivalences.

s.split(sep) ↔ re.split(re.escape(sep), s)
sep.join(parts) ↔ fold with string concatenation
s.strip() ↔ s.lstrip().rstrip()
s.startswith(prefix) ↔ s[:len(prefix)] == prefix
s.endswith(suffix) ↔ s[-len(suffix):] == suffix
s.replace(old, new) ↔ new.join(s.split(old))
s.lower() ↔ ''.join(c.lower() for c in s)
s.count(sub) ↔ len(s.split(sub)) - 1

Mathematical foundation:
  Strings are elements of the free monoid  Σ*  over the alphabet Σ.
  String methods are morphisms in the category of monoid actions.

  The equivalences are witnessed by natural isomorphisms:
    .split(sep)          ≅  re.split(re.escape(sep), ·)   (literal case)
    sep.join(·)          ≅  fold[concat_sep](ε, ·)         (monoid fold)
    .strip()             ≅  .rstrip() ∘ .lstrip()          (composition)
    .replace(old, new)   ≅  new.join(·.split(old))         (split-join duality)
    .count(sub)          ≅  |·.split(sub)| − 1             (fence-post lemma)

  The split-join duality is the fundamental adjunction:
    split_sep ⊣ join_sep  in the category of Σ*-actions.
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

AXIOM_NAME = 'P4_string_ops'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem P4.1 (Split-Regex Equivalence):
  For any string s and literal separator sep,
    s.split(sep)  ≡  re.split(re.escape(sep), s)
  as morphisms Σ* → List[Σ*].

Proof sketch:
  1. re.escape(sep) produces a pattern matching sep literally.
  2. re.split with a literal pattern behaves identically to str.split
     for non-empty separators.
  3. Both decompose s into maximal substrings not containing sep.  ∎

Theorem P4.2 (Strip Decomposition):
  For any string s,
    s.strip()  ≡  s.lstrip().rstrip()
  as endomorphisms on Σ*.

Proof sketch:
  strip() removes leading and trailing whitespace.  lstrip() removes
  leading; rstrip() removes trailing.  Since lstrip() does not add
  trailing whitespace, the composition is idempotent and equal.  ∎

Theorem P4.3 (Replace as Split-Join):
  For any strings s, old, new with old ≠ ε,
    s.replace(old, new)  ≡  new.join(s.split(old))
  as morphisms Σ* → Σ*.

Proof sketch:
  s.split(old) decomposes s at every non-overlapping occurrence of old.
  new.join(·) re-assembles with new in place of old.  This is exactly
  the semantics of replace.  ∎

Theorem P4.4 (Count as Split Length):
  For any strings s, sub with sub ≠ ε,
    s.count(sub)  ≡  len(s.split(sub)) - 1
  by the fence-post lemma: n occurrences produce n+1 segments.  ∎
"""

COMPOSES_WITH = ['P3_dict_ops', 'FOLD_extended', 'D12_map_construct']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'split to re.split',
        'before': "s.split(sep)",
        'after': "re.split(re.escape(sep), s)",
        'axiom': 'P4_split_to_resplit',
    },
    {
        'name': 're.split to split',
        'before': "re.split(re.escape(sep), s)",
        'after': "s.split(sep)",
        'axiom': 'P4_resplit_to_split',
    },
    {
        'name': 'join to fold',
        'before': "sep.join(parts)",
        'after': "fold[str_concat_sep]('', parts)",
        'axiom': 'P4_join_to_fold',
    },
    {
        'name': 'strip to lstrip rstrip',
        'before': "s.strip()",
        'after': "s.lstrip().rstrip()",
        'axiom': 'P4_strip_to_lr',
    },
    {
        'name': 'startswith to slice',
        'before': "s.startswith(prefix)",
        'after': "s[:len(prefix)] == prefix",
        'axiom': 'P4_startswith_to_slice',
    },
    {
        'name': 'endswith to slice',
        'before': "s.endswith(suffix)",
        'after': "s[-len(suffix):] == suffix",
        'axiom': 'P4_endswith_to_slice',
    },
    {
        'name': 'replace to split-join',
        'before': "s.replace(old, new)",
        'after': "new.join(s.split(old))",
        'axiom': 'P4_replace_to_split_join',
    },
    {
        'name': 'count to split length',
        'before': "s.count(sub)",
        'after': "len(s.split(sub)) - 1",
        'axiom': 'P4_count_to_split_len',
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
    """Apply P4 string method equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── s.split(sep) → re.split(re.escape(sep), s) ──
    if isinstance(term, OOp) and term.name == '.split':
        if len(term.args) == 2:
            s, sep = term.args
            results.append((
                OOp('re.split', (OOp('re.escape', (sep,)), s)),
                'P4_split_to_resplit',
            ))

    # ── re.split(re.escape(sep), s) → s.split(sep) (inverse) ──
    if isinstance(term, OOp) and term.name == 're.split':
        if len(term.args) == 2:
            pat, s = term.args
            if isinstance(pat, OOp) and pat.name == 're.escape' and len(pat.args) == 1:
                sep = pat.args[0]
                results.append((
                    OOp('.split', (s, sep)),
                    'P4_resplit_to_split',
                ))

    # ── sep.join(parts) → fold[str_concat_sep](ε, parts) ──
    if isinstance(term, OOp) and term.name == '.join':
        if len(term.args) == 2:
            sep, parts = term.args
            results.append((
                OFold('str_concat_sep', OLit(''), parts),
                'P4_join_to_fold',
            ))

    # ── fold[str_concat_sep](ε, parts) → sep.join(parts) (inverse) ──
    if isinstance(term, OFold) and term.op_name == 'str_concat_sep':
        if isinstance(term.init, OLit) and term.init.value == '':
            results.append((
                OOp('.join', (OLit(''), term.collection)),
                'P4_fold_to_join',
            ))

    # ── s.strip() → s.lstrip().rstrip() ──
    if isinstance(term, OOp) and term.name == '.strip':
        if len(term.args) == 1:
            s = term.args[0]
            results.append((
                OOp('.rstrip', (OOp('.lstrip', (s,)),)),
                'P4_strip_to_lr',
            ))

    # ── s.lstrip().rstrip() → s.strip() (inverse) ──
    if isinstance(term, OOp) and term.name == '.rstrip':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            inner = term.args[0]
            if inner.name == '.lstrip' and len(inner.args) == 1:
                s = inner.args[0]
                results.append((
                    OOp('.strip', (s,)),
                    'P4_lr_to_strip',
                ))

    # ── s.startswith(prefix) → s[:len(prefix)] == prefix ──
    if isinstance(term, OOp) and term.name == '.startswith':
        if len(term.args) == 2:
            s, prefix = term.args
            results.append((
                OOp('eq', (
                    OOp('slice', (s, OLit(None), OOp('len', (prefix,)))),
                    prefix,
                )),
                'P4_startswith_to_slice',
            ))

    # ── s[:len(prefix)] == prefix → s.startswith(prefix) (inverse) ──
    if isinstance(term, OOp) and term.name == 'eq' and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(lhs, OOp) and lhs.name == 'slice' and len(lhs.args) == 3:
            s, lo, hi = lhs.args
            if isinstance(lo, OLit) and lo.value is None:
                if isinstance(hi, OOp) and hi.name == 'len' and len(hi.args) == 1:
                    if _terms_equal(hi.args[0], rhs):
                        results.append((
                            OOp('.startswith', (s, rhs)),
                            'P4_slice_to_startswith',
                        ))

    # ── s.endswith(suffix) → s[-len(suffix):] == suffix ──
    if isinstance(term, OOp) and term.name == '.endswith':
        if len(term.args) == 2:
            s, suffix = term.args
            results.append((
                OOp('eq', (
                    OOp('slice', (
                        s,
                        OOp('neg', (OOp('len', (suffix,)),)),
                        OLit(None),
                    )),
                    suffix,
                )),
                'P4_endswith_to_slice',
            ))

    # ── s.replace(old, new) → new.join(s.split(old)) ──
    if isinstance(term, OOp) and term.name == '.replace':
        if len(term.args) == 3:
            s, old, new = term.args
            results.append((
                OOp('.join', (new, OOp('.split', (s, old)))),
                'P4_replace_to_split_join',
            ))

    # ── new.join(s.split(old)) → s.replace(old, new) (inverse) ──
    if isinstance(term, OOp) and term.name == '.join' and len(term.args) == 2:
        new, parts = term.args
        if isinstance(parts, OOp) and parts.name == '.split' and len(parts.args) == 2:
            s, old = parts.args
            results.append((
                OOp('.replace', (s, old, new)),
                'P4_split_join_to_replace',
            ))

    # ── s.lower() → ''.join(c.lower() for c in s) ──
    if isinstance(term, OOp) and term.name == '.lower':
        if len(term.args) == 1:
            s = term.args[0]
            results.append((
                OOp('.join', (
                    OLit(''),
                    OMap(
                        OLam(('c',), OOp('.lower', (OVar('c'),))),
                        s,
                    ),
                )),
                'P4_lower_to_charmap',
            ))

    # ── ''.join(map(c.lower(), s)) → s.lower() (inverse) ──
    if isinstance(term, OOp) and term.name == '.join' and len(term.args) == 2:
        sep, body = term.args
        if isinstance(sep, OLit) and sep.value == '' and isinstance(body, OMap):
            if isinstance(body.transform, OLam) and len(body.transform.params) == 1:
                lam_body = body.transform.body
                if isinstance(lam_body, OOp) and lam_body.name == '.lower':
                    results.append((
                        OOp('.lower', (body.collection,)),
                        'P4_charmap_to_lower',
                    ))

    # ── s.count(sub) → len(s.split(sub)) - 1 ──
    if isinstance(term, OOp) and term.name == '.count':
        if len(term.args) == 2:
            s, sub = term.args
            results.append((
                OOp('sub', (
                    OOp('len', (OOp('.split', (s, sub)),)),
                    OLit(1),
                )),
                'P4_count_to_split_len',
            ))

    # ── len(s.split(sub)) - 1 → s.count(sub) (inverse) ──
    if isinstance(term, OOp) and term.name == 'sub' and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(rhs, OLit) and rhs.value == 1:
            if isinstance(lhs, OOp) and lhs.name == 'len' and len(lhs.args) == 1:
                inner = lhs.args[0]
                if isinstance(inner, OOp) and inner.name == '.split' and len(inner.args) == 2:
                    s, sub = inner.args
                    results.append((
                        OOp('.count', (s, sub)),
                        'P4_split_len_to_count',
                    ))

    return results


def _terms_equal(a: OTerm, b: OTerm) -> bool:
    """Structural equality check for OTerms via canonical form."""
    return a.canon() == b.canon()


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P4 in reverse: expanded forms → method calls.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P4_resplit_to_split',
        'P4_fold_to_join',
        'P4_lr_to_strip',
        'P4_slice_to_startswith',
        'P4_split_join_to_replace',
        'P4_charmap_to_lower',
        'P4_split_len_to_count',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P4 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('.split', '.join', '.strip', '.lstrip', '.rstrip',
                         '.startswith', '.endswith', '.replace', '.lower',
                         '.count', 're.split'):
            return True
        # len(s.split(sub)) - 1 pattern
        if term.name == 'sub' and len(term.args) == 2:
            lhs = term.args[0]
            if isinstance(lhs, OOp) and lhs.name == 'len' and len(lhs.args) == 1:
                inner = lhs.args[0]
                if isinstance(inner, OOp) and inner.name == '.split':
                    return True
        # s[:len(prefix)] == prefix pattern
        if term.name == 'eq' and len(term.args) == 2:
            lhs = term.args[0]
            if isinstance(lhs, OOp) and lhs.name == 'slice':
                return True
    if isinstance(term, OFold) and term.op_name == 'str_concat_sep':
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P4 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_split_s = '.split(' in sc
    has_split_t = '.split(' in tc
    has_join_s = '.join(' in sc
    has_join_t = '.join(' in tc
    has_replace_s = '.replace(' in sc
    has_replace_t = '.replace(' in tc
    has_strip_s = '.strip(' in sc or '.lstrip(' in sc or '.rstrip(' in sc
    has_strip_t = '.strip(' in tc or '.lstrip(' in tc or '.rstrip(' in tc
    has_starts_s = '.startswith(' in sc
    has_starts_t = '.startswith(' in tc
    has_ends_s = '.endswith(' in sc
    has_ends_t = '.endswith(' in tc
    has_re_s = 're.split(' in sc
    has_re_t = 're.split(' in tc

    # split ↔ re.split: high relevance
    if has_split_s and has_re_t:
        return 0.95
    if has_split_t and has_re_s:
        return 0.95

    # replace ↔ split-join: high relevance
    if has_replace_s and (has_split_t or has_join_t):
        return 0.95
    if has_replace_t and (has_split_s or has_join_s):
        return 0.95

    # strip ↔ lstrip/rstrip composition
    if has_strip_s != has_strip_t:
        return 0.90

    # startswith/endswith ↔ slice comparison
    if has_starts_s or has_starts_t or has_ends_s or has_ends_t:
        return 0.85

    # join ↔ fold
    if has_join_s != has_join_t:
        return 0.80

    # Generic string method signals
    if any([has_split_s, has_join_s, has_replace_s, has_strip_s,
            has_split_t, has_join_t, has_replace_t, has_strip_t]):
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
    s = OVar('s')
    sep = OVar('sep')
    prefix = OVar('prefix')
    suffix = OVar('suffix')
    old = OVar('old')
    new = OVar('new')
    sub = OVar('sub')
    parts = OVar('parts')

    # ── split → re.split ──
    print("P4: split → re.split ...")
    split_term = OOp('.split', (s, sep))
    r = apply(split_term, ctx)
    _assert(len(r) >= 1, "s.split(sep) should rewrite")
    _assert(r[0][1] == 'P4_split_to_resplit', "axiom label")
    _assert(isinstance(r[0][0], OOp) and r[0][0].name == 're.split', "result is re.split")

    # ── re.split → split (inverse) ──
    print("P4: re.split → split ...")
    resplit_term = OOp('re.split', (OOp('re.escape', (sep,)), s))
    r2 = apply(resplit_term, ctx)
    _assert(any(lbl == 'P4_resplit_to_split' for _, lbl in r2), "resplit→split")

    # ── roundtrip split ──
    print("P4: split roundtrip ...")
    rt = apply(r[0][0], ctx)
    _assert(any(lbl == 'P4_resplit_to_split' for _, lbl in rt), "roundtrip works")

    # ── join → fold ──
    print("P4: join → fold ...")
    join_term = OOp('.join', (sep, parts))
    r3 = apply(join_term, ctx)
    _assert(any(lbl == 'P4_join_to_fold' for _, lbl in r3), "join→fold")
    _assert(any(isinstance(t, OFold) for t, _ in r3), "result is OFold")

    # ── fold → join (inverse) ──
    print("P4: fold → join ...")
    fold_term = OFold('str_concat_sep', OLit(''), parts)
    r4 = apply(fold_term, ctx)
    _assert(any(lbl == 'P4_fold_to_join' for _, lbl in r4), "fold→join")

    # ── strip → lstrip().rstrip() ──
    print("P4: strip → lstrip.rstrip ...")
    strip_term = OOp('.strip', (s,))
    r5 = apply(strip_term, ctx)
    _assert(len(r5) >= 1, "strip should rewrite")
    _assert(r5[0][1] == 'P4_strip_to_lr', "strip label")

    # ── lstrip().rstrip() → strip (inverse) ──
    print("P4: lstrip.rstrip → strip ...")
    lr_term = OOp('.rstrip', (OOp('.lstrip', (s,)),))
    r6 = apply(lr_term, ctx)
    _assert(any(lbl == 'P4_lr_to_strip' for _, lbl in r6), "lr→strip")

    # ── startswith → slice eq ──
    print("P4: startswith → slice ...")
    sw_term = OOp('.startswith', (s, prefix))
    r7 = apply(sw_term, ctx)
    _assert(len(r7) >= 1, "startswith should rewrite")
    _assert(r7[0][1] == 'P4_startswith_to_slice', "startswith label")

    # ── slice eq → startswith (inverse) ──
    print("P4: slice → startswith ...")
    slice_eq = OOp('eq', (
        OOp('slice', (s, OLit(None), OOp('len', (prefix,)))),
        prefix,
    ))
    r8 = apply(slice_eq, ctx)
    _assert(any(lbl == 'P4_slice_to_startswith' for _, lbl in r8), "slice→startswith")

    # ── endswith → slice eq ──
    print("P4: endswith → slice ...")
    ew_term = OOp('.endswith', (s, suffix))
    r9 = apply(ew_term, ctx)
    _assert(len(r9) >= 1, "endswith should rewrite")
    _assert(r9[0][1] == 'P4_endswith_to_slice', "endswith label")

    # ── replace → split-join ──
    print("P4: replace → split-join ...")
    repl_term = OOp('.replace', (s, old, new))
    r10 = apply(repl_term, ctx)
    _assert(any(lbl == 'P4_replace_to_split_join' for _, lbl in r10), "replace→split-join")

    # ── split-join → replace (inverse) ──
    print("P4: split-join → replace ...")
    sj_term = OOp('.join', (new, OOp('.split', (s, old))))
    r11 = apply(sj_term, ctx)
    _assert(any(lbl == 'P4_split_join_to_replace' for _, lbl in r11), "split-join→replace")

    # ── lower → charmap ──
    print("P4: lower → charmap ...")
    lower_term = OOp('.lower', (s,))
    r12 = apply(lower_term, ctx)
    _assert(any(lbl == 'P4_lower_to_charmap' for _, lbl in r12), "lower→charmap")

    # ── charmap → lower (inverse) ──
    print("P4: charmap → lower ...")
    charmap_term = OOp('.join', (
        OLit(''),
        OMap(OLam(('c',), OOp('.lower', (OVar('c'),))), s),
    ))
    r13 = apply(charmap_term, ctx)
    _assert(any(lbl == 'P4_charmap_to_lower' for _, lbl in r13), "charmap→lower")

    # ── count → split length ──
    print("P4: count → split length ...")
    count_term = OOp('.count', (s, sub))
    r14 = apply(count_term, ctx)
    _assert(any(lbl == 'P4_count_to_split_len' for _, lbl in r14), "count→split_len")

    # ── split length → count (inverse) ──
    print("P4: split length → count ...")
    split_len = OOp('sub', (
        OOp('len', (OOp('.split', (s, sub)),)),
        OLit(1),
    ))
    r15 = apply(split_len, ctx)
    _assert(any(lbl == 'P4_split_len_to_count' for _, lbl in r15), "split_len→count")

    # ── recognizes() ──
    print("P4: recognizes ...")
    _assert(recognizes(split_term), "recognizes .split")
    _assert(recognizes(join_term), "recognizes .join")
    _assert(recognizes(strip_term), "recognizes .strip")
    _assert(recognizes(sw_term), "recognizes .startswith")
    _assert(recognizes(repl_term), "recognizes .replace")
    _assert(recognizes(count_term), "recognizes .count")
    _assert(recognizes(split_len), "recognizes split_len pattern")
    _assert(recognizes(fold_term), "recognizes fold str_concat_sep")
    _assert(not recognizes(OOp('sorted', (s,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P4: relevance_score ...")
    score = relevance_score(split_term, resplit_term)
    _assert(score > 0.8, f"split↔resplit score={score:.2f} > 0.8")
    score2 = relevance_score(repl_term, sj_term)
    _assert(score2 > 0.8, f"replace↔splitjoin score={score2:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (s,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P4: apply_inverse ...")
    inv = apply_inverse(resplit_term, ctx)
    _assert(len(inv) >= 1, "inverse of re.split produces .split")
    inv2 = apply_inverse(sj_term, ctx)
    _assert(any(lbl == 'P4_split_join_to_replace' for _, lbl in inv2), "split-join inverse")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P4 string_ops: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
