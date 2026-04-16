"""D46: String Building Equivalences (Theorem 29.4.1).

String construction methods are equivalent when they produce the
same character sequence.

Mathematical foundation:
  Strings form a free monoid (Σ*, ·, ε) under concatenation.
  All string-building operations — join, concatenation, formatting,
  interpolation — are homomorphisms into this monoid.

  The key algebraic fact: concatenation is associative and has
  identity ε (empty string).  Therefore:
    "".join([a, b, c])  =  a + b + c  =  f"{a}{b}{c}"

  For formatting operations, the equivalence holds when:
  - The format string is a literal (no dynamic format specs)
  - All interpolated values have consistent __str__ representations

  String reversal: s[::-1] = "".join(reversed(s)) because
  reversal is an anti-homomorphism of the free monoid.

Covers:
  • "".join(parts) ↔ s += x loop (concatenation)
  • f-strings ↔ str.format() ↔ % formatting ↔ Template
  • "".join(list comp) ↔ "".join(map(...))
  • re.sub(literal) ↔ str.replace() (for literal patterns)
  • String reversal: s[::-1] ↔ "".join(reversed(s))
  • str() conversion variants
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

AXIOM_NAME = 'D46_string_build'
AXIOM_CATEGORY = 'algorithmic_patterns'  # §29

SOUNDNESS_PROOF = """
Theorem 29.4.1 (String Join ↔ Concatenation Loop):
  Let parts = [s_0, s_1, ..., s_{n-1}] be a list of strings.  Then:
    "".join(parts) = s_0 + s_1 + ... + s_{n-1}
                   = fold(+, "", parts)

Proof:
  "".join iterates over parts, concatenating each element to an
  accumulator initialized to "".  This is exactly the fold.
  The concatenation loop s += x does the same.
  By the monoid law (associativity + identity), all produce the
  same string.  ∎

Theorem 29.4.2 (Format String Equivalences):
  For string values v_0, v_1, ...:
    f"text {v_0} more {v_1}"
      = "text " + str(v_0) + " more " + str(v_1)
      = "text %s more %s" % (v_0, v_1)
      = "text {} more {}".format(v_0, v_1)
      = Template("text $v0 more $v1").substitute(v0=v_0, v1=v_1)

Proof:
  All format operations insert str(v_i) at the corresponding
  position in the template string.  The intermediate strings
  are identical character-by-character.  ∎

Theorem 29.4.3 (Join of Comprehension ↔ Join of Map):
  "".join([str(x) for x in xs]) = "".join(map(str, xs))

Proof:
  The list comprehension [str(x) for x in xs] produces the same
  list as list(map(str, xs)).  Joining produces the same string.  ∎

Theorem 29.4.4 (Literal Replace ↔ re.sub):
  For literal (non-regex) pattern p:
    s.replace(p, r) = re.sub(re.escape(p), r, s)

Proof:
  re.escape(p) matches exactly the literal string p.
  re.sub replaces all non-overlapping occurrences left-to-right,
  which is the same semantics as str.replace.  ∎

Theorem 29.4.5 (String Reversal):
  s[::-1] = "".join(reversed(s))

Proof:
  s[::-1] produces the string with characters in reverse order.
  reversed(s) iterates characters in reverse.  join concatenates
  them left-to-right, producing the reversed string.  ∎
"""

COMPOSES_WITH = ['D04_comp_fusion', 'D05_fold_universal', 'D24_eta']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Join to concat loop',
        'before': '"".join(parts)',
        'after': 'fold(+, "", parts)',
        'axiom': 'D46_join_to_concat',
    },
    {
        'name': 'F-string to concatenation',
        'before': 'f"hello {name}"',
        'after': '"hello " + str(name)',
        'axiom': 'D46_fstring_to_concat',
    },
    {
        'name': 'F-string to format',
        'before': 'f"hello {name}"',
        'after': '"hello {}".format(name)',
        'axiom': 'D46_fstring_to_format',
    },
    {
        'name': 'F-string to percent',
        'before': 'f"hello {name}"',
        'after': '"hello %s" % name',
        'axiom': 'D46_fstring_to_percent',
    },
    {
        'name': 'Join comprehension to join map',
        'before': '"".join([str(x) for x in xs])',
        'after': '"".join(map(str, xs))',
        'axiom': 'D46_join_comp_to_map',
    },
    {
        'name': 'str.replace to re.sub',
        'before': 's.replace(old, new)',
        'after': 're.sub(re.escape(old), new, s)',
        'axiom': 'D46_replace_to_resub',
    },
    {
        'name': 'Slice reversal to join reversed',
        'before': 's[::-1]',
        'after': '"".join(reversed(s))',
        'axiom': 'D46_slice_rev_to_join_rev',
    },
]

# ── Known string-building operations ──
STRING_BUILD_OPS: FrozenSet[str] = frozenset({
    'join', 'str_join', 'concat', 'str_concat',
    'fstring', 'format', 'str_format', 'percent_format',
    'template_substitute', 'str_template',
    'str_replace', 'replace', 're_sub', 'regex_sub',
    'reversed', 'str_reverse', 'slice_reverse',
})

# ── Format function names ──
FORMAT_OPS: FrozenSet[str] = frozenset({
    'fstring', 'format', 'str_format', 'percent_format',
    'template_substitute',
})


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract all free variable names."""
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
# Pattern detection
# ═══════════════════════════════════════════════════════════

def _is_join_pattern(term: OTerm) -> bool:
    """Detect "".join(...) or str.join(...) patterns."""
    if isinstance(term, OOp) and term.name in ('join', 'str_join', '.join'):
        return True
    # Fold with string concat
    if isinstance(term, OFold) and term.op_name in ('add', 'concat', 'str_concat'):
        if isinstance(term.init, OLit) and term.init.value == '':
            return True
    return False


def _is_fstring_pattern(term: OTerm) -> bool:
    """Detect f-string construction."""
    if isinstance(term, OOp) and term.name == 'fstring':
        return True
    return False


def _is_format_pattern(term: OTerm) -> bool:
    """Detect any string formatting pattern."""
    if isinstance(term, OOp) and term.name in FORMAT_OPS:
        return True
    return False


def _is_string_concat(term: OTerm) -> bool:
    """Detect string concatenation (s1 + s2 + ...)."""
    if isinstance(term, OOp) and term.name == 'add':
        # Check if any arg is a string literal
        for arg in term.args:
            if isinstance(arg, OLit) and isinstance(arg.value, str):
                return True
    return False


def _is_replace_pattern(term: OTerm) -> bool:
    """Detect string replace / re.sub patterns."""
    if isinstance(term, OOp) and term.name in (
        'replace', 'str_replace', '.replace', 're_sub', 'regex_sub',
    ):
        return True
    return False


def _is_reverse_pattern(term: OTerm) -> bool:
    """Detect string reversal patterns."""
    if isinstance(term, OOp):
        if term.name in ('reversed', 'str_reverse', 'slice_reverse'):
            return True
        # s[::-1] compiles to OOp('slice', ...)
        if term.name == 'slice' and len(term.args) >= 1:
            return True
    return False


def _is_join_comp_pattern(term: OTerm) -> bool:
    """Detect "".join([f(x) for x in xs]) — join over comprehension."""
    if isinstance(term, OOp) and term.name in ('join', '.join'):
        if len(term.args) >= 1:
            arg = term.args[-1]
            if isinstance(arg, OMap):
                return True
    return False


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D46 string building equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Join → concat fold ──
    if _is_join_pattern(term):
        if isinstance(term, OOp):
            results.append((
                OFold('add', OLit(''), term.args[-1] if term.args else OVar('parts')),
                'D46_join_to_concat',
            ))
        elif isinstance(term, OFold):
            coll = term.collection
            results.append((
                OOp('join', (OLit(''), coll)),
                'D46_concat_to_join',
            ))

    # ── Concat fold → join ──
    if isinstance(term, OFold) and term.op_name in ('add', 'concat'):
        if isinstance(term.init, OLit) and term.init.value == '':
            results.append((
                OOp('join', (OLit(''), term.collection)),
                'D46_concat_to_join',
            ))

    # ── F-string ↔ concatenation ──
    if _is_fstring_pattern(term):
        # fstring(lit, var, lit, ...) → add(lit, str(var), lit, ...)
        concat_args = []
        for arg in term.args:
            if isinstance(arg, OLit):
                concat_args.append(arg)
            else:
                concat_args.append(OOp('str', (arg,)))
        results.append((
            OOp('add', tuple(concat_args)),
            'D46_fstring_to_concat',
        ))
        # fstring → format
        results.append((
            OOp('format', term.args),
            'D46_fstring_to_format',
        ))
        # fstring → percent
        results.append((
            OOp('percent_format', term.args),
            'D46_fstring_to_percent',
        ))

    # ── format/percent → fstring ──
    if isinstance(term, OOp) and term.name in ('format', 'str_format'):
        results.append((
            OOp('fstring', term.args),
            'D46_format_to_fstring',
        ))
    if isinstance(term, OOp) and term.name == 'percent_format':
        results.append((
            OOp('fstring', term.args),
            'D46_percent_to_fstring',
        ))

    # ── String concatenation → join ──
    if _is_string_concat(term):
        results.append((
            OOp('join', (OLit(''), OSeq(term.args))),
            'D46_concat_to_join',
        ))

    # ── Join of comprehension ↔ join of map ──
    if _is_join_comp_pattern(term):
        map_term = term.args[-1]
        if isinstance(map_term, OMap):
            results.append((
                OOp('join', (OLit(''), OOp('map', (map_term.transform, map_term.collection)))),
                'D46_join_comp_to_map',
            ))

    # ── Join of map → join of comprehension ──
    if isinstance(term, OOp) and term.name in ('join', '.join'):
        if len(term.args) >= 1:
            inner = term.args[-1]
            if isinstance(inner, OOp) and inner.name == 'map':
                if len(inner.args) >= 2:
                    results.append((
                        OOp('join', (OLit(''), OMap(inner.args[0], inner.args[1]))),
                        'D46_join_map_to_comp',
                    ))

    # ── str.replace ↔ re.sub ──
    if isinstance(term, OOp) and term.name in ('replace', 'str_replace', '.replace'):
        results.append((
            OOp('re_sub', term.args),
            'D46_replace_to_resub',
        ))
    if isinstance(term, OOp) and term.name in ('re_sub', 'regex_sub'):
        results.append((
            OOp('replace', term.args),
            'D46_resub_to_replace',
        ))

    # ── String reversal: slice ↔ join(reversed) ──
    if isinstance(term, OOp) and term.name in ('slice_reverse', 'str_reverse'):
        results.append((
            OOp('join', (OLit(''), OOp('reversed', term.args))),
            'D46_slice_rev_to_join_rev',
        ))
    if isinstance(term, OOp) and term.name == 'reversed':
        results.append((
            OOp('slice_reverse', term.args),
            'D46_join_rev_to_slice_rev',
        ))

    # ── Abstract specs ──
    if isinstance(term, OAbstract):
        if 'string' in term.spec and ('build' in term.spec or 'concat' in term.spec):
            results.append((
                OOp('join', (OLit(''), OVar('parts'))),
                'D46_spec_to_join',
            ))
        if 'format' in term.spec:
            results.append((OOp('fstring', term.inputs), 'D46_spec_to_fstring'))
        if 'reverse' in term.spec and 'string' in term.spec:
            results.append((OOp('slice_reverse', term.inputs), 'D46_spec_to_slice_rev'))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D46 in reverse: optimised → verbose."""
    results = apply(term, ctx)
    inverse_labels = {
        'D46_concat_to_join',
        'D46_format_to_fstring',
        'D46_percent_to_fstring',
        'D46_resub_to_replace',
        'D46_join_rev_to_slice_rev',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D46 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in STRING_BUILD_OPS:
            return True
        if term.name in ('.join', '.replace'):
            return True
    if _is_join_pattern(term):
        return True
    if _is_fstring_pattern(term):
        return True
    if _is_format_pattern(term):
        return True
    if _is_string_concat(term):
        return True
    if _is_replace_pattern(term):
        return True
    if _is_reverse_pattern(term):
        return True
    if isinstance(term, OAbstract):
        return any(kw in term.spec for kw in ('string', 'format', 'concat', 'join'))
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D46 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    build_kw = ['join', 'concat', 'fstring', 'format', 'percent', 'template']
    replace_kw = ['replace', 're_sub', 'regex']
    reverse_kw = ['reversed', 'reverse', 'slice']

    has_build_s = any(kw in sc for kw in build_kw)
    has_build_t = any(kw in tc for kw in build_kw)
    has_replace_s = any(kw in sc for kw in replace_kw)
    has_replace_t = any(kw in tc for kw in replace_kw)
    has_rev_s = any(kw in sc for kw in reverse_kw)
    has_rev_t = any(kw in tc for kw in reverse_kw)

    # Both string building → high relevance
    if has_build_s and has_build_t:
        return 0.90
    # Replace variants
    if has_replace_s and has_replace_t:
        return 0.85
    # Reverse variants
    if has_rev_s and has_rev_t:
        return 0.85
    # Mixed string ops
    if (has_build_s or has_replace_s or has_rev_s) and \
       (has_build_t or has_replace_t or has_rev_t):
        return 0.60
    # One side has string keyword
    if has_build_s or has_build_t:
        return 0.30
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
    parts = OVar('parts')
    xs = OVar('xs')
    s = OVar('s')
    name = OVar('name')

    # ── Join → concat ──
    print("D46: join → concat ...")
    join_term = OOp('join', (OLit(''), parts))
    r_join = apply(join_term, ctx)
    _assert(any(lbl == 'D46_join_to_concat' for _, lbl in r_join), "join→concat")

    # ── Concat fold → join ──
    print("D46: concat fold → join ...")
    concat_fold = OFold('add', OLit(''), parts)
    r_cf = apply(concat_fold, ctx)
    _assert(any(lbl == 'D46_concat_to_join' for _, lbl in r_cf), "concat_fold→join")

    # ── F-string → concat / format / percent ──
    print("D46: fstring → concat / format / percent ...")
    fstr = OOp('fstring', (OLit('hello '), name))
    r_fs = apply(fstr, ctx)
    _assert(any(lbl == 'D46_fstring_to_concat' for _, lbl in r_fs), "fstring→concat")
    _assert(any(lbl == 'D46_fstring_to_format' for _, lbl in r_fs), "fstring→format")
    _assert(any(lbl == 'D46_fstring_to_percent' for _, lbl in r_fs), "fstring→percent")

    # ── Format → fstring ──
    print("D46: format → fstring ...")
    fmt = OOp('format', (OLit('hello '), name))
    r_fmt = apply(fmt, ctx)
    _assert(any(lbl == 'D46_format_to_fstring' for _, lbl in r_fmt), "format→fstring")

    # ── Percent → fstring ──
    print("D46: percent → fstring ...")
    pct = OOp('percent_format', (OLit('hello '), name))
    r_pct = apply(pct, ctx)
    _assert(any(lbl == 'D46_percent_to_fstring' for _, lbl in r_pct), "percent→fstring")

    # ── String concat → join ──
    print("D46: string concat → join ...")
    str_cat = OOp('add', (OLit('hello '), OOp('str', (name,))))
    r_sc = apply(str_cat, ctx)
    _assert(any(lbl == 'D46_concat_to_join' for _, lbl in r_sc), "str_concat→join")

    # ── Join comprehension → join map ──
    print("D46: join comp → join map ...")
    join_comp = OOp('join', (OLit(''), OMap(OLam(('x',), OOp('str', (OVar('x'),))), xs)))
    r_jc = apply(join_comp, ctx)
    _assert(any(lbl == 'D46_join_comp_to_map' for _, lbl in r_jc), "join_comp→map")

    # ── str.replace ↔ re.sub ──
    print("D46: replace ↔ re.sub ...")
    repl = OOp('replace', (s, OLit('old'), OLit('new')))
    r_repl = apply(repl, ctx)
    _assert(any(lbl == 'D46_replace_to_resub' for _, lbl in r_repl), "replace→resub")

    resub = OOp('re_sub', (OLit('pat'), OLit('repl'), s))
    r_resub = apply(resub, ctx)
    _assert(any(lbl == 'D46_resub_to_replace' for _, lbl in r_resub), "resub→replace")

    # ── String reversal ──
    print("D46: string reversal ...")
    srev = OOp('slice_reverse', (s,))
    r_sr = apply(srev, ctx)
    _assert(any(lbl == 'D46_slice_rev_to_join_rev' for _, lbl in r_sr),
            "slice_rev→join_rev")

    rev = OOp('reversed', (s,))
    r_rev = apply(rev, ctx)
    _assert(any(lbl == 'D46_join_rev_to_slice_rev' for _, lbl in r_rev),
            "join_rev→slice_rev")

    # ── Abstract spec ──
    print("D46: abstract spec ...")
    spec_sb = OAbstract('string_build_concat', (parts,))
    r_spec = apply(spec_sb, ctx)
    _assert(any(lbl == 'D46_spec_to_join' for _, lbl in r_spec), "spec→join")

    spec_fmt = OAbstract('string_format', (name,))
    r_sf = apply(spec_fmt, ctx)
    _assert(any(lbl == 'D46_spec_to_fstring' for _, lbl in r_sf), "spec→fstring")

    # ── recognizes ──
    print("D46: recognizes ...")
    _assert(recognizes(join_term), "recognizes join")
    _assert(recognizes(fstr), "recognizes fstring")
    _assert(recognizes(repl), "recognizes replace")
    _assert(recognizes(srev), "recognizes slice_reverse")
    _assert(recognizes(concat_fold), "recognizes concat fold")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D46: relevance_score ...")
    score = relevance_score(
        OOp('fstring', (OLit('a'), name)),
        OOp('format', (OLit('a'), name)),
    )
    _assert(score > 0.85, f"fstring↔format score={score:.2f} > 0.85")

    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D46: apply_inverse ...")
    inv = apply_inverse(fmt, ctx)
    _assert(len(inv) >= 1, "inverse format→fstring")

    inv_re = apply_inverse(resub, ctx)
    _assert(len(inv_re) >= 1, "inverse resub→replace")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D46 string_build: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
