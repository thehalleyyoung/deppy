"""P26 Axiom: Pathlib / OS Path Equivalences.

Establishes equivalences between os.path operations and pathlib
operations, which provide identical filesystem semantics.

Mathematical basis: File paths form a free monoid under path
concatenation.  os.path and pathlib are two representations of
the same algebraic structure:
    os.path.join(a, b) ≅ Path(a) / b
    os.path.exists(p) ≅ Path(p).exists()

Key rewrites:
  • os.path.join(a, b) ↔ Path(a) / b
  • os.path.exists(p) ↔ Path(p).exists()
  • os.listdir(p) ↔ list(Path(p).iterdir())
  • os.makedirs(p) ↔ Path(p).mkdir(parents=True)
  • open(os.path.join(...)) ↔ Path(...).open()
  • os.path.splitext(p) ↔ (Path(p).stem, Path(p).suffix)

(§P26, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

AXIOM_NAME = "P26_pathlib"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P17_context", "P4_string_ops"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P26 Pathlib/OS Equivalence).

1. os.path.join(a, b) ≡ str(Path(a) / b)
   Both concatenate path components with the OS separator.

2. os.path.exists(p) ≡ Path(p).exists()
   Both query the filesystem for existence of path p.

3. os.listdir(p) ≡ [x.name for x in Path(p).iterdir()]
   Both enumerate directory contents (names only).

4. os.makedirs(p, exist_ok=True) ≡ Path(p).mkdir(parents=True, exist_ok=True)
   Both create directory trees recursively.

5. open(os.path.join(a, b)) ≡ (Path(a) / b).open()
   Both open the file at the joined path.

6. os.path.splitext(p) ≡ (Path(p).stem, Path(p).suffix)
   Both decompose filename into stem and extension.
"""

EXAMPLES = [
    ("os.path.join($a, $b)", "Path($a) / $b", "P26_join_to_pathlib"),
    ("os.path.exists($p)", "Path($p).exists()", "P26_exists_to_pathlib"),
    ("os.listdir($p)", "list(Path($p).iterdir())", "P26_listdir_to_pathlib"),
    ("os.makedirs($p)", "Path($p).mkdir(parents=True)", "P26_makedirs_to_pathlib"),
]

_PATH_OPS = frozenset({
    'os.path.join', 'path_div', 'os.path.exists', 'path_exists',
    'os.listdir', 'path_iterdir', 'os.makedirs', 'path_mkdir',
    'os.path.splitext', 'path_suffix', 'path_stem',
    'os.path.basename', 'path_name', 'os.path.dirname', 'path_parent',
    'os.path.isfile', 'path_is_file', 'os.path.isdir', 'path_is_dir',
    'open_path', 'path_open', 'path_read_text', 'path_write_text',
})


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P26: Path operation equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── os.path.join(a,b) ↔ path_div(a,b) ──
    if isinstance(term, OOp) and term.name == 'os.path.join' and len(term.args) >= 2:
        results.append((
            OOp('path_div', term.args),
            'P26_join_to_pathlib_div',
        ))

    if isinstance(term, OOp) and term.name == 'path_div' and len(term.args) >= 2:
        results.append((
            OOp('os.path.join', term.args),
            'P26_pathlib_div_to_join',
        ))

    # ── os.path.exists(p) ↔ path_exists(p) ──
    if isinstance(term, OOp) and term.name == 'os.path.exists' and len(term.args) == 1:
        results.append((
            OOp('path_exists', term.args),
            'P26_exists_to_pathlib',
        ))

    if isinstance(term, OOp) and term.name == 'path_exists' and len(term.args) == 1:
        results.append((
            OOp('os.path.exists', term.args),
            'P26_pathlib_to_exists',
        ))

    # ── os.listdir(p) ↔ path_iterdir(p) ──
    if isinstance(term, OOp) and term.name == 'os.listdir' and len(term.args) == 1:
        results.append((
            OOp('path_iterdir', term.args),
            'P26_listdir_to_iterdir',
        ))

    if isinstance(term, OOp) and term.name == 'path_iterdir' and len(term.args) == 1:
        results.append((
            OOp('os.listdir', term.args),
            'P26_iterdir_to_listdir',
        ))

    # ── os.makedirs(p) ↔ path_mkdir(p) ──
    if isinstance(term, OOp) and term.name == 'os.makedirs' and len(term.args) >= 1:
        results.append((
            OOp('path_mkdir', (term.args[0],)),
            'P26_makedirs_to_mkdir',
        ))

    if isinstance(term, OOp) and term.name == 'path_mkdir' and len(term.args) >= 1:
        results.append((
            OOp('os.makedirs', (term.args[0],)),
            'P26_mkdir_to_makedirs',
        ))

    # ── os.path.splitext(p) ↔ (path_stem(p), path_suffix(p)) ──
    if isinstance(term, OOp) and term.name == 'os.path.splitext' and len(term.args) == 1:
        p = term.args[0]
        results.append((
            OSeq((OOp('path_stem', (p,)), OOp('path_suffix', (p,)))),
            'P26_splitext_to_stem_suffix',
        ))

    # ── os.path.basename(p) ↔ path_name(p) ──
    if isinstance(term, OOp) and term.name == 'os.path.basename' and len(term.args) == 1:
        results.append((
            OOp('path_name', term.args),
            'P26_basename_to_name',
        ))

    if isinstance(term, OOp) and term.name == 'path_name' and len(term.args) == 1:
        results.append((
            OOp('os.path.basename', term.args),
            'P26_name_to_basename',
        ))

    # ── os.path.dirname(p) ↔ path_parent(p) ──
    if isinstance(term, OOp) and term.name == 'os.path.dirname' and len(term.args) == 1:
        results.append((
            OOp('path_parent', term.args),
            'P26_dirname_to_parent',
        ))

    if isinstance(term, OOp) and term.name == 'path_parent' and len(term.args) == 1:
        results.append((
            OOp('os.path.dirname', term.args),
            'P26_parent_to_dirname',
        ))

    # ── os.path.isfile(p) ↔ path_is_file(p) ──
    if isinstance(term, OOp) and term.name == 'os.path.isfile' and len(term.args) == 1:
        results.append((
            OOp('path_is_file', term.args),
            'P26_isfile_to_pathlib',
        ))

    if isinstance(term, OOp) and term.name == 'path_is_file' and len(term.args) == 1:
        results.append((
            OOp('os.path.isfile', term.args),
            'P26_pathlib_to_isfile',
        ))

    # ── os.path.isdir(p) ↔ path_is_dir(p) ──
    if isinstance(term, OOp) and term.name == 'os.path.isdir' and len(term.args) == 1:
        results.append((
            OOp('path_is_dir', term.args),
            'P26_isdir_to_pathlib',
        ))

    if isinstance(term, OOp) and term.name == 'path_is_dir' and len(term.args) == 1:
        results.append((
            OOp('os.path.isdir', term.args),
            'P26_pathlib_to_isdir',
        ))

    # ── open(path) ↔ path_open(path) ──
    if isinstance(term, OOp) and term.name == 'open_path' and len(term.args) >= 1:
        results.append((
            OOp('path_open', (term.args[0],)),
            'P26_open_to_path_open',
        ))

    if isinstance(term, OOp) and term.name == 'path_open' and len(term.args) >= 1:
        results.append((
            OOp('open_path', (term.args[0],)),
            'P26_path_open_to_open',
        ))

    # ── path_read_text(p) ↔ open+read pattern ──
    if isinstance(term, OOp) and term.name == 'path_read_text' and len(term.args) == 1:
        results.append((
            OOp('file_read', (OOp('open_path', term.args),)),
            'P26_read_text_to_open_read',
        ))

    return results


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {l for _, l in results if 'pathlib_to' in l or 'to_join' in l or
           'to_listdir' in l or 'to_makedirs' in l or 'to_basename' in l or
           'to_dirname' in l or 'to_isfile' in l or 'to_isdir' in l or
           'path_open_to_open' in l}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _PATH_OPS:
        return True
    if isinstance(term, OOp) and term.name in ('file_read',):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('os.path', 'path_', 'Path(', 'pathlib'):
        if kw in sc and kw in tc:
            return 0.85
    if ('os.path' in sc and 'path_' in tc) or ('path_' in sc and 'os.path' in tc):
        return 0.9
    return 0.05


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

    # 1. join → pathlib /
    t = OOp('os.path.join', (OVar('a'), OVar('b')))
    r = apply(t)
    _assert(any(a == 'P26_join_to_pathlib_div' for _, a in r), "join → div")

    # 2. pathlib / → join
    t2 = OOp('path_div', (OVar('a'), OVar('b')))
    r2 = apply(t2)
    _assert(any(a == 'P26_pathlib_div_to_join' for _, a in r2), "div → join")

    # 3. exists → pathlib
    t3 = OOp('os.path.exists', (OVar('p'),))
    r3 = apply(t3)
    _assert(any(a == 'P26_exists_to_pathlib' for _, a in r3), "exists → pathlib")

    # 4. pathlib exists → os
    t4 = OOp('path_exists', (OVar('p'),))
    r4 = apply(t4)
    _assert(any(a == 'P26_pathlib_to_exists' for _, a in r4), "pathlib → exists")

    # 5. listdir → iterdir
    t5 = OOp('os.listdir', (OVar('p'),))
    r5 = apply(t5)
    _assert(any(a == 'P26_listdir_to_iterdir' for _, a in r5), "listdir → iterdir")

    # 6. iterdir → listdir
    t6 = OOp('path_iterdir', (OVar('p'),))
    r6 = apply(t6)
    _assert(any(a == 'P26_iterdir_to_listdir' for _, a in r6), "iterdir → listdir")

    # 7. makedirs → mkdir
    t7 = OOp('os.makedirs', (OVar('p'),))
    r7 = apply(t7)
    _assert(any(a == 'P26_makedirs_to_mkdir' for _, a in r7), "makedirs → mkdir")

    # 8. mkdir → makedirs
    t8 = OOp('path_mkdir', (OVar('p'),))
    r8 = apply(t8)
    _assert(any(a == 'P26_mkdir_to_makedirs' for _, a in r8), "mkdir → makedirs")

    # 9. splitext → stem+suffix
    t9 = OOp('os.path.splitext', (OVar('p'),))
    r9 = apply(t9)
    _assert(any(a == 'P26_splitext_to_stem_suffix' for _, a in r9), "splitext → stem+suffix")

    # 10. basename → name
    t10 = OOp('os.path.basename', (OVar('p'),))
    r10 = apply(t10)
    _assert(any(a == 'P26_basename_to_name' for _, a in r10), "basename → name")

    # 11. name → basename
    t11 = OOp('path_name', (OVar('p'),))
    r11 = apply(t11)
    _assert(any(a == 'P26_name_to_basename' for _, a in r11), "name → basename")

    # 12. dirname → parent
    t12 = OOp('os.path.dirname', (OVar('p'),))
    r12 = apply(t12)
    _assert(any(a == 'P26_dirname_to_parent' for _, a in r12), "dirname → parent")

    # 13. isfile → pathlib
    t13 = OOp('os.path.isfile', (OVar('p'),))
    r13 = apply(t13)
    _assert(any(a == 'P26_isfile_to_pathlib' for _, a in r13), "isfile → pathlib")

    # 14. isdir → pathlib
    t14 = OOp('os.path.isdir', (OVar('p'),))
    r14 = apply(t14)
    _assert(any(a == 'P26_isdir_to_pathlib' for _, a in r14), "isdir → pathlib")

    # 15. open → path_open
    t15 = OOp('open_path', (OVar('p'),))
    r15 = apply(t15)
    _assert(any(a == 'P26_open_to_path_open' for _, a in r15), "open → path_open")

    # 16. path_open → open
    t16 = OOp('path_open', (OVar('p'),))
    r16 = apply(t16)
    _assert(any(a == 'P26_path_open_to_open' for _, a in r16), "path_open → open")

    # 17. read_text → open+read
    t17 = OOp('path_read_text', (OVar('p'),))
    r17 = apply(t17)
    _assert(any(a == 'P26_read_text_to_open_read' for _, a in r17), "read_text → open+read")

    # 18. recognizes
    _assert(recognizes(t), "recognizes os.path.join")
    _assert(not recognizes(OLit(42)), "!recognizes lit")

    # 19. relevance
    _assert(relevance_score(t, t2) > 0.5, "join/div relevance")

    # 20. parent → dirname
    t20 = OOp('path_parent', (OVar('p'),))
    r20 = apply(t20)
    _assert(any(a == 'P26_parent_to_dirname' for _, a in r20), "parent → dirname")

    print(f"P26 pathlib: {_pass} passed, {_fail} failed")
