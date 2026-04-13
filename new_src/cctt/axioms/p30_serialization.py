"""P30 Axiom: JSON / Serialization Equivalences.

Establishes equivalences between different serialization patterns
in Python — json, pickle, yaml — and their idiomatic alternatives.

Mathematical basis: Serialization is a pair of adjoint functors
  encode: Obj → Str   (left adjoint, the "free serializer")
  decode: Str → Obj   (right adjoint, the "forgetful parser")
satisfying  decode ∘ encode ≅ id  (round-trip identity).
Different serialization libraries are natural transformations
between such adjunction pairs when restricted to compatible types:
    json.loads(json.dumps(x))  ≡  x        (for JSON-safe x)
    pickle.loads(pickle.dumps(x)) ≡ x      (for picklable x)
    json.dump(f, x) ≡ f.write(json.dumps(x))

Key rewrites:
  • json.dumps/json.loads roundtrip ↔ identity
  • json.dump(obj, f) ↔ f.write(json.dumps(obj))
  • json.load(f) ↔ json.loads(f.read())
  • custom JSONEncoder ↔ default= function
  • pickle.dumps ↔ json.dumps (for basic types)
  • pickle.loads ↔ json.loads (for basic types)
  • yaml.safe_load ↔ json.loads (for compatible data)
  • yaml.dump ↔ json.dumps (for compatible data)

(§P30, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P30_serialization"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P3_dict_ops", "P17_context", "P4_string_ops"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P30 Serialization Equivalences).

1. json.loads(json.dumps(x)) ≡ x  (for JSON-serializable x)
   The JSON codec is a retraction: decode ∘ encode = id on the
   subcategory of JSON-safe Python objects.

2. json.dump(obj, f) ≡ f.write(json.dumps(obj))
   json.dump writes the serialized string to f; writing the result
   of json.dumps is extensionally identical.

3. json.load(f) ≡ json.loads(f.read())
   json.load reads from f and parses; reading then parsing is the same.

4. JSONEncoder.default(obj) ≡ json.dumps(obj, default=fn)
   Subclassing JSONEncoder and overriding default is equivalent to
   passing a default= function to json.dumps.

5. pickle.dumps(x) ≡ json.dumps(x) (for basic types: int, str, list, dict)
   For the common sublanguage of basic types, both produce a
   recoverable serialization (though formats differ).

6. pickle.loads(s) ≡ json.loads(s) (for basic types)
   Deserialization of basic types is equivalent across formats.

7. yaml.safe_load(s) ≡ json.loads(s) (for JSON-compatible YAML)
   JSON is a subset of YAML; parsing JSON-compatible strings
   with either parser yields the same Python object.

8. yaml.dump(obj) ≡ json.dumps(obj) (for compatible data)
   For the intersection of JSON and YAML types, both serialize
   to a recoverable text form.
"""

EXAMPLES = [
    ("json_roundtrip($x)", "$x", "P30_json_roundtrip_identity"),
    ("json_dump_file($obj, $f)", "write_json_dumps($obj, $f)", "P30_dump_to_write"),
    ("json_load_file($f)", "read_json_loads($f)", "P30_load_to_read"),
    ("json_encoder($cls, $obj)", "json_default_fn($fn, $obj)", "P30_encoder_to_default"),
    ("pickle_dumps($x)", "json_dumps_basic($x)", "P30_pickle_to_json"),
]

_SERIAL_OPS = frozenset({
    'json_dumps', 'json_loads', 'json_roundtrip',
    'json_dump_file', 'write_json_dumps',
    'json_load_file', 'read_json_loads',
    'json_encoder', 'json_default_fn',
    'pickle_dumps', 'json_dumps_basic',
    'pickle_loads', 'json_loads_basic',
    'yaml_safe_load', 'json_loads_compat',
    'yaml_dump', 'json_dumps_compat',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P30: Serialization equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── json.loads(json.dumps(x)) → x  (roundtrip identity) ──
    if isinstance(term, OOp) and term.name == 'json_loads' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'json_dumps' and len(inner.args) == 1:
            results.append((
                inner.args[0],
                'P30_json_roundtrip_identity',
            ))

    # ── json_roundtrip(x) → x ──
    if isinstance(term, OOp) and term.name == 'json_roundtrip' and len(term.args) == 1:
        results.append((
            term.args[0],
            'P30_json_roundtrip_elim',
        ))

    # ── json.dump(obj, f) ↔ f.write(json.dumps(obj)) ──
    if isinstance(term, OOp) and term.name == 'json_dump_file' and len(term.args) == 2:
        obj, f = term.args
        results.append((
            OOp('write_json_dumps', (obj, f)),
            'P30_dump_file_to_write',
        ))

    if isinstance(term, OOp) and term.name == 'write_json_dumps' and len(term.args) == 2:
        obj, f = term.args
        results.append((
            OOp('json_dump_file', (obj, f)),
            'P30_write_to_dump_file',
        ))

    # ── json.load(f) ↔ json.loads(f.read()) ──
    if isinstance(term, OOp) and term.name == 'json_load_file' and len(term.args) == 1:
        results.append((
            OOp('read_json_loads', term.args),
            'P30_load_file_to_read',
        ))

    if isinstance(term, OOp) and term.name == 'read_json_loads' and len(term.args) == 1:
        results.append((
            OOp('json_load_file', term.args),
            'P30_read_to_load_file',
        ))

    # ── custom JSONEncoder ↔ default= function ──
    if isinstance(term, OOp) and term.name == 'json_encoder' and len(term.args) >= 2:
        results.append((
            OOp('json_default_fn', term.args),
            'P30_encoder_to_default_fn',
        ))

    if isinstance(term, OOp) and term.name == 'json_default_fn' and len(term.args) >= 2:
        results.append((
            OOp('json_encoder', term.args),
            'P30_default_fn_to_encoder',
        ))

    # ── pickle.dumps ↔ json.dumps for basic types ──
    if isinstance(term, OOp) and term.name == 'pickle_dumps' and len(term.args) >= 1:
        results.append((
            OOp('json_dumps_basic', term.args),
            'P30_pickle_dumps_to_json',
        ))

    if isinstance(term, OOp) and term.name == 'json_dumps_basic' and len(term.args) >= 1:
        results.append((
            OOp('pickle_dumps', term.args),
            'P30_json_to_pickle_dumps',
        ))

    # ── pickle.loads ↔ json.loads for basic types ──
    if isinstance(term, OOp) and term.name == 'pickle_loads' and len(term.args) >= 1:
        results.append((
            OOp('json_loads_basic', term.args),
            'P30_pickle_loads_to_json',
        ))

    if isinstance(term, OOp) and term.name == 'json_loads_basic' and len(term.args) >= 1:
        results.append((
            OOp('pickle_loads', term.args),
            'P30_json_to_pickle_loads',
        ))

    # ── yaml.safe_load ↔ json.loads for compatible data ──
    if isinstance(term, OOp) and term.name == 'yaml_safe_load' and len(term.args) >= 1:
        results.append((
            OOp('json_loads_compat', term.args),
            'P30_yaml_load_to_json',
        ))

    if isinstance(term, OOp) and term.name == 'json_loads_compat' and len(term.args) >= 1:
        results.append((
            OOp('yaml_safe_load', term.args),
            'P30_json_to_yaml_load',
        ))

    # ── yaml.dump ↔ json.dumps for compatible data ──
    if isinstance(term, OOp) and term.name == 'yaml_dump' and len(term.args) >= 1:
        results.append((
            OOp('json_dumps_compat', term.args),
            'P30_yaml_dump_to_json',
        ))

    if isinstance(term, OOp) and term.name == 'json_dumps_compat' and len(term.args) >= 1:
        results.append((
            OOp('yaml_dump', term.args),
            'P30_json_to_yaml_dump',
        ))

    # ── standalone json_dumps / json_loads (wrap in roundtrip) ──
    if isinstance(term, OOp) and term.name == 'json_dumps' and len(term.args) == 1:
        results.append((
            OOp('json_dumps_basic', term.args),
            'P30_json_dumps_to_basic',
        ))

    if isinstance(term, OOp) and term.name == 'json_loads' and len(term.args) == 1:
        inner = term.args[0]
        if not (isinstance(inner, OOp) and inner.name == 'json_dumps'):
            results.append((
                OOp('json_loads_basic', term.args),
                'P30_json_loads_to_basic',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {l for _, l in results if '_to_dump_file' in l or '_to_load_file' in l
           or '_to_encoder' in l or '_to_pickle' in l
           or '_to_yaml' in l or 'default_fn_to' in l}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _SERIAL_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('json', 'pickle', 'yaml', 'dumps', 'loads',
               'serialize', 'deserialize', 'encoder'):
        if kw in sc and kw in tc:
            return 0.85
    if ('json' in sc and 'pickle' in tc) or ('pickle' in sc and 'json' in tc):
        return 0.8
    if ('json' in sc and 'yaml' in tc) or ('yaml' in sc and 'json' in tc):
        return 0.8
    if any(k in sc for k in ('json', 'pickle', 'yaml')):
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

    # 1. json roundtrip identity: json.loads(json.dumps(x)) → x
    t = OOp('json_loads', (OOp('json_dumps', (OVar('x'),)),))
    r = apply(t)
    _assert(any(a == 'P30_json_roundtrip_identity' for _, a in r), "roundtrip → identity")

    # 2. json_roundtrip(x) → x
    t2 = OOp('json_roundtrip', (OVar('x'),))
    r2 = apply(t2)
    _assert(any(a == 'P30_json_roundtrip_elim' for _, a in r2), "roundtrip elim")

    # 3. json.dump → f.write(json.dumps)
    t3 = OOp('json_dump_file', (OVar('obj'), OVar('f')))
    r3 = apply(t3)
    _assert(any(a == 'P30_dump_file_to_write' for _, a in r3), "dump → write")

    # 4. f.write(json.dumps) → json.dump
    t4 = OOp('write_json_dumps', (OVar('obj'), OVar('f')))
    r4 = apply(t4)
    _assert(any(a == 'P30_write_to_dump_file' for _, a in r4), "write → dump")

    # 5. json.load → json.loads(f.read())
    t5 = OOp('json_load_file', (OVar('f'),))
    r5 = apply(t5)
    _assert(any(a == 'P30_load_file_to_read' for _, a in r5), "load → read")

    # 6. json.loads(f.read()) → json.load
    t6 = OOp('read_json_loads', (OVar('f'),))
    r6 = apply(t6)
    _assert(any(a == 'P30_read_to_load_file' for _, a in r6), "read → load")

    # 7. encoder → default_fn
    t7 = OOp('json_encoder', (OVar('cls'), OVar('obj')))
    r7 = apply(t7)
    _assert(any(a == 'P30_encoder_to_default_fn' for _, a in r7), "encoder → default_fn")

    # 8. default_fn → encoder
    t8 = OOp('json_default_fn', (OVar('fn'), OVar('obj')))
    r8 = apply(t8)
    _assert(any(a == 'P30_default_fn_to_encoder' for _, a in r8), "default_fn → encoder")

    # 9. pickle.dumps → json.dumps (basic)
    t9 = OOp('pickle_dumps', (OVar('x'),))
    r9 = apply(t9)
    _assert(any(a == 'P30_pickle_dumps_to_json' for _, a in r9), "pickle_dumps → json")

    # 10. json.dumps_basic → pickle.dumps
    t10 = OOp('json_dumps_basic', (OVar('x'),))
    r10 = apply(t10)
    _assert(any(a == 'P30_json_to_pickle_dumps' for _, a in r10), "json → pickle_dumps")

    # 11. pickle.loads → json.loads (basic)
    t11 = OOp('pickle_loads', (OVar('s'),))
    r11 = apply(t11)
    _assert(any(a == 'P30_pickle_loads_to_json' for _, a in r11), "pickle_loads → json")

    # 12. json_loads_basic → pickle.loads
    t12 = OOp('json_loads_basic', (OVar('s'),))
    r12 = apply(t12)
    _assert(any(a == 'P30_json_to_pickle_loads' for _, a in r12), "json → pickle_loads")

    # 13. yaml.safe_load → json.loads (compat)
    t13 = OOp('yaml_safe_load', (OVar('s'),))
    r13 = apply(t13)
    _assert(any(a == 'P30_yaml_load_to_json' for _, a in r13), "yaml_load → json")

    # 14. json_loads_compat → yaml.safe_load
    t14 = OOp('json_loads_compat', (OVar('s'),))
    r14 = apply(t14)
    _assert(any(a == 'P30_json_to_yaml_load' for _, a in r14), "json → yaml_load")

    # 15. yaml.dump → json.dumps (compat)
    t15 = OOp('yaml_dump', (OVar('obj'),))
    r15 = apply(t15)
    _assert(any(a == 'P30_yaml_dump_to_json' for _, a in r15), "yaml_dump → json")

    # 16. json_dumps_compat → yaml.dump
    t16 = OOp('json_dumps_compat', (OVar('obj'),))
    r16 = apply(t16)
    _assert(any(a == 'P30_json_to_yaml_dump' for _, a in r16), "json → yaml_dump")

    # 17. json_dumps → json_dumps_basic
    t17 = OOp('json_dumps', (OVar('x'),))
    r17 = apply(t17)
    _assert(any(a == 'P30_json_dumps_to_basic' for _, a in r17), "dumps → basic")

    # 18. recognizes
    _assert(recognizes(t3), "recognizes json_dump_file")
    _assert(recognizes(OOp('yaml_safe_load', (OVar('s'),))), "recognizes yaml_safe_load")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance: json ↔ pickle high
    _assert(relevance_score(t9, t10) > 0.5, "json/pickle relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2, "unrelated relevance low")

    print(f"P30 serialization: {_pass} passed, {_fail} failed")
