"""Python type annotation → Lean 4 type translation.

Used by both the obligation emitter and the pipeline's Lean-proof
discharge to turn the formal-parameter annotations of a Python
function into Lean binder types.

Coverage
--------

* Built-in scalar types — ``int``, ``float``, ``str``, ``bool``,
  ``bytes``, ``None``.
* Generic containers — ``list[T]``, ``dict[K, V]``, ``tuple[T, ...]``,
  ``set[T]``, ``frozenset[T]``.
* ``Optional[T]`` / ``T | None`` — ``Option <T>``.
* ``Union[A, B, ...]`` / ``A | B | ...`` — Lean ``Sum`` for two-element
  unions, an opaque ``axiom Deppy_Union_<hash> : Type`` for larger
  unions.
* ``Any`` — Lean's ``α`` polymorphic placeholder (or a fresh opaque
  type when α isn't bindable).
* ``Callable[[A, B], R]`` — Lean's arrow ``A → B → R``.  ``Callable``
  with an ellipsis or unspecified signature becomes ``α → β``.
* ``Literal[...]`` — the underlying scalar type plus a TODO note.
* User-defined classes — opaque ``axiom <ClassName> : Type`` so the
  user can refine in their .lean file.

Public API::

    TypeTranslation = NamedTuple(lean: str, aux_decls: list, notes: list)
    translate_annotation(ann_node, *, known_classes=()) -> TypeTranslation
    translate_annotation_str(text, *, known_classes=()) -> TypeTranslation
"""
from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, field
from typing import Iterable, NamedTuple, Optional


@dataclass
class TypeTranslation:
    """Result of translating a single annotation.

    ``aux_decls`` carries any deterministically-named ``axiom``
    declarations the file should emit so the translation type-checks
    in Lean.  Same predicate text → same axiom name across runs.
    """
    lean: str
    aux_decls: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
#  Scalar / built-in mapping
# ─────────────────────────────────────────────────────────────────────

_SCALAR_TABLE: dict[str, str] = {
    "int": "Int",
    "float": "Float",
    "str": "String",
    "bool": "Bool",
    "bytes": "ByteArray",
    "bytearray": "ByteArray",
    "None": "Unit",
    "NoneType": "Unit",
    "object": "α",          # totally opaque
    "Any": "α",             # universe-polymorphic placeholder
}


# ─────────────────────────────────────────────────────────────────────
#  Public entry points
# ─────────────────────────────────────────────────────────────────────

def translate_annotation(
    node: Optional[ast.expr],
    *,
    known_classes: Iterable[str] = (),
) -> TypeTranslation:
    """Translate an AST annotation node to a Lean 4 type.

    ``None`` (no annotation) defaults to ``Int`` — the most common
    runtime-safety case.  ``known_classes`` lets the caller declare
    user-defined class names so the translator emits opaque
    ``axiom <ClassName> : Type`` once for each (rather than per
    occurrence).
    """
    aux_decls: list[str] = []
    notes: list[str] = []
    known = set(known_classes)
    text = _translate(node, aux_decls, notes, known)
    return TypeTranslation(lean=text, aux_decls=aux_decls, notes=notes)


def translate_annotation_str(
    text: str,
    *,
    known_classes: Iterable[str] = (),
) -> TypeTranslation:
    """Translate a free-form annotation string (parsed as an AST)."""
    text = (text or "").strip()
    if not text:
        return TypeTranslation(lean="Int")
    try:
        node = ast.parse(text, mode="eval").body
    except SyntaxError:
        # Unparseable — emit opaque type referencing the original.
        aux: list[str] = []
        nm = _opaque_class(text, aux)
        return TypeTranslation(
            lean=nm, aux_decls=aux,
            notes=[f"unparseable annotation {text!r}"],
        )
    return translate_annotation(node, known_classes=known_classes)


# ─────────────────────────────────────────────────────────────────────
#  Internal recursive translator
# ─────────────────────────────────────────────────────────────────────

def _translate(
    node: Optional[ast.expr],
    aux: list[str],
    notes: list[str],
    known: set[str],
) -> str:
    if node is None:
        return "Int"

    # ``None`` literal in an annotation — e.g. ``int | None``.
    if isinstance(node, ast.Constant):
        if node.value is None:
            return "Unit"
        if isinstance(node.value, str):
            # Forward-reference annotation as a string literal.
            try:
                inner = ast.parse(node.value, mode="eval").body
                return _translate(inner, aux, notes, known)
            except SyntaxError:
                notes.append(f"unparseable forward ref: {node.value!r}")
                return _opaque_class(node.value, aux)
        notes.append(f"unsupported annotation literal {node.value!r}")
        return "Int"

    # Plain Name — int, str, list, custom class, …
    if isinstance(node, ast.Name):
        if node.id in _SCALAR_TABLE:
            return _SCALAR_TABLE[node.id]
        # Bare "list" / "dict" / "tuple" / "set" with no parameter.
        bare_table = {
            "list": "List Int",
            "dict": "Std.HashMap String Int",
            "tuple": "List Int",
            "set": "List Int",
            "frozenset": "List Int",
            "Callable": "α → β",
        }
        if node.id in bare_table:
            return bare_table[node.id]
        # User-defined class — opaque.
        if node.id in known or node.id[:1].isupper():
            return _opaque_class(node.id, aux)
        notes.append(f"unknown bare type {node.id}")
        return _opaque_class(node.id, aux)

    # Attribute access — e.g. ``typing.Optional`` / ``typing.Union``.
    if isinstance(node, ast.Attribute):
        # Render the full path then re-translate as a Name.
        try:
            text = ast.unparse(node)
        except Exception:
            text = node.attr
        return _translate_named(text, aux, notes, known)

    # Subscript — generics: list[T], Optional[T], Union[A, B], …
    if isinstance(node, ast.Subscript):
        base = _name_of(node.value)
        slc = node.slice
        if base in ("Optional", "typing.Optional"):
            inner = _translate(slc, aux, notes, known)
            return f"(Option {inner})"
        if base in ("Union", "typing.Union"):
            return _translate_union(slc, aux, notes, known)
        if base in ("List", "list", "typing.List", "Sequence", "Iterable",
                    "MutableSequence", "Collection"):
            inner = _translate(slc, aux, notes, known)
            return f"(List {inner})"
        if base in ("Dict", "dict", "typing.Dict",
                    "Mapping", "MutableMapping"):
            if isinstance(slc, ast.Tuple) and len(slc.elts) == 2:
                k = _translate(slc.elts[0], aux, notes, known)
                v = _translate(slc.elts[1], aux, notes, known)
                return f"(Std.HashMap {k} {v})"
            return "(Std.HashMap String Int)"
        if base in ("Tuple", "tuple", "typing.Tuple"):
            if isinstance(slc, ast.Tuple):
                parts = [
                    _translate(e, aux, notes, known) for e in slc.elts
                ]
                return "(" + " × ".join(parts) + ")"
            inner = _translate(slc, aux, notes, known)
            return f"(List {inner})"
        if base in ("Set", "set", "typing.Set",
                    "FrozenSet", "frozenset", "typing.FrozenSet"):
            inner = _translate(slc, aux, notes, known)
            return f"(List {inner})"
        if base in ("Callable", "typing.Callable"):
            return _translate_callable(slc, aux, notes, known)
        if base in ("Literal", "typing.Literal"):
            # The underlying scalar type, with a note.
            notes.append(
                f"Literal[{ast.unparse(slc) if hasattr(slc, '__class__') else slc}]"
                " translated as its scalar base"
            )
            if isinstance(slc, ast.Constant):
                v = slc.value
                if isinstance(v, bool):
                    return "Bool"
                if isinstance(v, int):
                    return "Int"
                if isinstance(v, float):
                    return "Float"
                if isinstance(v, str):
                    return "String"
            return "Int"
        # Unknown generic — opaque on the base.
        notes.append(f"unknown generic {base}[...]")
        return _opaque_class(_safe_text(node), aux)

    # X | Y syntax (PEP 604).
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return _translate_union_pair(node.left, node.right, aux, notes, known)

    notes.append(f"unsupported annotation form {type(node).__name__}")
    return _opaque_class(_safe_text(node), aux)


def _translate_named(
    text: str, aux: list[str], notes: list[str], known: set[str],
) -> str:
    if text in _SCALAR_TABLE:
        return _SCALAR_TABLE[text]
    if text == "typing.Any":
        return "α"
    if text == "typing.Callable":
        return "α → β"
    return _opaque_class(text, aux)


def _translate_union(
    slc, aux: list[str], notes: list[str], known: set[str],
) -> str:
    # Union[A, B, ...] — slice may be a Tuple or a single element.
    elts: list[ast.expr]
    if isinstance(slc, ast.Tuple):
        elts = list(slc.elts)
    else:
        elts = [slc]
    return _build_union(elts, aux, notes, known)


def _translate_union_pair(
    left: ast.expr, right: ast.expr,
    aux: list[str], notes: list[str], known: set[str],
) -> str:
    # Flatten chained unions: A | B | C → [A, B, C].
    elts: list[ast.expr] = []
    def collect(node: ast.expr) -> None:
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            collect(node.left)
            collect(node.right)
        else:
            elts.append(node)
    collect(left)
    collect(right)
    return _build_union(elts, aux, notes, known)


def _build_union(
    elts: list[ast.expr], aux: list[str], notes: list[str], known: set[str],
) -> str:
    # Detect Optional[T] (T | None) and use Lean Option.
    nones = [
        e for e in elts
        if isinstance(e, ast.Constant) and e.value is None
    ]
    non_none = [e for e in elts if e not in nones]
    if nones:
        if len(non_none) == 1:
            inner = _translate(non_none[0], aux, notes, known)
            return f"(Option {inner})"
        # Optional[Union[A, B]] — fall through to opaque union below.
        notes.append("Optional of Union — emitting opaque union type")
    if len(non_none) == 0:
        return "Unit"
    if len(non_none) == 1:
        return _translate(non_none[0], aux, notes, known)
    if len(non_none) == 2:
        a = _translate(non_none[0], aux, notes, known)
        b = _translate(non_none[1], aux, notes, known)
        return f"(Sum {a} {b})"
    # 3+ alternatives — opaque named axiom (deterministic).
    label = " | ".join(_safe_text(e) for e in non_none)
    notes.append(
        f"union of >2 alternatives ({label}) — emitting opaque type"
    )
    return _opaque_class(f"Union[{label}]", aux)


def _translate_callable(
    slc, aux: list[str], notes: list[str], known: set[str],
) -> str:
    # Callable[[A, B], R]  — slice is Tuple([List([A, B]), R]).
    if isinstance(slc, ast.Tuple) and len(slc.elts) == 2:
        params_node, ret_node = slc.elts
        if isinstance(params_node, ast.List):
            params = [
                _translate(p, aux, notes, known) for p in params_node.elts
            ]
            ret = _translate(ret_node, aux, notes, known)
            if not params:
                return f"(Unit → {ret})"
            return "(" + " → ".join(params + [ret]) + ")"
        if (isinstance(params_node, ast.Constant)
                and params_node.value is Ellipsis):
            ret = _translate(ret_node, aux, notes, known)
            notes.append(
                "Callable[..., R] — params unspecified; emitted as α → R"
            )
            return f"(α → {ret})"
    notes.append("Callable with unrecognised parameter form")
    return "(α → β)"


def _opaque_class(name: str, aux: list[str]) -> str:
    """Emit ``axiom <Name> : Type`` and return the name.

    The ``name`` is sanitised to a Lean identifier; long or
    Python-like names are abbreviated and hashed for determinism.
    """
    safe = _sanitize_ident(name)
    decl = f"axiom {safe} : Type"
    if decl not in aux:
        aux.append(decl)
    return safe


def _sanitize_ident(text: str) -> str:
    """Map a free-form Python type name to a Lean identifier."""
    raw = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in text)
    raw = raw.strip("_")
    if not raw:
        raw = "T"
    if not raw[0].isalpha() and raw[0] != "_":
        raw = "T_" + raw
    if len(raw) > 32:
        digest = hashlib.sha1(text.encode("utf-8")).hexdigest()[:8]
        raw = raw[:24] + "_" + digest
    return f"Deppy_{raw}" if not raw.startswith("Deppy_") else raw


def _name_of(node: ast.expr) -> str:
    """Best-effort dotted-name string for ``Name`` / ``Attribute``."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _name_of(node.value) + "." + node.attr
    return ""


def _safe_text(node) -> str:
    try:
        return ast.unparse(node)
    except Exception:
        return ast.dump(node) if hasattr(node, "_fields") else str(node)


__all__ = [
    "TypeTranslation",
    "translate_annotation",
    "translate_annotation_str",
]
