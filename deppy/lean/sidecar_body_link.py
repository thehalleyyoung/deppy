"""Connect each ``.deppy`` axiom to the actual library source via
deppy's own proof architecture.

This is the bridge from a sidecar specification to the real Python
implementation it claims to characterise.  For each axiom:

  1. Resolve every ``Class.method`` referenced in the axiom's
     statement (via ``importlib`` + ``getattr``).
  2. ``inspect.getsource`` the resolved method.
  3. Parse the source into an :class:`ast.FunctionDef`.
  4. Run :func:`deppy.lean.body_translation.translate_body` — the
     deppy body translator.  This is where the connection lives:
     deppy's own infrastructure consumes the source and produces a
     Lean term.  No external symbolic engine is used.
  5. Record the translation outcome:
       * ``lean_text`` — the translated body (may contain ``sorry``).
       * ``exact`` — did the translator handle the whole body?
       * ``sorry_count`` / ``notes`` — explicit limits the translator
         encountered.
       * ``source_hash`` — SHA-256 over the actual source bytes,
         committing the certificate to *this exact code*.

The certificate emits, for every linked method:

    -- Source: <module>.<Class>.<method>
    -- Source-hash: <sha256>           (commits the certificate to
    --                                  this exact byte sequence)
    -- deppy body-translator status: <exact | sorry_count=N: notes>
    def <Class>_<method> ( ... ) : Int := <translated body>

When the translator returns ``sorry``, the def still exists — the
axiom just can't yet be discharged against it.  When the translator
returns a real expression, the axiom's Lean Prop is *concretely*
about that body and the proof can use ``decide`` / ``simp [<def>]``
/ a chain of foundation rewrites.

This module is library-agnostic: it never imports sympy or numpy.
Targets are resolved generically via dotted paths from the .deppy.

Honest limit
------------

deppy's body translator currently rejects functions with non-terminal
``if`` branches, generator expressions, ``isinstance`` calls, and
many sympy/numpy-specific operators.  For libraries with such
implementations the translator returns ``sorry`` and the axiom
remains admitted.  Improving the translator's coverage *is* the
work that pushes the trust surface down — but that work happens in
``deppy/lean/body_translation.py``, not by wiring library-specific
shortcuts here.
"""
from __future__ import annotations

import ast
import hashlib
import importlib
import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Any, Optional


@dataclass
class BodyLinkResult:
    """Per-(target, method) translation outcome."""
    target_path: str            # e.g. "sympy.geometry.point.Point"
    method_name: str            # e.g. "distance"
    qualified: str              # "Point_distance"
    source: str = ""            # the original Python source bytes
    source_hash: str = ""       # SHA-256 of source (commitment)
    lean_def_text: str = ""     # full Lean def text including ``def``
    body_lean_text: str = ""    # just the translated body
    exact: bool = False
    sorry_count: int = 0
    notes: list[str] = field(default_factory=list)
    binders: str = ""
    return_type: str = ""
    error: str = ""             # populated when resolution/parsing fails
    # All identifiers the translated body references (for preamble).
    referenced_names: set[str] = field(default_factory=set)


@dataclass
class BodyLinkReport:
    results: list[BodyLinkResult] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.results)

    @property
    def exact_count(self) -> int:
        return sum(1 for r in self.results if r.exact)

    @property
    def sorry_count(self) -> int:
        return sum(r.sorry_count for r in self.results)

    @property
    def error_count(self) -> int:
        return sum(1 for r in self.results if r.error)

    def by_qualified(self) -> dict[str, BodyLinkResult]:
        return {r.qualified: r for r in self.results}


# ─────────────────────────────────────────────────────────────────────
#  Target resolution
# ─────────────────────────────────────────────────────────────────────

def _resolve_dotted(dotted: str) -> Optional[Any]:
    if not dotted:
        return None
    parts = dotted.split(".")
    for i in range(len(parts), 0, -1):
        try:
            mod = importlib.import_module(".".join(parts[:i]))
        except (ImportError, ValueError):
            continue
        cur: Any = mod
        ok = True
        for a in parts[i:]:
            if not hasattr(cur, a):
                ok = False
                break
            cur = getattr(cur, a)
        if ok:
            return cur
    return None


# ─────────────────────────────────────────────────────────────────────
#  Per-(target, method) translation
# ─────────────────────────────────────────────────────────────────────

def link_method(
    target_path: str,
    class_name: str,
    method_name: str,
) -> BodyLinkResult:
    """Resolve ``target_path.method_name`` and run deppy's body
    translator on its source.  Return a :class:`BodyLinkResult`."""
    qualified = f"{class_name}_{method_name}"
    target = _resolve_dotted(target_path)
    if target is None:
        return BodyLinkResult(
            target_path=target_path,
            method_name=method_name,
            qualified=qualified,
            error=f"could not resolve {target_path}",
        )
    if not hasattr(target, method_name):
        return BodyLinkResult(
            target_path=target_path,
            method_name=method_name,
            qualified=qualified,
            error=f"target has no attribute {method_name!r}",
        )
    method = getattr(target, method_name)
    # Unwrap ``@property``: ``inspect.getsource`` can't read a
    # property object, but ``property.fget`` is the underlying
    # function — use it directly.  Same for ``cached_property``
    # (which exposes ``func``) and ``classmethod`` /
    # ``staticmethod`` (which expose ``__func__``).
    if isinstance(method, property):
        if method.fget is not None:
            method = method.fget
    elif hasattr(method, "func") and callable(getattr(method, "func", None)):
        method = method.func
    elif hasattr(method, "__func__") and callable(getattr(method, "__func__", None)):
        method = method.__func__
    try:
        raw_src = inspect.getsource(method)
    except (OSError, TypeError) as e:
        return BodyLinkResult(
            target_path=target_path,
            method_name=method_name,
            qualified=qualified,
            error=f"inspect.getsource failed: {e}",
        )

    src = textwrap.dedent(raw_src)
    src_hash = hashlib.sha256(src.encode("utf-8")).hexdigest()

    try:
        mod = ast.parse(src)
    except SyntaxError as e:
        return BodyLinkResult(
            target_path=target_path,
            method_name=method_name,
            qualified=qualified,
            source=src,
            source_hash=src_hash,
            error=f"ast.parse failed: {e}",
        )
    fn_nodes = [
        n for n in mod.body
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    if not fn_nodes:
        return BodyLinkResult(
            target_path=target_path,
            method_name=method_name,
            qualified=qualified,
            source=src,
            source_hash=src_hash,
            error="no FunctionDef in source",
        )
    fn_node = fn_nodes[0]

    # Use deppy's own body translator — *not* an external engine.
    from deppy.lean.body_translation import (
        translate_body,
        infer_function_signature,
    )
    sig_result = infer_function_signature(
        fn_node, None, param_types=None,
    )
    if isinstance(sig_result, tuple) and len(sig_result) >= 2:
        binders, return_type = sig_result[0], sig_result[1]
    else:
        binders, return_type = "", "Int"
    body_result = translate_body(fn_node)

    body_text = body_result.lean_text
    # Wrap the translated body in a Lean ``def``.  Use the
    # ``Class_method`` convention so the rest of the certificate's
    # mechanization vocabulary lines up.
    lean_def = (
        f"def {qualified}{(' ' + binders) if binders else ''} : "
        f"{return_type or 'Int'} :=\n  {body_text}"
    )

    referenced = _collect_referenced_names(body_text)

    return BodyLinkResult(
        target_path=target_path,
        method_name=method_name,
        qualified=qualified,
        source=src,
        source_hash=src_hash,
        lean_def_text=lean_def,
        body_lean_text=body_text,
        exact=body_result.exact,
        sorry_count=body_result.sorry_count,
        notes=list(body_result.notes),
        binders=binders,
        return_type=return_type or "Int",
        referenced_names=referenced,
    )


# ─────────────────────────────────────────────────────────────────────
#  Identifier extraction from translated Lean text
# ─────────────────────────────────────────────────────────────────────

import re as _re

_LEAN_RESERVED = {
    "if", "then", "else", "let", "in", "fun", "do", "match", "with",
    "Prop", "Type", "Int", "Bool", "Float", "Char", "String", "Nat",
    "true", "false", "panic!", "sorry", "rfl", "True", "False",
    "List", "Array", "Option", "Set", "Map", "Eq", "And", "Or", "Not",
}

_LEAN_BUILTIN_OPS = {
    "List.zipWith", "List.map", "List.filter", "List.foldl",
    "List.foldr", "List.length", "List.take", "List.drop",
    "Option.get!", "Option.isNone", "Option.isSome",
    "Std.HashMap", "Std.HashMap.contains", "Std.HashMap.get!",
}


def _collect_referenced_names(text: str) -> set[str]:
    """Extract identifiers from Lean text that look like opaque names
    needing axiom declarations.  Filters out reserved words, numeric
    literals, and Lean builtins."""
    out: set[str] = set()
    # Match identifiers (incl. with dots like ``List.zipWith``)
    for tok in _re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", text):
        if tok in _LEAN_RESERVED or tok in _LEAN_BUILTIN_OPS:
            continue
        if tok.isnumeric():
            continue
        # Skip hand-introduced binders ``a``, ``b`` etc. common in our
        # generator translation (``fun a b => ...``).
        out.add(tok)
    return out


# ─────────────────────────────────────────────────────────────────────
#  Across an entire sidecar
# ─────────────────────────────────────────────────────────────────────

def link_all(
    sidecar_module,
    audit_report,
    mechanization_report,
) -> BodyLinkReport:
    """For every GROUNDED axiom, attempt to link each referenced
    ``Class.method`` to its source via deppy's body translator.

    Multiple axioms may reference the same method; we link each
    once.  ``mechanization_report.signature.class_methods`` carries
    the (class, method) pairs collected from AST walking — so this
    function is library-agnostic and just iterates that map.
    """
    from deppy.lean.sidecar_source_audit import AxiomGrounding

    out: list[BodyLinkResult] = []
    if sidecar_module is None:
        return BodyLinkReport(results=out)

    axioms = getattr(sidecar_module, "axioms", {}) or {}
    grounding_by_name = {r.name: r.grounding for r in audit_report.results}

    # Build {Class -> example target_path} from axioms.  When a
    # class is referenced from an axiom whose target is bound to
    # ``sympy.geometry.point.Point``, we link methods on that path.
    cls_to_target: dict[str, str] = {}
    for ax_name, ax in axioms.items():
        if grounding_by_name.get(ax_name) != AxiomGrounding.GROUNDED:
            continue
        target_path = getattr(ax, "target", "") or ""
        if not target_path:
            continue
        leaf = target_path.rsplit(".", 1)[-1]
        cls_to_target.setdefault(leaf, target_path)

    sig = mechanization_report.signature
    seen: set[tuple[str, str]] = set()
    for cls, methods in sig.class_methods.items():
        target_path = cls_to_target.get(cls)
        if target_path is None:
            continue
        for meth in sorted(methods.keys()):
            key = (cls, meth)
            if key in seen:
                continue
            seen.add(key)
            out.append(link_method(target_path, cls, meth))

    return BodyLinkReport(results=out)


__all__ = [
    "BodyLinkResult",
    "BodyLinkReport",
    "link_method",
    "link_all",
]
