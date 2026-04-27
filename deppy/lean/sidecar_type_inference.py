"""Infer Lean signatures for library methods from the library's own
Python type annotations.

The user shouldn't have to write
``code_types: | Circle.radius: Circle → Int`` — that signature is
already there in ``inspect.signature(sympy.geometry.Circle.radius)``.
This module:

  1. Walks every method PSDL / verify references in the .deppy.
  2. Resolves it via ``importlib`` + ``getattr``.
  3. Calls ``inspect.signature`` to read parameter + return types.
  4. Renders each type as a Lean type expression, falling back to
     a declared opaque ``axiom <T> : Type`` when the Python type is
     a class (sympy.geometry.Point → ``Point`` opaque).
  5. Outputs a ``{name: lean_signature}`` dict that the certificate
     emitter merges with any user-supplied ``code_types:`` (user
     wins on collision so they can override library quirks).

When a method is a ``@property`` we treat it as ``T → ReturnT``.
When a method is unannotated we conservatively emit ``Int → Int → … → Int``
so the certificate keeps compiling; the inference's ``coverage``
counter records how many were truly inferred vs defaulted.
"""
from __future__ import annotations

import importlib
import inspect
from dataclasses import dataclass, field
from typing import Any, get_args, get_origin


@dataclass
class TypeInferenceReport:
    inferred: dict[str, str] = field(default_factory=dict)
    needed_types: set[str] = field(default_factory=set)
    coverage_inferred: int = 0
    coverage_defaulted: int = 0
    notes: list[str] = field(default_factory=list)


_BUILTIN_TYPES = {"Int", "Nat", "Bool", "Float", "String"}


def _resolve_dotted(dotted: str) -> Any:
    """Resolve a dotted path via importlib + getattr."""
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


def _python_type_to_lean(
    annotation: Any, owner_class_name: str = "",
) -> tuple[str, set[str]]:
    """Render a Python annotation as a Lean type string.

    Returns ``(lean_text, opaque_types_used)``.  Opaque type names
    must be declared as ``axiom <name> : Type`` in the preamble.
    """
    needed: set[str] = set()
    if annotation is inspect.Parameter.empty or annotation is None:
        return "Int", needed
    # Built-in primitives.
    if annotation is int:
        return "Int", needed
    if annotation is float:
        return "Int", needed   # Int is our universal numeric proxy
    if annotation is bool:
        return "Bool", needed
    if annotation is str:
        return "String", needed
    if annotation is type(None):
        return "Unit", needed
    # Generic types: list[T], dict[K, V], tuple[A, B], Optional[T].
    origin = get_origin(annotation)
    if origin is not None:
        args = get_args(annotation)
        if origin in (list, tuple):
            if args:
                inner_lean, inner_needed = _python_type_to_lean(
                    args[0], owner_class_name,
                )
                needed |= inner_needed
                return f"List {inner_lean}", needed
            return "List Int", needed
        if origin is dict:
            return "Int", needed   # opaque
        # Optional[T] — origin is typing.Union with NoneType.
        if args:
            inner_lean, inner_needed = _python_type_to_lean(
                args[0], owner_class_name,
            )
            needed |= inner_needed
            return f"Option {inner_lean}", needed
        return "Int", needed
    # Class types.
    if isinstance(annotation, type):
        name = annotation.__name__
        if name in {"int", "float"}:
            return "Int", needed
        if name == "bool":
            return "Bool", needed
        if name == "str":
            return "String", needed
        if name not in _BUILTIN_TYPES:
            needed.add(name)
        return name, needed
    # ForwardRef / string annotation.
    if isinstance(annotation, str):
        if annotation in _BUILTIN_TYPES:
            return annotation, needed
        # Treat as opaque type.
        needed.add(annotation)
        return annotation, needed
    # Fallback.
    return "Int", needed


def _signature_to_lean(method: Any, owner_class_name: str) -> tuple[str, set[str], bool]:
    """Render a Python method's signature as a Lean type string.

    Returns ``(lean_signature, needed_types, was_inferred)``.

    ``method`` may be a function, method, classmethod, staticmethod,
    or property (we use ``method.fget`` then).
    """
    needed: set[str] = set()
    # Unwrap @property.
    if isinstance(method, property):
        if method.fget is None:
            return f"{owner_class_name} → Int", {owner_class_name}, False
        try:
            sig = inspect.signature(method.fget)
        except (TypeError, ValueError):
            return f"{owner_class_name} → Int", {owner_class_name}, False
        # property body: takes self only, returns ReturnT.
        ret_lean, ret_needed = _python_type_to_lean(
            sig.return_annotation, owner_class_name,
        )
        needed |= ret_needed
        if owner_class_name and owner_class_name not in _BUILTIN_TYPES:
            needed.add(owner_class_name)
        sig_text = (
            f"{owner_class_name} → {ret_lean}"
            if owner_class_name else f"Int → {ret_lean}"
        )
        was_inferred = (
            sig.return_annotation is not inspect.Parameter.empty
        )
        return sig_text, needed, was_inferred
    # Regular function or method.
    try:
        sig = inspect.signature(method)
    except (TypeError, ValueError):
        return "Int → Int", set(), False
    parts: list[str] = []
    inferred_any = False
    for name, p in sig.parameters.items():
        if name == "self":
            if owner_class_name and owner_class_name not in _BUILTIN_TYPES:
                needed.add(owner_class_name)
            parts.append(owner_class_name or "Int")
            continue
        if p.kind in (
            inspect.Parameter.VAR_POSITIONAL,
            inspect.Parameter.VAR_KEYWORD,
        ):
            # *args / **kwargs — fall back to Int.
            parts.append("Int")
            continue
        plean, pneeded = _python_type_to_lean(
            p.annotation, owner_class_name,
        )
        if p.annotation is not inspect.Parameter.empty:
            inferred_any = True
        needed |= pneeded
        parts.append(plean)
    ret_lean, ret_needed = _python_type_to_lean(
        sig.return_annotation, owner_class_name,
    )
    needed |= ret_needed
    if sig.return_annotation is not inspect.Parameter.empty:
        inferred_any = True
    parts.append(ret_lean)
    return " → ".join(parts), needed, inferred_any


def infer_code_types(
    sidecar_module,
    *,
    extra_methods: list[str] | None = None,
) -> TypeInferenceReport:
    """Infer Lean signatures for every method the .deppy references.

    Walks all ``verify`` blocks (their ``function:`` paths) and any
    additional dotted paths in ``extra_methods``.  For each, resolves
    via ``importlib`` and reads ``inspect.signature``.

    Returns a :class:`TypeInferenceReport` whose ``inferred`` dict
    maps ``Class.method`` → Lean signature.  Any opaque types
    encountered are recorded in ``needed_types`` so the preamble
    declares them.
    """
    report = TypeInferenceReport()
    if sidecar_module is None:
        return report

    methods_to_resolve: dict[str, str] = {}  # ``Class.method`` → dotted path
    verifies = getattr(sidecar_module, "verifies", []) or []
    for v in verifies:
        fn_path = getattr(v, "function", "") or ""
        if not fn_path:
            continue
        parts = fn_path.split(".")
        if len(parts) < 2:
            continue
        head = f"{parts[-2]}.{parts[-1]}"
        methods_to_resolve.setdefault(head, fn_path)
    for extra in (extra_methods or []):
        parts = extra.split(".")
        if len(parts) >= 2:
            head = f"{parts[-2]}.{parts[-1]}"
            methods_to_resolve.setdefault(head, extra)

    for head, dotted in sorted(methods_to_resolve.items()):
        method = _resolve_dotted(dotted)
        if method is None:
            report.notes.append(f"could not resolve {dotted}")
            report.coverage_defaulted += 1
            continue
        cls_name = head.split(".")[0]
        sig_text, needed, inferred = _signature_to_lean(method, cls_name)
        report.inferred[head] = sig_text
        report.needed_types |= needed
        if inferred:
            report.coverage_inferred += 1
        else:
            report.coverage_defaulted += 1
    return report


__all__ = ["TypeInferenceReport", "infer_code_types"]
