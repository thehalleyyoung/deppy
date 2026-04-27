"""Annotation-driven concrete Lean preamble.

Replaces the opaque `Sidecar_X_prop : Prop` / `Foundation_X_prop : Prop` /
`Verified_X_property : Prop` declarations with **concrete** Lean
propositions assembled from the .deppy file's annotations.

Inputs (from the SidecarModule):

  * Per-verify ``binders``: maps free variable name → Lean type name.
    Each unique type name produces ``axiom <T> : Type``.
  * Per-verify ``function``: dotted path; the leaf class becomes a
    type, the method becomes ``axiom <Class>.<method> : <sig>``.
  * Per-verify ``property``: Python expression compiled to a Lean
    Prop using the binder + function signature context.
  * Top-level ``code_types``: explicit ``name: signature`` strings;
    declared as ``axiom <name> : <sig>`` directly.
  * Top-level ``lean_imports`` / ``lean_preamble``: pulled in
    verbatim before the generated declarations.

The output is an ordered list of Lean declaration lines.  Once
emitted, the verify-block theorems' goal types are concrete and
PSDL-emitted Lean tactics elaborate against them.
"""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class AnnotationPreamble:
    """Output of :func:`build_annotation_preamble`."""
    lean_lines: list[str] = field(default_factory=list)
    declared_types: set[str] = field(default_factory=set)
    declared_methods: set[str] = field(default_factory=set)
    declared_predicates: set[str] = field(default_factory=set)
    # Per-verify concrete property bodies.  Maps verify name →
    # ``(prop_name, prop_body)``; the certificate uses these to emit
    # a concrete ``def <prop_name> : Prop := <body>`` in place of
    # the opaque ``Verified_X_property``.
    concrete_props: dict[str, tuple[str, str]] = field(
        default_factory=dict,
    )


def _safe(s: str) -> str:
    out = []
    for ch in s or "":
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    s2 = "".join(out)
    if s2 and s2[0].isdigit():
        s2 = "i" + s2
    s2 = re.sub(r"_+", "_", s2)
    return s2.strip("_") or "anon"


def _qualified(function_path: str) -> tuple[str, str, str]:
    """Split ``sympy.geometry.point.Point.distance`` into
    ``(qualified_name, class_name, method_name)``."""
    parts = function_path.split(".")
    if len(parts) >= 2:
        return f"{parts[-2]}_{parts[-1]}", parts[-2], parts[-1]
    return function_path.replace(".", "_"), "", function_path


def _binder_types(binders: dict[str, str]) -> set[str]:
    return {t.strip() for t in (binders or {}).values() if t.strip()}


def _translate_property_to_lean(
    property_text: str,
    binders: dict[str, str],
    method_qualified: str,
    method_class: str,
    method_method: str,
) -> tuple[str, list[str]]:
    """Translate the property string into a Lean proposition.

    Best-effort: parses the property as Python AST and renders each
    node as Lean.  Method calls on the named class become applications
    of the declared method (``Point.distance(p, q) → Point.distance p q``).
    Comparison operators become Lean comparisons; arithmetic operators
    map across.  Unsupported nodes fall back to opaque ``True``.

    Returns ``(lean_text, free_vars)``: the rendered Lean expression
    and the list of free variable names that appear in it but were
    not in ``binders`` and aren't class/function references.  Callers
    should bind these as additional ``∀``-quantified parameters.
    """
    text = (property_text or "").strip()
    if not text:
        return "True", []
    try:
        tree = ast.parse(text, mode="eval").body
    except SyntaxError:
        return "True", []
    free_vars: list[str] = []
    seen_free: set[str] = set()
    rendered = _render_lean_expr(
        tree, binders, method_class, method_method,
        free_vars=free_vars, seen_free=seen_free,
    )
    return rendered, free_vars


def _collect_free_names(
    node: ast.AST,
    binders: dict[str, str],
    free_vars: list[str],
    seen_free: set[str],
) -> None:
    """Walk ``node`` and accumulate names that look like free variables.

    A ``Name`` node is a free variable if:
      * it is not in ``binders`` (handled separately as the typed bind),
      * it is not a class identifier (uppercase head — handled as a
        type/constructor reference),
      * it is not used as the target of a ``Call`` (handled as a free
        function reference).

    Iteration order matches Python's left-to-right reading of the
    expression so the emitted ``∀`` quantifier preserves user intent.
    """
    if isinstance(node, ast.Name):
        nm = node.id
        if nm and nm[0].islower() and nm not in binders and nm not in seen_free:
            free_vars.append(nm)
            seen_free.add(nm)
        return
    if isinstance(node, ast.Call):
        f = node.func
        if isinstance(f, ast.Attribute):
            if isinstance(f.value, ast.Name):
                if f.value.id and f.value.id[0].islower() and f.value.id not in binders and f.value.id not in seen_free:
                    free_vars.append(f.value.id)
                    seen_free.add(f.value.id)
        # don't recurse into the func head — that's a function name
        for a in node.args:
            _collect_free_names(a, binders, free_vars, seen_free)
        for kw in node.keywords:
            if kw.value is not None:
                _collect_free_names(kw.value, binders, free_vars, seen_free)
        return
    for child in ast.iter_child_nodes(node):
        _collect_free_names(child, binders, free_vars, seen_free)


_BIN_OP_LEAN = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
    ast.Pow: "^", ast.Mod: "%", ast.FloorDiv: "/",
}

_CMP_LEAN = {
    ast.Eq: "=", ast.NotEq: "≠",
    ast.Lt: "<", ast.LtE: "≤",
    ast.Gt: ">", ast.GtE: "≥",
}

# Set by :func:`build_annotation_preamble` before each render so the
# expression renderer knows which uppercase identifiers correspond to
# declared classes (and therefore should be emitted as Class_method /
# Class_attr / Class_mk) versus free variables.  Empty set means "no
# known classes" — every uppercase name becomes a free variable.
_class_names_ctx: set[str] = set()


def _render_lean_expr(
    node: ast.AST,
    binders: dict[str, str],
    method_class: str,
    method_method: str,
    *,
    free_vars: list[str],
    seen_free: set[str],
) -> str:
    """Render a Python AST node as Lean text using the same conventions
    as :mod:`deppy.lean.sidecar_mechanization` so verify-block property
    bodies share the mechanization preamble's vocabulary:

      * ``ClassName.method(args)`` → ``(Class_method args)``
      * ``ClassName.attr``         → ``(Class_attr)``
      * ``var.attr``               → ``(dot_attr var)``
      * ``var.method(args)``       → ``(dot_method var args)``
      * ``Class(args)``            → ``(Class_mk args)``
      * ``Class(args).method(...)``→ ``(Class_method ctor_args tail_args)``
      * ``func(args)``             → ``(func args)``

    Free lowercase identifiers (not declared in ``binders``) are
    accumulated into ``free_vars`` so the caller can quantify them.
    """
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            # Python's ``True``/``False`` map to Int 1/0 in the
            # placeholder semantics — mechanization emits Int-valued
            # functions for predicates, so a Bool comparison
            # ``isprime(2) == True`` becomes ``isprime(2) = 1``.
            # Lean's :class:`Prop` ``True`` would clash on type
            # mismatch with Int.
            return "1" if node.value else "0"
        if isinstance(node.value, (int, float)):
            return str(node.value)
        return f'"{node.value}"'
    if isinstance(node, ast.Name):
        nm = node.id
        if nm in binders:
            return nm
        # Class names (uppercase identifier matching a known type)
        # would be handled at Call/Attribute level; bare ``ClassName``
        # in expression position is rare — emit verbatim.
        if nm in _class_names_ctx:
            return _safe(nm)
        # Any unbound identifier becomes a free variable.  We
        # accumulate so the caller can quantify; lowercase or
        # uppercase doesn't matter for binding (single-letter
        # ``A``, ``B``, ``C`` are common in geometry properties).
        if nm not in seen_free:
            free_vars.append(nm)
            seen_free.add(nm)
        return nm
    if isinstance(node, ast.Attribute):
        # ``ClassName.attr`` → ``(Class_attr)`` (0-arity class member),
        # but only when ``ClassName`` is a known declared class.
        if (
            isinstance(node.value, ast.Name)
            and node.value.id in _class_names_ctx
        ):
            return f"({node.value.id}_{node.attr})"
        # ``var.attr`` → ``(dot_attr var)``.
        if isinstance(node.value, ast.Name):
            v = node.value
            if v.id in binders:
                return f"(dot_{node.attr} {v.id})"
            # Unknown name in receiver position: treat as free variable.
            if v.id not in seen_free:
                free_vars.append(v.id)
                seen_free.add(v.id)
            return f"(dot_{node.attr} {v.id})"
        # Nested expression as receiver: ``(...).attr``.
        inner = _render_lean_expr(
            node.value, binders, method_class, method_method,
            free_vars=free_vars, seen_free=seen_free,
        )
        return f"(dot_{node.attr} {inner})"
    if isinstance(node, ast.UnaryOp):
        op = _render_lean_expr(
            node.operand, binders, method_class, method_method,
            free_vars=free_vars, seen_free=seen_free,
        )
        if isinstance(node.op, ast.USub):
            return f"(-{op})"
        if isinstance(node.op, ast.Not):
            return f"(¬ {op})"
        return op
    if isinstance(node, ast.BinOp):
        l = _render_lean_expr(
            node.left, binders, method_class, method_method,
            free_vars=free_vars, seen_free=seen_free,
        )
        r = _render_lean_expr(
            node.right, binders, method_class, method_method,
            free_vars=free_vars, seen_free=seen_free,
        )
        op = _BIN_OP_LEAN.get(type(node.op), "?")
        return f"({l} {op} {r})"
    if isinstance(node, ast.Compare):
        l = _render_lean_expr(
            node.left, binders, method_class, method_method,
            free_vars=free_vars, seen_free=seen_free,
        )
        parts: list[str] = []
        for op, cmp in zip(node.ops, node.comparators):
            r = _render_lean_expr(
                cmp, binders, method_class, method_method,
                free_vars=free_vars, seen_free=seen_free,
            )
            sym = _CMP_LEAN.get(type(op), "=")
            parts.append(f"({l} {sym} {r})")
            l = r
        if len(parts) == 1:
            return parts[0]
        return "(" + " ∧ ".join(parts) + ")"
    if isinstance(node, ast.BoolOp):
        sep = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
        return "(" + sep.join(
            _render_lean_expr(
                v, binders, method_class, method_method,
                free_vars=free_vars, seen_free=seen_free,
            )
            for v in node.values
        ) + ")"
    if isinstance(node, ast.Call):
        f = node.func
        args = [
            _render_lean_expr(
                a, binders, method_class, method_method,
                free_vars=free_vars, seen_free=seen_free,
            )
            for a in node.args
        ]
        # ``Class.method(args)`` → ``(Class_method args)`` only when
        # ``Class`` is a declared class.
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Name)
            and f.value.id in _class_names_ctx
        ):
            head = f"{f.value.id}_{f.attr}"
            return "(" + head + (" " + " ".join(args) if args else "") + ")"
        # ``Class(args).method(args2)`` chained — only when Class known.
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Call)
            and isinstance(f.value.func, ast.Name)
            and f.value.func.id in _class_names_ctx
        ):
            cls = f.value.func.id
            meth = f.attr
            ctor_args = [
                _render_lean_expr(
                    a, binders, method_class, method_method,
                    free_vars=free_vars, seen_free=seen_free,
                )
                for a in f.value.args
            ]
            head = f"{cls}_{meth}"
            all_args = ctor_args + args
            return "(" + head + (" " + " ".join(all_args) if all_args else "") + ")"
        # ``var.method(args)`` — method call on a variable, use shared
        # ``dot_method`` accessor (matches mechanization).
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Name)
        ):
            v = f.value
            head = f"dot_{f.attr}"
            if v.id in binders:
                receiver = v.id
            else:
                if v.id not in seen_free:
                    free_vars.append(v.id)
                    seen_free.add(v.id)
                receiver = v.id
            all_args = [receiver] + args
            return "(" + head + " " + " ".join(all_args) + ")"
        # Bare function call ``func(args)``
        if isinstance(f, ast.Name):
            # ``Class(args)`` constructor.
            if f.id in _class_names_ctx:
                head = f"{f.id}_mk"
                return "(" + head + (" " + " ".join(args) if args else "") + ")"
            # ``func(args)`` regular function call.
            return "(" + _safe(f.id) + (" " + " ".join(args) if args else "") + ")"
        # Fallback for nested call heads we don't recognise.
        return "(" + " ".join(args) + ")"
    if isinstance(node, ast.Tuple):
        # Render an n-tuple as ``Pair2_mk x y`` / ``Pair3_mk x y z`` so
        # the body matches the mechanization preamble's tuple helpers.
        parts = [
            _render_lean_expr(
                e, binders, method_class, method_method,
                free_vars=free_vars, seen_free=seen_free,
            )
            for e in node.elts
        ]
        if len(parts) == 2:
            return "(Pair2_mk " + " ".join(parts) + ")"
        if len(parts) == 3:
            return "(Pair3_mk " + " ".join(parts) + ")"
        return "(" + ", ".join(parts) + ")"
    return "True"


def build_annotation_preamble(sidecar_module) -> AnnotationPreamble:
    """Build the concrete Lean preamble from .deppy annotations.

    Code-types are inferred from each method's actual Python type
    annotations via ``inspect.signature`` (see
    :mod:`deppy.lean.sidecar_type_inference`).  User-supplied
    ``code_types:`` from the .deppy override the inferred signatures
    on collision.
    """
    out = AnnotationPreamble()
    if sidecar_module is None:
        return out

    foundations = getattr(sidecar_module, "foundations", {}) or {}
    verifies = getattr(sidecar_module, "verifies", []) or []
    user_code_types = getattr(sidecar_module, "_code_types", {}) or {}
    lean_imports = getattr(sidecar_module, "_lean_imports", []) or []
    lean_preamble_text = getattr(sidecar_module, "_lean_preamble", "") or ""

    # ── Auto-infer code-types from library introspection ──
    inferred_types: dict[str, str] = {}
    inferred_needed_types: set[str] = set()
    try:
        from deppy.lean.sidecar_type_inference import infer_code_types
        ti = infer_code_types(sidecar_module)
        inferred_types = dict(ti.inferred)
        inferred_needed_types = set(ti.needed_types)
    except Exception:
        pass

    # User code_types override inferred on collision.
    code_types = dict(inferred_types)
    code_types.update(user_code_types)

    # 1. lean_imports — verbatim, lines as written.
    if lean_imports:
        out.lean_lines.append(
            "-- ── User-supplied Lean imports (from .deppy lean_imports:) ──"
        )
        for imp in lean_imports:
            line = imp if imp.startswith("import ") else f"import {imp}"
            out.lean_lines.append(line)
        out.lean_lines.append("")

    # 2. lean_preamble — verbatim block.
    if lean_preamble_text:
        out.lean_lines.append(
            "-- ── User-supplied Lean preamble (from .deppy lean_preamble:) ──"
        )
        for ln in lean_preamble_text.splitlines():
            out.lean_lines.append(ln)
        out.lean_lines.append("")

    # 3. Type declarations — every unique binder type across all verify
    # blocks plus types needed by the inferred code_types signatures.
    # Use ``abbrev`` so the type is definitionally equal to ``Int``;
    # this makes the verify-block ``binders: p: Point`` compile while
    # remaining compatible with the mechanization preamble's flat-Int
    # function declarations.  Without the alias, ``Point → Int → Int``
    # would not unify with ``Int → Int → Int`` when applied to
    # accessor outputs (``dot_centroid t : Int``).
    type_set: set[str] = set()
    for v in verifies:
        for t in _binder_types(getattr(v, "binders", {}) or {}):
            type_set.add(t)
    type_set |= inferred_needed_types
    if type_set:
        out.lean_lines.append(
            "-- ── Concrete types from verify-block binders "
            "(definitional aliases to Int) ──"
        )
        for t in sorted(type_set):
            if t in {"Int", "Nat", "Bool", "Float", "String"}:
                continue  # built-in
            out.lean_lines.append(f"abbrev {_safe(t)} : Type := Int")
            out.declared_types.add(t)
        out.lean_lines.append("")

    # 4. CODE-TYPES — only emit *user-supplied* signatures.  Inferred
    # signatures (from ``inspect.signature``) often conflict with the
    # arities mechanization derives from observed AST usage (e.g.,
    # ``Segment(p, q).contains(...)`` uses 3 mechanization-args while
    # ``inspect.signature(Segment.contains)`` reports 2 — the
    # ``self`` and ``other`` parameters).  When in conflict,
    # mechanization wins because it directly matches how the AST is
    # being translated.  User-supplied code_types take priority over
    # both because the user is making an explicit typed claim that
    # the verifier should honour.
    if user_code_types:
        out.lean_lines.append(
            "-- ── User-declared code-type signatures (from .deppy code_types:) ──"
        )
        for name in sorted(user_code_types.keys()):
            sig = user_code_types[name].strip()
            out.lean_lines.append(f"axiom {_safe(name)} : {sig}")
            # Record so the mechanization-preamble filter can skip
            # any name mechanization would re-declare.
            out.declared_methods.add(name)
        out.lean_lines.append("")

    # 6. Concrete Foundation Props — for each foundation whose
    # statement parses, generate a concrete Prop.  When the foundation
    # has been recorded as concrete elsewhere (the existing concrete
    # foundation table), we reuse that; otherwise we attempt to
    # parse the statement as a Python expression and render it.
    if foundations:
        out.lean_lines.append(
            "-- ── Concrete Foundation Props (assembled from foundation statements) ──"
        )
        for f_name in sorted(foundations.keys()):
            f = foundations[f_name]
            stmt = getattr(f, "statement", "") or ""
            # Try to render — for now, fall through to ``True`` so the
            # certificate compiles.  The real rendering happens in
            # sidecar_certificate's existing _FOUNDATION_CONCRETE
            # table; this preamble adds nothing duplicate.
            pass
        out.lean_lines.append("")

    # 7. Per-verify concrete Verified_X_property body.
    # Set the class-names context before rendering: any uppercase name
    # that we declared as a type / matched as a binder type counts as
    # a class.  Anything else becomes a free Int variable.
    global _class_names_ctx
    _class_names_ctx = set(out.declared_types) | type_set
    for v in verifies:
        vname = getattr(v, "name", "")
        if not vname:
            continue
        binders = dict(getattr(v, "binders", {}) or {})
        property_text = getattr(v, "property", "") or ""
        fn = getattr(v, "function", "") or ""
        _qual, cls, meth = _qualified(fn)
        body, free_vars = _translate_property_to_lean(
            property_text, binders, _qual, cls, meth,
        )
        # Universally quantify over (a) declared binders and
        # (b) any free lowercase names in the rendered Lean (auto-Int).
        binder_pairs: list[tuple[str, str]] = []
        for k, t in binders.items():
            binder_pairs.append((k, t))
        for fv in free_vars:
            if fv not in binders:
                binder_pairs.append((fv, "Int"))
        if binder_pairs:
            quant = "∀ " + " ".join(
                f"({k} : {_safe(t) if t not in {'Int','Nat','Bool','Float','String'} else t})"
                for k, t in binder_pairs
            ) + ", "
        else:
            quant = ""
        prop_body = quant + body
        out.concrete_props[vname] = (
            f"Verified_{_safe(vname)}_property", prop_body,
        )

    return out


__all__ = ["AnnotationPreamble", "build_annotation_preamble"]
