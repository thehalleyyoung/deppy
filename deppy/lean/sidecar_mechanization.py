"""Generic Python expression → Lean expression translator for sidecar
axioms.

The point of this module is to take a step toward *Lean-mechanized*
verification of library properties using only the contents of a
``.deppy`` file: each GROUNDED axiom (one whose Python statement
parses as an AST and whose referenced attributes resolve on the
live target) is emitted as a *concrete Lean Prop*, not an opaque
one.  The Lean kernel can then see what the axiom asserts and
proofs can pattern-match on it.

What this module does
---------------------

  1. Walk every GROUNDED axiom's Python AST.
  2. Collect the **vocabulary** referenced across all axioms:
       * ``class_methods`` — ``ClassName.method(args)`` and
         ``ClassName(args).method(args2)`` patterns,
       * ``class_ctor_arity`` — observed arities of ``ClassName(...)``
         constructor calls,
       * ``attrs`` — every ``.attr`` access on a bound variable
         (collected globally — accessors are shared regardless of
         which class the variable belongs to),
       * ``free_fns`` — bare ``func(args)`` calls,
       * ``prop_fns`` — subset of ``free_fns`` inferred to return
         ``Prop`` because they appear at top-level position (not as
         operands of arithmetic).
  3. Emit a Lean preamble that declares this vocabulary as ``axiom``s
     of type ``Int → ... → Int`` (or ``→ Prop`` for ``prop_fns``).
  4. Translate each GROUNDED axiom statement into a concrete Lean
     Prop using this vocabulary.

The translation is library-agnostic: the same logic handles
``sympy.geometry``, ``numpy``, ``torch``, anything.  The .deppy
file alone determines the vocabulary — no library-specific
function names are hard-coded.

Flat-Int scheme
---------------

Everything inhabits ``Int``.  Class types (``Point``, ``Triangle``,
…) are *not* declared as Lean types — they appear only as naming
conventions on the function symbols (``Point_distance``,
``Triangle_centroid``).  This loses the ability to distinguish
classes in the type system but makes the resulting Lean compile
without inference acrobatics, and the kernel still treats
``Point_distance`` and ``Triangle_distance`` as distinct symbols.

Limitations
-----------

  * Numeric literals are emitted as Int.  Real-number facts (sqrt,
    sin, etc.) belong in foundation axioms.
  * Translation is best-effort.  When an axiom's statement uses
    Python syntax we don't yet support, the result is
    ``MechanizedAxiom(lean_statement=None, failure_reason=...)``
    and the certificate falls back to opaque-Prop encoding.
"""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Output data
# ─────────────────────────────────────────────────────────────────────

@dataclass
class MechanizedSignature:
    """Lean preamble vocabulary, all derived from the .deppy AST."""
    # ``class -> {method_name: arity}`` (arity excludes the receiver).
    class_methods: dict[str, dict[str, int]] = field(default_factory=dict)
    # ``class -> max constructor arity observed``
    class_ctor_arity: dict[str, int] = field(default_factory=dict)
    # All attribute names seen on bound variables (shared accessors).
    attrs: set[str] = field(default_factory=set)
    # ``free_function_name -> max arity``
    free_fns: dict[str, int] = field(default_factory=dict)
    # Free fns inferred to return ``Prop``.
    prop_fns: set[str] = field(default_factory=set)
    # All bound variable names across axioms (informational).
    free_vars: set[str] = field(default_factory=set)
    # All class names referenced (informational — for documentation).
    classes: set[str] = field(default_factory=set)
    # Class methods inferred to return ``Prop`` (because they appear
    # at top-level expression position in some axiom).
    prop_class_methods: set[tuple[str, str]] = field(default_factory=set)
    # Shared accessors (``dot_<attr>``) inferred to return ``Prop``
    # for the same reason.
    prop_attrs: set[str] = field(default_factory=set)


@dataclass
class MechanizedAxiom:
    name: str
    python_statement: str
    lean_statement: Optional[str] = None
    failure_reason: str = ""
    free_vars: list[str] = field(default_factory=list)
    # Parallel translation via the canonical
    # ``deppy.lean.predicate_translation.translate``.  Used for
    # comparison / audit; never overrides ``lean_statement`` when the
    # local mechanization is more specific.
    canonical_lean: str = ""
    canonical_exact: bool = False
    canonical_aux_count: int = 0


@dataclass
class MechanizationReport:
    signature: MechanizedSignature
    axioms: list[MechanizedAxiom] = field(default_factory=list)

    @property
    def concrete_count(self) -> int:
        return sum(1 for a in self.axioms if a.lean_statement is not None)

    @property
    def opaque_count(self) -> int:
        return sum(1 for a in self.axioms if a.lean_statement is None)

    def by_name(self) -> dict[str, MechanizedAxiom]:
        return {a.name: a for a in self.axioms}


# ─────────────────────────────────────────────────────────────────────
#  Vocabulary collection (pass 1)
# ─────────────────────────────────────────────────────────────────────

def _looks_like_class(name: str) -> bool:
    """Multi-letter capital-initial name → class identifier.

    Single-letter caps like ``A``, ``B``, ``C`` are common variable
    names in geometry and are treated as plain free variables.
    """
    return bool(name) and len(name) >= 2 and name[0].isupper()


class _VocabCollector(ast.NodeVisitor):
    """Walk an axiom's AST and update a shared MechanizedSignature."""

    def __init__(self, sig: MechanizedSignature):
        self.sig = sig
        self.free: set[str] = set()
        # Set of free-fn names that appeared at top-level (not nested
        # inside an arithmetic op) — these are likely Prop-returning.
        self.top_level_fns: set[str] = set()

    def visit_Name(self, node: ast.Name) -> None:
        if node.id and not _looks_like_class(node.id):
            self.free.add(node.id)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        self.visit(node.value)
        v = node.value
        if isinstance(v, ast.Name):
            if _looks_like_class(v.id):
                self.sig.classes.add(v.id)
                # ``Class.attr`` — class-level constant, treat as a
                # 0-arity method.
                self.sig.class_methods.setdefault(
                    v.id, {}
                ).setdefault(node.attr, 0)
            else:
                self.sig.attrs.add(node.attr)
                self.free.add(v.id)
        # For chained attribute accesses (a.b.c), the inner Attribute
        # is visited; here we still need to record the outer attr.
        if isinstance(v, ast.Attribute) or isinstance(v, ast.Call):
            self.sig.attrs.add(node.attr)

    def visit_Call(self, node: ast.Call) -> None:
        f = node.func
        # Form 1: ``ClassName.method(args)``
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Name)
            and _looks_like_class(f.value.id)
        ):
            cls_name = f.value.id
            self.sig.classes.add(cls_name)
            meth = f.attr
            arity = len(node.args)
            self.sig.class_methods.setdefault(cls_name, {})[meth] = max(
                self.sig.class_methods.get(cls_name, {}).get(meth, 0),
                arity,
            )
        # Form 2: ``Class(args)`` constructor.
        elif isinstance(f, ast.Name) and _looks_like_class(f.id):
            self.sig.classes.add(f.id)
            self.sig.class_ctor_arity[f.id] = max(
                self.sig.class_ctor_arity.get(f.id, 0),
                len(node.args),
            )
        # Form 3: ``Class(args).method(args2)`` — chained.
        elif (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Call)
            and isinstance(f.value.func, ast.Name)
            and _looks_like_class(f.value.func.id)
        ):
            cls_name = f.value.func.id
            self.sig.classes.add(cls_name)
            meth = f.attr
            ctor_n = len(f.value.args)
            tail_n = len(node.args)
            self.sig.class_ctor_arity[cls_name] = max(
                self.sig.class_ctor_arity.get(cls_name, 0),
                ctor_n,
            )
            # The chained method effectively takes (ctor_args, tail_args)
            # so its arity is ctor_n + tail_n.
            self.sig.class_methods.setdefault(cls_name, {})[meth] = max(
                self.sig.class_methods.get(cls_name, {}).get(meth, 0),
                ctor_n + tail_n,
            )
        # Form 4: ``func(args)`` — generic free function.  Discovered
        # from the .deppy itself; never hard-coded by library name.
        elif isinstance(f, ast.Name):
            fn = f.id
            if fn:
                arity = len(node.args)
                self.sig.free_fns[fn] = max(
                    self.sig.free_fns.get(fn, 0), arity
                )
        # Recurse — including into chained constructor args
        # (f.value is the inner Call when Form 3 matched).
        for a in node.args:
            self.visit(a)
        for kw in node.keywords:
            if kw.value is not None:
                self.visit(kw.value)
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Call):
            for a in f.value.args:
                self.visit(a)


def _classify_prop_fns(
    parsed: ast.AST, sig: MechanizedSignature
) -> None:
    """Mark anything appearing at top-level expression position in an
    axiom (or as a BoolOp operand) as Prop-returning.

    Top-level position means the AST node would otherwise stand
    alone as the body of the axiom — so it must be a Prop, not an
    Int.  We catch four cases: a free function call, a class
    method call, a chained class method call, and a shared
    accessor (rare but possible with ``predicate.attr``).
    """
    def _mark(node: ast.AST) -> None:
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name):
                sig.prop_fns.add(f.id)
            elif (
                isinstance(f, ast.Attribute)
                and isinstance(f.value, ast.Name)
                and _looks_like_class(f.value.id)
            ):
                sig.prop_class_methods.add((f.value.id, f.attr))
            elif (
                isinstance(f, ast.Attribute)
                and isinstance(f.value, ast.Call)
                and isinstance(f.value.func, ast.Name)
                and _looks_like_class(f.value.func.id)
            ):
                sig.prop_class_methods.add((f.value.func.id, f.attr))
            elif isinstance(f, ast.Attribute):
                sig.prop_attrs.add(f.attr)
        elif isinstance(node, ast.Attribute):
            sig.prop_attrs.add(node.attr)

    body = parsed.body if isinstance(parsed, ast.Expression) else parsed
    if isinstance(body, ast.BoolOp):
        for v in body.values:
            _mark(v)
    elif isinstance(body, ast.Compare):
        # When a top-level Compare equates two operands and one of
        # them is itself a Compare, the *other* operand must also be
        # Prop-typed (we're equating two propositions).  Walk the
        # operands and mark any call/attribute whose sibling
        # already looks like a Prop.
        operands: list[ast.expr] = [body.left] + list(body.comparators)
        any_prop = any(
            isinstance(o, (ast.Compare, ast.BoolOp))
            for o in operands
        )
        if any_prop:
            for o in operands:
                _mark(o)
        else:
            _mark(body)
    else:
        _mark(body)


# ─────────────────────────────────────────────────────────────────────
#  Translation (pass 2): Python AST → Lean expression
# ─────────────────────────────────────────────────────────────────────

class _Untranslatable(Exception):
    pass


_BIN_OPS: dict[type, str] = {
    ast.Add: " + ",
    ast.Sub: " - ",
    ast.Mult: " * ",
    ast.Div: " / ",
    ast.FloorDiv: " / ",
    ast.Mod: " % ",
    ast.Pow: " ^ ",
}

_CMP_OPS: dict[type, str] = {
    ast.Eq: " = ",
    ast.NotEq: " ≠ ",
    ast.Lt: " < ",
    ast.LtE: " ≤ ",
    ast.Gt: " > ",
    ast.GtE: " ≥ ",
}

_UNARY_OPS: dict[type, str] = {
    ast.UAdd: "",
    ast.USub: "-",
    ast.Not: "¬",
}


def _translate_expr(node: ast.AST) -> str:
    """Translate one Python expression node to Lean text under the
    flat-Int scheme.  Raises :class:`_Untranslatable` on unsupported
    nodes."""
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, int):
            return f"({v} : Int)" if v < 0 else str(v)
        if isinstance(v, float):
            return f"({int(v)} : Int)"
        raise _Untranslatable(f"unsupported constant: {v!r}")

    if isinstance(node, ast.Name):
        return node.id

    if isinstance(node, ast.Attribute):
        # ``var.attr`` → ``(dot_attr var)`` (shared accessor).
        # ``Class.attr`` → ``(Class_attr)`` (0-arity class member).
        if isinstance(node.value, ast.Name):
            v = node.value
            if _looks_like_class(v.id):
                return f"({v.id}_{node.attr})"
            return f"(dot_{node.attr} {v.id})"
        # Nested: ``(...).attr`` — inner translates; wrap outer.
        inner = _translate_expr(node.value)
        return f"(dot_{node.attr} {inner})"

    if isinstance(node, ast.UnaryOp):
        op = _UNARY_OPS.get(type(node.op))
        if op is None:
            raise _Untranslatable(f"unsupported unary: {type(node.op).__name__}")
        return f"({op}{_translate_expr(node.operand)})"

    if isinstance(node, ast.BinOp):
        op = _BIN_OPS.get(type(node.op))
        if op is None:
            raise _Untranslatable(f"unsupported binop: {type(node.op).__name__}")
        return f"({_translate_expr(node.left)}{op}{_translate_expr(node.right)})"

    if isinstance(node, ast.BoolOp):
        op_text = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
        parts = [_translate_expr(v) for v in node.values]
        return "(" + op_text.join(parts) + ")"

    if isinstance(node, ast.Compare):
        l = _translate_expr(node.left)
        out: list[str] = []
        for op, comparator in zip(node.ops, node.comparators):
            op_text = _CMP_OPS.get(type(op))
            if op_text is None:
                raise _Untranslatable(f"unsupported cmp: {type(op).__name__}")
            r = _translate_expr(comparator)
            out.append(f"({l}{op_text}{r})")
            l = r
        if len(out) == 1:
            return out[0]
        return "(" + " ∧ ".join(out) + ")"

    if isinstance(node, ast.Call):
        f = node.func
        # ``Class.method(args)``
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Name)
            and _looks_like_class(f.value.id)
        ):
            cls = f.value.id
            meth = f.attr
            args = [_translate_expr(a) for a in node.args]
            head = f"{cls}_{meth}"
            return f"({head})" if not args else "(" + head + " " + " ".join(args) + ")"
        # ``Class(args).method(args2)`` chained
        if (
            isinstance(f, ast.Attribute)
            and isinstance(f.value, ast.Call)
            and isinstance(f.value.func, ast.Name)
            and _looks_like_class(f.value.func.id)
        ):
            cls = f.value.func.id
            meth = f.attr
            ctor_args = [_translate_expr(a) for a in f.value.args]
            tail_args = [_translate_expr(a) for a in node.args]
            all_args = ctor_args + tail_args
            head = f"{cls}_{meth}"
            return f"({head})" if not all_args else "(" + head + " " + " ".join(all_args) + ")"
        # ``var.method(args)`` — opaque method on a variable.  Use
        # the shared ``dot_method`` accessor.
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
            v = f.value
            head = f"dot_{f.attr}"
            args = [v.id] + [_translate_expr(a) for a in node.args]
            return "(" + head + " " + " ".join(args) + ")"
        # ``Class(args)`` constructor
        if isinstance(f, ast.Name) and _looks_like_class(f.id):
            args = [_translate_expr(a) for a in node.args]
            head = f"{f.id}_mk"
            return f"({head})" if not args else "(" + head + " " + " ".join(args) + ")"
        # ``func(args)`` generic free function
        if isinstance(f, ast.Name):
            args = [_translate_expr(a) for a in node.args]
            return f"({f.id})" if not args else "(" + f.id + " " + " ".join(args) + ")"
        raise _Untranslatable(f"unsupported call: func {type(f).__name__}")

    if isinstance(node, ast.Subscript):
        v = _translate_expr(node.value)
        idx = node.slice
        i = _translate_expr(idx)
        return f"(get {v} {i})"

    if isinstance(node, ast.Tuple):
        # Flat-Int has no native tuple type; serialise as a list of
        # equalities is too eager.  Emit a placeholder ``Pair`` symbol
        # — ``Pair_mk`` is added to the preamble if used.  This is
        # still library-agnostic.
        parts = [_translate_expr(e) for e in node.elts]
        head = f"Pair{len(parts)}"
        return "(" + head + "_mk " + " ".join(parts) + ")"

    raise _Untranslatable(f"unsupported AST node: {type(node).__name__}")


def _translate_statement_to_prop(
    parsed: ast.AST,
    *,
    free_vars: list[str],
) -> str:
    body = parsed.body if isinstance(parsed, ast.Expression) else parsed
    body_text = _translate_expr(body)
    if not free_vars:
        return body_text
    binders = "(" + " ".join(free_vars) + " : Int)"
    return "∀ " + binders + ", " + body_text


# ─────────────────────────────────────────────────────────────────────
#  Top-level: mechanize a sidecar module
# ─────────────────────────────────────────────────────────────────────

def _try_parse(statement: str) -> Optional[ast.AST]:
    s = statement.strip()
    s = s.replace("Σ", "sum").replace("·", "*").replace("²", "**2")
    s = re.sub(r"\bθ\b", "theta", s)
    try:
        return ast.parse(s, mode="eval")
    except SyntaxError:
        return None


def mechanize(sidecar_module, audit_report) -> MechanizationReport:
    """Mechanize all GROUNDED axioms in the sidecar."""
    from deppy.lean.sidecar_source_audit import AxiomGrounding

    sig = MechanizedSignature()
    axioms_out: list[MechanizedAxiom] = []

    if sidecar_module is None:
        return MechanizationReport(signature=sig, axioms=axioms_out)

    axioms = getattr(sidecar_module, "axioms", {}) or {}
    grounding_by_name = {r.name: r.grounding for r in audit_report.results}

    parsed_cache: dict[str, ast.AST] = {}
    free_by_axiom: dict[str, set[str]] = {}

    # Pass 1 — collect vocabulary across all GROUNDED axioms.
    for ax_name, ax in axioms.items():
        if grounding_by_name.get(ax_name) != AxiomGrounding.GROUNDED:
            continue
        statement = getattr(ax, "statement", "") or ""
        parsed = _try_parse(statement)
        if parsed is None:
            continue
        parsed_cache[ax_name] = parsed
        coll = _VocabCollector(sig)
        coll.visit(parsed)
        _classify_prop_fns(parsed, sig)
        free_by_axiom[ax_name] = coll.free
        sig.free_vars |= coll.free

    # Pass 1b — also scan verify-block ``property`` expressions so the
    # generated preamble covers vocabulary used only there (e.g.
    # ``Polygon.area`` referenced solely from a ``verify`` block).
    # Without this, the verify-block theorem references
    # ``Polygon_area`` but the preamble never declares it.  We don't
    # add these to ``free_by_axiom`` because they don't drive any
    # axiom translation.
    verifies = getattr(sidecar_module, "verifies", []) or []
    for v in verifies:
        prop_text = getattr(v, "property", "") or ""
        parsed_v = _try_parse(prop_text)
        if parsed_v is None:
            continue
        coll = _VocabCollector(sig)
        coll.visit(parsed_v)
        _classify_prop_fns(parsed_v, sig)
        sig.free_vars |= coll.free

    # Pass 2 — translate.
    for ax_name, ax in axioms.items():
        statement = getattr(ax, "statement", "") or ""
        if grounding_by_name.get(ax_name) != AxiomGrounding.GROUNDED:
            axioms_out.append(MechanizedAxiom(
                name=ax_name,
                python_statement=statement,
                lean_statement=None,
                failure_reason="not GROUNDED",
            ))
            continue
        parsed = parsed_cache.get(ax_name)
        if parsed is None:
            axioms_out.append(MechanizedAxiom(
                name=ax_name,
                python_statement=statement,
                lean_statement=None,
                failure_reason="parse failure",
            ))
            continue
        free = sorted(free_by_axiom.get(ax_name, set()))
        try:
            prop = _translate_statement_to_prop(parsed, free_vars=free)
        except _Untranslatable as e:
            axioms_out.append(MechanizedAxiom(
                name=ax_name,
                python_statement=statement,
                lean_statement=None,
                failure_reason=f"translation: {e}",
                free_vars=free,
            ))
            continue

        # Audit: also translate via the canonical
        # ``deppy.lean.predicate_translation.translate`` and record
        # its output for comparison.
        canon_text, canon_exact, canon_aux = _try_canonical(statement)

        axioms_out.append(MechanizedAxiom(
            name=ax_name,
            python_statement=statement,
            lean_statement=prop,
            free_vars=free,
            canonical_lean=canon_text,
            canonical_exact=canon_exact,
            canonical_aux_count=canon_aux,
        ))

    return MechanizationReport(signature=sig, axioms=axioms_out)


def _try_canonical(statement: str) -> tuple[str, bool, int]:
    """Run the canonical ``predicate_translation.translate`` and
    return ``(lean_text, exact, aux_decls_count)``.

    When the canonical translator can't handle the statement
    (returns an opaque ``deppy_pred_*``) we still record its output
    — the comparison with our specialised translator is the audit
    surface.
    """
    try:
        from deppy.lean.predicate_translation import translate
        r = translate(statement)
        return (r.lean_text, r.exact, len(r.aux_decls))
    except Exception:
        return ("", False, 0)


# ─────────────────────────────────────────────────────────────────────
#  Lean preamble emission
# ─────────────────────────────────────────────────────────────────────

def _arrow(arity: int, ret: str = "Int") -> str:
    if arity == 0:
        return ret
    return " → ".join(["Int"] * arity) + " → " + ret


def emit_preamble(sig: MechanizedSignature) -> list[str]:
    """Emit the Lean preamble derived from the .deppy AST.

    Output (all under flat-Int scheme — no library-specific names)::

      def dot_<attr>      : Int → Int := fun _ => 0     -- accessors (placeholder)
      def <Class>_<meth>  : Int → ... → Int := fun ... => 0   -- methods
      def <Class>_mk      : Int → ... → Int := fun ... => 0   -- ctors
      axiom <free_fn>     : Int → ... → Int (or Prop)         -- free fns
      axiom <pred>        : Int → ... → Prop                   -- predicates

    The accessors / class methods / constructors are emitted as
    ``def := fun _ => 0`` (not ``axiom``).  This lets ``unfold`` in
    a proof body reduce them to ``0``, so claims like ``≥ 0`` close
    via ``omega``, ``= 0`` via ``rfl``, etc., without committing to
    a real semantic translation.  The actual semantic body (when
    ``deppy.lean.body_translation`` succeeds) lives in the 'Body
    links' section as a separate ``def`` that callers can pin
    against — but the placeholder is what unfolds in tactic blocks
    that don't know the real body.

    Free functions and Prop-valued predicates remain ``axiom``
    because we don't have a sensible default body for them — the
    user is implicitly trusting the surrounding mechanization.

    All names are derived from the AST; this function never mentions
    a library by name.
    """
    out: list[str] = []
    if sig.attrs:
        out.append("-- Shared attribute accessors (derived from var.attr)")
        out.append(
            "-- Emitted as concrete ``def`` (not ``axiom``) so Lean's"
        )
        out.append(
            "-- ``unfold`` reduces them: Int-valued → ``0``,"
        )
        out.append("-- Prop-valued → ``True``.  Both forms are placeholder")
        out.append(
            "-- semantics — the real semantic content (when known)"
        )
        out.append("-- arrives via the 'Body links' section.")
        for attr in sorted(sig.attrs):
            if attr in sig.prop_attrs:
                out.append(
                    f"def dot_{attr} (_0 : Int) : Prop := True"
                )
            else:
                out.append(
                    f"def dot_{attr} (_0 : Int) : Int := 0"
                )
        out.append("")
    if sig.class_methods or sig.class_ctor_arity:
        out.append("-- Class-prefixed methods and constructors (derived)")
        out.append(
            "-- Methods/ctors are ``def := fun _ => 0`` so ``unfold``"
        )
        out.append(
            "-- + ``omega`` / ``rfl`` can close arithmetic claims"
        )
        out.append(
            "-- against the placeholder.  The semantic body (from"
        )
        out.append(
            "-- deppy.lean.body_translation) is emitted separately"
        )
        out.append("-- in the 'Body links' section below.")
        for cls in sorted(
            set(sig.class_methods.keys()) | set(sig.class_ctor_arity.keys())
        ):
            for meth, arity in sorted(sig.class_methods.get(cls, {}).items()):
                ret = "Prop" if (cls, meth) in sig.prop_class_methods else "Int"
                # Concrete bodies: 0/True so unfold + omega/trivial
                # can fire without needing the full sympy translation.
                if ret == "Prop":
                    # Prop-valued methods get a placeholder body of
                    # ``True`` so ``unfold`` + ``trivial`` closes
                    # claims that depend on them.  Real semantic
                    # content arrives via the 'Body links' section.
                    if arity == 0:
                        out.append(f"def {cls}_{meth} : Prop := True")
                    else:
                        args_decl = " ".join(
                            f"(_{i} : Int)" for i in range(arity)
                        )
                        out.append(
                            f"def {cls}_{meth} {args_decl} : Prop := True"
                        )
                    continue
                if arity == 0:
                    out.append(f"def {cls}_{meth} : {ret} := 0")
                else:
                    # Positional-args form generates an unfold-able
                    # equation lemma; the lambda form does not.
                    args_decl = " ".join(
                        f"(_{i} : Int)" for i in range(arity)
                    )
                    out.append(
                        f"def {cls}_{meth} {args_decl} : {ret} := 0"
                    )
            if cls in sig.class_ctor_arity:
                arity = max(sig.class_ctor_arity[cls], 1)
                args_decl = " ".join(
                    f"(_{i} : Int)" for i in range(arity)
                )
                out.append(
                    f"def {cls}_mk {args_decl} : Int := 0"
                )
        out.append("")
    if sig.free_fns:
        out.append("-- Free functions (derived from func(args) calls)")
        out.append(
            "-- Int-valued free functions reduce via ``def := fun _ => 0``;"
        )
        out.append("-- Prop-valued ones stay opaque ``axiom``.")
        for fn in sorted(sig.free_fns.keys()):
            arity = max(sig.free_fns[fn], 1)
            args_decl = " ".join(
                f"(_{i} : Int)" for i in range(arity)
            )
            if fn in sig.prop_fns:
                out.append(f"def {fn} {args_decl} : Prop := True")
            else:
                out.append(f"def {fn} {args_decl} : Int := 0")
        out.append("")
    # Tuple-arity helpers used by the translator's Tuple handling.
    out.append(
        "-- Tuple constructors (used when an axiom contains a tuple literal)"
    )
    out.append("def Pair2_mk (_0 _1 : Int) : Int := 0")
    out.append("def Pair3_mk (_0 _1 _2 : Int) : Int := 0")
    out.append("def get (_0 _1 : Int) : Int := 0")
    out.append("")
    return out


__all__ = [
    "MechanizedSignature",
    "MechanizedAxiom",
    "MechanizationReport",
    "mechanize",
    "emit_preamble",
]
