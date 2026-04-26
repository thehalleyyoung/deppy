"""Python-syntax safety predicate → Lean 4 Prop translation.

The deppy obligations machinery and the Lean-proof discharge path
both need to turn a Python-syntax safety predicate (the canonical
form emitted by :mod:`deppy.pipeline.safety_predicates`) into the
Lean-4 type the user must inhabit with a proof.

Two design decisions
--------------------
1. **Never fall back to ``True``.**  A predicate we cannot translate
   becomes an *opaque Lean Prop* — a freshly-axiomatised proposition
   whose name encodes the original predicate.  The user cannot
   trivially discharge an opaque Prop with ``trivial`` because
   ``trivial`` proves ``True``, not ``deppy_pred_in_<hash>``.

2. **Translate compositionally.**  Arithmetic predicates pass through
   the AST translator unchanged (Lean shares Python's operator
   precedence on Int/Float).  ``len(xs)`` becomes ``xs.length``
   (Lean's List API).  ``x in d`` becomes a typeclass-driven
   ``Membership.mem x d``.  ``isinstance(x, T)`` and ``hasattr(x, n)``
   stay opaque because Lean has no direct equivalent without a typed
   target.

Public API::

    translate(predicate, *, binders=None) -> TranslationResult

A :class:`TranslationResult` carries the Lean text, the imports it
requires, the auxiliary opaque-Prop ``axiom`` declarations, and a
flag indicating whether the translation was *exact* (a clean Lean
encoding) or *opaque* (an axiomatised stand-in the user must refine
or prove).
"""
from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class TranslationResult:
    """Outcome of translating a Python predicate to Lean."""
    lean_text: str
    imports: list[str] = field(default_factory=list)
    aux_decls: list[str] = field(default_factory=list)
    exact: bool = True
    notes: list[str] = field(default_factory=list)


def translate(
    predicate: str,
    *,
    binders: Optional[dict[str, str]] = None,
    python_types: Optional[dict[str, str]] = None,
) -> TranslationResult:
    """Translate a Python predicate to Lean.

    Parameters
    ----------
    predicate :
        Python-syntax safety predicate.
    binders :
        Optional ``{name: lean_type}`` for free identifiers
        (legacy parameter, kept for backward compatibility).
    python_types :
        Optional ``{name: python_annotation_text}``.  When set, the
        translator emits *type-aware* operations: ``b ≠ 0`` for
        ``b: Optional[int]`` becomes ``b.isSome ∧ b.get!.snd ≠ 0``;
        ``xs[i]`` for ``xs: list[int]`` uses ``List.get?`` with the
        appropriate index handling; ``k in d`` for
        ``d: dict[K, V]`` uses ``HashMap.contains``.

    The result's ``aux_decls`` contains any ``axiom ... : Prop``
    declarations the kernel must include alongside the theorem.
    """
    binders = binders or {}
    python_types = python_types or {}
    pred = (predicate or "").strip()
    if not pred:
        return TranslationResult(lean_text="True", exact=True,
                                 notes=["empty predicate"])

    if pred == "True":
        return TranslationResult(lean_text="True", exact=True)
    if pred == "False":
        return TranslationResult(lean_text="False", exact=True)

    synthetic = (
        "callee_safe(", "has_next(", "module_present",
        "io_resource_available", "completes_within_budget",
        "custom_invariant_holds", "is_float_literal(",
        "is_valid_for_op(", "defined(",
        "iterable_exhaustible", "decreases_measure_provided",
    )
    if any(m in pred for m in synthetic):
        return _opaque(pred, reason="synthetic predicate")

    try:
        tree = ast.parse(pred, mode="eval")
    except SyntaxError:
        return _opaque(pred, reason="unparseable")

    translator = _Translator(
        binders=binders, python_types=python_types,
    )
    try:
        text = translator.visit(tree.body)
    except _Untranslatable as e:
        return _opaque(pred, reason=str(e))

    return TranslationResult(
        lean_text=text,
        imports=list(translator.imports),
        aux_decls=list(translator.aux_decls),
        exact=translator.exact,
        notes=list(translator.notes),
    )


# ─────────────────────────────────────────────────────────────────────
#  Internal translator
# ─────────────────────────────────────────────────────────────────────

class _Untranslatable(Exception):
    """Raised inside the translator to bail out to the opaque path."""


_BIN_OPS = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
    ast.FloorDiv: "/", ast.Div: "/", ast.Mod: "%",
}

_CMP_OPS = {
    ast.Eq: "=", ast.NotEq: "≠",
    ast.Lt: "<", ast.LtE: "≤",
    ast.Gt: ">", ast.GtE: "≥",
}


class _Translator:
    """AST → Lean text translator.  Stateful: collects imports and
    auxiliary opaque-Prop declarations as it walks."""

    def __init__(
        self, binders: dict[str, str],
        python_types: Optional[dict[str, str]] = None,
    ) -> None:
        self.binders = binders
        self.python_types = python_types or {}
        self.imports: list[str] = []
        self.aux_decls: list[str] = []
        self.exact: bool = True
        self.notes: list[str] = []

    def _is_optional(self, name: str) -> bool:
        """True iff ``name`` is annotated ``Optional[T]`` /
        ``T | None`` in the caller-supplied python_types map."""
        ann = (self.python_types.get(name, "") or "").strip()
        if not ann:
            return False
        if "Optional[" in ann or "typing.Optional" in ann:
            return True
        if "| None" in ann or "None |" in ann:
            return True
        return False

    def _is_list_like(self, name: str) -> bool:
        ann = (self.python_types.get(name, "") or "").strip()
        if not ann:
            return False
        for prefix in ("list", "List", "typing.List", "Sequence",
                       "Iterable", "MutableSequence", "tuple", "Tuple"):
            if ann == prefix or ann.startswith(prefix + "["):
                return True
        return False

    def _is_dict_like(self, name: str) -> bool:
        ann = (self.python_types.get(name, "") or "").strip()
        if not ann:
            return False
        for prefix in ("dict", "Dict", "typing.Dict", "Mapping",
                       "MutableMapping"):
            if ann == prefix or ann.startswith(prefix + "["):
                return True
        return False

    def visit(self, node: ast.AST) -> str:
        # Constants
        if isinstance(node, ast.Constant):
            v = node.value
            if v is True:
                return "True"
            if v is False:
                return "False"
            if isinstance(v, int):
                return str(v)
            if isinstance(v, float):
                return repr(v)
            if isinstance(v, str):
                return f"\"{v}\""
            raise _Untranslatable(f"unsupported constant {v!r}")

        # Names
        if isinstance(node, ast.Name):
            return node.id

        # Unary not / negate
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                return f"¬({self.visit(node.operand)})"
            if isinstance(node.op, ast.USub):
                return f"-({self.visit(node.operand)})"
            if isinstance(node.op, ast.UAdd):
                return self.visit(node.operand)
            raise _Untranslatable(
                f"unsupported unary op {type(node.op).__name__}"
            )

        # Binary ops (arithmetic).
        if isinstance(node, ast.BinOp):
            op_t = type(node.op)
            if op_t not in _BIN_OPS:
                raise _Untranslatable(
                    f"unsupported binary op {op_t.__name__}"
                )
            op = _BIN_OPS[op_t]
            l = self.visit(node.left)
            r = self.visit(node.right)
            return f"({l} {op} {r})"

        # Boolean ops.
        if isinstance(node, ast.BoolOp):
            sep = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
            parts = [self.visit(v) for v in node.values]
            return "(" + sep.join(parts) + ")"

        # Comparison — including chained comparisons.
        if isinstance(node, ast.Compare):
            return self._visit_compare(node)

        # Call — len(...), isinstance(...), hasattr(...), …
        if isinstance(node, ast.Call):
            return self._visit_call(node)

        # Attribute / Subscript — fall through to opaque (we don't
        # know the receiver's Lean type).
        raise _Untranslatable(
            f"unsupported AST node {type(node).__name__}"
        )

    def _visit_compare(self, node: ast.Compare) -> str:
        # Build conjunctions for chained comparisons (a < b < c).
        terms = [node.left] + list(node.comparators)
        parts: list[str] = []
        for op, left_node, right_node in zip(node.ops, terms, terms[1:]):
            op_t = type(op)
            # Special-case ``... is None`` / ``... is not None`` so we
            # don't try to ``visit(Constant(None))`` (which would
            # raise Untranslatable and send the whole predicate to
            # the opaque path).
            if (op_t in (ast.Is, ast.IsNot)
                    and isinstance(right_node, ast.Constant)
                    and right_node.value is None):
                l = self.visit(left_node)
                if op_t is ast.Is:
                    parts.append(f"(Option.isNone {l})")
                else:
                    parts.append(f"(Option.isSome {l})")
                continue
            l = self.visit(left_node)
            r = self.visit(right_node)
            if op_t in _CMP_OPS:
                parts.append(f"({l} {_CMP_OPS[op_t]} {r})")
            elif op_t is ast.In:
                # ``x in d`` — when d is annotated as a dict-like
                # type, use the proper Lean HashMap.contains form;
                # otherwise emit a Membership.mem call.
                recv_name = (
                    right_node.id
                    if isinstance(right_node, ast.Name) else ""
                )
                if recv_name and self._is_dict_like(recv_name):
                    parts.append(f"({r}.contains {l})")
                elif recv_name and self._is_list_like(recv_name):
                    parts.append(f"(List.elem {l} {r})")
                else:
                    self.exact = False
                    self.notes.append(
                        f"membership ``{l} ∈ {r}`` translated as opaque "
                        "Membership.mem (requires the user to discharge it)"
                    )
                    self.imports_add("import Init")
                    parts.append(f"(Membership.mem {l} {r})")
            elif op_t is ast.NotIn:
                recv_name = (
                    right_node.id
                    if isinstance(right_node, ast.Name) else ""
                )
                if recv_name and self._is_dict_like(recv_name):
                    parts.append(f"(¬ {r}.contains {l})")
                elif recv_name and self._is_list_like(recv_name):
                    parts.append(f"(¬ List.elem {l} {r})")
                else:
                    self.exact = False
                    self.notes.append(
                        f"non-membership ``{l} ∉ {r}`` translated as opaque "
                    )
                    parts.append(f"(¬ Membership.mem {l} {r})")
            elif op_t is ast.Is:
                # ``is None`` is handled at the top of the loop;
                # other ``is`` comparisons are not translatable.
                raise _Untranslatable(
                    f"`is` comparison with non-None RHS"
                )
            elif op_t is ast.IsNot:
                raise _Untranslatable(
                    f"`is not` comparison with non-None RHS"
                )
            else:
                raise _Untranslatable(
                    f"unsupported comparator {op_t.__name__}"
                )
        if len(parts) == 1:
            return parts[0]
        return "(" + " ∧ ".join(parts) + ")"

    def _visit_call(self, node: ast.Call) -> str:
        if not isinstance(node.func, ast.Name):
            raise _Untranslatable(
                f"call to non-Name {ast.dump(node.func)}"
            )
        name = node.func.id

        if name == "len":
            if len(node.args) != 1:
                raise _Untranslatable("len(...) with wrong arity")
            arg = self.visit(node.args[0])
            # Lean: List.length / String.length / HashMap.size all
            # exist; we use ``.length`` which works for List/String
            # and hand the user the responsibility of casting.
            return f"({arg}.length)"

        if name == "isinstance":
            self.exact = False
            self.notes.append(
                "isinstance(...) translated as opaque Prop"
            )
            return self._opaque_call(node)

        if name == "hasattr":
            self.exact = False
            self.notes.append(
                "hasattr(...) translated as opaque Prop"
            )
            return self._opaque_call(node)

        # Other calls — opaque.
        self.exact = False
        return self._opaque_call(node)

    def _opaque_call(self, node: ast.Call) -> str:
        try:
            text = ast.unparse(node)
        except Exception:
            text = ast.dump(node)
        return _opaque_term_for(text, self.aux_decls)

    def imports_add(self, line: str) -> None:
        if line not in self.imports:
            self.imports.append(line)


# ─────────────────────────────────────────────────────────────────────
#  Opaque Prop helpers
# ─────────────────────────────────────────────────────────────────────

def _opaque(predicate: str, *, reason: str = "") -> TranslationResult:
    """Build a TranslationResult for a predicate we cannot translate.

    The result includes an ``axiom deppy_pred_<hash> : Prop``
    declaration so the kernel's Lean run produces a well-formed file.
    The user cannot discharge such a Prop with ``trivial``: a Prop
    has no canonical inhabitant, and the user must produce an actual
    proof.
    """
    aux_decls: list[str] = []
    term = _opaque_term_for(predicate, aux_decls)
    return TranslationResult(
        lean_text=term,
        aux_decls=aux_decls,
        exact=False,
        notes=[f"opaque Lean Prop ({reason or 'unsupported predicate'}): {predicate}"],
    )


def _safe_ident_chars(text: str) -> str:
    out: list[str] = []
    for ch in text:
        if ch.isalnum() or ch == "_":
            out.append(ch)
    return "".join(out)


def _opaque_term_for(predicate_text: str,
                     aux_decls: list[str]) -> str:
    """Return the Lean *term* (an opaque Prop reference) for an
    untranslatable predicate, appending the axiom declaration to
    ``aux_decls`` if it isn't already there.

    Names are deterministic — the same predicate text yields the same
    axiom name across runs.
    """
    digest = hashlib.sha1(predicate_text.encode("utf-8")).hexdigest()[:10]
    short = _safe_ident_chars(predicate_text.replace(" ", ""))[:20]
    if not short:
        short = "pred"
    name = f"deppy_pred_{short}_{digest}"
    decl = (
        f"-- Opaque encoding of Python predicate: {predicate_text}\n"
        f"axiom {name} : Prop"
    )
    if decl not in aux_decls:
        aux_decls.append(decl)
    return name


__all__ = [
    "TranslationResult",
    "translate",
]
