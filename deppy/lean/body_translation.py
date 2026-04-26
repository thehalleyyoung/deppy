"""Python function-body → Lean 4 definition translator.

The deppy pipeline already translates *types* and *predicates* to
Lean.  For "Lean as the gold standard" the certificate also needs a
Lean *definition* of each Python function so theorems about the
function are well-typed.  This module translates a function body
best-effort:

* arithmetic (Int / Float / Bool) — direct
* if/elif/else → ``if-then-else``
* return — bound through to the result
* recursive self-calls — preserved
* list ops: ``xs[:n]`` → ``xs.take n``; ``xs[n:]`` → ``xs.drop n``;
  ``xs[i]`` → ``xs.get!``
* ``len(xs)`` → ``xs.length``
* function calls — preserved (the callee must also have a Lean
  definition or be in scope)

When a body uses constructs we can't translate, the function emits
``sorry`` for the body — the user fills it in (or accepts the
weaker ``Lean has not validated the body`` note).

Public API::

    translate_body(fn_node, *, type_context, predicate_registry=None)
        → BodyTranslation(lean_text, exact, sorry_count, notes)
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class BodyTranslation:
    """Result of translating a single function body to Lean."""
    lean_text: str
    exact: bool = True
    sorry_count: int = 0
    notes: list[str] = field(default_factory=list)


def translate_body(
    fn_node,
    *,
    type_context=None,
    predicate_registry: Optional[dict[str, str]] = None,
) -> BodyTranslation:
    """Translate ``fn_node``'s body into a Lean expression.

    The expression returned matches the Lean definition's body — i.e.
    it should be wrapped in ``def fn_name : ... := <body>`` by the
    caller.  Recursive self-calls in the body refer to the Lean
    function name unchanged.
    """
    if fn_node is None or not getattr(fn_node, "body", None):
        return BodyTranslation(lean_text="sorry", exact=False, sorry_count=1)

    translator = _BodyT(
        fn_name=fn_node.name,
        type_context=type_context,
        predicate_registry=predicate_registry or {},
    )
    try:
        text = translator.visit_block(fn_node.body)
    except _Untranslatable as e:
        return BodyTranslation(
            lean_text="sorry",
            exact=False,
            sorry_count=1,
            notes=[f"untranslatable body: {e}"],
        )
    return BodyTranslation(
        lean_text=text,
        exact=translator.exact,
        sorry_count=translator.sorry_count,
        notes=translator.notes,
    )


class _Untranslatable(Exception):
    pass


_BIN_OPS_LEAN = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
    ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "%",
    ast.BitAnd: "&&&", ast.BitOr: "|||", ast.BitXor: "^^^",
}

_CMP_LEAN = {
    ast.Eq: "==", ast.NotEq: "!=",
    ast.Lt: "<", ast.LtE: "≤",
    ast.Gt: ">", ast.GtE: "≥",
}


class _BodyT:
    """Stateful walker.  Tracks ``sorry`` insertions and notes."""

    def __init__(
        self, fn_name: str,
        type_context, predicate_registry: dict[str, str],
    ) -> None:
        self.fn_name = fn_name
        self.ctx = type_context
        self.preds = predicate_registry
        self.exact = True
        self.sorry_count = 0
        self.notes: list[str] = []

    def _sorry(self, why: str) -> str:
        self.exact = False
        self.sorry_count += 1
        self.notes.append(why)
        return "sorry"

    # -- block / statement entry ---------------------------------------

    def visit_block(self, stmts: list[ast.stmt]) -> str:
        """Translate a function/method body — a list of statements
        ending in (ideally) a ``return``.

        We recognise these shapes:

        * ``return e`` alone → translate ``e``.
        * ``if cond: ... else: ...`` whose branches both return →
          emit ``if cond then T else F``.
        * Sequenced ``a = e ; ...`` (assignments) → emit
          ``let a := e ; ...`` chained.
        * Anything else falls back to ``sorry``.
        """
        return self._fold_stmts(stmts)

    def _fold_stmts(self, stmts: list[ast.stmt]) -> str:
        if not stmts:
            return self._sorry("empty body")

        # Strip leading docstring.
        if (isinstance(stmts[0], ast.Expr)
                and isinstance(stmts[0].value, ast.Constant)
                and isinstance(stmts[0].value.value, str)):
            stmts = stmts[1:]
            if not stmts:
                return self._sorry("docstring-only body")

        head = stmts[0]
        rest = stmts[1:]

        if isinstance(head, ast.Return):
            if rest:
                self.notes.append(
                    "code after return ignored in Lean translation"
                )
            return self._visit_expr(head.value) if head.value else "()"

        if isinstance(head, ast.If):
            then_terminal = self._stmts_terminal(head.body)
            else_terminal = (
                self._stmts_terminal(head.orelse) if head.orelse else False
            )
            # Three workable shapes:
            #   1. ``if ... return ; else ... return``   (both terminal)
            #   2. ``if ... return ; rest ...``          (then terminal,
            #       rest treated as else)
            #   3. ``if ... rest ; else ... return``     (else terminal,
            #       symmetric — translate as ``if not cond then else
            #       else then`` essentially).
            if then_terminal:
                cond = self._visit_expr(head.test)
                t = self._fold_stmts(head.body)
                if head.orelse:
                    e = self._fold_stmts(head.orelse)
                    if rest and not else_terminal:
                        # Both else and rest exist — append rest after else.
                        e = self._fold_stmts(list(head.orelse) + rest)
                else:
                    # No else — rest IS the else.
                    e = (
                        self._fold_stmts(rest) if rest
                        else self._sorry("if-then with no else and no fall-through")
                    )
                return f"if {cond} then {t} else {e}"
            if else_terminal and head.orelse:
                # Mirror case: pull the else as the terminal arm.
                cond = self._visit_expr(head.test)
                t_body = self._fold_stmts(list(head.body) + rest)
                e = self._fold_stmts(head.orelse)
                return f"if {cond} then {t_body} else {e}"
            # Neither branch is terminal — bail.
            return self._sorry("if without terminal branches")

        if isinstance(head, ast.Assign) and len(head.targets) == 1:
            tgt = head.targets[0]
            if isinstance(tgt, ast.Name):
                value = self._visit_expr(head.value)
                tail = self._fold_stmts(rest)
                return f"let {tgt.id} := {value};\n  {tail}"
            return self._sorry("non-Name assignment target")

        if isinstance(head, ast.AnnAssign) and isinstance(head.target, ast.Name):
            if head.value is None:
                # type-only declaration — skip.
                return self._fold_stmts(rest)
            value = self._visit_expr(head.value)
            tail = self._fold_stmts(rest)
            return f"let {head.target.id} := {value};\n  {tail}"

        if isinstance(head, ast.AugAssign) and isinstance(head.target, ast.Name):
            op = _BIN_OPS_LEAN.get(type(head.op))
            if op is None:
                return self._sorry("unsupported augmented assign")
            value = self._visit_expr(head.value)
            tail = self._fold_stmts(rest)
            return (
                f"let {head.target.id} := {head.target.id} {op} {value};\n"
                f"  {tail}"
            )

        if isinstance(head, ast.Pass):
            return self._fold_stmts(rest)

        return self._sorry(
            f"unsupported statement {type(head).__name__}",
        )

    @staticmethod
    def _stmts_terminal(stmts: list[ast.stmt]) -> bool:
        if not stmts:
            return False
        last = stmts[-1]
        return isinstance(last, (ast.Return, ast.Raise))

    # -- expressions ---------------------------------------------------

    def _visit_expr(self, node: Optional[ast.expr]) -> str:
        if node is None:
            return "()"

        if isinstance(node, ast.Constant):
            v = node.value
            if v is None:
                return "()"
            if v is True:
                return "true"
            if v is False:
                return "false"
            if isinstance(v, int):
                return str(v)
            if isinstance(v, float):
                return repr(v)
            if isinstance(v, str):
                return f"\"{v}\""
            return self._sorry(f"unsupported constant {v!r}")

        if isinstance(node, ast.Name):
            return node.id

        if isinstance(node, ast.UnaryOp):
            inner = self._visit_expr(node.operand)
            if isinstance(node.op, ast.Not):
                return f"¬ ({inner})"
            if isinstance(node.op, ast.USub):
                return f"-({inner})"
            if isinstance(node.op, ast.UAdd):
                return inner
            return self._sorry(
                f"unsupported unary op {type(node.op).__name__}"
            )

        if isinstance(node, ast.BinOp):
            op = _BIN_OPS_LEAN.get(type(node.op))
            if op is None:
                return self._sorry(
                    f"unsupported binary op {type(node.op).__name__}"
                )
            l = self._visit_expr(node.left)
            r = self._visit_expr(node.right)
            return f"({l} {op} {r})"

        if isinstance(node, ast.BoolOp):
            sep = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
            parts = [self._visit_expr(v) for v in node.values]
            return "(" + sep.join(parts) + ")"

        if isinstance(node, ast.Compare):
            return self._visit_compare(node)

        if isinstance(node, ast.Call):
            return self._visit_call(node)

        if isinstance(node, ast.Subscript):
            return self._visit_subscript(node)

        if isinstance(node, ast.IfExp):
            cond = self._visit_expr(node.test)
            t = self._visit_expr(node.body)
            e = self._visit_expr(node.orelse)
            return f"if {cond} then {t} else {e}"

        if isinstance(node, ast.List):
            elts = [self._visit_expr(e) for e in node.elts]
            return "[" + ", ".join(elts) + "]"

        if isinstance(node, ast.Tuple):
            parts = [self._visit_expr(e) for e in node.elts]
            return "(" + ", ".join(parts) + ")"

        return self._sorry(f"unsupported expression {type(node).__name__}")

    def _visit_compare(self, node: ast.Compare) -> str:
        if len(node.ops) == 1:
            op_t = type(node.ops[0])
            if op_t in _CMP_LEAN:
                l = self._visit_expr(node.left)
                r = self._visit_expr(node.comparators[0])
                return f"({l} {_CMP_LEAN[op_t]} {r})"
        # Chained: a < b < c → (a < b) ∧ (b < c)
        terms = [node.left] + list(node.comparators)
        parts: list[str] = []
        for op, l_node, r_node in zip(node.ops, terms, terms[1:]):
            op_t = type(op)
            if op_t not in _CMP_LEAN:
                return self._sorry(f"unsupported comparator {op_t.__name__}")
            l = self._visit_expr(l_node)
            r = self._visit_expr(r_node)
            parts.append(f"({l} {_CMP_LEAN[op_t]} {r})")
        return "(" + " ∧ ".join(parts) + ")"

    def _visit_call(self, node: ast.Call) -> str:
        if isinstance(node.func, ast.Name):
            fn = node.func.id
            if fn == "len" and len(node.args) == 1:
                return f"({self._visit_expr(node.args[0])}.length)"
            if fn == "abs" and len(node.args) == 1:
                return f"(Int.natAbs {self._visit_expr(node.args[0])})"
            if fn == "min" and len(node.args) == 2:
                return f"(min {self._visit_expr(node.args[0])} {self._visit_expr(node.args[1])})"
            if fn == "max" and len(node.args) == 2:
                return f"(max {self._visit_expr(node.args[0])} {self._visit_expr(node.args[1])})"
            # Self-recursive call.
            if fn == self.fn_name:
                args = [self._visit_expr(a) for a in node.args]
                return f"({fn} " + " ".join(args) + ")"
            # Generic function call.
            args = [self._visit_expr(a) for a in node.args]
            return f"({fn} " + " ".join(args) + ")"
        if isinstance(node.func, ast.Attribute):
            recv = self._visit_expr(node.func.value)
            method = node.func.attr
            args = [self._visit_expr(a) for a in node.args]
            return f"({recv}.{method} " + " ".join(args) + ")"
        return self._sorry("call to non-name/attribute")

    def _visit_subscript(self, node: ast.Subscript) -> str:
        recv = self._visit_expr(node.value)
        slc = node.slice
        if isinstance(slc, ast.Slice):
            lower = (
                self._visit_expr(slc.lower) if slc.lower is not None else "0"
            )
            upper = self._visit_expr(slc.upper) if slc.upper is not None else None
            if slc.step is not None:
                return self._sorry("slice step not supported")
            if upper is None:
                return f"({recv}.drop {lower})"
            if lower == "0":
                return f"({recv}.take {upper})"
            return f"(({recv}.drop {lower}).take ({upper} - {lower}))"
        idx = self._visit_expr(slc)
        return f"({recv}.get! ({idx}.toNat))"


__all__ = [
    "BodyTranslation",
    "translate_body",
]
