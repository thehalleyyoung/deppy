"""AST-based result substitution for ``@implies(post)`` predicates.

Audit fix #11
=============

Postcondition predicates passed to ``@implies(precondition,
postcondition)`` may reference ``result`` to mean the function's
return value::

    @implies("x > 0", "result > 0")
    def f(x: int) -> int:
        return x + 1

When deppy lowers this to a Lean theorem, ``result`` must be replaced
with the function call expression ``(f x)``.  The original
implementation used Python's ``str.replace``::

    post_with_result = post_py.replace("result", f"({fn_name} ...)")

This was unsound because ``str.replace`` is purely textual:

* ``"result_count > 0"`` was rewritten to ``"(f x)_count > 0"``,
  which is syntactically wrong — ``result_count`` is a *different
  identifier*.
* ``"len(result) > 0 and 'result' in xs"`` had the string-literal
  ``'result'`` rewritten to ``'(f x)'`` — semantically wrong.
* ``"results == [1,2,3]"`` was rewritten because ``results`` contains
  ``result`` as a prefix.

The fix replaces the textual substitution with an AST-based one:
parse the predicate, find every ``Name(id="result")`` node, replace
it with the function-call expression's AST, and unparse.  Strings,
comments, and identifiers that merely *contain* the substring
``result`` are left alone.

The substitution also handles:

* ``isinstance(result, T)`` — properly substitutes the argument.
* ``result.attr`` — attribute access on the call result.
* ``result[0]`` — indexing the call result.
* ``f(result, x)`` — passing as an argument.
* ``[result, x]``, ``(result, x)``, ``{result: x}`` — within
  containers.
* nested expressions of any depth.

Public API
----------

::

    rewritten_text = substitute_result(
        post_py: str,
        *,
        fn_name: str,
        arg_names: list[str],
        result_var: str = "result",
    ) -> str

Soundness: when the predicate fails to parse (uncommon — the
@implies decorator should reject malformed predicates earlier in
the pipeline), we fall back to *not* substituting and returning the
original text.  The Lean translator will then surface a typecheck
error that points at the actual mistake, which is better than
silently emitting wrong code.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Optional


@dataclass
class SubstitutionResult:
    """Output of :func:`substitute_result_detailed`."""
    text: str
    occurrences: int
    used_string_literal_safe: bool
    parse_failed: bool = False
    notes: list[str] = None  # type: ignore[assignment]

    def __post_init__(self):
        if self.notes is None:
            self.notes = []


def substitute_result(
    post_py: str, *, fn_name: str, arg_names: list[str],
    result_var: str = "result",
) -> str:
    """Replace every free ``result_var`` in ``post_py`` with
    ``fn_name(arg1, arg2, ...)`` AST-style and return the unparsed
    result.

    See :func:`substitute_result_detailed` for the structured
    return value.
    """
    return substitute_result_detailed(
        post_py, fn_name=fn_name, arg_names=arg_names,
        result_var=result_var,
    ).text


def substitute_result_detailed(
    post_py: str, *, fn_name: str, arg_names: list[str],
    result_var: str = "result",
) -> SubstitutionResult:
    """Same as :func:`substitute_result` but returns a structured
    :class:`SubstitutionResult` describing how the substitution went."""
    notes: list[str] = []

    if not post_py:
        return SubstitutionResult(
            text="True", occurrences=0,
            used_string_literal_safe=True, parse_failed=False,
            notes=["empty post → True"],
        )

    try:
        tree = ast.parse(post_py, mode="eval")
    except SyntaxError as e:
        notes.append(f"parse failed: {e}")
        return SubstitutionResult(
            text=post_py, occurrences=0,
            used_string_literal_safe=False, parse_failed=True,
            notes=notes,
        )

    rewriter = _ResultRewriter(
        fn_name=fn_name, arg_names=list(arg_names),
        result_var=result_var,
    )
    new_body = rewriter.visit(tree.body)
    ast.fix_missing_locations(new_body)
    try:
        new_text = ast.unparse(new_body)
    except Exception as e:
        notes.append(f"unparse failed: {e}")
        return SubstitutionResult(
            text=post_py, occurrences=0,
            used_string_literal_safe=False, parse_failed=True,
            notes=notes,
        )
    return SubstitutionResult(
        text=new_text,
        occurrences=rewriter.count,
        used_string_literal_safe=True,
        parse_failed=False,
        notes=notes,
    )


class _ResultRewriter(ast.NodeTransformer):
    """Replace ``Name(id=result_var)`` nodes with the function call.

    The rewriter is careful to:

    * Skip ``Constant`` nodes whose value is a string — those are
      string literals, and the substring ``result`` inside them
      must not be touched.
    * Skip ``arg`` nodes (parameter declarations) — but our
      predicates don't normally contain those.
    * Recursively rewrite into all child positions: ``Call.args``,
      ``Compare.left``, ``BinOp.left/right``, ``Subscript.value``,
      ``Attribute.value``, etc.  The base ``ast.NodeTransformer``
      walks all of these by default through ``generic_visit``.
    """

    def __init__(
        self, *, fn_name: str, arg_names: list[str],
        result_var: str,
    ) -> None:
        super().__init__()
        self.fn_name = fn_name
        self.arg_names = arg_names
        self.result_var = result_var
        self.count = 0

    def visit_Name(self, node: ast.Name) -> ast.AST:
        if node.id == self.result_var:
            self.count += 1
            return self._call_ast()
        return node

    def visit_Constant(self, node: ast.Constant) -> ast.AST:
        # Don't recurse into string constants — they may contain
        # the substring ``result`` but those are user-authored
        # message strings, not references to the return value.
        return node

    def visit_arg(self, node: ast.arg) -> ast.AST:
        # ``arg`` nodes appear in lambda / comprehension binders.
        # The user's predicate may write ``lambda result: ...`` —
        # but that's a *binding*, not a use of the function's
        # return value.  Leave it alone.
        if node.arg == self.result_var:
            # Note: we keep the binder but rewrite uses inside the
            # body separately.  Since this is a NodeTransformer
            # we'd need to scope-track — for now we just return
            # the binder unchanged and accept that
            # ``lambda result: result + 1`` will still get its body
            # rewritten.  In practice nobody writes this.
            pass
        return node

    def visit_Lambda(self, node: ast.Lambda) -> ast.AST:
        # When the lambda binds ``result`` itself, do NOT rewrite
        # its body's ``result`` references — they're shadowed.
        binders = {a.arg for a in (node.args.args or [])}
        binders |= {a.arg for a in (
            getattr(node.args, "posonlyargs", None) or []
        )}
        binders |= {a.arg for a in (
            getattr(node.args, "kwonlyargs", None) or []
        )}
        if self.result_var in binders:
            return node  # don't recurse — fully shadowed
        return self.generic_visit(node)

    def visit_comprehension(self, node):
        # generators / comprehensions also bind names — but the
        # user typically wouldn't bind `result` in one.  We handle
        # the simple case (no shadowing) by recursing.
        return self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> ast.AST:
        return self._handle_comp(node)

    def visit_ListComp(self, node: ast.ListComp) -> ast.AST:
        return self._handle_comp(node)

    def visit_SetComp(self, node: ast.SetComp) -> ast.AST:
        return self._handle_comp(node)

    def visit_DictComp(self, node: ast.DictComp) -> ast.AST:
        return self._handle_comp(node)

    def _handle_comp(self, node):
        # Collect bound names from comprehension generators.
        bound: set[str] = set()
        for gen in getattr(node, "generators", []):
            for n in _names_in_target(gen.target):
                bound.add(n)
        if self.result_var in bound:
            # The comprehension binds ``result`` — its body and
            # filters may legitimately reference the bound name.
            # We can still rewrite the *iterables*, but not the
            # body or filters.  For simplicity we leave the
            # comprehension untouched in this case.
            return node
        return self.generic_visit(node)

    def _call_ast(self) -> ast.Call:
        return ast.Call(
            func=ast.Name(id=self.fn_name, ctx=ast.Load()),
            args=[
                ast.Name(id=name, ctx=ast.Load())
                for name in self.arg_names
            ],
            keywords=[],
        )


def _names_in_target(node: ast.expr) -> list[str]:
    """Return the names a comprehension target binds."""
    if isinstance(node, ast.Name):
        return [node.id]
    if isinstance(node, (ast.Tuple, ast.List)):
        out: list[str] = []
        for elt in node.elts:
            out.extend(_names_in_target(elt))
        return out
    if isinstance(node, ast.Starred):
        return _names_in_target(node.value)
    return []


# ─────────────────────────────────────────────────────────────────────
#  Convenience helpers for the certificate generator
# ─────────────────────────────────────────────────────────────────────


def render_call_text(fn_name: str, arg_names: list[str]) -> str:
    """Render the function call text in Lean prefix-style: ``(f x y)``.

    The certificate generator already emits Lean function calls in
    this form, so callers can use this helper when they need the
    *Lean* call form rather than the Python form returned by
    :func:`substitute_result`.
    """
    if not arg_names:
        return fn_name
    return "(" + fn_name + " " + " ".join(arg_names) + ")"


def substitute_result_lean(
    post_lean_or_py: str, *, fn_name: str, arg_names: list[str],
    result_var: str = "result",
) -> str:
    """Replace ``result_var`` with the Lean prefix-call ``(f x y)``.

    Audit fix (round 2): the previous implementation used an AST
    pass to substitute a placeholder, then a final ``str.replace``
    to swap the placeholder's Python-call rendering for the Lean
    prefix-call form.  That last ``str.replace`` was the same
    pattern audit fix #11 said was a cheat — safe in practice
    because the placeholder was unique, but conceptually the same
    textual substitution it claimed to remove.

    The new implementation is purely AST-driven: a custom unparser
    walks the rewritten AST and emits Lean syntax directly when it
    encounters the placeholder Call node.  No textual replacement
    occurs after AST processing.
    """
    if not post_lean_or_py:
        return "True"
    try:
        tree = ast.parse(post_lean_or_py, mode="eval")
    except SyntaxError:
        return post_lean_or_py
    rewriter = _ResultRewriter(
        fn_name=_LEAN_PREFIX_PLACEHOLDER, arg_names=list(arg_names),
        result_var=result_var,
    )
    new_body = rewriter.visit(tree.body)
    ast.fix_missing_locations(new_body)
    # Render to Lean using a custom unparser that recognises the
    # placeholder Call node and emits ``(fn_name x y)``.
    return _LeanUnparser(
        fn_name=fn_name, arg_names=list(arg_names),
    ).visit(new_body)


# Sentinel name used to mark the rewriter's substituted Call nodes.
# Distinct from any real Python identifier (starts with underscore-
# digit which is invalid as a Python name in source) so the
# unparser can recognise it without ambiguity.
_LEAN_PREFIX_PLACEHOLDER = "_0deppy_result_placeholder"


class _LeanUnparser(ast.NodeVisitor):
    """Render a (rewritten) Python AST as Lean predicate syntax.

    Only handles the AST shapes the @implies decorator and the
    result rewriter produce: comparisons, BoolOps, BinOps, Calls,
    Attributes, Subscripts, Names, Constants, IfExps, Tuples,
    Lists, UnaryOps.  Other shapes fall back to ``ast.unparse``.

    The unparser recognises the rewriter's placeholder Call node
    and renders it as ``(fn_name arg1 arg2 ...)`` — Lean prefix-
    call syntax — directly in the AST traversal.  No textual
    post-processing.
    """

    def __init__(self, *, fn_name: str, arg_names: list[str]) -> None:
        self.fn_name = fn_name
        self.arg_names = arg_names

    def visit(self, node) -> str:  # type: ignore[override]
        method = "visit_" + type(node).__name__
        handler = getattr(self, method, None)
        if handler is None:
            try:
                return ast.unparse(node)
            except Exception:
                return repr(node)
        return handler(node)

    def visit_Constant(self, node: ast.Constant) -> str:
        v = node.value
        if v is True:
            return "True"
        if v is False:
            return "False"
        if v is None:
            return "()"
        if isinstance(v, str):
            return repr(v)
        return repr(v)

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_BoolOp(self, node: ast.BoolOp) -> str:
        op = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
        parts = [self.visit(v) for v in node.values]
        return "(" + op.join(parts) + ")"

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        inner = self.visit(node.operand)
        if isinstance(node.op, ast.Not):
            return f"(¬ {inner})"
        if isinstance(node.op, ast.USub):
            return f"(-{inner})"
        if isinstance(node.op, ast.UAdd):
            return inner
        return ast.unparse(node)

    def visit_Compare(self, node: ast.Compare) -> str:
        op_map = {
            ast.Eq: "=", ast.NotEq: "≠",
            ast.Lt: "<", ast.LtE: "≤",
            ast.Gt: ">", ast.GtE: "≥",
        }
        if len(node.ops) == 1:
            op_t = type(node.ops[0])
            if op_t in op_map:
                l = self.visit(node.left)
                r = self.visit(node.comparators[0])
                return f"({l} {op_map[op_t]} {r})"
            if isinstance(node.ops[0], ast.In):
                l = self.visit(node.left)
                r = self.visit(node.comparators[0])
                return f"({l} ∈ {r})"
            if isinstance(node.ops[0], ast.NotIn):
                l = self.visit(node.left)
                r = self.visit(node.comparators[0])
                return f"({l} ∉ {r})"
        return ast.unparse(node)

    def visit_BinOp(self, node: ast.BinOp) -> str:
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "%",
        }
        op = op_map.get(type(node.op), None)
        if op is None:
            return ast.unparse(node)
        l = self.visit(node.left)
        r = self.visit(node.right)
        return f"({l} {op} {r})"

    def visit_Call(self, node: ast.Call) -> str:
        # Recognise the result-substitution placeholder and emit
        # the Lean prefix-call directly.
        if (isinstance(node.func, ast.Name)
                and node.func.id == _LEAN_PREFIX_PLACEHOLDER):
            if not self.arg_names:
                return self.fn_name
            return (
                "(" + self.fn_name + " "
                + " ".join(self.arg_names) + ")"
            )
        # Generic Lean call: prefix-form ``(f arg1 arg2 ...)``.
        if isinstance(node.func, ast.Name):
            args = [self.visit(a) for a in node.args]
            if not args:
                return f"({node.func.id})"
            return "(" + node.func.id + " " + " ".join(args) + ")"
        if isinstance(node.func, ast.Attribute):
            recv = self.visit(node.func.value)
            args = [self.visit(a) for a in node.args]
            if not args:
                return f"({recv}.{node.func.attr})"
            return f"({recv}.{node.func.attr} " + " ".join(args) + ")"
        return ast.unparse(node)

    def visit_Attribute(self, node: ast.Attribute) -> str:
        inner = self.visit(node.value)
        return f"{inner}.{node.attr}"

    def visit_Subscript(self, node: ast.Subscript) -> str:
        recv = self.visit(node.value)
        slc = self.visit(node.slice)
        return f"{recv}[{slc}]"

    def visit_IfExp(self, node: ast.IfExp) -> str:
        cond = self.visit(node.test)
        t = self.visit(node.body)
        e = self.visit(node.orelse)
        return f"(if {cond} then {t} else {e})"

    def visit_Tuple(self, node: ast.Tuple) -> str:
        parts = [self.visit(e) for e in node.elts]
        return "(" + ", ".join(parts) + ")"

    def visit_List(self, node: ast.List) -> str:
        parts = [self.visit(e) for e in node.elts]
        return "[" + ", ".join(parts) + "]"


# ─────────────────────────────────────────────────────────────────────
#  Detection helpers — for callers that want to know if substitution
#  *would* occur.
# ─────────────────────────────────────────────────────────────────────


def references_result(
    post_py: str, *, result_var: str = "result",
) -> bool:
    """Return True iff the predicate references ``result_var`` as a
    free identifier (i.e., not inside a shadowing binder).
    """
    try:
        tree = ast.parse(post_py or "True", mode="eval")
    except SyntaxError:
        return False
    finder = _NameFinder(result_var)
    finder.visit(tree.body)
    return finder.found


class _NameFinder(ast.NodeVisitor):
    def __init__(self, target: str) -> None:
        self.target = target
        self.found = False
        self._shadow_stack: list[set[str]] = []

    def visit_Name(self, node: ast.Name) -> None:
        if self.found:
            return
        if any(self.target in s for s in self._shadow_stack):
            return
        if node.id == self.target:
            self.found = True

    def visit_Lambda(self, node: ast.Lambda) -> None:
        binders = {a.arg for a in (node.args.args or [])}
        self._shadow_stack.append(binders)
        try:
            self.generic_visit(node)
        finally:
            self._shadow_stack.pop()

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._handle_comp(node)

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._handle_comp(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._handle_comp(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._handle_comp(node)

    def _handle_comp(self, node):
        bound: set[str] = set()
        for gen in getattr(node, "generators", []):
            for n in _names_in_target(gen.target):
                bound.add(n)
        self._shadow_stack.append(bound)
        try:
            self.generic_visit(node)
        finally:
            self._shadow_stack.pop()


def count_result_references(
    post_py: str, *, result_var: str = "result",
) -> int:
    """Return the number of free references to ``result_var``."""
    try:
        tree = ast.parse(post_py or "True", mode="eval")
    except SyntaxError:
        return 0
    counter = _NameCounter(result_var)
    counter.visit(tree.body)
    return counter.count


class _NameCounter(ast.NodeVisitor):
    def __init__(self, target: str) -> None:
        self.target = target
        self.count = 0
        self._shadow_stack: list[set[str]] = []

    def visit_Name(self, node: ast.Name) -> None:
        if any(self.target in s for s in self._shadow_stack):
            return
        if node.id == self.target:
            self.count += 1

    def visit_Lambda(self, node: ast.Lambda) -> None:
        binders = {a.arg for a in (node.args.args or [])}
        self._shadow_stack.append(binders)
        try:
            self.generic_visit(node)
        finally:
            self._shadow_stack.pop()

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._handle_comp(node)

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._handle_comp(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._handle_comp(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._handle_comp(node)

    def _handle_comp(self, node):
        bound: set[str] = set()
        for gen in getattr(node, "generators", []):
            for n in _names_in_target(gen.target):
                bound.add(n)
        self._shadow_stack.append(bound)
        try:
            self.generic_visit(node)
        finally:
            self._shadow_stack.pop()


__all__ = [
    "SubstitutionResult",
    "substitute_result",
    "substitute_result_detailed",
    "substitute_result_lean",
    "render_call_text",
    "references_result",
    "count_result_references",
]
