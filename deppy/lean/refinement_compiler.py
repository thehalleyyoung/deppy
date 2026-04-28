"""
deppy.lean.refinement_compiler — AST-based refinement-predicate compiler.

The legacy ``spec_translator`` matches predicates against ~30 hard-coded
regex patterns: anything that doesn't fit one of those patterns falls
through to ``sorry``.  In particular, *nested* predicates (``all(P(x)
for x in xs)``, ``any(...)``, list comprehensions, conditional
quantifiers, recursive predicates) have no support.

This module replaces that fallback with a full AST walker.  Given a
Python predicate as text, it parses to ``ast``, recursively translates
each node to a Lean 4 proposition, and emits a suggested tactic the
kernel can dispatch.

Public entry point::

    compile_refinement(predicate, params, param_types, return_type)
        → CompiledRefinement(lean_prop, tactic, sub_obligations)

When the AST contains a construct we cannot translate (e.g. an unknown
function call), the compiler returns an *honest* Refinement with a
``sorry`` tactic and the unparseable subterm logged in
``sub_obligations``.

This module is *purely* string + AST manipulation: no Z3, no kernel
imports, no external state.  The result is a Lean 4 proposition string
that the existing pipeline emits unchanged.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Any


# ───────────────────────────────────────────────────────────────────
#  Result dataclass
# ───────────────────────────────────────────────────────────────────

@dataclass
class CompiledRefinement:
    """Output of the refinement compiler.

    * ``lean_prop`` — the Lean 4 proposition (no ``theorem … :=`` wrapper).
    * ``tactic`` — a suggested ``by`` tactic; may be ``"sorry"`` for
      unhandled cases.
    * ``sub_obligations`` — sub-predicates the compiler couldn't
      discharge, each with a brief diagnostic.
    """
    lean_prop: str
    tactic: str = "sorry"
    sub_obligations: list[str] = field(default_factory=list)
    handled: bool = True   # False when the result contains a sorry


# ───────────────────────────────────────────────────────────────────
#  Compiler
# ───────────────────────────────────────────────────────────────────

class RefinementCompiler:
    """Walk a Python AST node and produce a Lean 4 proposition.

    The compiler tracks the current binding scope so quantifier
    variables introduced by ``all(... for x in xs)`` resolve before
    falling back to outer parameters.

    Soundness boundary: the compiler emits a ``by`` tactic that *should*
    discharge the resulting Lean proposition under standard arithmetic
    + list lemmas.  When the compiler isn't sure, it emits ``sorry``
    and marks ``handled=False`` so callers can route the obligation
    to Z3 or a counterexample search.
    """

    # Python comparison op → Lean infix.
    _CMP_OPS: dict[type, str] = {
        ast.Eq: "=",
        ast.NotEq: "≠",
        ast.Lt: "<",
        ast.LtE: "≤",
        ast.Gt: ">",
        ast.GtE: "≥",
    }

    # Python binop → Lean infix.
    _BIN_OPS: dict[type, str] = {
        ast.Add: "+",
        ast.Sub: "-",
        ast.Mult: "*",
        ast.Div: "/",
        ast.FloorDiv: "/",  # Lean Int division is floor division
        ast.Mod: "%",
        ast.Pow: "^",
    }

    # Python builtin → (Lean function, "function" or "method").
    _BUILTINS: dict[str, str] = {
        "len": "List.length",
        "abs": "Int.natAbs",
        "min": "min",
        "max": "max",
        "sum": "List.sum",
    }

    def __init__(self, *, params: list[str], app: str = "result") -> None:
        """Initialise with the parameter names and the surface
        ``result`` expression (typically ``(f x y)`` for the result of
        the function under spec).

        ``app`` is substituted for the literal name ``result`` when
        the predicate references the function's return value.
        """
        self.params = list(params)
        self.app = app
        # A stack of bound-variable names introduced by quantifiers.
        self._scope: list[str] = []
        # Sub-obligations the compiler couldn't translate.
        self._unhandled: list[str] = []

    # ── Top-level entry ──

    def compile(self, predicate: str) -> CompiledRefinement:
        """Parse ``predicate`` and translate to Lean 4."""
        try:
            tree = ast.parse(predicate, mode="eval").body
        except SyntaxError as e:
            return CompiledRefinement(
                lean_prop=f"True /- syntax error: {e!s} -/",
                tactic="sorry",
                sub_obligations=[f"syntax error: {predicate!r}"],
                handled=False,
            )
        prop = self._compile(tree)
        tactic = self._suggest_tactic(tree)
        handled = not self._unhandled
        if not handled:
            tactic = "sorry"
        return CompiledRefinement(
            lean_prop=prop,
            tactic=tactic,
            sub_obligations=list(self._unhandled),
            handled=handled,
        )

    # ── Recursive translation ──

    def _compile(self, node: ast.expr) -> str:
        if isinstance(node, ast.Constant):
            return self._compile_constant(node)
        if isinstance(node, ast.Name):
            return self._compile_name(node)
        if isinstance(node, ast.UnaryOp):
            return self._compile_unaryop(node)
        if isinstance(node, ast.BinOp):
            return self._compile_binop(node)
        if isinstance(node, ast.BoolOp):
            return self._compile_boolop(node)
        if isinstance(node, ast.Compare):
            return self._compile_compare(node)
        if isinstance(node, ast.IfExp):
            return self._compile_ifexp(node)
        if isinstance(node, ast.Call):
            return self._compile_call(node)
        if isinstance(node, ast.Subscript):
            return self._compile_subscript(node)
        if isinstance(node, ast.Attribute):
            return self._compile_attribute(node)
        if isinstance(node, ast.ListComp):
            return self._compile_listcomp(node)
        if isinstance(node, ast.GeneratorExp):
            # A bare generator-expr at the top level is unusual; treat
            # like a list-comp but warn.
            return self._compile_genexp(node)
        if isinstance(node, ast.List):
            return self._compile_list_literal(node)
        if isinstance(node, ast.Tuple):
            return self._compile_tuple_literal(node)
        # Unknown — emit a stub.
        text = ast.unparse(node)
        self._unhandled.append(f"unsupported expression: {text}")
        return f"sorry /- {text} -/"

    # ── Leaf translations ──

    def _compile_constant(self, node: ast.Constant) -> str:
        v = node.value
        if v is True:
            return "True"
        if v is False:
            return "False"
        if v is None:
            return "Unit.unit"
        if isinstance(v, bool):  # never reached after the True/False check
            return str(v)
        if isinstance(v, int):
            return str(v)
        if isinstance(v, float):
            return str(v)
        if isinstance(v, str):
            return f"\"{v}\""
        return f"sorry /- constant {v!r} -/"

    def _compile_name(self, node: ast.Name) -> str:
        name = node.id
        # ``result`` is the function-application expression.
        if name == "result":
            return self.app
        # Bound variable from an outer quantifier scope.
        if name in self._scope:
            return name
        # Function parameter.
        if name in self.params:
            return name
        # Free name — emit verbatim and let Lean handle.
        return name

    # ── Operators ──

    def _compile_unaryop(self, node: ast.UnaryOp) -> str:
        operand = self._compile(node.operand)
        if isinstance(node.op, ast.Not):
            return f"¬ ({operand})"
        if isinstance(node.op, ast.USub):
            return f"-({operand})"
        if isinstance(node.op, ast.UAdd):
            return operand
        self._unhandled.append(f"unary op {type(node.op).__name__}")
        return f"sorry /- unary {ast.unparse(node)} -/"

    def _compile_binop(self, node: ast.BinOp) -> str:
        left = self._compile(node.left)
        right = self._compile(node.right)
        op_t = type(node.op)
        if op_t in self._BIN_OPS:
            return f"({left} {self._BIN_OPS[op_t]} {right})"
        self._unhandled.append(f"binop {op_t.__name__}")
        return f"sorry /- binop {ast.unparse(node)} -/"

    def _compile_boolop(self, node: ast.BoolOp) -> str:
        parts = [self._compile(v) for v in node.values]
        joiner = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
        # Wrap each in parens for readability.
        return "(" + joiner.join(parts) + ")"

    def _compile_compare(self, node: ast.Compare) -> str:
        # Chained comparisons: a < b < c → (a < b) ∧ (b < c)
        left = self._compile(node.left)
        parts: list[str] = []
        prev = left
        for op, comp in zip(node.ops, node.comparators):
            right = self._compile(comp)
            op_t = type(op)
            if op_t in self._CMP_OPS:
                parts.append(f"({prev} {self._CMP_OPS[op_t]} {right})")
            elif op_t is ast.In:
                parts.append(self._compile_membership(prev, comp, negate=False))
            elif op_t is ast.NotIn:
                parts.append(self._compile_membership(prev, comp, negate=True))
            elif op_t is ast.Is:
                # ``x is None`` → ``x = none`` for Optional.
                if isinstance(comp, ast.Constant) and comp.value is None:
                    parts.append(f"({prev} = none)")
                else:
                    parts.append(f"({prev} = {right})")
            elif op_t is ast.IsNot:
                if isinstance(comp, ast.Constant) and comp.value is None:
                    parts.append(f"({prev} ≠ none)")
                else:
                    parts.append(f"({prev} ≠ {right})")
            else:
                self._unhandled.append(f"comparison {op_t.__name__}")
                parts.append(f"sorry /- {ast.unparse(node)} -/")
            prev = right
        if len(parts) == 1:
            return parts[0]
        return "(" + " ∧ ".join(parts) + ")"

    def _compile_membership(
        self, elem: str, container_node: ast.expr, *, negate: bool
    ) -> str:
        # ``x in [a, b, c]`` → ``x = a ∨ x = b ∨ x = c``
        if isinstance(container_node, (ast.List, ast.Tuple, ast.Set)):
            disjuncts = []
            for el in container_node.elts:
                disjuncts.append(f"({elem} = {self._compile(el)})")
            if not disjuncts:
                base = "False"
            else:
                base = "(" + " ∨ ".join(disjuncts) + ")"
            return f"¬ {base}" if negate else base
        # Otherwise standard ``∈``.
        container = self._compile(container_node)
        if negate:
            return f"({elem} ∉ {container})"
        return f"({elem} ∈ {container})"

    # ── Conditional ──

    def _compile_ifexp(self, node: ast.IfExp) -> str:
        c = self._compile(node.test)
        t = self._compile(node.body)
        e = self._compile(node.orelse)
        return f"(if {c} then {t} else {e})"

    # ── Calls (the interesting case for nested predicates) ──

    def _compile_call(self, node: ast.Call) -> str:
        # Quantifier calls: all(...) / any(...).
        if isinstance(node.func, ast.Name):
            if node.func.id == "all" and len(node.args) == 1:
                return self._compile_quantifier(node.args[0], universal=True)
            if node.func.id == "any" and len(node.args) == 1:
                return self._compile_quantifier(node.args[0], universal=False)
            if node.func.id in self._BUILTINS:
                return self._compile_builtin_call(node)
        # Method call.
        if isinstance(node.func, ast.Attribute):
            return self._compile_method_call(node)
        # Generic call.
        fname = self._compile(node.func)
        args = " ".join(self._compile(a) for a in node.args)
        if not args:
            return fname
        return f"({fname} {args})"

    def _compile_builtin_call(self, node: ast.Call) -> str:
        assert isinstance(node.func, ast.Name)
        name = node.func.id
        lean_name = self._BUILTINS[name]
        if name == "len" and len(node.args) == 1:
            arg = self._compile(node.args[0])
            return f"{arg}.length"
        if name == "abs" and len(node.args) == 1:
            arg = self._compile(node.args[0])
            return f"(if {arg} < 0 then -{arg} else {arg})"
        if name in {"min", "max"} and len(node.args) >= 2:
            args = [self._compile(a) for a in node.args]
            result = args[0]
            for a in args[1:]:
                result = f"({lean_name} {result} {a})"
            return result
        if name == "sum" and len(node.args) == 1:
            arg = self._compile(node.args[0])
            return f"{arg}.sum"
        # Default: prefix application.
        args = " ".join(self._compile(a) for a in node.args)
        return f"({lean_name} {args})"

    def _compile_quantifier(
        self, gen_node: ast.expr, *, universal: bool
    ) -> str:
        """Translate ``all(P(x) for x in xs if Q(x))`` (or any).

        Lean form: ``∀ x ∈ xs, Q x → P x`` (universal) or
        ``∃ x ∈ xs, Q x ∧ P x`` (existential).
        """
        if not isinstance(gen_node, ast.GeneratorExp):
            self._unhandled.append("quantifier without generator-expr")
            return f"sorry /- {ast.unparse(gen_node)} -/"

        if len(gen_node.generators) != 1:
            self._unhandled.append("nested quantifier (>1 for-clause)")
            return f"sorry /- {ast.unparse(gen_node)} -/"

        comp = gen_node.generators[0]
        if not isinstance(comp.target, ast.Name):
            self._unhandled.append("quantifier target is not a name")
            return f"sorry /- {ast.unparse(gen_node)} -/"

        var = comp.target.id
        # Translate the iterator: range(n), range(lo, hi), or a list expr.
        iter_text = self._compile_iterator(comp.iter)

        # Push the bound variable onto the scope.
        self._scope.append(var)
        try:
            body = self._compile(gen_node.elt)
            # Apply ``if`` filters.
            guards = [self._compile(g) for g in comp.ifs]
        finally:
            self._scope.pop()

        if universal:
            # ∀ x ∈ xs, (g₁ ∧ g₂ ∧ …) → body
            if guards:
                guard = " ∧ ".join(f"({g})" for g in guards)
                return f"(∀ {var} ∈ {iter_text}, ({guard}) → {body})"
            return f"(∀ {var} ∈ {iter_text}, {body})"
        else:
            if guards:
                guard = " ∧ ".join(f"({g})" for g in guards)
                return f"(∃ {var} ∈ {iter_text}, ({guard}) ∧ {body})"
            return f"(∃ {var} ∈ {iter_text}, {body})"

    def _compile_iterator(self, node: ast.expr) -> str:
        """Translate the iterator of a comprehension to a Lean
        finset-or-list expression."""
        # range(n) → (List.range n)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "range":
            args = node.args
            if len(args) == 1:
                hi = self._compile(args[0])
                return f"(List.range {hi})"
            if len(args) == 2:
                lo = self._compile(args[0])
                hi = self._compile(args[1])
                return f"(List.range' {lo} ({hi} - {lo}))"
        # range(lo, hi) handled above; otherwise compile as list expression.
        return self._compile(node)

    def _compile_method_call(self, node: ast.Call) -> str:
        """Method calls — ``s.startswith(p)``, ``xs.append(x)``, etc."""
        assert isinstance(node.func, ast.Attribute)
        recv = self._compile(node.func.value)
        method = node.func.attr
        args = [self._compile(a) for a in node.args]

        # String methods.
        if method == "startswith" and len(args) == 1:
            return f"({recv}.startsWith {args[0]})"
        if method == "endswith" and len(args) == 1:
            return f"({recv}.endsWith {args[0]})"
        # List methods.
        if method == "append" and len(args) == 1:
            return f"({recv} ++ [{args[0]}])"
        if method == "get" and len(args) == 2:
            # d.get(k, default) → d.find? k |>.getD default
            return f"({recv}.find? {args[0]} |>.getD {args[1]})"
        if method in {"keys", "values", "items"}:
            self._unhandled.append(f"dict.{method}() in predicate")
            return f"sorry /- {ast.unparse(node)} -/"
        # Generic method: recv.method args
        if not args:
            return f"({recv}.{method})"
        return f"({recv}.{method} {' '.join(args)})"

    # ── Subscript and attribute ──

    def _compile_subscript(self, node: ast.Subscript) -> str:
        recv = self._compile(node.value)
        idx = self._compile(node.slice)
        return f"({recv}[{idx}]!)"  # `!` panic-on-out-of-bounds; predicate context

    def _compile_attribute(self, node: ast.Attribute) -> str:
        recv = self._compile(node.value)
        return f"{recv}.{node.attr}"

    # ── List comprehensions ──

    def _compile_listcomp(self, node: ast.ListComp) -> str:
        """``[f(x) for x in xs if g(x)]`` → ``(xs.filter g).map f``.

        We restrict to single-clause comprehensions; nested for-clauses
        are emitted as a sorry.
        """
        if len(node.generators) != 1:
            self._unhandled.append("multi-for list comprehension")
            return f"sorry /- {ast.unparse(node)} -/"
        comp = node.generators[0]
        if not isinstance(comp.target, ast.Name):
            self._unhandled.append("listcomp target is not a name")
            return f"sorry /- {ast.unparse(node)} -/"
        var = comp.target.id
        iter_text = self._compile_iterator(comp.iter)
        self._scope.append(var)
        try:
            body = self._compile(node.elt)
            guards = [self._compile(g) for g in comp.ifs]
        finally:
            self._scope.pop()

        # Build (xs.filter (fun x => g₁ ∧ g₂)).map (fun x => body)
        if guards:
            guard = " ∧ ".join(f"({g})" for g in guards)
            filtered = f"({iter_text}.filter (fun {var} => {guard}))"
        else:
            filtered = iter_text
        if body == var:
            # Identity map — collapse.
            return filtered
        return f"({filtered}.map (fun {var} => {body}))"

    def _compile_genexp(self, node: ast.GeneratorExp) -> str:
        """A bare generator-expr — treat as a list comprehension."""
        # Re-build as a ListComp and recurse.
        listcomp = ast.ListComp(
            elt=node.elt,
            generators=node.generators,
        )
        return self._compile_listcomp(listcomp)

    def _compile_list_literal(self, node: ast.List) -> str:
        elems = ", ".join(self._compile(e) for e in node.elts)
        return f"[{elems}]"

    def _compile_tuple_literal(self, node: ast.Tuple) -> str:
        elems = ", ".join(self._compile(e) for e in node.elts)
        return f"({elems})"

    # ── Tactic suggestion ──

    def _suggest_tactic(self, node: ast.expr) -> str:
        """Pick a Lean tactic likely to discharge ``node``.

        Heuristics:
          * Unhandled subterm → ``sorry``.
          * Quantifier (``all`` / ``any``) → ``intros`` then arithmetic
            / simp combinator (covers both pure-arithmetic bodies and
            list-shaped iterators).
          * Predicate involving list ops (``.map``, ``.filter``,
            ``.length``, list comprehension) → mixed combinator: try
            omega first (handles ``len(xs) == len(ys)`` arithmetic),
            then simp with list lemmas.
          * Pure arithmetic → ``omega``.
          * Boolean combination → combinator that handles both pure
            arithmetic and structural simp.
        """
        if self._unhandled:
            return "sorry"

        is_quantifier = (
            isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in {"all", "any"}
        )
        has_list = self._has_list_op(node)

        if is_quantifier:
            # ``intros`` opens the binder; the body then handles via the
            # standard combinator.
            return (
                "by intros; first | omega | "
                "simp_all [List.length, List.map, List.filter, List.range] | "
                "trivial"
            )
        if has_list:
            return (
                "by first | omega | "
                "simp [List.length, List.map, List.filter, List.range] | "
                "trivial"
            )
        if isinstance(node, ast.Compare):
            return "by omega"
        if isinstance(node, ast.BoolOp):
            return "by first | omega | simp_all | trivial"
        if isinstance(node, ast.BinOp):
            return "by omega"
        return "by first | omega | simp_all | trivial"

    def _has_list_op(self, node: ast.expr) -> bool:
        """Walk ``node`` looking for any list-shaped operation that
        rules out pure-omega discharge.  Triggers ``simp`` instead. """
        for sub in ast.walk(node):
            if isinstance(sub, (ast.ListComp, ast.GeneratorExp)):
                return True
            if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name) \
                    and sub.func.id == "len":
                return True
            if isinstance(sub, ast.Attribute) and sub.attr in {
                "map", "filter", "append", "length", "find", "find?",
                "startsWith", "endsWith", "startswith", "endswith",
            }:
                return True
            if isinstance(sub, ast.Subscript):
                # `xs[i]` is a list/dict op for proof purposes.
                return True
        return False


# ───────────────────────────────────────────────────────────────────
#  Public entry point
# ───────────────────────────────────────────────────────────────────

def compile_refinement(
    predicate: str,
    *,
    params: list[str],
    param_types: dict[str, Any] | None = None,
    return_type: Any = None,
    func_app: str = "result",
) -> CompiledRefinement:
    """Compile a Python refinement predicate to a Lean 4 proposition.

    ``params`` lists the function's parameter names so they can be
    used as free variables in the predicate.

    ``param_types`` and ``return_type`` are accepted for API symmetry
    with ``spec_translator`` but currently aren't used by the AST
    walker (they'll matter when type-aware tactic selection is
    plugged in).

    ``func_app`` is the surface form used to render ``result``
    (typically ``"(f x y)"`` for a function ``f`` with parameters
    ``x``, ``y``).

    Returns a :class:`CompiledRefinement`.
    """
    _ = param_types, return_type  # reserved for future type-aware tactics
    compiler = RefinementCompiler(params=params, app=func_app)
    return compiler.compile(predicate)


__all__ = [
    "CompiledRefinement",
    "RefinementCompiler",
    "compile_refinement",
]
