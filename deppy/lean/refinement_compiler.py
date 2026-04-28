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
        → CompiledRefinement(lean_prop, tactic, sub_obligations,
                             proof_term)

The ``proof_term`` field is a kernel-level :class:`ProofTerm` (when
constructible) so the kernel can structurally re-check the predicate
*without* the Lean toolchain hop.  The chain becomes:

    Python predicate → Lean tactic + structural ProofTerm
                     → kernel checks ProofTerm directly

When the AST contains a construct we cannot translate (e.g. an unknown
function call), the compiler returns an *honest* Refinement with a
``sorry`` tactic and the unparseable subterm logged in
``sub_obligations``; ``proof_term`` is then ``None``.

This module is *almost* purely string + AST manipulation; it imports
the kernel ``ProofTerm`` hierarchy lazily inside the constructor
helpers so the AST translation paths remain side-effect free.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from deppy.core.kernel import ProofTerm


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
    * ``proof_term`` — a kernel-level :class:`ProofTerm` matching the
      predicate's structural shape (Z3Proof for arithmetic / membership,
      PathComp for ``and``, Cases for ``or``, Structural for quantifiers,
      Cong for list-comprehension equalities).  ``None`` when no clean
      structural witness is available, in which case downstream code
      should fall back to the Lean tactic.
    """
    lean_prop: str
    tactic: str = "sorry"
    sub_obligations: list[str] = field(default_factory=list)
    handled: bool = True   # False when the result contains a sorry
    proof_term: "ProofTerm | None" = None


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

    def __init__(
        self,
        *,
        params: list[str],
        app: str = "result",
        param_types: dict[str, Any] | None = None,
    ) -> None:
        """Initialise with the parameter names and the surface
        ``result`` expression (typically ``(f x y)`` for the result of
        the function under spec).

        ``app`` is substituted for the literal name ``result`` when
        the predicate references the function's return value.

        ``param_types`` is forwarded into the optional Z3 binders dict
        we attach to constructed Z3Proof terms; supplying it lets the
        kernel use the typed Z3 encoder.
        """
        self.params = list(params)
        self.app = app
        self.param_types = dict(param_types or {})
        # A stack of bound-variable names introduced by quantifiers.
        self._scope: list[str] = []
        # Sub-obligations the compiler couldn't translate.
        self._unhandled: list[str] = []
        # When True, ``_proof_term`` saw a sub-AST it can't structurally
        # witness; the caller drops the proof_term and falls back to the
        # Lean tactic.  This is set on encountering features like
        # quantifier-with-filter or unknown function calls.
        self._proof_unhandled: bool = False

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
                proof_term=None,
            )
        prop = self._compile(tree)
        tactic = self._suggest_tactic(tree)
        handled = not self._unhandled
        if not handled:
            tactic = "sorry"
        # Build the kernel-level ProofTerm shadow.  This walks the same
        # AST but produces ``deppy.core.kernel.ProofTerm`` nodes (Z3Proof,
        # PathComp, Cases, Cong, Structural).  Failures are silent — we
        # fall back to ``proof_term=None`` so callers route through the
        # Lean tactic instead.
        proof_term: "ProofTerm | None" = None
        if handled:
            try:
                proof_term = self._build_proof_term(tree, prop)
            except Exception:
                proof_term = None
            if self._proof_unhandled:
                proof_term = None
        return CompiledRefinement(
            lean_prop=prop,
            tactic=tactic,
            sub_obligations=list(self._unhandled),
            handled=handled,
            proof_term=proof_term,
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

    # ── Kernel ProofTerm construction ──

    def _build_proof_term(
        self, node: ast.expr, lean_prop: str,
    ) -> "ProofTerm | None":
        """Construct a kernel :class:`ProofTerm` mirroring ``node``.

        The returned term is a *structural shadow* of the AST: it lets
        the kernel re-check the predicate without invoking Lean.  The
        shape rules are:

        * Pure arithmetic / membership / comparison           → ``Z3Proof``
          (the Z3 encoder handles ``in``, ``len``, ``+``, ``*``, etc.)
        * ``and``                                              → ``PathComp``
        * ``or``                                               → ``Cases``
        * Universal/existential quantifier (``all`` / ``any``) → ``Structural``
        * Equality whose RHS is a list comprehension           → ``Cong``
        * Conditional ``IfExp``                                → ``Cases``

        Anything outside these shapes (unknown calls, multi-clause
        comprehensions, free names with no Z3 encoding) sets
        ``self._proof_unhandled`` and the caller drops the term.
        """
        # Local imports — kernel pulls in z3 transitively, which is
        # heavy; do it lazily so AST translation is cheap when the
        # caller never inspects the proof_term.
        from deppy.core.kernel import (
            Cases, Cong, PathComp, Refl, Structural, Z3Proof,
        )
        from deppy.core.types import Var

        binders = self._z3_binders_for(node)

        # ── Equality with list-comp RHS → Cong over Refl ──
        if (
            isinstance(node, ast.Compare)
            and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)
            and isinstance(node.comparators[0], (ast.ListComp, ast.GeneratorExp))
        ):
            comp = node.comparators[0]
            # Use the comprehension's iterator + body as the function
            # description.  ``Cong(f, Refl(x))`` says "applying f to a
            # reflexive equality yields the result equality".
            try:
                map_label = ast.unparse(comp.elt)
            except Exception:
                map_label = "map_body"
            return Cong(func=Var(name=f"map({map_label})"),
                        proof=Refl(term=Var(name=lean_prop)))

        # ── Quantifier (all / any) → Structural ──
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in {"all", "any"}
        ):
            kind = "universal" if node.func.id == "all" else "existential"
            try:
                desc = ast.unparse(node)
            except Exception:
                desc = node.func.id
            # Quantifier bodies aren't generally Z3-encodable as-is, so
            # we surface the obligation as a Structural witness; the
            # body's discharge is left to the Lean tactic.
            return Structural(
                description=f"{kind}_over_list: {desc}",
            )

        # ── BoolOp ── ``and`` → PathComp; ``or`` → Cases.
        if isinstance(node, ast.BoolOp):
            sub_terms: list[Any] = []
            for v in node.values:
                sub = self._build_proof_term(v, self._compile(v))
                if sub is None:
                    self._proof_unhandled = True
                    return None
                sub_terms.append(sub)
            if not sub_terms:
                return None
            if isinstance(node.op, ast.And):
                # Left-associative chain of PathComp.
                t = sub_terms[0]
                for nxt in sub_terms[1:]:
                    t = PathComp(left_path=t, right_path=nxt)
                return t
            # Or → Cases over a synthetic scrutinee with one branch
            # per disjunct.  The kernel records the branches as a list
            # of ``(pattern, proof)`` pairs.
            try:
                scrut_label = ast.unparse(node)
            except Exception:
                scrut_label = "or_scrutinee"
            branches: list[tuple[str, Any]] = [
                (f"alt_{i}", t) for i, t in enumerate(sub_terms)
            ]
            return Cases(scrutinee=Var(name=scrut_label), branches=branches)

        # ── IfExp → Cases on the test ──
        if isinstance(node, ast.IfExp):
            then_t = self._build_proof_term(node.body, self._compile(node.body))
            else_t = self._build_proof_term(node.orelse, self._compile(node.orelse))
            if then_t is None or else_t is None:
                self._proof_unhandled = True
                return None
            try:
                test_label = ast.unparse(node.test)
            except Exception:
                test_label = "ifexp_test"
            return Cases(
                scrutinee=Var(name=test_label),
                branches=[("then", then_t), ("else", else_t)],
            )

        # ── Unary not — wrap inner.  If inner is Z3, produce a
        #    negated-formula Z3Proof; else fall through to Z3 with the
        #    full lean_prop so the kernel can dispatch.
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return Z3Proof(formula=lean_prop, binders=binders)

        # ── Pure arithmetic / membership / comparison → Z3Proof ──
        if isinstance(node, (ast.Compare, ast.BinOp, ast.UnaryOp,
                             ast.Constant)):
            return Z3Proof(formula=lean_prop, binders=binders)

        # ── A bare ``len(xs)`` etc. — Z3 encoder handles List.length ─
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id in self._BUILTINS:
                return Z3Proof(formula=lean_prop, binders=binders)

        # ── Bare Name as a boolean predicate (e.g. an alias for True) ──
        if isinstance(node, ast.Name):
            return Z3Proof(formula=lean_prop, binders=binders)

        # Anything else: signal we don't have a clean structural proof.
        self._proof_unhandled = True
        return None

    def _z3_binders_for(self, node: ast.expr) -> dict[str, str]:
        """Build the binders dict for a ``Z3Proof`` from the parameter
        annotations.

        The kernel's typed Z3 encoder accepts annotation *strings*
        (e.g. ``"int"``, ``"list[int]"``), so we stringify whatever
        annotation we have.  Free names that aren't in ``param_types``
        are omitted; the kernel falls back to its heuristic encoder
        for those.
        """
        binders: dict[str, str] = {}
        # Determine which names actually appear in this AST node.
        names: set[str] = set()
        for sub in ast.walk(node):
            if isinstance(sub, ast.Name):
                names.add(sub.id)
        for name in names:
            if name in self.param_types:
                ann = self.param_types[name]
                # Stringify type annotation (handle bare types and
                # generic aliases).
                if isinstance(ann, str):
                    binders[name] = ann
                else:
                    text = getattr(ann, "__name__", None) or repr(ann)
                    binders[name] = text
        return binders

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

    ``param_types`` is forwarded into the ``binders`` dict of any
    ``Z3Proof`` we attach to the result, so the kernel can use the
    typed Z3 encoder.  ``return_type`` is accepted for API symmetry
    with ``spec_translator`` but isn't currently used.

    ``func_app`` is the surface form used to render ``result``
    (typically ``"(f x y)"`` for a function ``f`` with parameters
    ``x``, ``y``).

    Returns a :class:`CompiledRefinement` with the Lean proposition,
    suggested tactic, sub-obligations, and (when constructible) a
    kernel-level :class:`ProofTerm` shadowing the predicate's structural
    shape.
    """
    _ = return_type  # reserved for future type-aware tactics
    compiler = RefinementCompiler(
        params=params, app=func_app, param_types=param_types,
    )
    return compiler.compile(predicate)


def extract_proof_term(
    predicate: str,
    *,
    params: list[str],
    param_types: dict[str, Any] | None = None,
    return_type: Any = None,
    func_app: str = "result",
) -> "ProofTerm | None":
    """Convenience wrapper that returns just the ``proof_term`` field
    of :func:`compile_refinement`, or ``None`` when the predicate
    can't be structurally witnessed.

    Use this when you already have a Lean proposition / tactic in hand
    (e.g. the legacy regex catalogue produced one) and only want the
    kernel-level :class:`ProofTerm` so the kernel can re-check the
    obligation directly.
    """
    cr = compile_refinement(
        predicate,
        params=params,
        param_types=param_types,
        return_type=return_type,
        func_app=func_app,
    )
    return cr.proof_term


__all__ = [
    "CompiledRefinement",
    "RefinementCompiler",
    "compile_refinement",
    "extract_proof_term",
]
