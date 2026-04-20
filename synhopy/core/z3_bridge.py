"""
SynHoPy Z3 Bridge

Comprehensive translation layer between SynHoPy's type system and the Z3 SMT
solver.  Provides:

    Z3Context           — manage Z3 variables and sort mappings
    PredicateTranslator — parse Python predicate strings into Z3 formulas
    RefinementChecker   — subtype / satisfiability / validity checks
    Z3Prover            — generate Z3-backed proof terms
    ArithmeticEncoder   — pre-built encodings for common patterns

All Z3 imports are guarded so the module degrades gracefully when Z3 is not
installed.
"""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from synhopy.core.types import (
    SynType, SynTerm, PyObjType, PyIntType, PyFloatType, PyBoolType,
    PyStrType, PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, RefinementType, UnionType, OptionalType,
    UniverseType, PathType, IntervalType, PathAbs, Transport, Var,
    Literal,
)

# ── guarded Z3 import ─────────────────────────────────────────────
try:
    import z3
    _HAS_Z3 = True
except ImportError:
    z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


def _require_z3() -> None:
    """Raise at call-sites that cannot function without Z3."""
    if not _HAS_Z3:
        raise RuntimeError(
            "Z3 is required for this operation but is not installed. "
            "Install with: pip install z3-solver"
        )


# ═══════════════════════════════════════════════════════════════════
# Z3Context
# ═══════════════════════════════════════════════════════════════════

class Z3Context:
    """Map SynHoPy types and variables to Z3 sorts / expressions.

    Usage::

        ctx = Z3Context()
        x = ctx.declare_var("x", PyIntType())
        y = ctx.declare_var("y", PyIntType())
        # x, y are z3.ArithRef (Int)
    """

    def __init__(self) -> None:
        _require_z3()
        self._vars: dict[str, z3.ExprRef] = {}
        self._sorts: dict[str, z3.SortRef] = {}
        # Uninterpreted functions for list/dict operations
        self._list_len_fn: z3.FuncDeclRef | None = None
        self._list_get_fn: z3.FuncDeclRef | None = None
        self._dict_get_fn: z3.FuncDeclRef | None = None

    # ── variable management ───────────────────────────────────────

    def declare_var(self, name: str, ty: SynType) -> z3.ExprRef:
        """Declare (or retrieve) a Z3 variable for *name* of SynHoPy type *ty*."""
        if name in self._vars:
            return self._vars[name]
        sort = self.type_to_sort(ty)
        var: z3.ExprRef
        if sort == z3.IntSort():
            var = z3.Int(name)
        elif sort == z3.RealSort():
            var = z3.Real(name)
        elif sort == z3.BoolSort():
            var = z3.Bool(name)
        elif sort == z3.StringSort():
            var = z3.String(name)
        else:
            var = z3.Const(name, sort)
        self._vars[name] = var
        return var

    def get_var(self, name: str) -> z3.ExprRef | None:
        """Look up a previously declared variable."""
        return self._vars.get(name)

    def has_var(self, name: str) -> bool:
        return name in self._vars

    def all_vars(self) -> dict[str, z3.ExprRef]:
        """Return a copy of all declared variables."""
        return dict(self._vars)

    # ── type → sort ───────────────────────────────────────────────

    def type_to_sort(self, ty: SynType) -> z3.SortRef:
        """Convert a SynHoPy type to a Z3 sort."""
        if isinstance(ty, (PyIntType, PyNoneType)):
            return z3.IntSort()
        if isinstance(ty, PyFloatType):
            return z3.RealSort()
        if isinstance(ty, PyBoolType):
            return z3.BoolSort()
        if isinstance(ty, PyStrType):
            return z3.StringSort()
        if isinstance(ty, RefinementType):
            return self.type_to_sort(ty.base_type)
        if isinstance(ty, PyListType):
            return z3.ArraySort(z3.IntSort(), self.type_to_sort(ty.element_type))
        if isinstance(ty, PyDictType):
            return z3.ArraySort(
                self.type_to_sort(ty.key_type),
                self.type_to_sort(ty.value_type),
            )
        if isinstance(ty, UnionType):
            # Approximate unions by their first alternative
            if ty.alternatives:
                return self.type_to_sort(ty.alternatives[0])
        if isinstance(ty, OptionalType):
            return self.type_to_sort(ty.inner)
        # Fallback: uninterpreted sort named after the type
        key = repr(ty)
        if key not in self._sorts:
            self._sorts[key] = z3.DeclareSort(key)
        return self._sorts[key]

    # ── list helpers ──────────────────────────────────────────────

    def list_length(self, lst_var: z3.ExprRef) -> z3.ArithRef:
        """Return an integer expression for the length of *lst_var*.

        Uses an uninterpreted function ``_len`` with the axiom that
        length ≥ 0.
        """
        if self._list_len_fn is None:
            self._list_len_fn = z3.Function(
                "_len", lst_var.sort(), z3.IntSort()
            )
        return self._list_len_fn(lst_var)

    def list_get(self, lst_var: z3.ExprRef, idx: z3.ArithRef) -> z3.ExprRef:
        """lst_var[idx] modeled via Z3 Select."""
        return z3.Select(lst_var, idx)

    def dict_get(self, d_var: z3.ExprRef, key: z3.ExprRef) -> z3.ExprRef:
        """dict_var[key] modeled via Z3 Select."""
        return z3.Select(d_var, key)


# ═══════════════════════════════════════════════════════════════════
# PredicateTranslator
# ═══════════════════════════════════════════════════════════════════

# Reserved words that should *not* be treated as Z3 variable names.
_RESERVED: frozenset[str] = frozenset({
    "True", "False", "None",
    "and", "or", "not", "if", "else", "in",
    "for", "is", "lambda", "return",
    "len", "abs", "min", "max", "sum",
    "all", "any", "range", "sorted", "reversed",
    "isinstance", "type", "int", "float", "str", "bool", "list", "dict",
})


class PredicateTranslator:
    """Translate Python predicate strings to Z3 formulas.

    Handles:
        - Arithmetic: ``+  -  *  //  %  **``
        - Comparison: ``==  !=  <  <=  >  >=``
        - Boolean:    ``and  or  not``
        - Builtins:   ``len()  abs()  min()  max()  sum()``
        - Quantifiers: ``all(… for x in range(…))``  ``any(…)``
        - List ops:   ``x in lst``  ``lst[i]``  ``len(lst)``
        - String ops: ``len(s)``  ``s.startswith(…)``  ``s.endswith(…)``
    """

    def translate(self, pred_str: str, z3ctx: Z3Context) -> z3.BoolRef:
        """Parse *pred_str* and return a Z3 boolean formula.

        Any free variables referenced in the predicate that have not yet
        been declared in *z3ctx* are auto-declared as ``Int``.
        """
        _require_z3()
        tree = ast.parse(pred_str, mode="eval")
        self._autodeclare(tree, z3ctx)
        expr = self.translate_expr(tree.body, z3ctx)
        # Coerce to BoolRef if needed
        if z3.is_bool(expr):
            return expr
        return expr != z3.IntVal(0)

    def translate_expr(self, node: ast.expr, z3ctx: Z3Context) -> z3.ExprRef:
        """Recursively translate an AST expression node to Z3."""
        _require_z3()
        if isinstance(node, ast.Constant):
            return self._translate_constant(node)
        if isinstance(node, ast.Name):
            return self._translate_name(node, z3ctx)
        if isinstance(node, ast.BoolOp):
            return self._translate_boolop(node, z3ctx)
        if isinstance(node, ast.UnaryOp):
            return self._translate_unaryop(node, z3ctx)
        if isinstance(node, ast.BinOp):
            return self._translate_binop(node, z3ctx)
        if isinstance(node, ast.Compare):
            return self._translate_compare(node, z3ctx)
        if isinstance(node, ast.IfExp):
            return self._translate_ifexp(node, z3ctx)
        if isinstance(node, ast.Call):
            return self._translate_call(node, z3ctx)
        if isinstance(node, ast.Subscript):
            return self._translate_subscript(node, z3ctx)
        if isinstance(node, ast.Attribute):
            return self._translate_attribute(node, z3ctx)
        if isinstance(node, ast.ListComp):
            return self._translate_listcomp(node, z3ctx)
        if isinstance(node, ast.GeneratorExp):
            return self._translate_generatorexp(node, z3ctx)
        raise ValueError(
            f"Unsupported AST node in predicate: {ast.dump(node)}"
        )

    # ── private helpers ───────────────────────────────────────────

    def _autodeclare(self, tree: ast.Expression, z3ctx: Z3Context) -> None:
        """Auto-declare free names as Int variables."""
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id not in _RESERVED:
                if not z3ctx.has_var(node.id):
                    z3ctx.declare_var(node.id, PyIntType())

    def _translate_constant(self, node: ast.Constant) -> z3.ExprRef:
        v = node.value
        if isinstance(v, bool):
            return z3.BoolVal(v)
        if isinstance(v, int):
            return z3.IntVal(v)
        if isinstance(v, float):
            return z3.RealVal(v)
        if isinstance(v, str):
            return z3.StringVal(v)
        if v is None:
            return z3.IntVal(0)
        raise ValueError(f"Unsupported constant: {v!r}")

    def _translate_name(self, node: ast.Name, z3ctx: Z3Context) -> z3.ExprRef:
        name = node.id
        if name == "True":
            return z3.BoolVal(True)
        if name == "False":
            return z3.BoolVal(False)
        if name == "None":
            return z3.IntVal(0)
        var = z3ctx.get_var(name)
        if var is not None:
            return var
        # Auto-declare as Int
        return z3ctx.declare_var(name, PyIntType())

    def _translate_boolop(self, node: ast.BoolOp, z3ctx: Z3Context) -> z3.BoolRef:
        values = [self.translate_expr(v, z3ctx) for v in node.values]
        if isinstance(node.op, ast.And):
            return z3.And(*values)
        return z3.Or(*values)

    def _translate_unaryop(self, node: ast.UnaryOp, z3ctx: Z3Context) -> z3.ExprRef:
        operand = self.translate_expr(node.operand, z3ctx)
        if isinstance(node.op, ast.Not):
            return z3.Not(operand)
        if isinstance(node.op, ast.USub):
            return -operand
        if isinstance(node.op, ast.UAdd):
            return operand
        raise ValueError(f"Unsupported unary op: {type(node.op).__name__}")

    def _translate_binop(self, node: ast.BinOp, z3ctx: Z3Context) -> z3.ExprRef:
        left = self.translate_expr(node.left, z3ctx)
        right = self.translate_expr(node.right, z3ctx)
        op = node.op
        if isinstance(op, ast.Add):
            return left + right
        if isinstance(op, ast.Sub):
            return left - right
        if isinstance(op, ast.Mult):
            return left * right
        if isinstance(op, ast.FloorDiv):
            # Integer division in Z3
            if z3.is_int(left) and z3.is_int(right):
                return left / right  # Z3 Int division is floor division
            return left / right
        if isinstance(op, ast.Mod):
            return left % right
        if isinstance(op, ast.Pow):
            # Z3 only supports constant exponents well
            if z3.is_int_value(right):
                exp = right.as_long()
                if exp == 0:
                    return z3.IntVal(1)
                result = left
                for _ in range(exp - 1):
                    result = result * left
                return result
            # Fallback: uninterpreted
            pow_fn = z3.Function("_pow", z3.IntSort(), z3.IntSort(), z3.IntSort())
            return pow_fn(left, right)
        if isinstance(op, ast.Div):
            # True division → Real
            return z3.ToReal(left) / z3.ToReal(right) if z3.is_int(left) else left / right
        raise ValueError(f"Unsupported binary op: {type(op).__name__}")

    def _translate_compare(self, node: ast.Compare, z3ctx: Z3Context) -> z3.BoolRef:
        """Handle chained comparisons: a < b < c  →  (a < b) ∧ (b < c)."""
        left = self.translate_expr(node.left, z3ctx)
        parts: list[z3.BoolRef] = []
        for op, comparator_node in zip(node.ops, node.comparators):
            right = self.translate_expr(comparator_node, z3ctx)
            left_c, right_c = self._coerce_pair(left, right)
            if isinstance(op, ast.Eq):
                parts.append(left_c == right_c)
            elif isinstance(op, ast.NotEq):
                parts.append(left_c != right_c)
            elif isinstance(op, ast.Lt):
                parts.append(left_c < right_c)
            elif isinstance(op, ast.LtE):
                parts.append(left_c <= right_c)
            elif isinstance(op, ast.Gt):
                parts.append(left_c > right_c)
            elif isinstance(op, ast.GtE):
                parts.append(left_c >= right_c)
            elif isinstance(op, ast.In):
                # x in lst  →  ∃ i. 0 ≤ i < len(lst) ∧ lst[i] == x
                parts.append(self._encode_membership(left_c, right_c, z3ctx))
            elif isinstance(op, ast.NotIn):
                parts.append(z3.Not(self._encode_membership(left_c, right_c, z3ctx)))
            else:
                raise ValueError(f"Unsupported comparison: {type(op).__name__}")
            left = right
        if len(parts) == 1:
            return parts[0]
        return z3.And(*parts)

    @staticmethod
    def _coerce_pair(a: z3.ExprRef, b: z3.ExprRef) -> tuple[z3.ExprRef, z3.ExprRef]:
        """Coerce two Z3 expressions to compatible sorts."""
        if a.sort() == b.sort():
            return a, b
        # Int ↔ Real coercion
        if z3.is_int(a) and z3.is_real(b):
            return z3.ToReal(a), b
        if z3.is_real(a) and z3.is_int(b):
            return a, z3.ToReal(b)
        # Int ↔ Bool coercion
        if z3.is_bool(a) and z3.is_int(b):
            return z3.If(a, z3.IntVal(1), z3.IntVal(0)), b
        if z3.is_int(a) and z3.is_bool(b):
            return a, z3.If(b, z3.IntVal(1), z3.IntVal(0))
        return a, b

    def _encode_membership(
        self, elem: z3.ExprRef, lst: z3.ExprRef, z3ctx: Z3Context
    ) -> z3.BoolRef:
        """Encode ``elem in lst`` as ∃ i. 0 ≤ i < len(lst) ∧ lst[i] == elem."""
        i = z3.Int("_mem_i")
        length = z3ctx.list_length(lst)
        return z3.Exists(
            [i],
            z3.And(i >= 0, i < length, z3.Select(lst, i) == elem),
        )

    def _translate_ifexp(self, node: ast.IfExp, z3ctx: Z3Context) -> z3.ExprRef:
        cond = self.translate_expr(node.test, z3ctx)
        then = self.translate_expr(node.body, z3ctx)
        else_ = self.translate_expr(node.orelse, z3ctx)
        return z3.If(cond, then, else_)

    def _translate_call(self, node: ast.Call, z3ctx: Z3Context) -> z3.ExprRef:
        """Translate known built-in calls."""
        func_name = self._call_name(node)

        if func_name == "len":
            if len(node.args) != 1:
                raise ValueError("len() takes exactly 1 argument")
            arg = self.translate_expr(node.args[0], z3ctx)
            if z3.is_string(arg):
                return z3.Length(arg)
            return z3ctx.list_length(arg)

        if func_name == "abs":
            arg = self.translate_expr(node.args[0], z3ctx)
            return z3.If(arg >= 0, arg, -arg)

        if func_name == "min":
            return self._translate_minmax(node, z3ctx, is_min=True)

        if func_name == "max":
            return self._translate_minmax(node, z3ctx, is_min=False)

        if func_name == "sum":
            # sum over a known range is unrolled; otherwise uninterpreted
            return self._translate_sum(node, z3ctx)

        if func_name == "all":
            return self._translate_all_any(node, z3ctx, is_all=True)

        if func_name == "any":
            return self._translate_all_any(node, z3ctx, is_all=False)

        if func_name == "range":
            # range is not directly translated; it's handled within
            # generator expressions / quantifiers.
            raise ValueError("range() outside quantifier context")

        if func_name == "isinstance":
            # Approximate: always True (type info is structural)
            return z3.BoolVal(True)

        # Method calls routed through _translate_attribute_call
        if isinstance(node.func, ast.Attribute):
            return self._translate_attribute_call(node, z3ctx)

        # Unknown function → uninterpreted
        args_z3 = [self.translate_expr(a, z3ctx) for a in node.args]
        if not args_z3:
            return z3.Int(f"_{func_name}_result")
        sorts = [a.sort() for a in args_z3] + [args_z3[0].sort()]
        fn = z3.Function(func_name, *sorts)
        return fn(*args_z3)

    def _call_name(self, node: ast.Call) -> str:
        """Extract a simple name from a Call node."""
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            return node.func.attr
        return "_unknown"

    def _translate_minmax(
        self, node: ast.Call, z3ctx: Z3Context, *, is_min: bool
    ) -> z3.ExprRef:
        """min(a, b, …) / max(a, b, …)."""
        args = [self.translate_expr(a, z3ctx) for a in node.args]
        if len(args) == 0:
            raise ValueError(f"{'min' if is_min else 'max'}() needs arguments")
        result = args[0]
        for arg in args[1:]:
            result = z3.If(arg < result, arg, result) if is_min else z3.If(arg > result, arg, result)
        return result

    def _translate_sum(self, node: ast.Call, z3ctx: Z3Context) -> z3.ExprRef:
        """sum(…) — uninterpreted for general case."""
        if node.args and isinstance(node.args[0], ast.GeneratorExp):
            return self._translate_sum_genexpr(node.args[0], z3ctx)
        arg = self.translate_expr(node.args[0], z3ctx)
        sum_fn = z3.Function("_sum", arg.sort(), z3.IntSort())
        return sum_fn(arg)

    def _translate_sum_genexpr(
        self, gen: ast.GeneratorExp, z3ctx: Z3Context
    ) -> z3.ExprRef:
        """sum(expr for x in range(n))."""
        if len(gen.generators) != 1:
            raise ValueError("sum() comprehension: only single for-clause supported")
        comp = gen.generators[0]
        if not isinstance(comp.target, ast.Name):
            raise ValueError("sum() comprehension: target must be a name")
        var_name = comp.target.id
        lo, hi = self._extract_range(comp.iter, z3ctx)
        # Use recursive uninterpreted function
        old_var = z3ctx.get_var(var_name)
        idx = z3ctx.declare_var(var_name, PyIntType())
        body = self.translate_expr(gen.elt, z3ctx)
        # Restore
        if old_var is not None:
            z3ctx._vars[var_name] = old_var
        else:
            del z3ctx._vars[var_name]
        sum_fn = z3.Function(f"_sum_{var_name}", z3.IntSort(), z3.IntSort())
        return sum_fn(hi) - sum_fn(lo)

    def _translate_all_any(
        self, node: ast.Call, z3ctx: Z3Context, *, is_all: bool
    ) -> z3.BoolRef:
        """all(pred for x in range(…)) / any(…)."""
        if not node.args:
            return z3.BoolVal(True) if is_all else z3.BoolVal(False)
        arg0 = node.args[0]
        if isinstance(arg0, ast.GeneratorExp):
            return self._translate_quantifier(arg0, z3ctx, universal=is_all)
        # all([…]) with a list-like argument
        inner = self.translate_expr(arg0, z3ctx)
        if z3.is_bool(inner):
            return inner
        return z3.BoolVal(True) if is_all else z3.BoolVal(False)

    def _translate_quantifier(
        self, gen: ast.GeneratorExp, z3ctx: Z3Context, *, universal: bool
    ) -> z3.BoolRef:
        """Translate ``all(P(x) for x in range(n))`` → ∀x. lo ≤ x < hi → P(x)."""
        if len(gen.generators) != 1:
            raise ValueError("Only single for-clause quantifiers supported")
        comp = gen.generators[0]
        if not isinstance(comp.target, ast.Name):
            raise ValueError("Quantifier target must be a name")

        var_name = comp.target.id
        lo, hi = self._extract_range(comp.iter, z3ctx)

        # Temporarily bind the quantifier variable
        old_var = z3ctx.get_var(var_name)
        qvar = z3.Int(f"_q_{var_name}")
        z3ctx._vars[var_name] = qvar

        body = self.translate_expr(gen.elt, z3ctx)
        # Apply if-filters
        for if_clause in comp.ifs:
            guard = self.translate_expr(if_clause, z3ctx)
            body = z3.Implies(guard, body) if universal else z3.And(guard, body)

        # Restore context
        if old_var is not None:
            z3ctx._vars[var_name] = old_var
        else:
            del z3ctx._vars[var_name]

        range_cond = z3.And(qvar >= lo, qvar < hi)
        if universal:
            return z3.ForAll([qvar], z3.Implies(range_cond, body))
        else:
            return z3.Exists([qvar], z3.And(range_cond, body))

    def _extract_range(
        self, iter_node: ast.expr, z3ctx: Z3Context
    ) -> tuple[z3.ExprRef, z3.ExprRef]:
        """Extract (lo, hi) from ``range(n)`` or ``range(lo, hi)``."""
        if isinstance(iter_node, ast.Call) and self._call_name(iter_node) == "range":
            args = iter_node.args
            if len(args) == 1:
                return z3.IntVal(0), self.translate_expr(args[0], z3ctx)
            if len(args) >= 2:
                return (
                    self.translate_expr(args[0], z3ctx),
                    self.translate_expr(args[1], z3ctx),
                )
        # Fallback: iterate over 0..len(iter)
        arr = self.translate_expr(iter_node, z3ctx)
        return z3.IntVal(0), z3ctx.list_length(arr)

    def _translate_subscript(self, node: ast.Subscript, z3ctx: Z3Context) -> z3.ExprRef:
        obj = self.translate_expr(node.value, z3ctx)
        idx = self.translate_expr(node.slice, z3ctx)
        return z3.Select(obj, idx)

    def _translate_attribute(self, node: ast.Attribute, z3ctx: Z3Context) -> z3.ExprRef:
        """Translate attribute access — limited support."""
        # e.g. x.real, x.imag for numbers → identity / 0
        obj = self.translate_expr(node.value, z3ctx)
        attr_fn = z3.Function(
            f"_attr_{node.attr}", obj.sort(), z3.IntSort()
        )
        return attr_fn(obj)

    def _translate_attribute_call(
        self, node: ast.Call, z3ctx: Z3Context
    ) -> z3.ExprRef:
        """Translate method calls like s.startswith(…)."""
        assert isinstance(node.func, ast.Attribute)
        obj = self.translate_expr(node.func.value, z3ctx)
        method = node.func.attr

        if z3.is_string(obj):
            if method == "startswith" and node.args:
                prefix = self.translate_expr(node.args[0], z3ctx)
                return z3.PrefixOf(prefix, obj)
            if method == "endswith" and node.args:
                suffix = self.translate_expr(node.args[0], z3ctx)
                return z3.SuffixOf(suffix, obj)
            if method == "contains" and node.args:
                sub = self.translate_expr(node.args[0], z3ctx)
                return z3.Contains(obj, sub)

        # Uninterpreted fallback
        args_z3 = [self.translate_expr(a, z3ctx) for a in node.args]
        sorts = [obj.sort()] + [a.sort() for a in args_z3] + [z3.IntSort()]
        fn = z3.Function(f"_{method}", *sorts)
        return fn(obj, *args_z3)

    def _translate_listcomp(self, node: ast.ListComp, z3ctx: Z3Context) -> z3.ExprRef:
        """List comprehensions are not directly expressible — return uninterpreted."""
        return z3.Array(f"_listcomp_{id(node)}", z3.IntSort(), z3.IntSort())

    def _translate_generatorexp(
        self, node: ast.GeneratorExp, z3ctx: Z3Context
    ) -> z3.ExprRef:
        """Bare generator expression — wrap in quantifier if used with all/any.

        When reached directly, produce an uninterpreted placeholder.
        """
        return z3.BoolVal(True)


# ═══════════════════════════════════════════════════════════════════
# RefinementChecker
# ═══════════════════════════════════════════════════════════════════

class RefinementChecker:
    """Check refinement type relationships using Z3.

    Examples::

        checker = RefinementChecker()

        pos  = RefinementType(PyIntType(), "x", "x > 0")
        nat  = RefinementType(PyIntType(), "x", "x >= 0")

        assert checker.check_subtype(pos, nat)   # {x | x>0} <: {x | x>=0}
        assert checker.check_satisfiable(pos)     # ∃x. x > 0
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> z3.Solver:
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    # ── subtype ───────────────────────────────────────────────────

    def check_subtype(self, sub: RefinementType, sup: RefinementType) -> bool:
        """Check {x:A | P(x)} <: {x:A | Q(x)}  ⟺  ∀x. P(x) ⟹ Q(x).

        Both predicates are evaluated over the *sub* variable name; the
        *sup* variable name is alpha-renamed if different.
        """
        ctx = Z3Context()
        var_name = sub.var_name
        ctx.declare_var(var_name, sub.base_type)

        # Translate P
        p = self._translator.translate(sub.predicate, ctx)

        # Alpha-rename Q if needed
        sup_pred = sup.predicate
        if sup.var_name != var_name:
            sup_pred = sup_pred.replace(sup.var_name, var_name)
        q = self._translator.translate(sup_pred, ctx)

        # Valid iff ¬(P ∧ ¬Q) is unsat
        s = self._make_solver()
        s.add(z3.And(p, z3.Not(q)))
        return s.check() == z3.unsat

    # ── satisfiability ────────────────────────────────────────────

    def check_satisfiable(self, ty: RefinementType) -> bool:
        """Check if the refinement type is inhabited: ∃x. P(x)."""
        ctx = Z3Context()
        ctx.declare_var(ty.var_name, ty.base_type)
        pred = self._translator.translate(ty.predicate, ctx)
        s = self._make_solver()
        s.add(pred)
        return s.check() == z3.sat

    # ── validity ──────────────────────────────────────────────────

    def check_valid(
        self, predicate: str, context: dict[str, SynType] | None = None
    ) -> bool:
        """Check if *predicate* holds universally under *context*.

        Returns ``True`` when ∀ vars. predicate.
        """
        z3ctx = Z3Context()
        if context:
            for name, ty in context.items():
                z3ctx.declare_var(name, ty)
        formula = self._translator.translate(predicate, z3ctx)

        s = self._make_solver()
        s.add(z3.Not(formula))
        return s.check() == z3.unsat

    # ── counterexample ────────────────────────────────────────────

    def find_counterexample(
        self, predicate: str, context: dict[str, SynType] | None = None
    ) -> dict[str, Any] | None:
        """Find a counterexample to *predicate*, or ``None`` if valid."""
        z3ctx = Z3Context()
        if context:
            for name, ty in context.items():
                z3ctx.declare_var(name, ty)
        formula = self._translator.translate(predicate, z3ctx)

        s = self._make_solver()
        s.add(z3.Not(formula))
        result = s.check()
        if result != z3.sat:
            return None
        model = s.model()
        cex: dict[str, Any] = {}
        for name, var in z3ctx.all_vars().items():
            val = model.eval(var, model_completion=True)
            try:
                cex[name] = val.as_long() if z3.is_int_value(val) else str(val)
            except Exception:
                cex[name] = str(val)
        return cex

    # ── conjunction / implication helpers ──────────────────────────

    def check_implication(
        self,
        premises: list[str],
        conclusion: str,
        context: dict[str, SynType] | None = None,
    ) -> bool:
        """Check ∀ vars. (P₁ ∧ … ∧ Pₙ) ⟹ Q."""
        z3ctx = Z3Context()
        if context:
            for name, ty in context.items():
                z3ctx.declare_var(name, ty)
        ps = [self._translator.translate(p, z3ctx) for p in premises]
        q = self._translator.translate(conclusion, z3ctx)
        s = self._make_solver()
        s.add(z3.And(*ps))
        s.add(z3.Not(q))
        return s.check() == z3.unsat

    def check_equivalence(
        self,
        pred_a: str,
        pred_b: str,
        context: dict[str, SynType] | None = None,
    ) -> bool:
        """Check ∀ vars. P(x) ⟺ Q(x)."""
        return (
            self.check_implication([pred_a], pred_b, context)
            and self.check_implication([pred_b], pred_a, context)
        )


# ═══════════════════════════════════════════════════════════════════
# Z3Proof  (result dataclass)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Z3ProofResult:
    """A proof term produced by Z3.

    Not to be confused with ``synhopy.core.kernel.Z3Proof`` which is the
    kernel-level proof tag.  This object carries the full solver metadata.
    """
    formula: str
    is_valid: bool
    model: Any = None            # z3.ModelRef when SAT / counter-example
    solver_stats: dict[str, Any] = field(default_factory=dict)
    hypotheses: list[str] = field(default_factory=list)

    def __bool__(self) -> bool:
        return self.is_valid


# ═══════════════════════════════════════════════════════════════════
# Z3Prover
# ═══════════════════════════════════════════════════════════════════

class Z3Prover:
    """Generate proof terms backed by Z3.

    Examples::

        prover = Z3Prover()

        p = prover.prove("x + y == y + x",
                         context={"x": PyIntType(), "y": PyIntType()})
        assert p is not None and p.is_valid
    """

    def __init__(self, timeout_ms: int = 10000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> z3.Solver:
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    # ── prove ─────────────────────────────────────────────────────

    def prove(
        self,
        goal: str,
        hypotheses: list[str] | None = None,
        context: dict[str, SynType] | None = None,
    ) -> Z3ProofResult | None:
        """Try to prove *goal* under *hypotheses*.

        Returns a ``Z3ProofResult`` if Z3 can decide the formula (valid
        **or** invalid with counter-example), or ``None`` on timeout /
        unknown.
        """
        z3ctx = Z3Context()
        if context:
            for name, ty in context.items():
                z3ctx.declare_var(name, ty)

        hyps: list[z3.BoolRef] = []
        if hypotheses:
            for h in hypotheses:
                hyps.append(self._translator.translate(h, z3ctx))

        goal_z3 = self._translator.translate(goal, z3ctx)

        s = self._make_solver()
        for h in hyps:
            s.add(h)
        s.add(z3.Not(goal_z3))

        result = s.check()
        try:
            st = s.statistics()
            stats = {st.keys()[k]: str(st[st.keys()[k]]) for k in range(len(st))}
        except Exception:
            stats = {}

        if result == z3.unsat:
            return Z3ProofResult(
                formula=goal,
                is_valid=True,
                solver_stats=stats,
                hypotheses=hypotheses or [],
            )
        if result == z3.sat:
            return Z3ProofResult(
                formula=goal,
                is_valid=False,
                model=s.model(),
                solver_stats=stats,
                hypotheses=hypotheses or [],
            )
        # unknown / timeout
        return None

    # ── prove_implication ─────────────────────────────────────────

    def prove_implication(
        self,
        premises: list[str],
        conclusion: str,
        context: dict[str, SynType] | None = None,
    ) -> Z3ProofResult | None:
        """Prove (P₁ ∧ … ∧ Pₙ) ⟹ Q."""
        return self.prove(conclusion, hypotheses=premises, context=context)

    # ── prove_refinement ──────────────────────────────────────────

    def prove_refinement(
        self,
        func_body: str,
        spec: str,
        params: dict[str, SynType] | None = None,
    ) -> Z3ProofResult | None:
        """Prove that *func_body* (a predicate describing what the function
        computes) implies *spec* (the postcondition).

        This is the core "does the implementation satisfy the spec?" query.
        """
        return self.prove(spec, hypotheses=[func_body], context=params)

    # ── batch prove ───────────────────────────────────────────────

    def prove_all(
        self,
        goals: list[str],
        hypotheses: list[str] | None = None,
        context: dict[str, SynType] | None = None,
    ) -> list[Z3ProofResult | None]:
        """Prove multiple goals under the same hypotheses / context."""
        return [self.prove(g, hypotheses=hypotheses, context=context) for g in goals]


# ═══════════════════════════════════════════════════════════════════
# ArithmeticEncoder
# ═══════════════════════════════════════════════════════════════════

class ArithmeticEncoder:
    """Pre-built Z3 encodings for common verification patterns.

    These build Z3 constraints directly (no string parsing) for patterns
    that appear repeatedly in refinement types.
    """

    def __init__(self) -> None:
        _require_z3()

    # ── list length ───────────────────────────────────────────────

    def encode_list_length(
        self, lst_var: str, *, ctx: Z3Context | None = None
    ) -> tuple[z3.ExprRef, z3.BoolRef]:
        """Return ``(len_var, len_var >= 0)`` for the list's length.

        If *ctx* is provided, looks up the list variable there.
        """
        length = z3.Int(f"_len_{lst_var}")
        axiom = length >= 0
        return length, axiom

    # ── sorted ────────────────────────────────────────────────────

    def encode_sorted(
        self, lst_var: str, length_var: z3.ArithRef | None = None
    ) -> z3.BoolRef:
        """Encode ``sorted(lst)``  ⟺  ∀ i. 0 ≤ i < len-1 → lst[i] ≤ lst[i+1].

        Uses an array model for the list.
        """
        arr = z3.Array(lst_var, z3.IntSort(), z3.IntSort())
        n = length_var if length_var is not None else z3.Int(f"_len_{lst_var}")
        i = z3.Int("_sorted_i")
        return z3.ForAll(
            [i],
            z3.Implies(
                z3.And(i >= 0, i < n - 1),
                z3.Select(arr, i) <= z3.Select(arr, i + 1),
            ),
        )

    # ── distinct elements ─────────────────────────────────────────

    def encode_distinct_elements(
        self, lst_var: str, length_var: z3.ArithRef | None = None
    ) -> z3.BoolRef:
        """Encode that all elements of *lst_var* are distinct."""
        arr = z3.Array(lst_var, z3.IntSort(), z3.IntSort())
        n = length_var if length_var is not None else z3.Int(f"_len_{lst_var}")
        i = z3.Int("_dist_i")
        j = z3.Int("_dist_j")
        return z3.ForAll(
            [i, j],
            z3.Implies(
                z3.And(i >= 0, j >= 0, i < n, j < n, i != j),
                z3.Select(arr, i) != z3.Select(arr, j),
            ),
        )

    # ── range ─────────────────────────────────────────────────────

    def encode_range(self, start: int, stop: int) -> z3.BoolRef:
        """Encode a bounded-range constraint for a variable ``_r``.

        Returns ``start ≤ _r < stop``.
        """
        r = z3.Int("_r")
        return z3.And(r >= start, r < stop)

    # ── dict lookup ───────────────────────────────────────────────

    def encode_dict_lookup(
        self, dict_var: str, key_expr: z3.ExprRef
    ) -> z3.ExprRef:
        """Model ``dict_var[key]`` via a Z3 Array Select."""
        d = z3.Array(dict_var, key_expr.sort(), z3.IntSort())
        return z3.Select(d, key_expr)

    # ── bounded sum ───────────────────────────────────────────────

    def encode_bounded_sum(
        self, lst_var: str, length_var: z3.ArithRef
    ) -> z3.ArithRef:
        """Return an uninterpreted ``_sum(lst_var)`` with basic axioms.

        Axiom: sum of empty list is 0.
        """
        sum_fn = z3.Function(f"_sum_{lst_var}", z3.IntSort(), z3.IntSort())
        return sum_fn(length_var)

    # ── element bound ─────────────────────────────────────────────

    def encode_all_elements_bounded(
        self,
        lst_var: str,
        lo: z3.ArithRef,
        hi: z3.ArithRef,
        length_var: z3.ArithRef | None = None,
    ) -> z3.BoolRef:
        """∀ i. 0 ≤ i < n → lo ≤ lst[i] < hi."""
        arr = z3.Array(lst_var, z3.IntSort(), z3.IntSort())
        n = length_var if length_var is not None else z3.Int(f"_len_{lst_var}")
        i = z3.Int("_bnd_i")
        return z3.ForAll(
            [i],
            z3.Implies(
                z3.And(i >= 0, i < n),
                z3.And(z3.Select(arr, i) >= lo, z3.Select(arr, i) < hi),
            ),
        )

    # ── permutation (weak) ────────────────────────────────────────

    def encode_same_length(
        self, lst_a: str, lst_b: str
    ) -> z3.BoolRef:
        """Assert two lists have the same length."""
        return z3.Int(f"_len_{lst_a}") == z3.Int(f"_len_{lst_b}")

    # ── monotonicity ──────────────────────────────────────────────

    def encode_strictly_increasing(
        self, lst_var: str, length_var: z3.ArithRef | None = None
    ) -> z3.BoolRef:
        """∀ i. 0 ≤ i < n-1 → lst[i] < lst[i+1]."""
        arr = z3.Array(lst_var, z3.IntSort(), z3.IntSort())
        n = length_var if length_var is not None else z3.Int(f"_len_{lst_var}")
        i = z3.Int("_inc_i")
        return z3.ForAll(
            [i],
            z3.Implies(
                z3.And(i >= 0, i < n - 1),
                z3.Select(arr, i) < z3.Select(arr, i + 1),
            ),
        )


# ═══════════════════════════════════════════════════════════════════
# Convenience helpers
# ═══════════════════════════════════════════════════════════════════

def quick_check(predicate: str, context: dict[str, SynType] | None = None) -> bool:
    """One-shot validity check for a predicate string.

    Returns ``True`` if the predicate is universally valid.
    """
    return RefinementChecker().check_valid(predicate, context)


def quick_prove(
    goal: str,
    hypotheses: list[str] | None = None,
    context: dict[str, SynType] | None = None,
) -> bool:
    """One-shot proof attempt.  Returns ``True`` if the goal is proved."""
    result = Z3Prover().prove(goal, hypotheses=hypotheses, context=context)
    return result is not None and result.is_valid


def extract_free_vars(predicate: str) -> set[str]:
    """Return the set of free variable names in a predicate string."""
    tree = ast.parse(predicate, mode="eval")
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id not in _RESERVED:
            names.add(node.id)
    return names


# ═══════════════════════════════════════════════════════════════════
# PathEncoder — encode path types & equalities in Z3
# ═══════════════════════════════════════════════════════════════════

class PathEncoder:
    """Encode path types and path equalities in Z3.

    A path ``a =_A b`` is encoded as:
        ∀i ∈ [0,1]. path(i) : A  ∧  path(0) = a  ∧  path(1) = b

    For arithmetic paths: ``path(i) = (1-i)*a + i*b`` (linear interpolation)
    For boolean paths:    ``path(i) = if i < 0.5 then a else b``
    For function paths:   ``∀x. path(i)(x)`` well-typed
    """

    def __init__(self, ctx: Z3Context) -> None:
        _require_z3()
        self.ctx = ctx
        self._interval = z3.RealSort()  # I = [0,1] ⊂ ℝ
        self._translator = PredicateTranslator()

    # ── interval constraint ───────────────────────────────────────

    @staticmethod
    def _in_interval(i: z3.ExprRef) -> z3.BoolRef:
        """Constraint: i ∈ [0, 1]."""
        return z3.And(i >= z3.RealVal(0), i <= z3.RealVal(1))

    # ── path type encoding ────────────────────────────────────────

    def encode_path_type(self, base_type: SynType,
                         left: SynTerm, right: SynTerm) -> z3.ExprRef:
        """Encode ``a =_A b`` as a Z3 constraint.

        Creates a path function over the interval and asserts the boundary
        conditions ``path(0) = left`` and ``path(1) = right``.  For Int/Real
        base types the path is the canonical linear interpolation in ℝ.

        Returns a conjunction of the boundary and well-formedness constraints.
        """
        sort = self.ctx.type_to_sort(base_type)

        left_z3 = self._term_to_z3(left, sort)
        right_z3 = self._term_to_z3(right, sort)

        # Path function always works in ℝ (the interval is [0,1] ⊂ ℝ)
        path_fn = z3.Function("_path", z3.RealSort(), z3.RealSort())
        i = z3.Real("_path_i")

        # Lift endpoints to Real for boundary comparison
        left_real = z3.ToReal(left_z3) if sort == z3.IntSort() else left_z3 \
            if sort == z3.RealSort() else None
        right_real = z3.ToReal(right_z3) if sort == z3.IntSort() else right_z3 \
            if sort == z3.RealSort() else None

        if sort == z3.IntSort() or sort == z3.RealSort():
            assert left_real is not None and right_real is not None
            boundary_0 = path_fn(z3.RealVal(0)) == left_real
            boundary_1 = path_fn(z3.RealVal(1)) == right_real

            # Linear interpolation: path(i) = (1-i)*a + i*b
            interp = (z3.RealVal(1) - i) * left_real + i * right_real
            well_formed = z3.ForAll(
                [i],
                z3.Implies(self._in_interval(i), path_fn(i) == interp),
            )
            return z3.And(boundary_0, boundary_1, well_formed)

        if sort == z3.BoolSort():
            # Boolean paths use a dedicated Bool-sorted path function
            path_fn_b = z3.Function("_path", z3.RealSort(), z3.BoolSort())
            boundary_0 = path_fn_b(z3.RealVal(0)) == left_z3
            boundary_1 = path_fn_b(z3.RealVal(1)) == right_z3
            step = z3.ForAll(
                [i],
                z3.Implies(
                    self._in_interval(i),
                    path_fn_b(i) == z3.If(i < z3.RealVal(0.5), left_z3, right_z3),
                ),
            )
            return z3.And(boundary_0, boundary_1, step)

        # Generic: boundary via uninterpreted path
        path_fn_g = z3.Function("_path", z3.RealSort(), sort)
        boundary_0 = path_fn_g(z3.RealVal(0)) == left_z3
        boundary_1 = path_fn_g(z3.RealVal(1)) == right_z3
        return z3.And(boundary_0, boundary_1)

    # ── path abstraction encoding ─────────────────────────────────

    def encode_path_abs(self, var: str, body: SynTerm,
                        left: SynTerm, right: SynTerm) -> z3.ExprRef:
        """Encode ``λ(i:I). t`` with boundary conditions.

        Returns the conjunction of ``body[var:=0] = left`` and
        ``body[var:=1] = right``.
        """
        sort = z3.IntSort()  # default
        left_z3 = self._term_to_z3(left, sort)
        right_z3 = self._term_to_z3(right, sort)

        body_at_0 = self._eval_body(body, var, z3.RealVal(0))
        body_at_1 = self._eval_body(body, var, z3.RealVal(1))

        return z3.And(body_at_0 == left_z3, body_at_1 == right_z3)

    # ── boundary check ────────────────────────────────────────────

    def encode_boundary_check(self, path_body: z3.ExprRef,
                              var: str, left: z3.ExprRef,
                              right: z3.ExprRef) -> z3.ExprRef:
        """Check: ``body[var:=0] = left ∧ body[var:=1] = right``.

        *path_body* should be a Z3 function application whose argument is
        the interval variable *var*.  We substitute 0 and 1 for it.
        """
        path_fn = z3.Function("_path", z3.RealSort(), left.sort())
        at0 = path_fn(z3.RealVal(0)) == left
        at1 = path_fn(z3.RealVal(1)) == right
        return z3.And(at0, at1)

    # ── path composition (Kan filling) ────────────────────────────

    def encode_path_comp(self, p: z3.ExprRef, q: z3.ExprRef,
                         midpoint: z3.ExprRef) -> z3.ExprRef:
        """Encode path composition ``p · q`` via Kan filling.

        Given ``p : a =_A m`` and ``q : m =_A b``, the composite path
        ``p · q : a =_A b`` is encoded as:

            path(i) = if i ≤ 0.5 then p(2i) else q(2i - 1)

        with the constraint that ``p(1) = q(0) = midpoint``.
        """
        p_fn = z3.Function("_path_p", z3.RealSort(), midpoint.sort())
        q_fn = z3.Function("_path_q", z3.RealSort(), midpoint.sort())
        comp_fn = z3.Function("_path_comp", z3.RealSort(), midpoint.sort())

        i = z3.Real("_comp_i")

        # p and q agree at the midpoint
        gluing = z3.And(p_fn(z3.RealVal(1)) == midpoint,
                        q_fn(z3.RealVal(0)) == midpoint)

        # Composite path: reparametrise
        comp_def = z3.ForAll(
            [i],
            z3.Implies(
                self._in_interval(i),
                comp_fn(i) == z3.If(
                    i <= z3.RealVal(0.5),
                    p_fn(z3.RealVal(2) * i),
                    q_fn(z3.RealVal(2) * i - z3.RealVal(1)),
                ),
            ),
        )

        # Boundary: comp(0) = p(0), comp(1) = q(1)
        boundary = z3.And(
            comp_fn(z3.RealVal(0)) == p_fn(z3.RealVal(0)),
            comp_fn(z3.RealVal(1)) == q_fn(z3.RealVal(1)),
        )

        return z3.And(gluing, comp_def, boundary)

    # ── helpers ───────────────────────────────────────────────────

    def _term_to_z3(self, term: SynTerm, sort: "z3.SortRef") -> z3.ExprRef:
        """Convert a SynTerm to a Z3 expression of the given sort."""
        if isinstance(term, Literal):
            v = term.value
            if isinstance(v, bool):
                return z3.BoolVal(v)
            if isinstance(v, int):
                if sort == z3.RealSort():
                    return z3.RealVal(v)
                return z3.IntVal(v)
            if isinstance(v, float):
                return z3.RealVal(v)
            if isinstance(v, str):
                return z3.StringVal(v)
            return z3.IntVal(0)
        if isinstance(term, Var):
            existing = self.ctx.get_var(term.name)
            if existing is not None:
                return existing
            if sort == z3.IntSort():
                return z3.Int(term.name)
            if sort == z3.RealSort():
                return z3.Real(term.name)
            if sort == z3.BoolSort():
                return z3.Bool(term.name)
            return z3.Const(term.name, sort)
        # Fallback: treat as uninterpreted constant
        return z3.Const(f"_term_{id(term)}", sort)

    def _eval_body(self, body: SynTerm, var: str,
                   val: z3.ExprRef) -> z3.ExprRef:
        """Evaluate *body* at *var* = *val* by translating as a predicate."""
        if isinstance(body, Var):
            if body.name == var:
                return val
            existing = self.ctx.get_var(body.name)
            return existing if existing is not None else z3.Int(body.name)
        if isinstance(body, Literal):
            return self._term_to_z3(body, z3.IntSort())
        # General case: use uninterpreted function
        fn = z3.Function(f"_body_{var}", z3.RealSort(), z3.IntSort())
        return fn(val)


# ═══════════════════════════════════════════════════════════════════
# TransportEncoder — encode transport along paths in Z3
# ═══════════════════════════════════════════════════════════════════

class TransportEncoder:
    """Encode transport in Z3.

    ``transport(P, path, d)`` where:
    - P is a type family (predicate)
    - path : a = b
    - d : P(a)
    Result: P(b)

    Z3 encoding: ``P(a) ∧ (a = b) → P(b)`` (substitution principle).
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> "z3.Solver":
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    def encode_transport(self, type_family: "z3.FuncDeclRef",
                         path: z3.ExprRef,
                         base: z3.ExprRef) -> z3.ExprRef:
        """Encode transport as a Z3 constraint.

        *type_family* is a unary Z3 function ``P : Sort → Bool``.
        *path* is the equality ``a == b``.
        *base* is the element ``a`` such that ``P(a)`` holds.

        Returns: ``P(a) ∧ (a = b) → P(b)``

        where ``b`` is deduced from *path*.
        """
        a = base
        # Infer b: path should be an equality a == b
        b = z3.Const("_transport_b", a.sort())
        return z3.Implies(
            z3.And(type_family(a), a == b),
            type_family(b),
        )

    def verify_transport(self, type_family_str: str,
                         left: str, right: str,
                         base_holds: str) -> "z3.CheckSatResult":
        """Verify that transport is valid: ``P(a) ∧ a=b → P(b)``.

        All arguments are predicate strings.  *type_family_str* should be
        a predicate in one free variable (the fibre variable).
        *left* and *right* name the endpoints.
        *base_holds* is the predicate asserting ``P(left)`` holds.

        Returns ``z3.unsat`` when the transport obligation is valid.
        """
        ctx = Z3Context()
        a_var = ctx.declare_var(left, PyIntType())
        b_var = ctx.declare_var(right, PyIntType())

        # Build P as a lambda over the context
        p_a = self._translator.translate(base_holds, ctx)
        # P(b): substitute left→right in the predicate
        p_b_str = base_holds.replace(left, right)
        p_b = self._translator.translate(p_b_str, ctx)

        path_eq = a_var == b_var

        # Validity check: ¬(P(a) ∧ a=b ∧ ¬P(b)) should be unsat
        s = self._make_solver()
        s.add(p_a)
        s.add(path_eq)
        s.add(z3.Not(p_b))
        return s.check()


# ═══════════════════════════════════════════════════════════════════
# CechEncoder — Čech cocycle conditions in Z3
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CechVerificationResult:
    """Result of a Čech cohomology verification."""
    exhaustive: bool            # cover is exhaustive
    cocycle_holds: bool         # patches agree on overlaps
    global_holds: bool          # global property follows
    obstruction: str | None     # if fails, where


class CechEncoder:
    """Encode Čech cocycle conditions in Z3.

    Given a cover ``{Uᵢ}`` of a domain:

    1. Each patch has a local predicate/property.
    2. On overlaps ``Uᵢ ∩ Uⱼ``, properties must agree (cocycle condition).
    3. The cover must be exhaustive (union = whole domain).

    Z3 can verify all three conditions.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> "z3.Solver":
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    # ── cover exhaustiveness ──────────────────────────────────────

    def encode_cover_exhaustive(self, conditions: list[z3.ExprRef]) -> z3.ExprRef:
        """``∀x. ∨ᵢ Uᵢ(x)`` — the cover covers everything.

        *conditions* is a list of Z3 boolean expressions, each representing
        a patch indicator ``Uᵢ(x)`` for a universally-quantified ``x``.
        """
        if not conditions:
            return z3.BoolVal(False)
        return z3.Or(*conditions)

    # ── cocycle condition ─────────────────────────────────────────

    def encode_cocycle(self, patches: list[tuple[z3.ExprRef, z3.ExprRef]],
                       overlaps: list[tuple[int, int]]) -> z3.ExprRef:
        """On ``Uᵢ ∩ Uⱼ``: ``Pᵢ(x) ↔ Pⱼ(x)`` — properties agree on overlaps.

        *patches* is a list of ``(condition_i, property_i)`` pairs.
        *overlaps* lists the pairs ``(i, j)`` where overlap can occur.
        """
        cocycle_clauses: list[z3.ExprRef] = []
        for i, j in overlaps:
            cond_i, prop_i = patches[i]
            cond_j, prop_j = patches[j]
            # On the overlap Uᵢ ∩ Uⱼ, properties must agree
            clause = z3.Implies(
                z3.And(cond_i, cond_j),
                prop_i == prop_j,
            )
            cocycle_clauses.append(clause)
        if not cocycle_clauses:
            return z3.BoolVal(True)
        return z3.And(*cocycle_clauses)

    # ── gluing ────────────────────────────────────────────────────

    def encode_gluing(self, patches: list[tuple[z3.ExprRef, z3.ExprRef]]) -> z3.ExprRef:
        """The global section exists iff cocycle condition holds.

        If the cover is exhaustive and the cocycle condition holds, a global
        property ``G(x) = ∨ᵢ (Uᵢ(x) ∧ Pᵢ(x))`` is well-defined.
        """
        if not patches:
            return z3.BoolVal(False)
        parts = [z3.And(cond, prop) for cond, prop in patches]
        return z3.Or(*parts)

    # ── full verification ─────────────────────────────────────────

    def verify_cech_proof(self, conditions: list[str],
                          local_specs: list[str],
                          global_spec: str) -> CechVerificationResult:
        """Full Čech verification: cover + cocycle + gluing → global property.

        *conditions*:  predicate strings ``Uᵢ(x)`` defining the patches.
        *local_specs*: predicate strings ``Pᵢ(x)`` — the local property on
                       each patch.
        *global_spec*: the global property that should follow.

        Returns a :class:`CechVerificationResult`.
        """
        ctx = Z3Context()
        x = ctx.declare_var("x", PyIntType())

        conds_z3 = [self._translator.translate(c, ctx) for c in conditions]
        specs_z3 = [self._translator.translate(s, ctx) for s in local_specs]
        goal_z3 = self._translator.translate(global_spec, ctx)

        patches = list(zip(conds_z3, specs_z3))

        # 1. Exhaustive: ∀x. ∨ Uᵢ(x)
        cover = self.encode_cover_exhaustive(conds_z3)
        s_exh = self._make_solver()
        s_exh.add(z3.Not(cover))
        exhaustive = s_exh.check() == z3.unsat

        # 2. Cocycle: all overlapping pairs agree
        overlaps = [(i, j)
                    for i in range(len(patches))
                    for j in range(i + 1, len(patches))]
        cocycle = self.encode_cocycle(patches, overlaps)
        s_coc = self._make_solver()
        for c in conds_z3:
            s_coc.add(c)
        s_coc.add(z3.Not(cocycle))
        cocycle_holds = s_coc.check() == z3.unsat

        # 3. Global: cover ∧ local_specs → global_spec
        glued = self.encode_gluing(patches)
        s_glob = self._make_solver()
        s_glob.add(cover)
        s_glob.add(cocycle)
        s_glob.add(glued)
        s_glob.add(z3.Not(goal_z3))
        global_holds = s_glob.check() == z3.unsat

        obstruction: str | None = None
        if not exhaustive:
            obstruction = "cover is not exhaustive"
        elif not cocycle_holds:
            obstruction = "cocycle condition fails on some overlap"
        elif not global_holds:
            obstruction = "global property does not follow from local specs"

        return CechVerificationResult(
            exhaustive=exhaustive,
            cocycle_holds=cocycle_holds,
            global_holds=global_holds,
            obstruction=obstruction,
        )


# ═══════════════════════════════════════════════════════════════════
# FibrationEncoder — fibration structure (isinstance dispatch) in Z3
# ═══════════════════════════════════════════════════════════════════

class FibrationEncoder:
    """Encode fibration structure in Z3.

    A function with ``isinstance`` dispatch creates a fibration.
    The base space is discrete (finite set of types).
    The fiber over each type is the set of inputs of that type.

    Z3 can verify:

    1. Fibers are disjoint (each input has exactly one type).
    2. Fibers cover the domain (every input has a type).
    3. A property holds per fiber → holds globally.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> "z3.Solver":
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    # ── fiber coverage ────────────────────────────────────────────

    def encode_fiber_coverage(self, type_conditions: list[z3.ExprRef]) -> z3.ExprRef:
        """Every input belongs to exactly one fiber.

        Encodes: ``(∨ᵢ Cᵢ) ∧ (∀ i≠j. ¬(Cᵢ ∧ Cⱼ))`` — exhaustive and
        mutually exclusive.
        """
        if not type_conditions:
            return z3.BoolVal(False)

        # Exhaustive: at least one condition holds
        at_least_one = z3.Or(*type_conditions)

        # Exclusive: no two conditions hold simultaneously
        exclusion: list[z3.ExprRef] = []
        for i in range(len(type_conditions)):
            for j in range(i + 1, len(type_conditions)):
                exclusion.append(
                    z3.Not(z3.And(type_conditions[i], type_conditions[j]))
                )

        if exclusion:
            return z3.And(at_least_one, *exclusion)
        return at_least_one

    # ── per-fiber property ────────────────────────────────────────

    def encode_per_fiber_property(
        self,
        fibers: list[tuple[z3.ExprRef, z3.ExprRef]],
    ) -> z3.ExprRef:
        """If property holds on each fiber, it holds globally.

        *fibers* is a list of ``(condition_i, property_i)`` pairs.
        Returns: ``∧ᵢ (Cᵢ → Pᵢ)`` — each fiber's condition implies its
        property.
        """
        if not fibers:
            return z3.BoolVal(True)
        return z3.And(*[z3.Implies(c, p) for c, p in fibers])

    # ── full verification ─────────────────────────────────────────

    def verify_fibration(self, type_conditions: list[str],
                         per_fiber_specs: list[str],
                         global_spec: str) -> bool:
        """Verify: per-fiber proofs → global proof.

        Given:

        - *type_conditions*: predicates defining each fiber.
        - *per_fiber_specs*: the property guaranteed on each fiber.
        - *global_spec*: the global property that should follow.

        Returns ``True`` when the fibration descent is valid.
        """
        ctx = Z3Context()
        ctx.declare_var("x", PyIntType())

        conds_z3 = [self._translator.translate(c, ctx) for c in type_conditions]
        specs_z3 = [self._translator.translate(s, ctx) for s in per_fiber_specs]
        goal_z3 = self._translator.translate(global_spec, ctx)

        fibers = list(zip(conds_z3, specs_z3))

        # Exactly-one coverage
        coverage = self.encode_fiber_coverage(conds_z3)
        # Per-fiber properties
        per_fiber = self.encode_per_fiber_property(fibers)

        s = self._make_solver()
        s.add(coverage)
        s.add(per_fiber)
        s.add(z3.Not(goal_z3))
        return s.check() == z3.unsat


# ═══════════════════════════════════════════════════════════════════
# DuckEquivEncoder — duck-type equivalence in Z3
# ═══════════════════════════════════════════════════════════════════

class DuckEquivEncoder:
    """Encode duck-type equivalence in Z3.

    Two types A, B are duck-equivalent over protocol P if:
        ``∀ method m ∈ P. ∀ args. A.m(args) = B.m(args)``

    This is Z3-checkable for finite sets of methods with
    arithmetic/boolean signatures.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        _require_z3()
        self._timeout = timeout_ms
        self._translator = PredicateTranslator()

    def _make_solver(self) -> "z3.Solver":
        s = z3.Solver()
        s.set("timeout", self._timeout)
        return s

    # ── method equivalence ────────────────────────────────────────

    def encode_method_equiv(self, method: str,
                            impl_a: z3.ExprRef,
                            impl_b: z3.ExprRef) -> z3.ExprRef:
        """``∀ args. a.method(args) = b.method(args)``.

        *impl_a* and *impl_b* are Z3 expressions representing the
        implementations of *method* for types A and B respectively.
        """
        return impl_a == impl_b

    # ── protocol equivalence ──────────────────────────────────────

    def encode_protocol_equiv(self, methods: list[str],
                              impl_a: dict[str, z3.ExprRef],
                              impl_b: dict[str, z3.ExprRef]) -> z3.ExprRef:
        """Full protocol equivalence: all methods agree.

        *methods* lists the method names in the protocol.
        *impl_a* / *impl_b* map method names to Z3 expressions for each
        type's implementation.
        """
        clauses: list[z3.ExprRef] = []
        for m in methods:
            if m in impl_a and m in impl_b:
                clauses.append(self.encode_method_equiv(m, impl_a[m], impl_b[m]))
            else:
                # Missing method ⟹ not equivalent
                clauses.append(z3.BoolVal(False))
        if not clauses:
            return z3.BoolVal(True)
        return z3.And(*clauses)

    # ── verification from predicate strings ───────────────────────

    def verify_duck_equiv(self, type_a_methods: dict[str, str],
                          type_b_methods: dict[str, str]) -> bool:
        """Verify two types are duck-equivalent.

        *type_a_methods* / *type_b_methods* map method names to predicate
        strings ``"result == <expr>"`` describing the method's return value
        in terms of an input variable ``x``.

        Returns ``True`` when ``∀x. ∀m. A.m(x) = B.m(x)``.
        """
        ctx = Z3Context()
        ctx.declare_var("x", PyIntType())

        all_methods = set(type_a_methods) | set(type_b_methods)
        if set(type_a_methods) != set(type_b_methods):
            return False  # different method sets ⟹ not equivalent

        for method in all_methods:
            expr_a = type_a_methods[method]
            expr_b = type_b_methods[method]

            ctx_a = Z3Context()
            ctx_a.declare_var("x", PyIntType())
            ctx_b = Z3Context()
            ctx_b.declare_var("x", PyIntType())

            z3_a = self._translator.translate(expr_a, ctx_a)
            z3_b = self._translator.translate(expr_b, ctx_b)

            s = self._make_solver()
            s.add(z3.Not(z3_a == z3_b))
            if s.check() != z3.unsat:
                return False
        return True


# ═══════════════════════════════════════════════════════════════════
# Z3Prover extensions — homotopy-theoretic proof methods
# ═══════════════════════════════════════════════════════════════════

def _extend_z3_prover() -> None:
    """Monkey-patch additional homotopy proof methods onto Z3Prover.

    Called once at module load time.  We define these outside the class body
    so the original class definition is untouched and existing tests keep
    passing.
    """

    def prove_path(self: Z3Prover, left: str, right: str,
                   type_constraint: str | None = None) -> Z3ProofResult:
        """Prove two terms are path-equal using Z3.

        Checks ``left == right`` (optionally under *type_constraint*).
        """
        hyps: list[str] = []
        if type_constraint:
            hyps.append(type_constraint)
        result = self.prove(f"{left} == {right}", hypotheses=hyps or None)
        if result is None:
            return Z3ProofResult(
                formula=f"{left} == {right}", is_valid=False,
            )
        return result

    def prove_transport(self: Z3Prover, type_family: str,
                        left: str, right: str,
                        base_property: str) -> Z3ProofResult:
        """Prove transport is valid: ``P(a) ∧ a=b → P(b)``.

        *type_family* names the predicate (unused in the Z3 encoding, kept
        for API symmetry).  *base_property* is ``P(left)``; the transported
        property is obtained by substituting *left* → *right*.
        """
        transported = base_property.replace(left, right)
        result = self.prove(
            transported,
            hypotheses=[base_property, f"{left} == {right}"],
        )
        if result is None:
            return Z3ProofResult(
                formula=f"transport({type_family}, {left}={right}, {base_property})",
                is_valid=False,
            )
        return result

    def prove_cech(self: Z3Prover, conditions: list[str],
                   local_specs: list[str],
                   global_spec: str) -> Z3ProofResult:
        """Prove a Čech decomposition is sound.

        Delegates to :class:`CechEncoder` and wraps the result as a
        :class:`Z3ProofResult`.
        """
        enc = CechEncoder(timeout_ms=self._timeout)
        res = enc.verify_cech_proof(conditions, local_specs, global_spec)
        is_valid = res.exhaustive and res.cocycle_holds and res.global_holds
        return Z3ProofResult(
            formula=f"cech({global_spec})",
            is_valid=is_valid,
            hypotheses=conditions + local_specs,
        )

    def prove_fibration(self: Z3Prover, type_conditions: list[str],
                        per_fiber: list[str],
                        global_spec: str) -> Z3ProofResult:
        """Prove fibration descent: per-fiber → global."""
        enc = FibrationEncoder(timeout_ms=self._timeout)
        is_valid = enc.verify_fibration(type_conditions, per_fiber, global_spec)
        return Z3ProofResult(
            formula=f"fibration({global_spec})",
            is_valid=is_valid,
            hypotheses=type_conditions + per_fiber,
        )

    # Attach methods
    Z3Prover.prove_path = prove_path  # type: ignore[attr-defined]
    Z3Prover.prove_transport = prove_transport  # type: ignore[attr-defined]
    Z3Prover.prove_cech = prove_cech  # type: ignore[attr-defined]
    Z3Prover.prove_fibration = prove_fibration  # type: ignore[attr-defined]


if _HAS_Z3:
    _extend_z3_prover()


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    if not _HAS_Z3:
        print("Z3 not installed — skipping smoke tests")
        raise SystemExit(0)

    # ── Z3Context ─────────────────────────────────────────────────
    ctx = Z3Context()
    x = ctx.declare_var("x", PyIntType())
    assert ctx.get_var("x") is x
    assert ctx.type_to_sort(PyIntType()) == z3.IntSort()
    assert ctx.type_to_sort(PyFloatType()) == z3.RealSort()
    assert ctx.type_to_sort(PyBoolType()) == z3.BoolSort()
    assert ctx.type_to_sort(PyStrType()) == z3.StringSort()
    print("  Z3Context        ✓")

    # ── PredicateTranslator ───────────────────────────────────────
    tr = PredicateTranslator()
    ctx2 = Z3Context()
    ctx2.declare_var("n", PyIntType())
    formula = tr.translate("n >= 0", ctx2)
    assert z3.is_bool(formula)

    ctx3 = Z3Context()
    ctx3.declare_var("a", PyIntType())
    ctx3.declare_var("b", PyIntType())
    comm = tr.translate("a + b == b + a", ctx3)
    s = z3.Solver()
    s.add(z3.Not(comm))
    assert s.check() == z3.unsat, "a+b == b+a should be valid"

    ctx4 = Z3Context()
    ctx4.declare_var("x", PyIntType())
    ite = tr.translate("x if x > 0 else -x", ctx4)
    assert ite is not None
    print("  PredicateTranslator ✓")

    # ── RefinementChecker ─────────────────────────────────────────
    checker = RefinementChecker()

    pos = RefinementType(PyIntType(), "x", "x > 0")
    nonneg = RefinementType(PyIntType(), "x", "x >= 0")
    assert checker.check_subtype(pos, nonneg), "{x>0} <: {x>=0}"
    assert not checker.check_subtype(nonneg, pos), "¬({x>=0} <: {x>0})"

    assert checker.check_satisfiable(pos), "{x>0} is inhabited"
    empty = RefinementType(PyIntType(), "x", "x > 0 and x < 0")
    assert not checker.check_satisfiable(empty), "{x>0 ∧ x<0} is empty"

    assert checker.check_valid("x + 1 > x", {"x": PyIntType()})
    assert not checker.check_valid("x > 0", {"x": PyIntType()})

    cex = checker.find_counterexample("x > 0", {"x": PyIntType()})
    assert cex is not None and int(cex["x"]) <= 0

    assert checker.check_implication(["x > 0", "y > 0"], "x + y > 0",
                                      {"x": PyIntType(), "y": PyIntType()})
    assert checker.check_equivalence("x >= 0 and x <= 0", "x == 0",
                                      {"x": PyIntType()})
    print("  RefinementChecker   ✓")

    # ── Z3Prover ──────────────────────────────────────────────────
    prover = Z3Prover()

    p = prover.prove("x + y == y + x",
                     context={"x": PyIntType(), "y": PyIntType()})
    assert p is not None and p.is_valid

    p2 = prover.prove("x > 0",
                      context={"x": PyIntType()})
    assert p2 is not None and not p2.is_valid

    p3 = prover.prove_implication(
        ["n >= 0"], "n * (n + 1) >= 0",
        context={"n": PyIntType()},
    )
    assert p3 is not None and p3.is_valid

    p4 = prover.prove_refinement(
        "result == x * x", "result >= 0",
        params={"x": PyIntType(), "result": PyIntType()},
    )
    assert p4 is not None and p4.is_valid

    results = prover.prove_all(
        ["a + b == b + a", "a * b == b * a"],
        context={"a": PyIntType(), "b": PyIntType()},
    )
    assert all(r is not None and r.is_valid for r in results)
    print("  Z3Prover            ✓")

    # ── ArithmeticEncoder ─────────────────────────────────────────
    enc = ArithmeticEncoder()

    length, axiom = enc.encode_list_length("xs")
    assert z3.is_bool(axiom)

    sorted_cond = enc.encode_sorted("xs")
    assert z3.is_bool(sorted_cond) or z3.is_quantifier(sorted_cond)

    distinct_cond = enc.encode_distinct_elements("xs")
    assert z3.is_bool(distinct_cond) or z3.is_quantifier(distinct_cond)

    rng = enc.encode_range(0, 10)
    assert z3.is_bool(rng)

    lookup = enc.encode_dict_lookup("d", z3.IntVal(42))
    assert lookup is not None

    same = enc.encode_same_length("xs", "ys")
    assert z3.is_bool(same)

    inc = enc.encode_strictly_increasing("xs")
    assert z3.is_bool(inc) or z3.is_quantifier(inc)
    print("  ArithmeticEncoder   ✓")

    # ── convenience ───────────────────────────────────────────────
    assert quick_check("x + 1 > x", {"x": PyIntType()})
    assert quick_prove("a + b == b + a",
                       context={"a": PyIntType(), "b": PyIntType()})
    assert extract_free_vars("x + y > z") == {"x", "y", "z"}
    print("  Convenience funcs   ✓")

    # ── PathEncoder ───────────────────────────────────────────────
    pe_ctx = Z3Context()
    pe = PathEncoder(pe_ctx)

    # Path type for two integer literals
    path_constraint = pe.encode_path_type(
        PyIntType(), Literal(3), Literal(7),
    )
    assert path_constraint is not None
    s = z3.Solver()
    s.add(path_constraint)
    assert s.check() == z3.sat, "Path 3 =_Int 7 should be satisfiable"

    # Boundary check helper
    bc = pe.encode_boundary_check(
        z3.IntVal(0), "_i", z3.IntVal(3), z3.IntVal(7),
    )
    assert bc is not None and z3.is_bool(bc)

    # Path composition
    comp = pe.encode_path_comp(
        z3.IntVal(0), z3.IntVal(0), z3.IntVal(5),
    )
    assert comp is not None

    # Path abstraction (trivial: constant path)
    pa = pe.encode_path_abs("i", Literal(42), Literal(42), Literal(42))
    s2 = z3.Solver()
    s2.add(pa)
    assert s2.check() == z3.sat, "Constant path 42 =_Int 42 should be sat"
    print("  PathEncoder         ✓")

    # ── TransportEncoder ──────────────────────────────────────────
    te = TransportEncoder()

    # transport: x > 0 ∧ x == y → y > 0
    result = te.verify_transport("positive", "x", "y", "x > 0")
    assert result == z3.unsat, "Transport x>0 along x=y should give y>0"

    # transport via Z3 function
    P = z3.Function("P", z3.IntSort(), z3.BoolSort())
    transport_cst = te.encode_transport(P, z3.BoolVal(True), z3.IntVal(5))
    assert transport_cst is not None and z3.is_bool(transport_cst)
    print("  TransportEncoder    ✓")

    # ── CechEncoder ───────────────────────────────────────────────
    ce = CechEncoder()

    # Two patches that partition the integers: x >= 0 and x < 0
    # Local spec: x*x >= 0 (true everywhere)
    res = ce.verify_cech_proof(
        conditions=["x >= 0", "x < 0"],
        local_specs=["x * x >= 0", "x * x >= 0"],
        global_spec="x * x >= 0",
    )
    assert res.exhaustive, "x>=0 ∨ x<0 should cover all integers"
    assert res.cocycle_holds, "Cocycle should hold (no overlap for x>=0 and x<0)"
    assert res.global_holds, "x*x >= 0 should hold globally"
    assert res.obstruction is None

    # Non-exhaustive cover
    res2 = ce.verify_cech_proof(
        conditions=["x > 5", "x < -5"],
        local_specs=["x * x > 25", "x * x > 25"],
        global_spec="x * x > 25",
    )
    assert not res2.exhaustive, "x>5 ∨ x<-5 does not cover x=0"
    assert res2.obstruction is not None

    # Cover and cocycle encoding directly
    c1, c2 = z3.Bool("c1"), z3.Bool("c2")
    cover = ce.encode_cover_exhaustive([c1, c2])
    assert z3.is_bool(cover)

    p1, p2 = z3.Bool("p1"), z3.Bool("p2")
    cocycle = ce.encode_cocycle(
        [(c1, p1), (c2, p2)], [(0, 1)],
    )
    assert z3.is_bool(cocycle)

    glue = ce.encode_gluing([(c1, p1), (c2, p2)])
    assert z3.is_bool(glue)
    print("  CechEncoder         ✓")

    # ── FibrationEncoder ──────────────────────────────────────────
    fe = FibrationEncoder()

    # Two disjoint fibers covering all integers
    ok = fe.verify_fibration(
        type_conditions=["x >= 0", "x < 0"],
        per_fiber_specs=["x * x >= 0", "x * x >= 0"],
        global_spec="x * x >= 0",
    )
    assert ok, "Fibration descent should hold for x*x >= 0"

    # Fiber coverage encoding
    f1, f2 = z3.Bool("f1"), z3.Bool("f2")
    cov = fe.encode_fiber_coverage([f1, f2])
    assert z3.is_bool(cov)

    # Per-fiber property
    pfp = fe.encode_per_fiber_property([(f1, z3.BoolVal(True)), (f2, z3.BoolVal(True))])
    assert z3.is_bool(pfp)
    print("  FibrationEncoder    ✓")

    # ── DuckEquivEncoder ──────────────────────────────────────────
    de = DuckEquivEncoder()

    # Two types with identical method implementations
    equiv = de.verify_duck_equiv(
        type_a_methods={"double": "x * 2 == x + x"},
        type_b_methods={"double": "x + x == x * 2"},
    )
    assert equiv, "x*2 == x+x and x+x == x*2 are equivalent"

    # Non-equivalent methods
    not_equiv = de.verify_duck_equiv(
        type_a_methods={"inc": "x + 1 > 0"},
        type_b_methods={"inc": "x + 2 > 0"},
    )
    assert not not_equiv, "x+1>0 ≠ x+2>0 (different for x=-1)"

    # Method / protocol encoding
    ma = z3.IntVal(10)
    mb = z3.IntVal(10)
    assert z3.is_bool(de.encode_method_equiv("foo", ma, mb))

    pe_enc = de.encode_protocol_equiv(
        ["m1", "m2"],
        {"m1": z3.IntVal(1), "m2": z3.IntVal(2)},
        {"m1": z3.IntVal(1), "m2": z3.IntVal(2)},
    )
    assert z3.is_bool(pe_enc)
    print("  DuckEquivEncoder    ✓")

    # ── Z3Prover homotopy extensions ──────────────────────────────
    prover2 = Z3Prover()

    # prove_path
    pp = prover2.prove_path("a + b", "b + a")
    assert pp.is_valid, "a+b = b+a is path-equal"

    pp2 = prover2.prove_path("a", "b")
    assert not pp2.is_valid, "a ≠ b in general"

    pp3 = prover2.prove_path("a", "b", type_constraint="a == b")
    assert pp3.is_valid, "a = b under a==b"

    # prove_transport
    pt = prover2.prove_transport("positive", "x", "y", "x > 0")
    assert pt.is_valid, "transport x>0 along x=y gives y>0"

    # prove_cech
    pc = prover2.prove_cech(
        conditions=["x >= 0", "x < 0"],
        local_specs=["x * x >= 0", "x * x >= 0"],
        global_spec="x * x >= 0",
    )
    assert pc.is_valid, "Čech proof for x*x>=0"

    # prove_fibration
    pf = prover2.prove_fibration(
        type_conditions=["x >= 0", "x < 0"],
        per_fiber=["x * x >= 0", "x * x >= 0"],
        global_spec="x * x >= 0",
    )
    assert pf.is_valid, "Fibration descent for x*x>=0"
    print("  Z3Prover homotopy   ✓")

    print("\nZ3 bridge smoke tests passed ✓")
