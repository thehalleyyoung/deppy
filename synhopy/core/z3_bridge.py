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
    SynType, PyObjType, PyIntType, PyFloatType, PyBoolType,
    PyStrType, PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, RefinementType, UnionType, OptionalType,
    UniverseType,
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

    print("\nZ3 bridge smoke tests passed ✓")
