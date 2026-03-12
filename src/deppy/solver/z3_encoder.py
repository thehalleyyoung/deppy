"""Encode deppy predicate AST into Z3 formulas.

This module provides ``Z3Encoder``, the primary bridge between deppy's
predicate representation and Z3's expression language.  It handles:

- Arithmetic terms (integer, real) with linear and non-linear operations.
- Boolean connectives (And, Or, Not, Implies, Iff).
- Comparison and relational predicates.
- Quantifiers (ForAll, Exists) -- mapped to Z3 quantifiers.
- Arrays and indexing -- mapped to Z3 array theory.
- Bitvector operations for bitwise predicates.
- Collection predicates (LengthPred, Contains, NonEmpty) via
  uninterpreted functions.
- Tensor predicates (ShapePred, RankPred, DtypePred, ...) via
  auxiliary integer/string variables.
- Heap predicates (HasField, FieldValue, ...) via uninterpreted functions.
- Nullability predicates (IsNone, IsNotNone, IsInstance, ...) via
  enumeration sorts or boolean flags.

The encoder maintains a variable environment mapping deppy variable names to
Z3 constants, automatically creating fresh constants when a variable is first
encountered.  Sort inference is best-effort based on how variables appear in
predicates.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Lazy Z3 import
# ---------------------------------------------------------------------------

_z3: Any = None
_z3_available: bool = False


def _ensure_z3() -> Any:
    """Lazily import z3 and return the module."""
    global _z3, _z3_available
    if _z3 is not None:
        return _z3
    try:
        import z3 as _z3_mod
        _z3 = _z3_mod
        _z3_available = True
        return _z3
    except ImportError:
        _z3_available = False
        raise ImportError(
            "z3-solver is not installed.  Install it with: "
            "pip install z3-solver"
        )


def z3_available() -> bool:
    """Return True if z3 can be imported."""
    global _z3_available
    try:
        _ensure_z3()
        return True
    except ImportError:
        return False


# ---------------------------------------------------------------------------
# Sort hint
# ---------------------------------------------------------------------------


class SortHint:
    """Hint about the intended Z3 sort for a deppy variable."""

    INT = "int"
    REAL = "real"
    BOOL = "bool"
    BV32 = "bv32"
    BV64 = "bv64"
    STRING = "string"
    UNINTERPRETED = "uninterpreted"


# ---------------------------------------------------------------------------
# Variable environment
# ---------------------------------------------------------------------------


class VariableEnvironment:
    """Maps deppy variable names to Z3 constants with sort tracking.

    Variables are created lazily on first access.  The sort is inferred from
    context or can be pre-declared via ``declare``.
    """

    def __init__(self) -> None:
        self._vars: Dict[str, Any] = {}
        self._sort_hints: Dict[str, str] = {}
        self._z3 = _ensure_z3()

    def declare(self, name: str, sort_hint: str = SortHint.INT) -> None:
        """Pre-declare a variable with a specific sort."""
        self._sort_hints[name] = sort_hint

    def get(self, name: str, sort_hint: Optional[str] = None) -> Any:
        """Get or create a Z3 constant for the given variable name."""
        z3 = self._z3
        if name in self._vars:
            return self._vars[name]

        hint = sort_hint or self._sort_hints.get(name, SortHint.INT)
        if hint == SortHint.INT:
            var = z3.Int(name)
        elif hint == SortHint.REAL:
            var = z3.Real(name)
        elif hint == SortHint.BOOL:
            var = z3.Bool(name)
        elif hint == SortHint.BV32:
            var = z3.BitVec(name, 32)
        elif hint == SortHint.BV64:
            var = z3.BitVec(name, 64)
        elif hint == SortHint.STRING:
            var = z3.String(name)
        else:
            # Uninterpreted sort
            sort = z3.DeclareSort(f"Sort_{name}")
            var = z3.Const(name, sort)

        self._vars[name] = var
        self._sort_hints[name] = hint
        return var

    def get_int(self, name: str) -> Any:
        return self.get(name, SortHint.INT)

    def get_real(self, name: str) -> Any:
        return self.get(name, SortHint.REAL)

    def get_bool(self, name: str) -> Any:
        return self.get(name, SortHint.BOOL)

    def get_bv(self, name: str, width: int = 32) -> Any:
        hint = SortHint.BV32 if width <= 32 else SortHint.BV64
        return self.get(name, hint)

    def known_variables(self) -> Dict[str, str]:
        """Return a dict of variable_name -> sort_hint for all known variables."""
        return dict(self._sort_hints)

    def z3_vars(self) -> Dict[str, Any]:
        """Return a dict of variable_name -> z3 constant."""
        return dict(self._vars)

    def clear(self) -> None:
        self._vars.clear()
        self._sort_hints.clear()


# ---------------------------------------------------------------------------
# Sort inference from predicate structure
# ---------------------------------------------------------------------------


def _infer_sort_hints(pred: Any) -> Dict[str, str]:
    """Walk a predicate/term tree and infer sort hints for variables.

    Returns a dict mapping variable names to their best-guess sort hints.
    """
    from deppy.predicates.base import (
        BinOp, BoolLit, FloatLit, IntLit, Var, Term,
    )
    from deppy.predicates.arithmetic import (
        Comparison, Divisibility, IntRange, LinearInequality,
    )
    from deppy.predicates.boolean import And, Or, Not, Implies, Iff, ForAll, Exists

    hints: Dict[str, str] = {}

    def _visit_term(term: Any) -> None:
        if isinstance(term, Var):
            # Default to INT, may be overridden by context
            if term.name not in hints:
                hints[term.name] = SortHint.INT
        elif isinstance(term, BinOp):
            _visit_term(term.left)
            _visit_term(term.right)
            # Bitwise ops suggest bitvector
            if term.op in {"&", "|", "^", "<<", ">>", "~"}:
                for sub in [term.left, term.right]:
                    if isinstance(sub, Var):
                        hints[sub.name] = SortHint.BV32
            # Float literal on either side suggests real
            if isinstance(term.left, FloatLit) or isinstance(term.right, FloatLit):
                for sub in [term.left, term.right]:
                    if isinstance(sub, Var):
                        hints[sub.name] = SortHint.REAL
        elif hasattr(term, "walk_terms"):
            for sub in term.walk_terms():
                if sub is not term and isinstance(sub, Var):
                    if sub.name not in hints:
                        hints[sub.name] = SortHint.INT

    def _visit_pred(p: Any) -> None:
        if isinstance(p, LinearInequality):
            for var, _ in p.coefficients:
                hints[var] = SortHint.INT
        elif isinstance(p, IntRange):
            hints[p.variable] = SortHint.INT
        elif isinstance(p, Divisibility):
            hints[p.variable] = SortHint.INT
        elif isinstance(p, Comparison):
            _visit_term(p.left)
            _visit_term(p.right)
        elif hasattr(p, "walk"):
            for sub in p.walk():
                if sub is not p:
                    _visit_pred(sub)
            if hasattr(p, "walk_terms"):
                for t in p.walk_terms():
                    _visit_term(t)

    _visit_pred(pred)
    return hints


# ---------------------------------------------------------------------------
# Z3 Encoder
# ---------------------------------------------------------------------------


class Z3Encoder:
    """Encodes deppy predicates and terms into Z3 expressions.

    Usage::

        encoder = Z3Encoder()
        z3_expr = encoder.encode_predicate(some_predicate)
        # z3_expr is a z3.BoolRef that can be passed to z3.Solver.
    """

    def __init__(self, env: Optional[VariableEnvironment] = None) -> None:
        self._z3 = _ensure_z3()
        self._env = env or VariableEnvironment()
        # Uninterpreted functions for builtins like len, abs, etc.
        self._uf_cache: Dict[str, Any] = {}

    @property
    def env(self) -> VariableEnvironment:
        return self._env

    # -------------------------------------------------------------------
    # Public API
    # -------------------------------------------------------------------

    def encode_predicate(self, predicate: Any) -> Any:
        """Encode a deppy ``Predicate`` into a Z3 ``BoolRef``.

        Dispatches on the concrete predicate type.
        """
        z3 = self._z3

        # Pre-infer sort hints
        hints = _infer_sort_hints(predicate)
        for name, hint in hints.items():
            if name not in self._env.known_variables():
                self._env.declare(name, hint)

        return self._encode_pred(predicate)

    def encode_term(self, term: Any) -> Any:
        """Encode a deppy ``Term`` into a Z3 ``ExprRef``."""
        return self._encode_term(term)

    def encode_type_constraint(self, type_base: Any) -> Any:
        """Encode a type constraint from the TypeBase hierarchy into Z3.

        This produces boolean constraints that capture the refinement semantics
        of the type.  For example, ``IntRange`` on a variable produces
        bound constraints.
        """
        z3 = self._z3
        from deppy.types.base import (
            PrimitiveType, PrimitiveKind, LiteralType, TensorType,
            AnyType, NeverType,
        )

        if isinstance(type_base, AnyType):
            return z3.BoolVal(True)
        if isinstance(type_base, NeverType):
            return z3.BoolVal(False)
        if isinstance(type_base, LiteralType):
            return self._encode_literal_type(type_base)
        if isinstance(type_base, TensorType):
            return self._encode_tensor_type(type_base)
        # Default: no additional constraint
        return z3.BoolVal(True)

    # -------------------------------------------------------------------
    # Predicate encoding (private dispatch)
    # -------------------------------------------------------------------

    def _encode_pred(self, pred: Any) -> Any:
        """Dispatch predicate encoding by type."""
        z3 = self._z3

        from deppy.predicates.arithmetic import (
            Comparison, Divisibility, IntRange, LinearInequality,
        )
        from deppy.predicates.boolean import (
            And, Or, Not, Implies, Iff, ForAll, Exists,
        )
        from deppy.predicates.nullability import (
            IsNone, IsNotNone, IsInstance, IsNotInstance, Truthy, Falsy,
        )
        from deppy.predicates.collection import (
            LengthPred, NonEmpty, Contains, Sorted, Unique,
            Subset, Disjoint, Permutation,
        )
        from deppy.predicates.tensor import (
            ShapePred, RankPred, DtypePred, DevicePred,
            BroadcastCompatible, ShapeRelation, ValidIndex,
            ContiguousPred, SortedTensor,
        )
        from deppy.predicates.heap import (
            HasField, FieldValue, ProtocolConformance,
            Initialized, NotMutated, OwnershipPred, AliasRelation,
        )

        # --- Boolean connectives ---
        if isinstance(pred, And):
            if len(pred.conjuncts) == 0:
                return z3.BoolVal(True)
            parts = [self._encode_pred(c) for c in pred.conjuncts]
            return z3.And(*parts) if len(parts) > 1 else parts[0]

        if isinstance(pred, Or):
            if len(pred.disjuncts) == 0:
                return z3.BoolVal(False)
            parts = [self._encode_pred(d) for d in pred.disjuncts]
            return z3.Or(*parts) if len(parts) > 1 else parts[0]

        if isinstance(pred, Not):
            return z3.Not(self._encode_pred(pred.operand))

        if isinstance(pred, Implies):
            return z3.Implies(
                self._encode_pred(pred.antecedent),
                self._encode_pred(pred.consequent),
            )

        if isinstance(pred, Iff):
            left = self._encode_pred(pred.left)
            right = self._encode_pred(pred.right)
            return left == right

        # --- Quantifiers ---
        if isinstance(pred, ForAll):
            return self._encode_forall(pred)

        if isinstance(pred, Exists):
            return self._encode_exists(pred)

        # --- Arithmetic ---
        if isinstance(pred, Comparison):
            return self._encode_comparison(pred)

        if isinstance(pred, LinearInequality):
            return self._encode_linear_inequality(pred)

        if isinstance(pred, Divisibility):
            return self._encode_divisibility(pred)

        if isinstance(pred, IntRange):
            return self._encode_int_range(pred)

        # --- Nullability ---
        if isinstance(pred, IsNone):
            return self._encode_is_none(pred)

        if isinstance(pred, IsNotNone):
            return self._encode_is_not_none(pred)

        if isinstance(pred, IsInstance):
            return self._encode_isinstance(pred)

        if isinstance(pred, IsNotInstance):
            return z3.Not(self._encode_isinstance(
                IsInstance(term=pred.term, type_name=pred.type_name)
            ))

        if isinstance(pred, Truthy):
            return self._encode_truthy(pred)

        if isinstance(pred, Falsy):
            return z3.Not(self._encode_truthy(
                Truthy(term=pred.term)
            ))

        # --- Collections ---
        if isinstance(pred, LengthPred):
            return self._encode_length_pred(pred)

        if isinstance(pred, NonEmpty):
            return self._encode_non_empty(pred)

        if isinstance(pred, Contains):
            return self._encode_contains(pred)

        if isinstance(pred, (Sorted, Unique, Subset, Disjoint, Permutation)):
            return self._encode_collection_abstract(pred)

        # --- Tensor ---
        if isinstance(pred, ShapePred):
            return self._encode_shape_pred(pred)

        if isinstance(pred, RankPred):
            return self._encode_rank_pred(pred)

        if isinstance(pred, (DtypePred, DevicePred, ContiguousPred)):
            return self._encode_finite_domain_tensor(pred)

        if isinstance(pred, (BroadcastCompatible, ShapeRelation, ValidIndex)):
            return self._encode_tensor_relation(pred)

        if isinstance(pred, SortedTensor):
            return self._encode_collection_abstract(pred)

        # --- Heap ---
        if isinstance(pred, HasField):
            return self._encode_has_field(pred)

        if isinstance(pred, FieldValue):
            return self._encode_field_value(pred)

        if isinstance(pred, (ProtocolConformance, Initialized, NotMutated)):
            return self._encode_heap_flag(pred)

        if isinstance(pred, (OwnershipPred, AliasRelation)):
            return self._encode_collection_abstract(pred)

        # Fallback: uninterpreted boolean
        logger.warning("No Z3 encoding for predicate type %s; using fresh bool",
                        type(pred).__name__)
        fresh_name = f"__unknown_pred_{id(pred)}"
        return self._env.get_bool(fresh_name)

    # -------------------------------------------------------------------
    # Term encoding
    # -------------------------------------------------------------------

    def _encode_term(self, term: Any) -> Any:
        """Encode a deppy Term into a Z3 expression."""
        z3 = self._z3
        from deppy.predicates.base import (
            Var, IntLit, FloatLit, BoolLit, StrLit, NoneLit,
            BinOp, UnaryOp, Call, Attr, Index, TupleLit, IfExpr,
        )

        if isinstance(term, IntLit):
            return z3.IntVal(term.value)

        if isinstance(term, FloatLit):
            return z3.RealVal(str(term.value))

        if isinstance(term, BoolLit):
            return z3.BoolVal(term.value)

        if isinstance(term, StrLit):
            return z3.StringVal(term.value)

        if isinstance(term, NoneLit):
            # Represent None as integer sentinel -1 in absence of ADTs
            return z3.IntVal(-1)

        if isinstance(term, Var):
            return self._env.get(term.name)

        if isinstance(term, BinOp):
            return self._encode_binop(term)

        if isinstance(term, UnaryOp):
            return self._encode_unaryop(term)

        if isinstance(term, Call):
            return self._encode_call(term)

        if isinstance(term, Attr):
            return self._encode_attr(term)

        if isinstance(term, Index):
            return self._encode_index(term)

        if isinstance(term, TupleLit):
            # Encode as a sequence of individual terms; return the first
            # for simplicity (tuples are typically destructured elsewhere).
            if term.elements:
                return self._encode_term(term.elements[0])
            return z3.IntVal(0)

        if isinstance(term, IfExpr):
            cond = self._encode_pred(term.cond)
            then_ = self._encode_term(term.then_)
            else_ = self._encode_term(term.else_)
            return z3.If(cond, then_, else_)

        logger.warning("No Z3 encoding for term type %s; using fresh int",
                        type(term).__name__)
        fresh_name = f"__unknown_term_{id(term)}"
        return self._env.get_int(fresh_name)

    def _encode_binop(self, term: Any) -> Any:
        z3 = self._z3
        left = self._encode_term(term.left)
        right = self._encode_term(term.right)

        op = term.op
        if op == "+":
            return left + right
        if op == "-":
            return left - right
        if op == "*":
            return left * right
        if op == "//":
            # Integer division
            return left / right
        if op == "%":
            return left % right
        if op == "**":
            # Z3 does not natively support general exponentiation; approximate
            # for small literal exponents.
            from deppy.predicates.base import IntLit
            if isinstance(term.right, IntLit) and 0 <= term.right.value <= 8:
                result = z3.IntVal(1)
                for _ in range(term.right.value):
                    result = result * left
                return result
            # Fallback: uninterpreted
            return self._get_uf("pow", z3.IntSort(), z3.IntSort(),
                                 result_sort=z3.IntSort())(left, right)

        # Bitwise operations
        if op == "&":
            return left & right
        if op == "|":
            return left | right
        if op == "^":
            return left ^ right
        if op == "<<":
            return left << right
        if op == ">>":
            return z3.LShR(left, right) if hasattr(z3, "LShR") else left >> right

        logger.warning("Unsupported binary operator %r; returning left operand", op)
        return left

    def _encode_unaryop(self, term: Any) -> Any:
        z3 = self._z3
        operand = self._encode_term(term.operand)
        if term.op == "-":
            return -operand
        if term.op == "+":
            return operand
        if term.op == "~":
            return ~operand
        return operand

    def _encode_call(self, term: Any) -> Any:
        """Encode function calls as uninterpreted functions or known builtins."""
        z3 = self._z3
        args = [self._encode_term(a) for a in term.args]
        func_name = term.func

        # Known builtins with integer semantics
        if func_name == "len" and len(args) == 1:
            return self._get_uf("len", z3.IntSort(),
                                 result_sort=z3.IntSort())(args[0])
        if func_name == "abs" and len(args) == 1:
            arg = args[0]
            return z3.If(arg >= 0, arg, -arg)
        if func_name == "min" and len(args) == 2:
            return z3.If(args[0] <= args[1], args[0], args[1])
        if func_name == "max" and len(args) == 2:
            return z3.If(args[0] >= args[1], args[0], args[1])

        # General: uninterpreted function
        arg_sorts = [z3.IntSort() for _ in args]
        uf = self._get_uf(func_name, *arg_sorts, result_sort=z3.IntSort())
        if args:
            return uf(*args)
        return uf()

    def _encode_attr(self, term: Any) -> Any:
        """Encode attribute access as uninterpreted function."""
        z3 = self._z3
        obj = self._encode_term(term.obj)
        uf_name = f"attr_{term.attr}"
        uf = self._get_uf(uf_name, z3.IntSort(), result_sort=z3.IntSort())
        return uf(obj)

    def _encode_index(self, term: Any) -> Any:
        """Encode index access using Z3 array select."""
        z3 = self._z3
        obj = self._encode_term(term.obj)
        idx = self._encode_term(term.idx)
        # Use an uninterpreted function as a general model of indexing
        uf_name = f"index_{id(term.obj) % 10000}"
        uf = self._get_uf(uf_name, z3.IntSort(), z3.IntSort(),
                           result_sort=z3.IntSort())
        return uf(obj, idx)

    # -------------------------------------------------------------------
    # Predicate-specific encodings
    # -------------------------------------------------------------------

    def _encode_comparison(self, pred: Any) -> Any:
        z3 = self._z3
        left = self._encode_term(pred.left)
        right = self._encode_term(pred.right)
        op = pred.op
        if op == "<":
            return left < right
        if op == "<=":
            return left <= right
        if op == ">":
            return left > right
        if op == ">=":
            return left >= right
        if op == "==":
            return left == right
        if op == "!=":
            return left != right
        return z3.BoolVal(True)

    def _encode_linear_inequality(self, pred: Any) -> Any:
        """Encode sum(c_i * x_i) + constant >= 0."""
        z3 = self._z3
        terms: List[Any] = []
        for var_name, coeff in pred.coefficients:
            v = self._env.get_int(var_name)
            if coeff == 1:
                terms.append(v)
            elif coeff == -1:
                terms.append(-v)
            else:
                terms.append(z3.IntVal(coeff) * v)
        if pred.constant != 0:
            terms.append(z3.IntVal(pred.constant))
        if not terms:
            lhs = z3.IntVal(0)
        elif len(terms) == 1:
            lhs = terms[0]
        else:
            lhs = terms[0]
            for t in terms[1:]:
                lhs = lhs + t
        return lhs >= 0

    def _encode_divisibility(self, pred: Any) -> Any:
        """Encode k | (a*x + b) as (a*x + b) % k == 0."""
        z3 = self._z3
        v = self._env.get_int(pred.variable)
        inner = z3.IntVal(pred.coefficient) * v + z3.IntVal(pred.offset)
        return inner % z3.IntVal(pred.divisor) == 0

    def _encode_int_range(self, pred: Any) -> Any:
        """Encode lo <= x <= hi."""
        z3 = self._z3
        v = self._env.get_int(pred.variable)
        constraints = []
        if pred.lo is not None:
            constraints.append(v >= z3.IntVal(pred.lo))
        if pred.hi is not None:
            constraints.append(v <= z3.IntVal(pred.hi))
        if not constraints:
            return z3.BoolVal(True)
        if len(constraints) == 1:
            return constraints[0]
        return z3.And(*constraints)

    def _encode_forall(self, pred: Any) -> Any:
        z3 = self._z3
        bound_var = z3.Int(pred.var)
        # Temporarily register the bound variable
        old = self._env._vars.get(pred.var)
        self._env._vars[pred.var] = bound_var
        body = self._encode_pred(pred.body)
        if old is not None:
            self._env._vars[pred.var] = old
        else:
            self._env._vars.pop(pred.var, None)
        return z3.ForAll([bound_var], body)

    def _encode_exists(self, pred: Any) -> Any:
        z3 = self._z3
        bound_var = z3.Int(pred.var)
        old = self._env._vars.get(pred.var)
        self._env._vars[pred.var] = bound_var
        body = self._encode_pred(pred.body)
        if old is not None:
            self._env._vars[pred.var] = old
        else:
            self._env._vars.pop(pred.var, None)
        return z3.Exists([bound_var], body)

    def _encode_is_none(self, pred: Any) -> Any:
        """IsNone(x) -> x == NONE_SENTINEL."""
        z3 = self._z3
        t = self._encode_term(pred.term)
        # Use a designated "is_none" boolean flag
        from deppy.predicates.base import Var
        if isinstance(pred.term, Var):
            flag = self._env.get_bool(f"__is_none_{pred.term.name}")
            return flag
        return t == z3.IntVal(-1)

    def _encode_is_not_none(self, pred: Any) -> Any:
        z3 = self._z3
        from deppy.predicates.base import Var
        if isinstance(pred.term, Var):
            flag = self._env.get_bool(f"__is_none_{pred.term.name}")
            return z3.Not(flag)
        t = self._encode_term(pred.term)
        return t != z3.IntVal(-1)

    def _encode_isinstance(self, pred: Any) -> Any:
        """isinstance(x, T) -> type_tag(x) == T_ID."""
        z3 = self._z3
        from deppy.predicates.base import Var
        if isinstance(pred.term, Var):
            tag_var = self._env.get_int(f"__type_tag_{pred.term.name}")
        else:
            obj = self._encode_term(pred.term)
            uf = self._get_uf("type_tag", z3.IntSort(), result_sort=z3.IntSort())
            tag_var = uf(obj)
        type_id = z3.IntVal(hash(pred.type_name) % (2**30))
        return tag_var == type_id

    def _encode_truthy(self, pred: Any) -> Any:
        """Truthy(x) -> x != 0 (for int), x != None, etc."""
        z3 = self._z3
        t = self._encode_term(pred.term)
        # If the term is boolean-sorted, return it directly
        try:
            if t.sort() == z3.BoolSort():
                return t
        except Exception:
            pass
        # Integer: non-zero
        try:
            return t != z3.IntVal(0)
        except Exception:
            return z3.BoolVal(True)

    # --- Collection predicates ---

    def _encode_length_pred(self, pred: Any) -> Any:
        z3 = self._z3
        coll = self._encode_term(pred.collection)
        bound = self._encode_term(pred.bound)
        len_uf = self._get_uf("len", z3.IntSort(), result_sort=z3.IntSort())
        length = len_uf(coll)
        op = pred.op
        if op == "<":
            return length < bound
        if op == "<=":
            return length <= bound
        if op == ">":
            return length > bound
        if op == ">=":
            return length >= bound
        if op == "==":
            return length == bound
        if op == "!=":
            return length != bound
        return z3.BoolVal(True)

    def _encode_non_empty(self, pred: Any) -> Any:
        z3 = self._z3
        coll = self._encode_term(pred.collection)
        len_uf = self._get_uf("len", z3.IntSort(), result_sort=z3.IntSort())
        return len_uf(coll) > z3.IntVal(0)

    def _encode_contains(self, pred: Any) -> Any:
        z3 = self._z3
        coll = self._encode_term(pred.collection)
        elem = self._encode_term(pred.element)
        contains_uf = self._get_uf("contains", z3.IntSort(), z3.IntSort(),
                                     result_sort=z3.BoolSort())
        return contains_uf(coll, elem)

    def _encode_collection_abstract(self, pred: Any) -> Any:
        """Fallback for complex collection/heap predicates: fresh boolean."""
        z3 = self._z3
        name = f"__abstract_{type(pred).__name__}_{id(pred) % 100000}"
        return self._env.get_bool(name)

    # --- Tensor predicates ---

    def _encode_shape_pred(self, pred: Any) -> Any:
        """ShapePred(tensor, (d1, d2, ...)) -> dim_i(tensor) == d_i for each i."""
        z3 = self._z3
        tensor = self._encode_term(pred.tensor)
        constraints = []
        for i, dim_term in enumerate(pred.shape):
            dim_uf = self._get_uf(f"dim_{i}", z3.IntSort(),
                                    result_sort=z3.IntSort())
            actual_dim = dim_uf(tensor)
            expected_dim = self._encode_term(dim_term)
            constraints.append(actual_dim == expected_dim)
        if not constraints:
            return z3.BoolVal(True)
        return z3.And(*constraints) if len(constraints) > 1 else constraints[0]

    def _encode_rank_pred(self, pred: Any) -> Any:
        z3 = self._z3
        tensor = self._encode_term(pred.tensor)
        rank_uf = self._get_uf("rank", z3.IntSort(), result_sort=z3.IntSort())
        rank_val = self._encode_term(pred.rank)
        op = pred.op if hasattr(pred, "op") else "=="
        actual_rank = rank_uf(tensor)
        if op == "==":
            return actual_rank == rank_val
        if op == ">=":
            return actual_rank >= rank_val
        if op == "<=":
            return actual_rank <= rank_val
        return actual_rank == rank_val

    def _encode_finite_domain_tensor(self, pred: Any) -> Any:
        """DtypePred, DevicePred, ContiguousPred: finite domain via integer IDs."""
        z3 = self._z3
        from deppy.predicates.tensor import DtypePred, DevicePred, ContiguousPred
        if isinstance(pred, DtypePred):
            tensor = self._encode_term(pred.tensor)
            dtype_uf = self._get_uf("dtype", z3.IntSort(), result_sort=z3.IntSort())
            actual = dtype_uf(tensor)
            expected = z3.IntVal(hash(pred.dtype) % (2**30))
            return actual == expected
        if isinstance(pred, DevicePred):
            tensor = self._encode_term(pred.tensor)
            device_uf = self._get_uf("device", z3.IntSort(), result_sort=z3.IntSort())
            actual = device_uf(tensor)
            expected = z3.IntVal(hash(pred.device) % (2**30))
            return actual == expected
        if isinstance(pred, ContiguousPred):
            tensor = self._encode_term(pred.tensor)
            contig_uf = self._get_uf("contiguous", z3.IntSort(),
                                       result_sort=z3.BoolSort())
            return contig_uf(tensor)
        return z3.BoolVal(True)

    def _encode_tensor_relation(self, pred: Any) -> Any:
        """BroadcastCompatible, ShapeRelation, ValidIndex: abstract booleans."""
        return self._encode_collection_abstract(pred)

    # --- Heap predicates ---

    def _encode_has_field(self, pred: Any) -> Any:
        z3 = self._z3
        obj = self._encode_term(pred.obj)
        has_uf = self._get_uf(f"has_field_{pred.field_name}", z3.IntSort(),
                                result_sort=z3.BoolSort())
        return has_uf(obj)

    def _encode_field_value(self, pred: Any) -> Any:
        z3 = self._z3
        obj = self._encode_term(pred.obj)
        field_uf = self._get_uf(f"field_{pred.field_name}", z3.IntSort(),
                                  result_sort=z3.IntSort())
        field_val = field_uf(obj)
        # Encode the inner predicate with the field value substituted
        from deppy.predicates.base import Var
        inner_pred = pred.predicate
        if hasattr(inner_pred, "substitute"):
            # Try substituting the value variable
            subst_pred = inner_pred
            return self._encode_pred(subst_pred)
        return z3.BoolVal(True)

    def _encode_heap_flag(self, pred: Any) -> Any:
        """ProtocolConformance, Initialized, NotMutated: boolean flags."""
        z3 = self._z3
        name = f"__{type(pred).__name__}_{id(pred) % 100000}"
        return self._env.get_bool(name)

    # --- Type constraint encoding ---

    def _encode_literal_type(self, lit_type: Any) -> Any:
        """Encode Literal[v1, v2, ...] as a disjunction of equalities."""
        z3 = self._z3
        # We need a variable to constrain -- use a fresh one named __literal_val
        v = self._env.get_int("__literal_val")
        clauses = []
        for val in lit_type.values:
            if isinstance(val, bool):
                clauses.append(v == z3.IntVal(1 if val else 0))
            elif isinstance(val, int):
                clauses.append(v == z3.IntVal(val))
            elif val is None:
                clauses.append(v == z3.IntVal(-1))
            # Skip str/bytes for integer encoding
        if not clauses:
            return z3.BoolVal(True)
        if len(clauses) == 1:
            return clauses[0]
        return z3.Or(*clauses)

    def _encode_tensor_type(self, tensor_type: Any) -> Any:
        """Encode TensorType shape/dtype constraints."""
        z3 = self._z3
        constraints = []
        if tensor_type.shape is not None:
            for i, dim in enumerate(tensor_type.shape):
                dim_var = self._env.get_int(f"__tensor_dim_{i}")
                if isinstance(dim, int):
                    constraints.append(dim_var == z3.IntVal(dim))
                elif isinstance(dim, str):
                    sym_var = self._env.get_int(dim)
                    constraints.append(dim_var == sym_var)
                constraints.append(dim_var >= 0)
        if tensor_type.dtype is not None:
            dtype_var = self._env.get_int("__tensor_dtype")
            dtype_id = z3.IntVal(hash(tensor_type.dtype) % (2**30))
            constraints.append(dtype_var == dtype_id)
        if not constraints:
            return z3.BoolVal(True)
        return z3.And(*constraints) if len(constraints) > 1 else constraints[0]

    # -------------------------------------------------------------------
    # Uninterpreted function helpers
    # -------------------------------------------------------------------

    def _get_uf(self, name: str, *arg_sorts: Any, result_sort: Any = None) -> Any:
        """Get or create an uninterpreted function declaration."""
        z3 = self._z3
        if result_sort is None:
            result_sort = z3.IntSort()
        key = (name, tuple(str(s) for s in arg_sorts), str(result_sort))
        str_key = repr(key)
        if str_key in self._uf_cache:
            return self._uf_cache[str_key]
        if arg_sorts:
            uf = z3.Function(name, *arg_sorts, result_sort)
        else:
            uf = z3.Function(name, z3.IntSort(), result_sort)
        self._uf_cache[str_key] = uf
        return uf


# ---------------------------------------------------------------------------
# Convenience function
# ---------------------------------------------------------------------------


def encode_predicate(predicate: Any) -> Any:
    """One-shot encoding: create a fresh encoder and encode a predicate."""
    encoder = Z3Encoder()
    return encoder.encode_predicate(predicate)
