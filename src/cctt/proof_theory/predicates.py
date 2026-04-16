"""Predicate AST — the language of refinement-type conditions.

Refinement types are {x : T | φ(x)}.  This module defines φ: a typed
predicate language that can express ARBITRARY properties, including
library-specific ones like:

    x : torch.Tensor | x.mean() == 0
    xs : list[int] | sorted(xs) == xs
    A : np.ndarray | A.shape[0] == A.shape[1]   (square matrix)
    e : sympy.Expr | sympy.expand(e) == e        (already expanded)
    d : dict | 'port' in d and isinstance(d['port'], int)

Design: predicates are a small AST that mirrors Python expressions
extended with logical connectives.  Every predicate has a
*decidability level* indicating what proof strategy can verify it:

    Z3          — pure arithmetic/boolean: Z3 decides it
    STRUCTURAL  — isinstance, is None, hasattr: AST pattern match
    LIBRARY     — involves library operations: needs library axioms
    ORACLE      — complex semantic property: needs LLM judgment
    UNKNOWN     — cannot determine a strategy

Predicates compose: conjunction narrows covers, disjunction widens them,
negation flips sides.  The cover algebra (RefinementCover) builds on
this to form Čech covers whose exhaustiveness is verifiable.

The key insight: a predicate like x.mean() == 0 is meaningful because
the torch library theory gives `mean()` semantics.  Decidability of a
predicate depends on what library axioms are available — this connects
the library axiom system DIRECTLY to the type system through the
refinement lattice.
"""
from __future__ import annotations

import ast as python_ast
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

try:
    from z3 import (
        Int, Bool, Real, IntVal, BoolVal, RealVal,
        And as Z3And, Or as Z3Or, Not as Z3Not, Implies as Z3Implies,
        Solver, unsat, sat, unknown as z3_unknown,
        ArithRef, BoolRef, ExprRef,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════════
# Decidability levels
# ═══════════════════════════════════════════════════════════════════

class Decidability(Enum):
    """What proof strategy can verify this predicate?"""
    Z3 = "z3"                    # Pure arithmetic/boolean — Z3 decides
    STRUCTURAL = "structural"    # isinstance, is None, hasattr — pattern match
    LIBRARY = "library"          # Involves library ops — needs library axioms
    ORACLE = "oracle"            # Complex semantic — needs LLM judgment
    UNKNOWN = "unknown"          # Can't determine


def _join_decidability(a: Decidability, b: Decidability) -> Decidability:
    """Least upper bound: the combined predicate is as hard as the harder part."""
    order = {Decidability.Z3: 0, Decidability.STRUCTURAL: 1,
             Decidability.LIBRARY: 2, Decidability.ORACLE: 3,
             Decidability.UNKNOWN: 4}
    return a if order.get(a, 4) >= order.get(b, 4) else b


# ═══════════════════════════════════════════════════════════════════
# Predicate AST
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Pred:
    """Base class for predicates in refinement types.

    Every predicate knows:
    - Its free variables (for scoping in covers)
    - Its decidability level (for proof strategy selection)
    - How to pretty-print itself
    """

    def free_vars(self) -> FrozenSet[str]:
        """Free variables in this predicate."""
        return frozenset()

    def decidability(self) -> Decidability:
        """What proof strategy can verify this?"""
        return Decidability.UNKNOWN

    def pretty(self) -> str:
        return repr(self)

    def negate(self) -> 'Pred':
        """Logical negation."""
        return PNot(self)

    def __and__(self, other: 'Pred') -> 'Pred':
        return PAnd((self, other))

    def __or__(self, other: 'Pred') -> 'Pred':
        return POr((self, other))

    def __invert__(self) -> 'Pred':
        return PNot(self)


# ─── Atoms ────────────────────────────────────────────────────────

@dataclass(frozen=True)
class PTrue(Pred):
    """Logical truth — the trivial predicate."""
    def decidability(self) -> Decidability:
        return Decidability.Z3

    def pretty(self) -> str:
        return 'True'


@dataclass(frozen=True)
class PFalse(Pred):
    """Logical falsity — the empty predicate."""
    def decidability(self) -> Decidability:
        return Decidability.Z3

    def pretty(self) -> str:
        return 'False'


@dataclass(frozen=True)
class PVar(Pred):
    """A variable reference in a predicate."""
    name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.name})

    def decidability(self) -> Decidability:
        return Decidability.Z3

    def pretty(self) -> str:
        return self.name


@dataclass(frozen=True)
class PLit(Pred):
    """A literal value (int, float, str, bool, None)."""
    value: Any

    def decidability(self) -> Decidability:
        return Decidability.Z3

    def pretty(self) -> str:
        return repr(self.value)


# ─── Arithmetic / operations ─────────────────────────────────────

@dataclass(frozen=True)
class PBinOp(Pred):
    """Binary operation: +, -, *, /, //, %, **."""
    left: Pred
    op: str
    right: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()

    def decidability(self) -> Decidability:
        return _join_decidability(self.left.decidability(),
                                  self.right.decidability())

    def pretty(self) -> str:
        return f'({self.left.pretty()} {self.op} {self.right.pretty()})'


@dataclass(frozen=True)
class PUnaryOp(Pred):
    """Unary operation: -, not, ~, abs."""
    op: str
    operand: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.operand.free_vars()

    def decidability(self) -> Decidability:
        return self.operand.decidability()

    def pretty(self) -> str:
        return f'{self.op}({self.operand.pretty()})'


# ─── Comparisons ─────────────────────────────────────────────────

@dataclass(frozen=True)
class PCompare(Pred):
    """Comparison: ==, !=, <, <=, >, >=."""
    left: Pred
    op: str   # '==', '!=', '<', '<=', '>', '>='
    right: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()

    def decidability(self) -> Decidability:
        return _join_decidability(self.left.decidability(),
                                  self.right.decidability())

    def pretty(self) -> str:
        return f'{self.left.pretty()} {self.op} {self.right.pretty()}'


# ─── Attribute access and indexing ────────────────────────────────

@dataclass(frozen=True)
class PAttr(Pred):
    """Attribute access: x.shape, x.dtype, x.mean.

    When the attribute is a property (not a method call), this is a
    value-level predicate term.  For method calls, use PCall(PAttr(...)).
    """
    obj: Pred
    attr: str

    def free_vars(self) -> FrozenSet[str]:
        return self.obj.free_vars()

    def decidability(self) -> Decidability:
        # Attribute access on library objects requires library knowledge
        if isinstance(self.obj, PVar):
            return Decidability.STRUCTURAL
        return _join_decidability(self.obj.decidability(),
                                  Decidability.LIBRARY)

    def pretty(self) -> str:
        return f'{self.obj.pretty()}.{self.attr}'


@dataclass(frozen=True)
class PIndex(Pred):
    """Indexing: x[0], d['key'], A[i, j]."""
    obj: Pred
    index: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.obj.free_vars() | self.index.free_vars()

    def decidability(self) -> Decidability:
        return _join_decidability(self.obj.decidability(),
                                  self.index.decidability())

    def pretty(self) -> str:
        return f'{self.obj.pretty()}[{self.index.pretty()}]'


# ─── Function / method calls ─────────────────────────────────────

@dataclass(frozen=True)
class PCall(Pred):
    """Function or method call: len(x), sorted(xs), x.mean().

    func can be:
    - PVar("len") for builtins
    - PAttr(PVar("x"), "mean") for methods
    - PLibCall for explicit library calls
    """
    func: Pred
    args: Tuple[Pred, ...]

    def free_vars(self) -> FrozenSet[str]:
        result = self.func.free_vars()
        for a in self.args:
            result |= a.free_vars()
        return result

    def decidability(self) -> Decidability:
        # Built-in pure functions: len, sorted, range, abs
        if isinstance(self.func, PVar) and self.func.name in (
            'len', 'abs', 'min', 'max', 'sum', 'range',
        ):
            base = Decidability.Z3
        elif isinstance(self.func, PVar) and self.func.name in (
            'sorted', 'reversed', 'list', 'tuple', 'set', 'dict',
            'isinstance', 'hasattr', 'type',
        ):
            base = Decidability.STRUCTURAL
        else:
            base = Decidability.LIBRARY

        for a in self.args:
            base = _join_decidability(base, a.decidability())
        return base

    def pretty(self) -> str:
        args_str = ', '.join(a.pretty() for a in self.args)
        return f'{self.func.pretty()}({args_str})'


@dataclass(frozen=True)
class PLibCall(Pred):
    """Explicit library function call: sympy.expand(e), np.linalg.norm(x).

    Separates the library name from the function for axiom lookup.
    """
    library: str
    function: str
    args: Tuple[Pred, ...]

    def free_vars(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for a in self.args:
            result |= a.free_vars()
        return frozenset(result)

    def decidability(self) -> Decidability:
        return Decidability.LIBRARY

    def pretty(self) -> str:
        args_str = ', '.join(a.pretty() for a in self.args)
        return f'{self.library}.{self.function}({args_str})'


# ─── Logical connectives ─────────────────────────────────────────

@dataclass(frozen=True)
class PAnd(Pred):
    """Conjunction: φ ∧ ψ."""
    conjuncts: Tuple[Pred, ...]

    def free_vars(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for c in self.conjuncts:
            result |= c.free_vars()
        return frozenset(result)

    def decidability(self) -> Decidability:
        d = Decidability.Z3
        for c in self.conjuncts:
            d = _join_decidability(d, c.decidability())
        return d

    def pretty(self) -> str:
        return ' and '.join(c.pretty() for c in self.conjuncts)


@dataclass(frozen=True)
class POr(Pred):
    """Disjunction: φ ∨ ψ."""
    disjuncts: Tuple[Pred, ...]

    def free_vars(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for d in self.disjuncts:
            result |= d.free_vars()
        return frozenset(result)

    def decidability(self) -> Decidability:
        d = Decidability.Z3
        for dj in self.disjuncts:
            d = _join_decidability(d, dj.decidability())
        return d

    def pretty(self) -> str:
        return ' or '.join(d.pretty() for d in self.disjuncts)


@dataclass(frozen=True)
class PNot(Pred):
    """Negation: ¬φ."""
    inner: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.inner.free_vars()

    def decidability(self) -> Decidability:
        return self.inner.decidability()

    def pretty(self) -> str:
        return f'not ({self.inner.pretty()})'


@dataclass(frozen=True)
class PImplies(Pred):
    """Implication: φ → ψ."""
    antecedent: Pred
    consequent: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.antecedent.free_vars() | self.consequent.free_vars()

    def decidability(self) -> Decidability:
        return _join_decidability(self.antecedent.decidability(),
                                  self.consequent.decidability())

    def pretty(self) -> str:
        return f'({self.antecedent.pretty()}) implies ({self.consequent.pretty()})'


# ─── Quantifiers ──────────────────────────────────────────────────

@dataclass(frozen=True)
class PForall(Pred):
    """Universal quantification: ∀x ∈ domain. φ(x)."""
    var: str
    body: Pred
    domain: Optional[Pred] = None  # e.g., range(n), or a type constraint

    def free_vars(self) -> FrozenSet[str]:
        result = self.body.free_vars() - {self.var}
        if self.domain:
            result |= self.domain.free_vars()
        return frozenset(result)

    def decidability(self) -> Decidability:
        # Quantifiers are generally not Z3-decidable in QF fragments
        return _join_decidability(Decidability.ORACLE,
                                  self.body.decidability())

    def pretty(self) -> str:
        dom = f' in {self.domain.pretty()}' if self.domain else ''
        return f'forall {self.var}{dom}. {self.body.pretty()}'


@dataclass(frozen=True)
class PExists(Pred):
    """Existential quantification: ∃x ∈ domain. φ(x)."""
    var: str
    body: Pred
    domain: Optional[Pred] = None

    def free_vars(self) -> FrozenSet[str]:
        result = self.body.free_vars() - {self.var}
        if self.domain:
            result |= self.domain.free_vars()
        return frozenset(result)

    def decidability(self) -> Decidability:
        return _join_decidability(Decidability.ORACLE,
                                  self.body.decidability())

    def pretty(self) -> str:
        dom = f' in {self.domain.pretty()}' if self.domain else ''
        return f'exists {self.var}{dom}. {self.body.pretty()}'


# ─── Python-specific predicates ───────────────────────────────────

@dataclass(frozen=True)
class PIsInstance(Pred):
    """isinstance(x, T) — structural type test."""
    obj: Pred
    type_name: str

    def free_vars(self) -> FrozenSet[str]:
        return self.obj.free_vars()

    def decidability(self) -> Decidability:
        return Decidability.STRUCTURAL

    def pretty(self) -> str:
        return f'isinstance({self.obj.pretty()}, {self.type_name})'


@dataclass(frozen=True)
class PIsNone(Pred):
    """x is None — the billion-dollar test."""
    obj: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.obj.free_vars()

    def decidability(self) -> Decidability:
        return Decidability.STRUCTURAL

    def pretty(self) -> str:
        return f'{self.obj.pretty()} is None'


@dataclass(frozen=True)
class PHasAttr(Pred):
    """hasattr(x, 'attr') — duck-type probe."""
    obj: Pred
    attr: str

    def free_vars(self) -> FrozenSet[str]:
        return self.obj.free_vars()

    def decidability(self) -> Decidability:
        return Decidability.STRUCTURAL

    def pretty(self) -> str:
        return f'hasattr({self.obj.pretty()}, {self.attr!r})'


@dataclass(frozen=True)
class PContains(Pred):
    """key in container — membership test."""
    element: Pred
    container: Pred

    def free_vars(self) -> FrozenSet[str]:
        return self.element.free_vars() | self.container.free_vars()

    def decidability(self) -> Decidability:
        return _join_decidability(self.element.decidability(),
                                  self.container.decidability())

    def pretty(self) -> str:
        return f'{self.element.pretty()} in {self.container.pretty()}'


# ═══════════════════════════════════════════════════════════════════
# Predicate parsing — Python string → Pred AST
# ═══════════════════════════════════════════════════════════════════

def parse_predicate(source: str) -> Pred:
    """Parse a Python expression string into a Pred AST.

    Supports arbitrary Python expressions including:
    - Arithmetic: x > 0, x + y == z
    - Method calls: x.mean() == 0, xs.count(v) > 0
    - Library calls: sympy.expand(e) == e
    - Logic: x > 0 and x < 100
    - Type tests: isinstance(x, int)
    - Membership: 'key' in d
    - Attribute access: A.shape[0] == A.shape[1]
    - Indexing: d['port'] > 0

    Falls back to a PVar wrapping the raw string on parse failure.
    """
    try:
        tree = python_ast.parse(source, mode='eval')
        return _ast_to_pred(tree.body)
    except (SyntaxError, ValueError, TypeError):
        return PVar(source)


def _ast_to_pred(node: python_ast.AST) -> Pred:
    """Convert a Python AST node to a Pred."""

    # ── Constants ──
    if isinstance(node, python_ast.Constant):
        if node.value is True:
            return PTrue()
        if node.value is False:
            return PFalse()
        if node.value is None:
            return PLit(None)
        return PLit(node.value)

    # ── Names ──
    if isinstance(node, python_ast.Name):
        if node.id == 'True':
            return PTrue()
        if node.id == 'False':
            return PFalse()
        if node.id == 'None':
            return PLit(None)
        return PVar(node.id)

    # ── Binary ops ──
    if isinstance(node, python_ast.BinOp):
        op_map = {
            python_ast.Add: '+', python_ast.Sub: '-',
            python_ast.Mult: '*', python_ast.Div: '/',
            python_ast.FloorDiv: '//', python_ast.Mod: '%',
            python_ast.Pow: '**',
        }
        op_str = op_map.get(type(node.op), '?')
        return PBinOp(_ast_to_pred(node.left), op_str, _ast_to_pred(node.right))

    # ── Unary ops ──
    if isinstance(node, python_ast.UnaryOp):
        op_map = {
            python_ast.USub: '-', python_ast.Not: 'not',
            python_ast.Invert: '~', python_ast.UAdd: '+',
        }
        op_str = op_map.get(type(node.op), '?')
        if isinstance(node.op, python_ast.Not):
            return PNot(_ast_to_pred(node.operand))
        return PUnaryOp(op_str, _ast_to_pred(node.operand))

    # ── Comparisons (can be chained: a < b < c) ──
    if isinstance(node, python_ast.Compare):
        op_map = {
            python_ast.Eq: '==', python_ast.NotEq: '!=',
            python_ast.Lt: '<', python_ast.LtE: '<=',
            python_ast.Gt: '>', python_ast.GtE: '>=',
            python_ast.Is: 'is', python_ast.IsNot: 'is not',
            python_ast.In: 'in', python_ast.NotIn: 'not in',
        }
        parts: List[Pred] = []
        left = _ast_to_pred(node.left)
        for op_node, comparator_node in zip(node.ops, node.comparators):
            right = _ast_to_pred(comparator_node)

            if isinstance(op_node, python_ast.Is):
                if isinstance(comparator_node, python_ast.Constant) and comparator_node.value is None:
                    parts.append(PIsNone(left))
                else:
                    parts.append(PCompare(left, 'is', right))
            elif isinstance(op_node, python_ast.IsNot):
                if isinstance(comparator_node, python_ast.Constant) and comparator_node.value is None:
                    parts.append(PNot(PIsNone(left)))
                else:
                    parts.append(PNot(PCompare(left, 'is', right)))
            elif isinstance(op_node, python_ast.In):
                parts.append(PContains(left, right))
            elif isinstance(op_node, python_ast.NotIn):
                parts.append(PNot(PContains(left, right)))
            else:
                op_str = op_map.get(type(op_node), '?')
                parts.append(PCompare(left, op_str, right))

            left = right

        if len(parts) == 1:
            return parts[0]
        return PAnd(tuple(parts))

    # ── Boolean ops ──
    if isinstance(node, python_ast.BoolOp):
        preds = [_ast_to_pred(v) for v in node.values]
        if isinstance(node.op, python_ast.And):
            return PAnd(tuple(preds))
        return POr(tuple(preds))

    # ── Attribute access ──
    if isinstance(node, python_ast.Attribute):
        return PAttr(_ast_to_pred(node.value), node.attr)

    # ── Subscript ──
    if isinstance(node, python_ast.Subscript):
        obj = _ast_to_pred(node.value)
        if isinstance(node.slice, python_ast.Tuple):
            # Multi-dimensional: A[i, j]
            idx = PLit(tuple(_ast_to_pred(e) for e in node.slice.elts))
        else:
            idx = _ast_to_pred(node.slice)
        return PIndex(obj, idx)

    # ── Function call ──
    if isinstance(node, python_ast.Call):
        args = tuple(_ast_to_pred(a) for a in node.args)

        # isinstance(x, T)
        if (isinstance(node.func, python_ast.Name) and
                node.func.id == 'isinstance' and len(args) == 2):
            type_arg = args[1]
            type_name = type_arg.pretty() if isinstance(type_arg, PVar) else str(type_arg)
            return PIsInstance(args[0], type_name)

        # hasattr(x, 'attr')
        if (isinstance(node.func, python_ast.Name) and
                node.func.id == 'hasattr' and len(args) == 2):
            attr = args[1]
            attr_str = attr.value if isinstance(attr, PLit) else attr.pretty()
            return PHasAttr(args[0], str(attr_str))

        # module.function(args) — detect library calls
        if isinstance(node.func, python_ast.Attribute):
            obj_pred = _ast_to_pred(node.func.value)
            method = node.func.attr
            # If the object is a simple name, it might be a library module
            if isinstance(obj_pred, PVar):
                # Could be library call (sympy.expand) or method (x.mean)
                # Heuristic: known library modules vs. variable methods
                known_libs = {'sympy', 'numpy', 'np', 'torch', 'scipy',
                              'pandas', 'pd', 'sklearn', 'math', 'os',
                              'itertools', 'functools', 'collections'}
                if obj_pred.name in known_libs:
                    return PLibCall(obj_pred.name, method, args)
            # Method call: x.mean(), xs.count(v)
            return PCall(PAttr(obj_pred, method), args)

        func_pred = _ast_to_pred(node.func)
        return PCall(func_pred, args)

    # ── Tuple (for multi-index or tuple predicates) ──
    if isinstance(node, python_ast.Tuple):
        return PLit(tuple(_ast_to_pred(e) for e in node.elts))

    # ── List ──
    if isinstance(node, python_ast.List):
        return PCall(PVar('list'), tuple(_ast_to_pred(e) for e in node.elts))

    # ── IfExp: a if cond else b ──
    if isinstance(node, python_ast.IfExp):
        cond = _ast_to_pred(node.test)
        then = _ast_to_pred(node.body)
        else_ = _ast_to_pred(node.orelse)
        return POr((PAnd((cond, then)), PAnd((PNot(cond), else_))))

    # Fallback
    try:
        source = python_ast.unparse(node)
    except Exception:
        source = repr(node)
    return PVar(source)


# ═══════════════════════════════════════════════════════════════════
# Z3 compilation — Pred → Z3 expression (partial)
# ═══════════════════════════════════════════════════════════════════

def pred_to_z3(pred: Pred, var_sorts: Optional[Dict[str, str]] = None,
               ) -> Optional[Any]:
    """Compile a Pred to a Z3 expression, if possible.

    Returns None for predicates that can't be compiled to Z3
    (library calls, method calls on non-Z3 objects, etc.).

    var_sorts maps variable names to Z3 sort strings:
    {'x': 'Int', 'y': 'Real', 'b': 'Bool'}
    """
    if not _HAS_Z3:
        return None

    var_sorts = var_sorts or {}
    z3_vars: Dict[str, Any] = {}

    def _get_var(name: str) -> Optional[Any]:
        if name in z3_vars:
            return z3_vars[name]
        sort = var_sorts.get(name, 'Int')
        if sort in ('Int', 'int'):
            z3_vars[name] = Int(name)
        elif sort in ('Real', 'float'):
            z3_vars[name] = Real(name)
        elif sort in ('Bool', 'bool'):
            z3_vars[name] = Bool(name)
        else:
            z3_vars[name] = Int(name)  # default to Int
        return z3_vars[name]

    def _compile(p: Pred) -> Optional[Any]:
        if isinstance(p, PTrue):
            return BoolVal(True)
        if isinstance(p, PFalse):
            return BoolVal(False)
        if isinstance(p, PVar):
            return _get_var(p.name)
        if isinstance(p, PLit):
            if isinstance(p.value, bool):
                return BoolVal(p.value)
            if isinstance(p.value, int):
                return IntVal(p.value)
            if isinstance(p.value, float):
                return RealVal(p.value)
            return None

        if isinstance(p, PBinOp):
            l = _compile(p.left)
            r = _compile(p.right)
            if l is None or r is None:
                return None
            ops = {'+': lambda a, b: a + b, '-': lambda a, b: a - b,
                   '*': lambda a, b: a * b, '//': lambda a, b: a / b,
                   '%': lambda a, b: a % b}
            fn = ops.get(p.op)
            return fn(l, r) if fn else None

        if isinstance(p, PUnaryOp):
            inner = _compile(p.operand)
            if inner is None:
                return None
            if p.op == '-':
                return -inner
            return None

        if isinstance(p, PCompare):
            l = _compile(p.left)
            r = _compile(p.right)
            if l is None or r is None:
                return None
            ops = {'==': lambda a, b: a == b, '!=': lambda a, b: a != b,
                   '<': lambda a, b: a < b, '<=': lambda a, b: a <= b,
                   '>': lambda a, b: a > b, '>=': lambda a, b: a >= b}
            fn = ops.get(p.op)
            return fn(l, r) if fn else None

        if isinstance(p, PAnd):
            parts = [_compile(c) for c in p.conjuncts]
            if any(x is None for x in parts):
                return None
            return Z3And(*parts)

        if isinstance(p, POr):
            parts = [_compile(d) for d in p.disjuncts]
            if any(x is None for x in parts):
                return None
            return Z3Or(*parts)

        if isinstance(p, PNot):
            inner = _compile(p.inner)
            return Z3Not(inner) if inner is not None else None

        if isinstance(p, PImplies):
            ant = _compile(p.antecedent)
            con = _compile(p.consequent)
            if ant is None or con is None:
                return None
            return Z3Implies(ant, con)

        # Non-Z3-compilable: library calls, method calls, isinstance, etc.
        return None

    return _compile(pred)


# ═══════════════════════════════════════════════════════════════════
# Cover algebra — refinement covers for Čech descent
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class RefinementFiber:
    """A single fiber in a refinement cover.

    A refinement fiber is an open set in the refinement lattice:
        {x : base | predicate(x)}

    where predicate is an arbitrary Pred expression that may reference
    library operations, method calls, attribute accesses, etc.

    Examples:
        RefinementFiber("positive", INT, parse_predicate("x > 0"))
        RefinementFiber("zero_mean", TENSOR, parse_predicate("x.mean() == 0"))
        RefinementFiber("expanded", EXPR, parse_predicate("sympy.expand(x) == x"))
    """
    name: str
    base_type_name: str   # string description of base type (e.g., 'int', 'Tensor')
    predicate: Pred
    variables: Dict[str, str] = field(default_factory=dict)  # var → Z3 sort

    @property
    def decidability(self) -> Decidability:
        return self.predicate.decidability()

    @property
    def is_z3_decidable(self) -> bool:
        return self.decidability == Decidability.Z3

    def intersection(self, other: 'RefinementFiber') -> 'RefinementFiber':
        """Compute the intersection fiber: {x | φ(x) ∧ ψ(x)}."""
        return RefinementFiber(
            name=f'{self.name}∩{other.name}',
            base_type_name=self.base_type_name,
            predicate=PAnd((self.predicate, other.predicate)),
            variables={**self.variables, **other.variables},
        )

    def pretty(self) -> str:
        return f'{{{self.base_type_name} | {self.predicate.pretty()}}}'


@dataclass(frozen=True)
class OverlapInfo:
    """Information about the overlap of two fibers.

    If the overlap is Z3-provably empty (UNSAT), no compatibility proof is
    needed.  Otherwise, the intersection predicate tells the prover what
    hypothesis to work under.
    """
    fiber_a: str
    fiber_b: str
    intersection: Pred
    is_empty: Optional[bool] = None   # True if Z3-proved empty, None if unknown
    decidability: Decidability = Decidability.UNKNOWN


@dataclass
class RefinementCover:
    """A Čech cover by refinement types over a base type.

    A cover is a collection of fibers whose predicates together cover
    the entire domain.  The cover carries:

    1. **Fibers**: named refinement types
    2. **Exhaustiveness obligation**: ∨ of all predicates = True
    3. **Overlap data**: for each pair, the intersection predicate +
       whether it's empty (disjoint fibers need no compatibility proof)

    Exhaustiveness verification:
    - If all predicates are Z3-decidable: Z3 checks ∨φᵢ is valid
    - If some are LIBRARY: need library axioms to verify coverage
    - If some are ORACLE: coverage is trusted / LLM-judged

    Examples:

        # Numeric sign cover (Z3-decidable)
        sign_cover = RefinementCover.from_predicates("int", "x", [
            ("positive", "x > 0"),
            ("zero",     "x == 0"),
            ("negative", "x < 0"),
        ])

        # Tensor normalization cover (library-level)
        norm_cover = RefinementCover.from_predicates("Tensor", "x", [
            ("normalized",   "x.norm() == 1.0"),
            ("unnormalized", "x.norm() != 1.0"),
        ])

        # SymPy form cover (library-level)
        form_cover = RefinementCover.from_predicates("Expr", "e", [
            ("expanded", "sympy.expand(e) == e"),
            ("factored", "sympy.factor(e) == e"),
            ("other",    "sympy.expand(e) != e and sympy.factor(e) != e"),
        ])
    """
    base_type_name: str
    bound_var: str
    fibers: Dict[str, RefinementFiber]
    overlaps: Dict[Tuple[str, str], OverlapInfo] = field(default_factory=dict)
    exhaustiveness_status: Optional[str] = None  # 'z3_proved', 'assumed', None

    @classmethod
    def from_predicates(cls, base_type: str, var: str,
                        specs: List[Tuple[str, str]],
                        var_sorts: Optional[Dict[str, str]] = None,
                        ) -> 'RefinementCover':
        """Build a cover from (name, predicate_string) pairs.

        Automatically:
        1. Parses predicates
        2. Computes all pairwise overlaps
        3. Tries Z3 to check emptiness of overlaps
        4. Tries Z3 to check exhaustiveness
        """
        sorts = var_sorts or {var: 'Int'}
        fibers: Dict[str, RefinementFiber] = {}
        for name, pred_str in specs:
            pred = parse_predicate(pred_str)
            fibers[name] = RefinementFiber(
                name=name,
                base_type_name=base_type,
                predicate=pred,
                variables=sorts,
            )

        cover = cls(base_type_name=base_type, bound_var=var, fibers=fibers)
        cover._compute_overlaps()
        cover._check_exhaustiveness()
        return cover

    def _compute_overlaps(self) -> None:
        """Compute pairwise overlap info, using Z3 to detect empty overlaps."""
        names = list(self.fibers.keys())
        for i, a_name in enumerate(names):
            for b_name in names[i + 1:]:
                a = self.fibers[a_name]
                b = self.fibers[b_name]
                intersection = PAnd((a.predicate, b.predicate))
                dec = _join_decidability(a.decidability, b.decidability)

                is_empty = None
                if dec == Decidability.Z3 and _HAS_Z3:
                    is_empty = _z3_check_unsat(intersection, a.variables)

                self.overlaps[(a_name, b_name)] = OverlapInfo(
                    fiber_a=a_name,
                    fiber_b=b_name,
                    intersection=intersection,
                    is_empty=is_empty,
                    decidability=dec,
                )

    def _check_exhaustiveness(self) -> None:
        """Try to verify the cover is exhaustive: ∨φᵢ is valid."""
        all_preds = [f.predicate for f in self.fibers.values()]
        if not all_preds:
            self.exhaustiveness_status = None
            return

        disjunction = POr(tuple(all_preds)) if len(all_preds) > 1 else all_preds[0]

        # Check if all predicates are Z3-decidable
        if all(f.is_z3_decidable for f in self.fibers.values()) and _HAS_Z3:
            all_vars = {}
            for f in self.fibers.values():
                all_vars.update(f.variables)
            if _z3_check_valid(disjunction, all_vars):
                self.exhaustiveness_status = 'z3_proved'
                return

        # Non-Z3: mark as assumed
        self.exhaustiveness_status = 'assumed'

    def non_empty_overlaps(self) -> Dict[Tuple[str, str], OverlapInfo]:
        """Return only the overlaps that are not provably empty."""
        return {k: v for k, v in self.overlaps.items() if v.is_empty is not True}

    def fiber_names(self) -> List[str]:
        return list(self.fibers.keys())

    @property
    def decidability(self) -> Decidability:
        """Overall decidability: the hardest fiber."""
        d = Decidability.Z3
        for f in self.fibers.values():
            d = _join_decidability(d, f.decidability)
        return d

    def pretty(self) -> str:
        lines = [f'Cover over {self.base_type_name} (var={self.bound_var}):']
        for f in self.fibers.values():
            lines.append(f'  fiber {f.name}: {f.pretty()} [{f.decidability.value}]')
        if self.exhaustiveness_status:
            lines.append(f'  exhaustiveness: {self.exhaustiveness_status}')
        nonempty = self.non_empty_overlaps()
        if nonempty:
            lines.append(f'  non-empty overlaps: {len(nonempty)}')
            for (a, b), info in nonempty.items():
                lines.append(f'    {a} ∩ {b}: [{info.decidability.value}]')
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════════
# Z3 helpers for cover verification
# ═══════════════════════════════════════════════════════════════════

def _z3_check_unsat(pred: Pred, var_sorts: Dict[str, str],
                    timeout_ms: int = 3000) -> Optional[bool]:
    """Check if a predicate is unsatisfiable (empty).  Returns True/False/None."""
    if not _HAS_Z3:
        return None
    z3_expr = pred_to_z3(pred, var_sorts)
    if z3_expr is None:
        return None
    try:
        s = Solver()
        s.set('timeout', timeout_ms)
        s.add(z3_expr)
        result = s.check()
        if result == unsat:
            return True
        if result == sat:
            return False
        return None  # timeout
    except Exception:
        return None


def _z3_check_valid(pred: Pred, var_sorts: Dict[str, str],
                    timeout_ms: int = 3000) -> bool:
    """Check if a predicate is valid (true for all assignments).

    A predicate φ is valid iff ¬φ is unsatisfiable.
    """
    if not _HAS_Z3:
        return False
    z3_expr = pred_to_z3(pred, var_sorts)
    if z3_expr is None:
        return False
    try:
        s = Solver()
        s.set('timeout', timeout_ms)
        s.add(Z3Not(z3_expr))
        result = s.check()
        return result == unsat
    except Exception:
        return False


def check_cover_exhaustive(cover: RefinementCover) -> Optional[bool]:
    """Externally check if a cover is exhaustive.

    Returns True if Z3-proved, False if Z3-refuted, None if unknown.
    """
    all_preds = [f.predicate for f in cover.fibers.values()]
    if not all_preds:
        return False
    disjunction = POr(tuple(all_preds)) if len(all_preds) > 1 else all_preds[0]
    all_vars = {}
    for f in cover.fibers.values():
        all_vars.update(f.variables)
    z3_expr = pred_to_z3(disjunction, all_vars)
    if z3_expr is None:
        return None
    return _z3_check_valid(disjunction, all_vars) or None


def check_overlap_empty(fiber_a: RefinementFiber,
                        fiber_b: RefinementFiber) -> Optional[bool]:
    """Check if two fibers have empty intersection."""
    intersection = PAnd((fiber_a.predicate, fiber_b.predicate))
    all_vars = {**fiber_a.variables, **fiber_b.variables}
    return _z3_check_unsat(intersection, all_vars)


# ═══════════════════════════════════════════════════════════════════
# Predicate simplification
# ═══════════════════════════════════════════════════════════════════

def simplify_pred(pred: Pred) -> Pred:
    """Basic predicate simplification (logical identities)."""
    if isinstance(pred, PAnd):
        simplified = []
        for c in pred.conjuncts:
            s = simplify_pred(c)
            if isinstance(s, PFalse):
                return PFalse()
            if isinstance(s, PTrue):
                continue
            if isinstance(s, PAnd):
                simplified.extend(s.conjuncts)
            else:
                simplified.append(s)
        if not simplified:
            return PTrue()
        if len(simplified) == 1:
            return simplified[0]
        return PAnd(tuple(simplified))

    if isinstance(pred, POr):
        simplified = []
        for d in pred.disjuncts:
            s = simplify_pred(d)
            if isinstance(s, PTrue):
                return PTrue()
            if isinstance(s, PFalse):
                continue
            if isinstance(s, POr):
                simplified.extend(s.disjuncts)
            else:
                simplified.append(s)
        if not simplified:
            return PFalse()
        if len(simplified) == 1:
            return simplified[0]
        return POr(tuple(simplified))

    if isinstance(pred, PNot):
        inner = simplify_pred(pred.inner)
        if isinstance(inner, PTrue):
            return PFalse()
        if isinstance(inner, PFalse):
            return PTrue()
        if isinstance(inner, PNot):
            return inner.inner
        return PNot(inner)

    return pred


# ═══════════════════════════════════════════════════════════════════
# Library-aware predicate analysis
# ═══════════════════════════════════════════════════════════════════

def extract_library_deps(pred: Pred) -> Set[str]:
    """Find all library modules referenced in a predicate."""
    deps: Set[str] = set()

    def _walk(p: Pred) -> None:
        if isinstance(p, PLibCall):
            deps.add(p.library)
        elif isinstance(p, PCall):
            _walk(p.func)
            for a in p.args:
                _walk(a)
        elif isinstance(p, PAttr):
            _walk(p.obj)
        elif isinstance(p, PIndex):
            _walk(p.obj)
            _walk(p.index)
        elif isinstance(p, PBinOp):
            _walk(p.left)
            _walk(p.right)
        elif isinstance(p, PUnaryOp):
            _walk(p.operand)
        elif isinstance(p, PCompare):
            _walk(p.left)
            _walk(p.right)
        elif isinstance(p, PAnd):
            for c in p.conjuncts:
                _walk(c)
        elif isinstance(p, POr):
            for d in p.disjuncts:
                _walk(d)
        elif isinstance(p, PNot):
            _walk(p.inner)
        elif isinstance(p, PImplies):
            _walk(p.antecedent)
            _walk(p.consequent)
        elif isinstance(p, PForall):
            _walk(p.body)
        elif isinstance(p, PExists):
            _walk(p.body)
        elif isinstance(p, PContains):
            _walk(p.element)
            _walk(p.container)
        elif isinstance(p, PIsInstance):
            _walk(p.obj)
        elif isinstance(p, PIsNone):
            _walk(p.obj)
        elif isinstance(p, PHasAttr):
            _walk(p.obj)

    _walk(pred)
    return deps


def required_axioms_for_cover(cover: RefinementCover) -> Dict[str, Set[str]]:
    """Determine which library axioms are needed to verify a cover.

    Returns {library: {axiom_names_that_might_help}} — a best-effort guide.
    """
    result: Dict[str, Set[str]] = {}
    for fiber in cover.fibers.values():
        deps = extract_library_deps(fiber.predicate)
        for lib in deps:
            result.setdefault(lib, set()).add(f'{fiber.name}_fiber')
    return result
