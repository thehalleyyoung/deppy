"""
Deppy Denotational Semantics — compositional interpretation of SynTerms.

Maps every SynTerm ``t`` in an environment ``ρ`` to a SemanticValue:

    ⟦t⟧ρ : SemanticValue

The semantics is *compositional*: the meaning of a compound term is
determined entirely by the meanings of its sub-terms.  This enables
semantic equivalence checking (⟦t₁⟧ = ⟦t₂⟧ for all ρ) via
type-directed random testing.

Architecture:
    SemanticValue           — the semantic domain
    Environment             — mapping names → values
    Denotation              — the ⟦_⟧ function
    SemanticEquivalence     — check ⟦t₁⟧ = ⟦t₂⟧
    TypeDirectedGenerator   — generate random values by type
    python_builtins_env()   — standard Python builtins as an environment
"""
from __future__ import annotations

import math
import operator
import random
import string
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from deppy.core.types import (
    SynType, SynTerm, Context,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PyTupleType, PySetType, PyClassType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    OptionalType, IntervalType, UniverseType, GlueType,
    ProtocolType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
)

# ═══════════════════════════════════════════════════════════════════
# Semantic Domain
# ═══════════════════════════════════════════════════════════════════


class SemanticValue:
    """Base class for all denotational values."""

    def semantic_eq(self, other: SemanticValue) -> bool:
        """Structural/value equality between semantic values."""
        return self is other

    def __repr__(self) -> str:
        return f"{type(self).__name__}()"


@dataclass
class ConcreteValue(SemanticValue):
    """A concrete Python value (int, str, list, …)."""
    value: Any = None

    def semantic_eq(self, other: SemanticValue) -> bool:
        if not isinstance(other, ConcreteValue):
            return False
        try:
            return self.value == other.value
        except Exception:
            return self.value is other.value

    def __repr__(self) -> str:
        return f"ConcreteValue({self.value!r})"


@dataclass
class FunctionValue(SemanticValue):
    """A function closure: λ-body captured with its defining environment."""
    params: list[str] = field(default_factory=list)
    body: SynTerm = field(default_factory=lambda: Var("x"))
    env: Environment = field(default_factory=lambda: Environment())

    def semantic_eq(self, other: SemanticValue) -> bool:
        # Function equality is undecidable in general; we use identity.
        return self is other

    def __repr__(self) -> str:
        p = ", ".join(self.params)
        return f"FunctionValue(λ{p}. {self.body})"


@dataclass
class NativeFunctionValue(SemanticValue):
    """A native Python callable wrapped as a semantic value."""
    func: Callable[..., Any] = field(default_factory=lambda: (lambda: None))
    name: str = "<native>"

    def semantic_eq(self, other: SemanticValue) -> bool:
        if not isinstance(other, NativeFunctionValue):
            return False
        return self.func is other.func

    def __repr__(self) -> str:
        return f"NativeFunctionValue({self.name})"


@dataclass
class BottomValue(SemanticValue):
    """⊥ — non-termination or error."""
    reason: str = ""

    def semantic_eq(self, other: SemanticValue) -> bool:
        return isinstance(other, BottomValue)

    def __repr__(self) -> str:
        return f"⊥({self.reason})" if self.reason else "⊥"


@dataclass
class TypeValue(SemanticValue):
    """A type reified as a value (for Type : Type levels)."""
    type_: SynType = field(default_factory=PyObjType)

    def semantic_eq(self, other: SemanticValue) -> bool:
        return isinstance(other, TypeValue) and self.type_ == other.type_

    def __repr__(self) -> str:
        return f"TypeValue({self.type_})"


@dataclass
class PairValue(SemanticValue):
    """A dependent-pair value (a, b)."""
    fst: SemanticValue = field(default_factory=lambda: ConcreteValue(None))
    snd: SemanticValue = field(default_factory=lambda: ConcreteValue(None))

    def semantic_eq(self, other: SemanticValue) -> bool:
        return (isinstance(other, PairValue)
                and self.fst.semantic_eq(other.fst)
                and self.snd.semantic_eq(other.snd))

    def __repr__(self) -> str:
        return f"PairValue({self.fst}, {self.snd})"


@dataclass
class PathValue(SemanticValue):
    """A path (proof of equality) between two semantic values.

    Witnesses behavioral equivalence: a path p : a = b means a and b
    are interchangeable in all observable contexts.

    ``witness`` is a callable I → SemanticValue that interpolates
    from ``start`` (at 0) to ``end`` (at 1).  The path is continuous
    in the sense that the observable behavior varies smoothly.
    """
    start: SemanticValue = field(default_factory=lambda: ConcreteValue(None))
    end: SemanticValue = field(default_factory=lambda: ConcreteValue(None))
    witness: Any = None  # Callable[[float], SemanticValue] | None

    @property
    def left(self) -> SemanticValue:
        """Alias for start — left endpoint of the path."""
        return self.start

    @property
    def right(self) -> SemanticValue:
        """Alias for end — right endpoint of the path."""
        return self.end

    def at(self, i: float) -> SemanticValue:
        """Evaluate the path at a point i ∈ [0, 1].

        at(0) = start, at(1) = end, and intermediate values are
        produced by the witness function (interpolation).
        """
        if i == 0.0:
            return self.start
        if i == 1.0:
            return self.end
        if self.witness is not None:
            return self.witness(i)
        # Degenerate path: no witness, return start
        return self.start

    def semantic_eq(self, other: SemanticValue) -> bool:
        return (isinstance(other, PathValue)
                and self.start.semantic_eq(other.start)
                and self.end.semantic_eq(other.end))

    def __repr__(self) -> str:
        return f"PathValue({self.start} ~> {self.end})"


@dataclass
class HigherPathValue(SemanticValue):
    """A path between paths — 2-cell in the ∞-groupoid.

    If left_path, right_path : a = b, then a HigherPathValue witnesses
    that left_path and right_path are themselves equal as paths.  This
    is the first layer of genuine higher structure: a homotopy between
    homotopies.

    ``witness_2d`` maps (i, j) ∈ [0,1]² → SemanticValue such that:
      witness_2d(i, 0) = left_path.at(i)
      witness_2d(i, 1) = right_path.at(i)
      witness_2d(0, j) = left_path.start = right_path.start
      witness_2d(1, j) = left_path.end   = right_path.end
    """
    left_path: PathValue = field(default_factory=PathValue)
    right_path: PathValue = field(default_factory=PathValue)
    witness_2d: Any = None  # Callable[[float, float], SemanticValue] | None

    def at(self, i: float, j: float) -> SemanticValue:
        """Evaluate the 2-cell at point (i, j) on [0,1]²."""
        if self.witness_2d is not None:
            return self.witness_2d(i, j)
        # Degenerate: linear interpolation between left and right paths
        left_val = self.left_path.at(i)
        right_val = self.right_path.at(i)
        if j <= 0.5:
            return left_val
        return right_val

    def semantic_eq(self, other: SemanticValue) -> bool:
        return (isinstance(other, HigherPathValue)
                and self.left_path.semantic_eq(other.left_path)
                and self.right_path.semantic_eq(other.right_path))

    def __repr__(self) -> str:
        return f"HigherPathValue({self.left_path} ≃ {self.right_path})"


# ═══════════════════════════════════════════════════════════════════
# Environment
# ═══════════════════════════════════════════════════════════════════


@dataclass
class Environment:
    """Semantic environment mapping names to SemanticValues.

    Environments form a chain via ``parent`` for lexical scoping.
    """
    bindings: dict[str, SemanticValue] = field(default_factory=dict)
    parent: Environment | None = None

    def lookup(self, name: str) -> SemanticValue | None:
        """Look up a variable, walking the parent chain."""
        if name in self.bindings:
            return self.bindings[name]
        if self.parent is not None:
            return self.parent.lookup(name)
        return None

    def extend(self, name: str, val: SemanticValue) -> Environment:
        """Return a new environment with one extra binding."""
        return Environment(bindings={name: val}, parent=self)

    def extend_many(self, new_bindings: dict[str, SemanticValue]) -> Environment:
        """Return a new environment with several extra bindings."""
        return Environment(bindings=dict(new_bindings), parent=self)

    def all_bindings(self) -> dict[str, SemanticValue]:
        """Flatten the chain into a single dict (closest binding wins)."""
        result: dict[str, SemanticValue] = {}
        if self.parent is not None:
            result.update(self.parent.all_bindings())
        result.update(self.bindings)
        return result

    def __repr__(self) -> str:
        names = list(self.all_bindings().keys())
        return f"Environment({', '.join(names)})"


# ═══════════════════════════════════════════════════════════════════
# Denotation — the ⟦_⟧ function
# ═══════════════════════════════════════════════════════════════════

# Maximum recursion depth for evaluation to prevent runaway terms
_MAX_EVAL_DEPTH = 512


class EvalError(Exception):
    """Raised when evaluation fails in a recoverable way."""


class Denotation:
    """Compositional denotational semantics for Deppy.

    Usage::

        den = Denotation()
        val = den.eval(term, env)

    Each ``eval_*`` method handles one SynTerm constructor and calls
    ``eval`` recursively for sub-terms, ensuring compositionality.
    """

    def __init__(self, *, max_depth: int = _MAX_EVAL_DEPTH) -> None:
        self._max_depth = max_depth
        self._depth = 0
        self._dispatch: dict[type, Callable[..., SemanticValue]] = {
            Var: self.eval_var,
            Literal: self.eval_literal,
            Lam: self.eval_lambda,
            App: self.eval_app,
            Pair: self.eval_pair,
            Fst: self.eval_fst,
            Snd: self.eval_snd,
            LetIn: self.eval_let,
            IfThenElse: self.eval_if,
            PyCall: self.eval_pycall,
            GetAttr: self.eval_getattr,
            GetItem: self.eval_getitem,
            PathAbs: self.eval_path_abs,
            PathApp: self.eval_path_app,
            Transport: self.eval_transport,
            Comp: self.eval_comp,
        }

    # ─── main entry point ───────────────────────────────────────

    def eval(self, term: SynTerm, env: Environment) -> SemanticValue:
        """Evaluate ⟦term⟧ in environment env."""
        self._depth += 1
        if self._depth > self._max_depth:
            self._depth -= 1
            return BottomValue(reason="max recursion depth exceeded")
        try:
            handler = self._dispatch.get(type(term))
            if handler is None:
                return BottomValue(reason=f"no handler for {type(term).__name__}")
            return handler(term, env)
        finally:
            self._depth -= 1

    # ─── individual term forms ──────────────────────────────────

    def eval_var(self, term: Var, env: Environment) -> SemanticValue:
        """⟦x⟧ρ = ρ(x)."""
        val = env.lookup(term.name)
        if val is None:
            return BottomValue(reason=f"unbound variable: {term.name}")
        return val

    def eval_literal(self, term: Literal, env: Environment) -> SemanticValue:
        """⟦v⟧ρ = ConcreteValue(v)."""
        return ConcreteValue(term.value)

    def eval_lambda(self, term: Lam, env: Environment) -> SemanticValue:
        """⟦λx.body⟧ρ = FunctionValue([x], body, ρ)."""
        return FunctionValue(params=[term.param], body=term.body, env=env)

    def eval_app(self, term: App, env: Environment) -> SemanticValue:
        """⟦f(a)⟧ρ = apply(⟦f⟧ρ, ⟦a⟧ρ)."""
        func_val = self.eval(term.func, env)
        arg_val = self.eval(term.arg, env)
        return self._apply(func_val, [arg_val])

    def eval_pair(self, term: Pair, env: Environment) -> SemanticValue:
        """⟦(a, b)⟧ρ = PairValue(⟦a⟧ρ, ⟦b⟧ρ)."""
        fst_val = self.eval(term.fst, env)
        snd_val = self.eval(term.snd, env)
        return PairValue(fst=fst_val, snd=snd_val)

    def eval_fst(self, term: Fst, env: Environment) -> SemanticValue:
        """⟦π₁(p)⟧ρ = (⟦p⟧ρ).fst."""
        p = self.eval(term.pair, env)
        if isinstance(p, PairValue):
            return p.fst
        if isinstance(p, ConcreteValue) and isinstance(p.value, (tuple, list)):
            if len(p.value) >= 1:
                return ConcreteValue(p.value[0])
        return BottomValue(reason=f"fst applied to non-pair: {p}")

    def eval_snd(self, term: Snd, env: Environment) -> SemanticValue:
        """⟦π₂(p)⟧ρ = (⟦p⟧ρ).snd."""
        p = self.eval(term.pair, env)
        if isinstance(p, PairValue):
            return p.snd
        if isinstance(p, ConcreteValue) and isinstance(p.value, (tuple, list)):
            if len(p.value) >= 2:
                return ConcreteValue(p.value[1])
        return BottomValue(reason=f"snd applied to non-pair: {p}")

    def eval_let(self, term: LetIn, env: Environment) -> SemanticValue:
        """⟦let x = e in body⟧ρ = ⟦body⟧(ρ[x ↦ ⟦e⟧ρ])."""
        val = self.eval(term.value, env)
        new_env = env.extend(term.var_name, val)
        return self.eval(term.body, new_env)

    def eval_if(self, term: IfThenElse, env: Environment) -> SemanticValue:
        """⟦if c then t else f⟧ρ = ⟦t⟧ρ if ⟦c⟧ρ is truthy, else ⟦f⟧ρ."""
        cond_val = self.eval(term.cond, env)
        if _is_truthy(cond_val):
            return self.eval(term.then_branch, env)
        return self.eval(term.else_branch, env)

    def eval_pycall(self, term: PyCall, env: Environment) -> SemanticValue:
        """⟦f(a₁, …, aₙ, k₁=v₁, …)⟧ρ = apply(⟦f⟧ρ, args, kwargs)."""
        func_val = self.eval(term.func, env)
        arg_vals = [self.eval(a, env) for a in term.args]
        kwarg_vals = {k: self.eval(v, env) for k, v in term.kwargs}
        return self._apply(func_val, arg_vals, kwarg_vals)

    def eval_getattr(self, term: GetAttr, env: Environment) -> SemanticValue:
        """⟦obj.attr⟧ρ = getattr(⟦obj⟧ρ, attr)."""
        obj_val = self.eval(term.obj, env)
        if isinstance(obj_val, ConcreteValue):
            try:
                return ConcreteValue(getattr(obj_val.value, term.attr))
            except AttributeError:
                return BottomValue(
                    reason=f"{obj_val.value!r} has no attribute {term.attr!r}"
                )
        return BottomValue(reason=f"getattr on non-concrete: {obj_val}")

    def eval_getitem(self, term: GetItem, env: Environment) -> SemanticValue:
        """⟦obj[key]⟧ρ = obj_val[key_val]."""
        obj_val = self.eval(term.obj, env)
        key_val = self.eval(term.key, env)
        if isinstance(obj_val, ConcreteValue) and isinstance(key_val, ConcreteValue):
            try:
                return ConcreteValue(obj_val.value[key_val.value])
            except (KeyError, IndexError, TypeError) as exc:
                return BottomValue(reason=str(exc))
        return BottomValue(reason=f"getitem on non-concrete: {obj_val}[{key_val}]")

    # ─── path / cubical forms ───────────────────────────────────

    def eval_path_abs(self, term: PathAbs, env: Environment) -> SemanticValue:
        """⟦<i> body⟧ρ = PathValue(body[0/i], body[1/i], witness).

        The witness is a function I → SemanticValue obtained by
        evaluating the body with the interval variable bound to
        concrete values.
        """
        start = self.eval(term.body, env.extend(term.ivar, ConcreteValue(0)))
        end = self.eval(term.body, env.extend(term.ivar, ConcreteValue(1)))

        def witness(t: float) -> SemanticValue:
            return self.eval(term.body, env.extend(term.ivar, ConcreteValue(t)))

        return PathValue(start=start, end=end, witness=witness)

    def eval_path_app(self, term: PathApp, env: Environment) -> SemanticValue:
        """⟦p @ r⟧ρ = witness(⟦r⟧ρ)."""
        path_val = self.eval(term.path, env)
        arg_val = self.eval(term.arg, env)
        if isinstance(path_val, PathValue) and path_val.witness is not None:
            r = _to_python(arg_val)
            if r is not None:
                try:
                    return path_val.witness(r)
                except Exception as exc:
                    return BottomValue(reason=f"path application error: {exc}")
        # Degenerate path: start = end regardless of argument
        if isinstance(path_val, PathValue):
            r = _to_python(arg_val)
            if r == 0:
                return path_val.start
            if r == 1:
                return path_val.end
        return BottomValue(reason=f"path application to non-path: {path_val}")

    def eval_transport(self, term: Transport, env: Environment) -> SemanticValue:
        """⟦transp(P, p, d)⟧ρ.

        For concrete paths between equal values, transport is the identity.
        Otherwise we return ⊥ (transport requires computation rules we
        cannot materialise in general).
        """
        path_val = self.eval(term.path, env)
        base_val = self.eval(term.base_term, env)
        if isinstance(path_val, PathValue) and path_val.start.semantic_eq(path_val.end):
            return base_val
        return BottomValue(reason="transport along non-trivial path")

    def eval_comp(self, term: Comp, env: Environment) -> SemanticValue:
        """⟦comp⟧ρ — Kan composition (returns base for trivial faces)."""
        return self.eval(term.base, env)

    # ─── application helper ─────────────────────────────────────

    def _apply(
        self,
        func_val: SemanticValue,
        args: list[SemanticValue],
        kwargs: dict[str, SemanticValue] | None = None,
    ) -> SemanticValue:
        """Apply a semantic function to arguments."""
        if isinstance(func_val, BottomValue):
            return func_val

        if isinstance(func_val, FunctionValue):
            return self._apply_closure(func_val, args)

        if isinstance(func_val, NativeFunctionValue):
            return self._apply_native(func_val, args, kwargs)

        return BottomValue(reason=f"application of non-function: {func_val}")

    def _apply_closure(
        self, closure: FunctionValue, args: list[SemanticValue]
    ) -> SemanticValue:
        """Apply a Deppy closure (FunctionValue) to arguments.

        Supports multi-parameter functions via currying: if the closure
        has more parameters than supplied arguments, a partially-applied
        closure is returned.
        """
        env = closure.env
        params = closure.params
        for i, param in enumerate(params):
            if i < len(args):
                env = env.extend(param, args[i])
            else:
                # Partial application: return a new closure over remaining params
                return FunctionValue(
                    params=params[i:], body=closure.body, env=env
                )
        return self.eval(closure.body, env)

    def _apply_native(
        self,
        native: NativeFunctionValue,
        args: list[SemanticValue],
        kwargs: dict[str, SemanticValue] | None = None,
    ) -> SemanticValue:
        """Apply a native Python function.

        Arguments are unwrapped to Python values before calling; the
        result is re-wrapped as a ConcreteValue.
        """
        py_args = [_to_python(a) for a in args]
        py_kwargs = {}
        if kwargs:
            py_kwargs = {k: _to_python(v) for k, v in kwargs.items()}
        try:
            result = native.func(*py_args, **py_kwargs)
            return ConcreteValue(result)
        except Exception as exc:
            return BottomValue(reason=f"{native.name}: {exc}")


# ═══════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════


def _to_python(val: SemanticValue) -> Any:
    """Unwrap a SemanticValue to a plain Python object."""
    if isinstance(val, ConcreteValue):
        return val.value
    if isinstance(val, PairValue):
        return (_to_python(val.fst), _to_python(val.snd))
    if isinstance(val, NativeFunctionValue):
        return val.func
    if isinstance(val, FunctionValue):
        # Cannot fully unwrap a Deppy closure, but we can make a
        # callable that goes through the evaluator.
        den = Denotation()

        def _wrapper(*py_args: Any) -> Any:
            sv_args = [ConcreteValue(a) for a in py_args]
            result = den._apply_closure(val, sv_args)
            return _to_python(result)

        return _wrapper
    if isinstance(val, BottomValue):
        return None
    if isinstance(val, TypeValue):
        return val.type_
    if isinstance(val, PathValue):
        return (_to_python(val.start), _to_python(val.end))
    return None


def _is_truthy(val: SemanticValue) -> bool:
    """Test whether a semantic value is truthy."""
    if isinstance(val, ConcreteValue):
        try:
            return bool(val.value)
        except Exception:
            return True
    if isinstance(val, BottomValue):
        return False
    # Functions, pairs, types, paths are truthy.
    return True


# ═══════════════════════════════════════════════════════════════════
# Python Builtins Environment
# ═══════════════════════════════════════════════════════════════════


def _wrap(func: Callable[..., Any], name: str | None = None) -> NativeFunctionValue:
    """Wrap a Python callable as a NativeFunctionValue."""
    return NativeFunctionValue(func=func, name=name or getattr(func, "__name__", "?"))


def python_builtins_env() -> Environment:
    """Create an environment pre-populated with standard Python builtins.

    Includes common functions (``len``, ``sorted``, ``range``, …),
    type constructors (``int``, ``str``, ``list``, …), and arithmetic
    operators exposed as named functions.
    """
    builtins: dict[str, SemanticValue] = {
        # Type constructors
        "int": _wrap(int, "int"),
        "float": _wrap(float, "float"),
        "str": _wrap(str, "str"),
        "bool": _wrap(bool, "bool"),
        "list": _wrap(list, "list"),
        "dict": _wrap(dict, "dict"),
        "tuple": _wrap(tuple, "tuple"),
        "set": _wrap(set, "set"),
        "frozenset": _wrap(frozenset, "frozenset"),
        # Common functions
        "len": _wrap(len, "len"),
        "sorted": _wrap(sorted, "sorted"),
        "reversed": _wrap(lambda x: list(reversed(x)), "reversed"),
        "range": _wrap(range, "range"),
        "enumerate": _wrap(lambda x: list(enumerate(x)), "enumerate"),
        "zip": _wrap(lambda *a: list(zip(*a)), "zip"),
        "map": _wrap(lambda f, *a: list(map(f, *a)), "map"),
        "filter": _wrap(lambda f, a: list(filter(f, a)), "filter"),
        "sum": _wrap(sum, "sum"),
        "min": _wrap(min, "min"),
        "max": _wrap(max, "max"),
        "abs": _wrap(abs, "abs"),
        "round": _wrap(round, "round"),
        "all": _wrap(all, "all"),
        "any": _wrap(any, "any"),
        "print": _wrap(print, "print"),
        "repr": _wrap(repr, "repr"),
        "type": _wrap(type, "type"),
        "isinstance": _wrap(isinstance, "isinstance"),
        "hasattr": _wrap(hasattr, "hasattr"),
        "getattr": _wrap(getattr, "getattr"),
        # Constants
        "True": ConcreteValue(True),
        "False": ConcreteValue(False),
        "None": ConcreteValue(None),
        # Arithmetic helpers (useful for term-level arithmetic)
        "__add__": _wrap(operator.add, "__add__"),
        "__sub__": _wrap(operator.sub, "__sub__"),
        "__mul__": _wrap(operator.mul, "__mul__"),
        "__truediv__": _wrap(operator.truediv, "__truediv__"),
        "__floordiv__": _wrap(operator.floordiv, "__floordiv__"),
        "__mod__": _wrap(operator.mod, "__mod__"),
        "__pow__": _wrap(operator.pow, "__pow__"),
        "__neg__": _wrap(operator.neg, "__neg__"),
        "__eq__": _wrap(operator.eq, "__eq__"),
        "__ne__": _wrap(operator.ne, "__ne__"),
        "__lt__": _wrap(operator.lt, "__lt__"),
        "__le__": _wrap(operator.le, "__le__"),
        "__gt__": _wrap(operator.gt, "__gt__"),
        "__ge__": _wrap(operator.ge, "__ge__"),
        "__and__": _wrap(operator.and_, "__and__"),
        "__or__": _wrap(operator.or_, "__or__"),
        "__not__": _wrap(operator.not_, "__not__"),
    }
    return Environment(bindings=builtins)


# ═══════════════════════════════════════════════════════════════════
# Type-Directed Test Generation
# ═══════════════════════════════════════════════════════════════════


class TypeDirectedGenerator:
    """Generate random SemanticValues inhabiting a given SynType.

    Used by ``SemanticEquivalence`` to sample environments.

    ``size`` controls the magnitude of generated values:
    - for ints, values lie in ``[-size, size]``
    - for strings, length ≤ ``size``
    - for lists, length ≤ ``size``

    The generator is deterministic if seeded via ``random.seed``.
    """

    def __init__(self, *, rng: random.Random | None = None) -> None:
        self._rng = rng or random.Random()

    def generate(self, ty: SynType, size: int = 10) -> SemanticValue:
        """Produce a random value of the given type."""
        if isinstance(ty, PyIntType):
            return ConcreteValue(self._rng.randint(-size, size))

        if isinstance(ty, PyFloatType):
            return ConcreteValue(self._rng.uniform(-size, size))

        if isinstance(ty, PyBoolType):
            return ConcreteValue(self._rng.choice([True, False]))

        if isinstance(ty, PyStrType):
            length = self._rng.randint(0, size)
            chars = self._rng.choices(string.ascii_lowercase, k=length)
            return ConcreteValue("".join(chars))

        if isinstance(ty, PyNoneType):
            return ConcreteValue(None)

        if isinstance(ty, PyListType):
            length = self._rng.randint(0, size)
            elems = [
                _to_python(self.generate(ty.element_type, size=max(1, size // 2)))
                for _ in range(length)
            ]
            return ConcreteValue(elems)

        if isinstance(ty, PyDictType):
            length = self._rng.randint(0, max(1, size // 2))
            d: dict[Any, Any] = {}
            for _ in range(length):
                k = _to_python(self.generate(ty.key_type, size=max(1, size // 2)))
                v = _to_python(self.generate(ty.value_type, size=max(1, size // 2)))
                try:
                    d[k] = v
                except TypeError:
                    pass
            return ConcreteValue(d)

        if isinstance(ty, PyTupleType):
            if ty.element_types:
                elems = tuple(
                    _to_python(self.generate(et, size=max(1, size // 2)))
                    for et in ty.element_types
                )
                return ConcreteValue(elems)
            length = self._rng.randint(0, size)
            return ConcreteValue(
                tuple(self._rng.randint(-size, size) for _ in range(length))
            )

        if isinstance(ty, PySetType):
            length = self._rng.randint(0, size)
            elems = set()
            for _ in range(length):
                v = _to_python(self.generate(ty.element_type, size=max(1, size // 2)))
                try:
                    elems.add(v)
                except TypeError:
                    pass
            return ConcreteValue(elems)

        if isinstance(ty, RefinementType):
            # Generate from the base type; we do not enforce the predicate
            # (the predicate is a string parsed elsewhere).
            return self.generate(ty.base_type, size=size)

        if isinstance(ty, UnionType):
            if ty.alternatives:
                alt = self._rng.choice(ty.alternatives)
                return self.generate(alt, size=size)
            return ConcreteValue(None)

        if isinstance(ty, OptionalType):
            if self._rng.random() < 0.2:
                return ConcreteValue(None)
            return self.generate(ty.inner, size=size)

        if isinstance(ty, SigmaType):
            fst = self.generate(ty.fst_type, size=max(1, size // 2))
            snd = self.generate(ty.snd_type, size=max(1, size // 2))
            return PairValue(fst=fst, snd=snd)

        if isinstance(ty, PiType):
            # We cannot generate truly random *functions*. Instead we
            # generate a constant function returning a random value of
            # the body type.
            ret = self.generate(ty.body_type, size=max(1, size // 2))
            py_ret = _to_python(ret)
            return NativeFunctionValue(
                func=lambda *_a, _v=py_ret: _v,
                name="<gen-const>",
            )

        if isinstance(ty, IntervalType):
            return ConcreteValue(self._rng.choice([0, 1]))

        if isinstance(ty, UniverseType):
            return TypeValue(PyObjType())

        if isinstance(ty, PathType):
            v = self.generate(ty.base_type, size=size)
            return PathValue(start=v, end=v)

        if isinstance(ty, PyCallableType):
            ret = self.generate(ty.return_type, size=max(1, size // 2))
            py_ret = _to_python(ret)
            return NativeFunctionValue(
                func=lambda *_a, _v=py_ret: _v,
                name="<gen-callable>",
            )

        if isinstance(ty, PyObjType):
            choice = self._rng.randint(0, 3)
            if choice == 0:
                return ConcreteValue(self._rng.randint(-size, size))
            if choice == 1:
                return ConcreteValue(
                    "".join(self._rng.choices(string.ascii_lowercase,
                                              k=self._rng.randint(0, size)))
                )
            if choice == 2:
                return ConcreteValue(self._rng.random() < 0.5)
            return ConcreteValue(None)

        # Fallback: produce None for unknown types
        return ConcreteValue(None)


# ═══════════════════════════════════════════════════════════════════
# Semantic Equivalence
# ═══════════════════════════════════════════════════════════════════


class SemanticEquivalence:
    """Check whether ⟦t₁⟧ρ = ⟦t₂⟧ρ for randomly sampled environments ρ.

    This is *not* a proof of equivalence — it is a lightweight
    property-based test.  If ``check_equal`` returns ``False`` the
    terms are *definitely* not equivalent; if it returns ``True`` they
    are *likely* equivalent (modulo sampling).
    """

    def __init__(
        self,
        denotation: Denotation | None = None,
        generator: TypeDirectedGenerator | None = None,
    ) -> None:
        self._den = denotation or Denotation()
        self._gen = generator or TypeDirectedGenerator()

    def check_equal(
        self,
        t1: SynTerm,
        t2: SynTerm,
        context: Context,
        num_samples: int = 100,
    ) -> bool:
        """Return ``True`` if ⟦t1⟧ρ ≡ ⟦t2⟧ρ for ``num_samples`` random ρ.

        ``context`` specifies the types of free variables so the
        generator can produce well-typed environments.
        """
        for _ in range(num_samples):
            env = self._sample_env(context)
            v1 = self._den.eval(t1, env)
            v2 = self._den.eval(t2, env)
            # Treat two ⊥ results as equal (both fail).
            if isinstance(v1, BottomValue) and isinstance(v2, BottomValue):
                continue
            if not v1.semantic_eq(v2):
                return False
        return True

    def find_difference(
        self,
        t1: SynTerm,
        t2: SynTerm,
        context: Context,
        num_samples: int = 200,
    ) -> tuple[Environment, SemanticValue, SemanticValue] | None:
        """Find an environment where ⟦t1⟧ and ⟦t2⟧ differ.

        Returns ``(env, v1, v2)`` on the first discrepancy, or ``None``
        if none is found within ``num_samples`` attempts.
        """
        for _ in range(num_samples):
            env = self._sample_env(context)
            v1 = self._den.eval(t1, env)
            v2 = self._den.eval(t2, env)
            if isinstance(v1, BottomValue) and isinstance(v2, BottomValue):
                continue
            if not v1.semantic_eq(v2):
                return (env, v1, v2)
        return None

    # ─── homotopy-native path operations ───────────────────────

    def find_path(
        self,
        a: SemanticValue,
        b: SemanticValue,
        context: Context | None = None,
        num_samples: int = 100,
    ) -> PathValue | None:
        """Find a semantic path between two values.

        Two functions f, g have a path between them iff
        ∀ inputs. f(inputs) and g(inputs) are path-equal.

        The path is constructed as:
        λ(i:I). λ(x). if i == 0 then f(x) else if i == 1 then g(x)
                       else interpolate(f(x), g(x), i)

        For concrete values, interpolation is trivial (they're equal or
        not).  For functions, we construct a pointwise path.  Returns
        ``None`` when no path can be found (the values are observably
        different).
        """
        # Identity: every value has a reflexivity path to itself
        if a is b:
            return PathValue(start=a, end=b, witness=lambda i: a)

        # Concrete values
        if isinstance(a, ConcreteValue) and isinstance(b, ConcreteValue):
            if a.semantic_eq(b):
                return PathValue(
                    start=a, end=b,
                    witness=lambda i, _a=a, _b=b: _a if i <= 0.5 else _b,
                )
            return None

        # Pair values: construct a componentwise path
        if isinstance(a, PairValue) and isinstance(b, PairValue):
            fst_path = self.find_path(a.fst, b.fst, context)
            snd_path = self.find_path(a.snd, b.snd, context)
            if fst_path is not None and snd_path is not None:
                def _pair_witness(
                    i: float,
                    _fp: PathValue = fst_path,
                    _sp: PathValue = snd_path,
                ) -> SemanticValue:
                    return PairValue(fst=_fp.at(i), snd=_sp.at(i))
                return PathValue(start=a, end=b, witness=_pair_witness)
            return None

        # Bottom values: all ⊥ are path-equal
        if isinstance(a, BottomValue) and isinstance(b, BottomValue):
            return PathValue(
                start=a, end=b,
                witness=lambda i, _a=a, _b=b: _a if i <= 0.5 else _b,
            )

        # Type values
        if isinstance(a, TypeValue) and isinstance(b, TypeValue):
            if a.semantic_eq(b):
                return PathValue(start=a, end=b, witness=lambda i, _a=a: _a)
            return None

        # Path values (paths between paths → higher structure)
        if isinstance(a, PathValue) and isinstance(b, PathValue):
            if a.semantic_eq(b):
                return PathValue(
                    start=a, end=b,
                    witness=lambda i, _a=a, _b=b: _a if i <= 0.5 else _b,
                )
            return None

        # Functions: test pointwise via sampling
        if (isinstance(a, (FunctionValue, NativeFunctionValue))
                and isinstance(b, (FunctionValue, NativeFunctionValue))):
            return self._find_function_path(a, b, context, num_samples)

        return None

    def are_equivalent(
        self,
        a: SemanticValue,
        b: SemanticValue,
        context: Context | None = None,
        num_samples: int = 100,
    ) -> PathValue | None:
        """Return a path witnessing a ≡ b, or ``None``.

        This is the homotopy-native replacement for a bare boolean
        equivalence check: instead of answering *whether* two values
        are equal it returns *evidence* (a path) when they are.
        """
        return self.find_path(a, b, context, num_samples)

    def _find_function_path(
        self,
        f: SemanticValue,
        g: SemanticValue,
        context: Context | None,
        num_samples: int,
    ) -> PathValue | None:
        """Attempt to construct a pointwise path between two functions."""
        for _ in range(num_samples):
            arg = self._gen.generate(PyObjType(), size=10)
            f_result = self._den._apply(f, [arg])
            g_result = self._den._apply(g, [arg])
            if isinstance(f_result, BottomValue) and isinstance(g_result, BottomValue):
                continue
            if not f_result.semantic_eq(g_result):
                return None

        def _func_witness(
            i: float,
            _f: SemanticValue = f,
            _g: SemanticValue = g,
        ) -> SemanticValue:
            if i == 0.0:
                return _f
            if i == 1.0:
                return _g
            if isinstance(_f, NativeFunctionValue):
                return NativeFunctionValue(
                    func=lambda *args, _i=i, __f=_f, __g=_g: (
                        __f.func(*args) if _i <= 0.5 else __g.func(*args)
                    ),
                    name=f"<path-interp-{i:.2f}>",
                )
            return _f if i <= 0.5 else _g

        return PathValue(start=f, end=g, witness=_func_witness)

    def compose_paths(self, p: PathValue, q: PathValue) -> PathValue:
        """Compose paths: if p : a = b and q : b = c, return p·q : a = c.

        Composition traverses p at double speed on [0, 0.5], then
        traverses q at double speed on [0.5, 1].
        """
        def _witness(i: float, _p: PathValue = p, _q: PathValue = q) -> SemanticValue:
            if i <= 0.5:
                return _p.at(2 * i)
            return _q.at(2 * i - 1)

        return PathValue(start=p.start, end=q.end, witness=_witness)

    def invert_path(self, p: PathValue) -> PathValue:
        """Invert a path: if p : a = b, return p⁻¹ : b = a."""
        def _witness(i: float, _p: PathValue = p) -> SemanticValue:
            return _p.at(1.0 - i)

        return PathValue(start=p.end, end=p.start, witness=_witness)

    def ap_path(
        self,
        f: FunctionValue | NativeFunctionValue,
        p: PathValue,
    ) -> PathValue:
        """Apply a function to a path: ap f p : f(a) = f(b).

        Given f : A → B and p : a = b (in A), produces a path
        f(a) = f(b) in B by applying f pointwise along the path.
        """
        f_start = self._den._apply(f, [p.start])
        f_end = self._den._apply(f, [p.end])

        def _witness(
            i: float,
            _f: SemanticValue = f,
            _p: PathValue = p,
            _den: Denotation = self._den,
        ) -> SemanticValue:
            return _den._apply(_f, [_p.at(i)])

        return PathValue(start=f_start, end=f_end, witness=_witness)

    # ─── private helpers ────────────────────────────────────────

    def _sample_env(self, context: Context) -> Environment:
        """Build a random environment matching a typing context."""
        all_bindings = context.all_bindings()
        env = python_builtins_env()
        for name, ty in all_bindings.items():
            env = env.extend(name, self._gen.generate(ty))
        return env


# ═══════════════════════════════════════════════════════════════════
# Homotopy Structures — Čech covers, fibrations, transport, ∞-groupoid
# ═══════════════════════════════════════════════════════════════════


@dataclass
class DenotationalPatch:
    """A local denotation on a subdomain of inputs.

    Part of a Čech cover: the ``condition`` selects which inputs
    this patch applies to, and ``denotation`` gives the local meaning
    of the function restricted to that sub-domain.
    """
    condition: Callable[..., bool]
    denotation: FunctionValue | NativeFunctionValue
    domain_description: str = ""


class DenotationalCechCover:
    """A Čech cover of a function's denotation.

    The denotation of a branching function is a SHEAF: different input
    regions have different local denotations.  A ``DenotationalCechCover``
    decomposes the function into patches and lets you verify the
    *sheaf condition*: patches must agree on their overlaps.

    Example: a function with ``if isinstance(x, int)`` and ``elif
    isinstance(x, str)`` branches has two natural patches.  The
    sheaf condition is trivially satisfied because the patches
    don't overlap.
    """

    def __init__(self, func_value: FunctionValue | NativeFunctionValue):
        self.func = func_value
        self.patches: list[DenotationalPatch] = []
        self._den = Denotation()

    def add_patch(
        self,
        condition: Callable[..., bool],
        denotation: FunctionValue | NativeFunctionValue,
        description: str = "",
    ) -> None:
        """Add a local denotation for inputs satisfying *condition*."""
        self.patches.append(DenotationalPatch(
            condition=condition,
            denotation=denotation,
            domain_description=description,
        ))

    def check_sheaf_condition(
        self,
        num_samples: int = 100,
        rng: random.Random | None = None,
    ) -> bool:
        """Verify the sheaf condition: patches agree on overlaps.

        For each pair of patches (Uᵢ, Uⱼ) we sample inputs that lie in
        Uᵢ ∩ Uⱼ and check that the two local denotations produce the
        same output.  Returns ``True`` iff no disagreement is found.
        """
        _rng = rng or random.Random()
        gen = TypeDirectedGenerator(rng=_rng)

        for i, pi in enumerate(self.patches):
            for j, pj in enumerate(self.patches):
                if i >= j:
                    continue
                for _ in range(num_samples):
                    test_input = gen.generate(PyObjType(), size=10)
                    py_input = _to_python(test_input)
                    try:
                        in_i = pi.condition(py_input)
                        in_j = pj.condition(py_input)
                    except Exception:
                        continue
                    if in_i and in_j:
                        result_i = self._den._apply(pi.denotation, [test_input])
                        result_j = self._den._apply(pj.denotation, [test_input])
                        if (isinstance(result_i, BottomValue)
                                and isinstance(result_j, BottomValue)):
                            continue
                        if not result_i.semantic_eq(result_j):
                            return False
        return True

    def global_section(self) -> NativeFunctionValue:
        """Reconstruct the global denotation from local patches.

        Applies the first matching patch for each input; falls back to
        the original function when no patch matches.
        """
        patches = list(self.patches)
        den = self._den
        original = self.func

        def _global(*args: Any) -> Any:
            sv_args = [ConcreteValue(a) for a in args]
            for patch in patches:
                try:
                    if patch.condition(*args):
                        result = den._apply(patch.denotation, sv_args)
                        return _to_python(result)
                except Exception:
                    continue
            result = den._apply(original, sv_args)
            return _to_python(result)

        return NativeFunctionValue(func=_global, name="<global-section>")


class DenotationalFibration:
    """The fibration structure of isinstance-dispatched functions.

    Total space: all (input, output) pairs.
    Base space:  the set of runtime types.
    Fiber over type T: the restriction of the function to inputs of
    type T.

    This mirrors how Python dispatches on ``isinstance``: each branch
    is a fiber, and the total function is the disjoint union of fibers
    over the type lattice.
    """

    def __init__(self, func_value: FunctionValue | NativeFunctionValue):
        self.func = func_value
        self.fibers: dict[type, FunctionValue | NativeFunctionValue] = {}
        self._den = Denotation()

    def add_fiber(
        self,
        typ: type,
        restriction: FunctionValue | NativeFunctionValue,
    ) -> None:
        """Add the fiber over a specific type."""
        self.fibers[typ] = restriction

    def total_denotation(self) -> NativeFunctionValue:
        """Reconstruct the total function from fibers.

        Dispatches to the first matching fiber based on the runtime
        type of the first argument.
        """
        fibers = dict(self.fibers)
        den = self._den
        original = self.func

        def _total(*args: Any) -> Any:
            if args:
                for typ, fiber in fibers.items():
                    if isinstance(args[0], typ):
                        sv_args = [ConcreteValue(a) for a in args]
                        result = den._apply(fiber, sv_args)
                        return _to_python(result)
            sv_args = [ConcreteValue(a) for a in args]
            result = den._apply(original, sv_args)
            return _to_python(result)

        return NativeFunctionValue(func=_total, name="<total-denotation>")

    def verify_per_fiber(
        self,
        spec: Callable[[Any], bool],
        num_samples: int = 50,
        rng: random.Random | None = None,
    ) -> dict[type, bool]:
        """Verify *spec* on each fiber independently.

        Returns a mapping ``{type: bool}`` indicating whether the spec
        holds for every sampled input of that type.
        """
        _rng = rng or random.Random()
        gen = TypeDirectedGenerator(rng=_rng)

        _type_map: dict[type, SynType] = {
            int: PyIntType(),
            float: PyFloatType(),
            str: PyStrType(),
            bool: PyBoolType(),
            list: PyListType(element_type=PyIntType()),
        }

        results: dict[type, bool] = {}
        for typ, fiber in self.fibers.items():
            syntype = _type_map.get(typ, PyObjType())
            passed = True
            for _ in range(num_samples):
                test_input = gen.generate(syntype, size=10)
                result = self._den._apply(fiber, [test_input])
                py_result = _to_python(result)
                try:
                    if not spec(py_result):
                        passed = False
                        break
                except Exception:
                    passed = False
                    break
            results[typ] = passed

        return results


class SemanticTransport:
    """Transport semantic properties along paths.

    In HoTT, transport takes a type family P, a path p : a = b, and
    a proof of P(a), and produces a proof of P(b).  Semantically: if a
    spec holds for one implementation and another implementation is
    path-equivalent, the spec transfers.
    """

    def transport(
        self,
        property: Callable[[SemanticValue], bool],
        path: PathValue,
    ) -> bool:
        """Given that *property* holds at path.start, check path.end.

        Verifies the property at several sample points along the path
        to ensure it is preserved under the equivalence.
        """
        if not property(path.start):
            return False
        for i_val in (0.0, 0.25, 0.5, 0.75, 1.0):
            intermediate = path.at(i_val)
            if not property(intermediate):
                return False
        return True

    def transport_proof(
        self,
        proof_of_left: Any,
        path: PathValue,
        type_family: Callable[[SemanticValue], type] | None = None,
    ) -> Any:
        """Transport a proof term along a semantic path.

        When *type_family* is given, the transported proof is
        re-interpreted in the fiber over ``path.end``.  Without a type
        family the proof is returned unchanged (identity transport).
        """
        if type_family is not None:
            target_type = type_family(path.end)
            if callable(target_type):
                try:
                    return target_type(proof_of_left)
                except Exception:
                    return proof_of_left
        return proof_of_left


class InfinityGroupoid:
    """The ∞-groupoid of Python semantic values.

    - 0-cells: SemanticValues
    - 1-cells: PathValues (behavioral equivalences)
    - 2-cells: HigherPathValues (equivalences between equivalences)
    - n-cells: …

    This gives Python values genuine higher structure.  Values are
    objects, paths between values are (invertible) morphisms, and paths
    between paths are 2-morphisms.  All morphisms are invertible
    (groupoid condition), composable (category), and the composition
    is associative up to higher paths.
    """

    def __init__(self) -> None:
        self._values: dict[int, SemanticValue] = {}
        self._paths: dict[tuple[int, int], list[PathValue]] = {}
        self._higher: dict[tuple[int, int], list[HigherPathValue]] = {}

    # ── 0-cells ─────────────────────────────────────────────────

    def add_value(self, v: SemanticValue) -> None:
        """Register a 0-cell (value) in the groupoid."""
        self._values[id(v)] = v

    # ── 1-cells ─────────────────────────────────────────────────

    def add_path(
        self,
        a: SemanticValue,
        b: SemanticValue,
        p: PathValue,
    ) -> None:
        """Add a 1-cell (path) between two 0-cells."""
        self.add_value(a)
        self.add_value(b)
        key = (id(a), id(b))
        self._paths.setdefault(key, []).append(p)

    def get_paths(
        self,
        a: SemanticValue,
        b: SemanticValue,
    ) -> list[PathValue]:
        """Return all registered paths from *a* to *b*."""
        return list(self._paths.get((id(a), id(b)), []))

    # ── 2-cells ─────────────────────────────────────────────────

    def add_2_cell(
        self,
        p: PathValue,
        q: PathValue,
        h: HigherPathValue,
    ) -> None:
        """Add a 2-cell (higher path) between two 1-cells."""
        key = (id(p), id(q))
        self._higher.setdefault(key, []).append(h)

    # ── connectivity ────────────────────────────────────────────

    def are_connected(
        self,
        a: SemanticValue,
        b: SemanticValue,
    ) -> bool:
        """Check if there is any path between *a* and *b*.

        Uses BFS over registered 1-cells in both directions (every
        path is invertible in a groupoid).
        """
        aid, bid = id(a), id(b)
        if aid == bid:
            return True

        visited: set[int] = set()
        frontier: list[int] = [aid]

        while frontier:
            current = frontier.pop(0)
            if current == bid:
                return True
            if current in visited:
                continue
            visited.add(current)

            for (src, tgt), paths in self._paths.items():
                if not paths:
                    continue
                if src == current and tgt not in visited:
                    frontier.append(tgt)
                if tgt == current and src not in visited:
                    frontier.append(src)

        return False

    def path_components(self) -> list[set[int]]:
        """Compute connected components (equivalence classes of values).

        Returns a list of sets, each containing the ``id``s of values
        in one connected component of the groupoid.
        """
        remaining = set(self._values.keys())
        components: list[set[int]] = []

        while remaining:
            seed = next(iter(remaining))
            component: set[int] = set()
            frontier = [seed]

            while frontier:
                current = frontier.pop(0)
                if current in component:
                    continue
                component.add(current)

                for (src, tgt), paths in self._paths.items():
                    if not paths:
                        continue
                    if src == current and tgt not in component:
                        frontier.append(tgt)
                    if tgt == current and src not in component:
                        frontier.append(src)

            components.append(component)
            remaining -= component

        return components

    def fundamental_group(
        self,
        basepoint: SemanticValue,
    ) -> list[PathValue]:
        """Compute loops at *basepoint* (π₁).

        Returns all registered paths that start and end at the
        basepoint, including compositions of registered paths.
        """
        bp_id = id(basepoint)
        loops: list[PathValue] = []

        # Direct loops: basepoint → basepoint
        loops.extend(self._paths.get((bp_id, bp_id), []))

        # Composed loops: basepoint → x → basepoint
        equiv = SemanticEquivalence()
        for (src, tgt), p_list in self._paths.items():
            if src == bp_id and tgt != bp_id:
                for (src2, tgt2), q_list in self._paths.items():
                    if src2 == tgt and tgt2 == bp_id:
                        for p in p_list:
                            for q in q_list:
                                loops.append(equiv.compose_paths(p, q))

        return loops

    def values(self) -> list[SemanticValue]:
        """Return all registered 0-cells."""
        return list(self._values.values())


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════


def _self_test() -> None:
    """Run basic sanity checks (invoked by ``python -m … denotation``)."""
    den = Denotation()
    builtins = python_builtins_env()
    empty = Environment()

    # ── literals ────────────────────────────────────────────────
    assert den.eval(Literal(42), empty).semantic_eq(ConcreteValue(42))
    assert den.eval(Literal("hello"), empty).semantic_eq(ConcreteValue("hello"))
    assert den.eval(Literal(True), empty).semantic_eq(ConcreteValue(True))
    print("  ✓ literals")

    # ── variables ───────────────────────────────────────────────
    env = empty.extend("x", ConcreteValue(7))
    assert den.eval(Var("x"), env).semantic_eq(ConcreteValue(7))
    assert isinstance(den.eval(Var("y"), env), BottomValue)
    print("  ✓ variables")

    # ── lambda / application ────────────────────────────────────
    # λx. x  applied to 5  →  5
    identity = Lam(param="x", body=Var("x"))
    result = den.eval(App(func=identity, arg=Literal(5)), empty)
    assert result.semantic_eq(ConcreteValue(5)), f"got {result}"
    print("  ✓ lambda / app (identity)")

    # ── let binding ─────────────────────────────────────────────
    # let y = 10 in y  →  10
    let_term = LetIn(var_name="y", value=Literal(10), body=Var("y"))
    assert den.eval(let_term, empty).semantic_eq(ConcreteValue(10))
    print("  ✓ let binding")

    # ── if-then-else ────────────────────────────────────────────
    ite = IfThenElse(
        cond=Literal(True), then_branch=Literal(1), else_branch=Literal(2),
    )
    assert den.eval(ite, empty).semantic_eq(ConcreteValue(1))
    ite_f = IfThenElse(
        cond=Literal(False), then_branch=Literal(1), else_branch=Literal(2),
    )
    assert den.eval(ite_f, empty).semantic_eq(ConcreteValue(2))
    print("  ✓ if-then-else")

    # ── pair / fst / snd ────────────────────────────────────────
    pair = Pair(fst=Literal(3), snd=Literal(4))
    pv = den.eval(pair, empty)
    assert isinstance(pv, PairValue)
    assert den.eval(Fst(pair=pair), empty).semantic_eq(ConcreteValue(3))
    assert den.eval(Snd(pair=pair), empty).semantic_eq(ConcreteValue(4))
    print("  ✓ pair / fst / snd")

    # ── PyCall with builtins ────────────────────────────────────
    call_len = PyCall(func=Var("len"), args=(Literal([1, 2, 3]),))
    assert den.eval(call_len, builtins).semantic_eq(ConcreteValue(3))
    print("  ✓ pycall (len)")

    # ── getattr ─────────────────────────────────────────────────
    ga = GetAttr(obj=Literal("hello"), attr="upper")
    ga_val = den.eval(ga, empty)
    assert isinstance(ga_val, ConcreteValue) and callable(ga_val.value)
    print("  ✓ getattr")

    # ── getitem ─────────────────────────────────────────────────
    gi = GetItem(obj=Literal([10, 20, 30]), key=Literal(1))
    assert den.eval(gi, empty).semantic_eq(ConcreteValue(20))
    print("  ✓ getitem")

    # ── path abstraction / application ──────────────────────────
    pa = PathAbs(ivar="i", body=Var("i"))
    pv2 = den.eval(pa, empty)
    assert isinstance(pv2, PathValue)
    assert pv2.start.semantic_eq(ConcreteValue(0))
    assert pv2.end.semantic_eq(ConcreteValue(1))
    # p @ 0 = start, p @ 1 = end
    pa_app0 = PathApp(path=pa, arg=Literal(0))
    assert den.eval(pa_app0, empty).semantic_eq(ConcreteValue(0))
    pa_app1 = PathApp(path=pa, arg=Literal(1))
    assert den.eval(pa_app1, empty).semantic_eq(ConcreteValue(1))
    print("  ✓ path abs / app")

    # ── semantic equivalence ────────────────────────────────────
    equiv = SemanticEquivalence()

    # (λx. x)(y) ≡ y  for all y : int
    ctx = Context(bindings={"y": PyIntType()})
    t1 = App(func=Lam(param="x", body=Var("x")), arg=Var("y"))
    t2 = Var("y")
    assert equiv.check_equal(t1, t2, ctx), "identity app should equal variable"

    # (λx. x + 1)(y) ≢ y  for int y
    # Encode x + 1 as a pycall to __add__
    plus_one_body = PyCall(
        func=Var("__add__"), args=(Var("x"), Literal(1)),
    )
    t3 = App(func=Lam(param="x", body=plus_one_body), arg=Var("y"))
    assert not equiv.check_equal(t3, t2, ctx), "x+1 should differ from x"
    print("  ✓ semantic equivalence (identity ≡ id, id+1 ≢ id)")

    # ── find_difference ─────────────────────────────────────────
    diff = equiv.find_difference(t3, t2, ctx)
    assert diff is not None, "should find a difference for x+1 vs x"
    print("  ✓ find_difference")

    # ── type-directed generation ────────────────────────────────
    gen = TypeDirectedGenerator(rng=random.Random(42))
    for ty in [
        PyIntType(), PyStrType(), PyBoolType(), PyFloatType(),
        PyNoneType(), PyListType(element_type=PyIntType()),
        PyDictType(key_type=PyStrType(), value_type=PyIntType()),
        SigmaType(fst_type=PyIntType(), snd_type=PyStrType()),
    ]:
        v = gen.generate(ty, size=5)
        assert isinstance(v, SemanticValue), f"bad generation for {ty}: {v}"
    print("  ✓ type-directed generation")

    # ── environment operations ──────────────────────────────────
    e1 = Environment()
    e2 = e1.extend("a", ConcreteValue(1))
    e3 = e2.extend_many({"b": ConcreteValue(2), "c": ConcreteValue(3)})
    assert e3.lookup("a") is not None
    assert e3.lookup("b") is not None
    assert e3.lookup("c") is not None
    assert e3.lookup("d") is None
    assert set(e3.all_bindings().keys()) == {"a", "b", "c"}
    print("  ✓ environment operations")

    print("\nAll self-tests passed ✓")


if __name__ == "__main__":
    _self_test()
