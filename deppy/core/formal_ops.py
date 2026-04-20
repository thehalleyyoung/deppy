"""
Deppy Formal Operations
==========================

Provides the **Op** node (a dedicated operator/constant distinct from Var),
formal axiom entries with machine-checkable content, pattern matching for
axiom instantiation, and a library of canonical Python/math operation
constructors.

Design principle:  ``Op("matmul")`` is an *operation symbol* in the kernel's
signature — it is **not** a user variable.  This prevents ambiguity between
library operations and user bindings, and makes normalization/canonicalization
tractable.

Architecture
------------
- ``Op``           — term node for named operations (replaces ``Var`` for ops)
- ``FormalAxiomEntry`` — axiom with machine-checkable params + conclusion
- ``PatternMatcher``   — one-way match from axiom schema → goal
- ``op_*`` helpers     — canonical constructors for every Python/math operation
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PyClassType, PyTupleType, PySetType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
)


# ═══════════════════════════════════════════════════════════════════
# Op — dedicated operator / constant node
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Op(SynTerm):
    """A named operation/constant in the kernel signature.

    Unlike ``Var``, an ``Op`` is never bound by a lambda or let — it is
    a *constant* whose meaning is fixed by the axiom library.

    Examples::

        Op("matmul")           # matrix multiplication
        Op("list.append")      # list append method
        Op("sympy.expand")     # sympy expand function
        Op("torch.relu")       # PyTorch ReLU
        Op("__add__")          # Python dunder add
    """
    name: str = ""
    module: str = ""  # optional qualifier ("sympy", "torch", etc.)

    @property
    def qualified(self) -> str:
        return f"{self.module}.{self.name}" if self.module else self.name

    def _repr(self) -> str:
        return f"Op({self.qualified})"

    def free_vars(self) -> set[str]:
        return set()  # Ops are constants, never free variables


# ═══════════════════════════════════════════════════════════════════
# OpCall — apply an Op to arguments (replaces PyCall(Var(...), ...))
# ═══════════════════════════════════════════════════════════════════

@dataclass
class OpCall(SynTerm):
    """Apply a named operation to arguments.

    ``OpCall(Op("matmul"), (A, B))`` represents ``matmul(A, B)``.
    This is the canonical form for operation applications — the kernel
    normalizes ``PyCall(Var("matmul"), ...)`` to this when matching.
    """
    op: Op = field(default_factory=Op)
    args: tuple[SynTerm, ...] = ()
    kwargs: tuple[tuple[str, SynTerm], ...] = ()

    def _repr(self) -> str:
        parts = [str(a) for a in self.args]
        parts += [f"{k}={v}" for k, v in self.kwargs]
        return f"{self.op.qualified}({', '.join(parts)})"

    def free_vars(self) -> set[str]:
        fv: set[str] = set()
        for a in self.args:
            fv |= a.free_vars()
        for _, v in self.kwargs:
            fv |= v.free_vars()
        return fv


# ═══════════════════════════════════════════════════════════════════
# FormalAxiomEntry — axiom with machine-checkable content
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FormalAxiomEntry:
    """An axiom with a formally stated, machine-checkable conclusion.

    The axiom is universally quantified over ``params``::

        ∀ (A : Matrix) (B : Matrix) (C : Matrix).
            matmul(matmul(A, B), C) =_{Matrix} matmul(A, matmul(B, C))

    When invoked in a proof, the kernel pattern-matches the goal
    against ``conclusion`` to infer the substitution for ``params``,
    then verifies the match is valid.
    """
    name: str
    module: str
    params: list[tuple[str, SynType]]   # universally quantified variables
    conclusion: Judgment                 # formal statement
    description: str = ""               # human-readable
    verified_by_testing: bool = False

    @property
    def qualified_name(self) -> str:
        return f"{self.module}.{self.name}" if self.module else self.name

    def param_names(self) -> set[str]:
        return {p for p, _ in self.params}


# ═══════════════════════════════════════════════════════════════════
# Pattern Matching — match axiom schema against goal
# ═══════════════════════════════════════════════════════════════════

class PatternMatcher:
    """One-way pattern matching from axiom schema terms to goal terms.

    Given an axiom schema with free variables {A, B, C} and a
    concrete goal, produces a substitution σ such that schema[σ] = goal,
    or None if no match exists.
    """

    def match_judgment(self, schema: Judgment, goal: Judgment,
                       param_names: set[str]) -> dict[str, SynTerm] | None:
        """Match a schema judgment against a goal.

        Returns substitution dict if match succeeds, None otherwise.
        """
        if schema.kind != goal.kind:
            return None

        subst: dict[str, SynTerm] = {}

        if schema.kind == JudgmentKind.EQUAL:
            if schema.left is None or schema.right is None:
                return None
            if goal.left is None or goal.right is None:
                return None
            s1 = self.match_term(schema.left, goal.left, param_names, subst)
            if s1 is None:
                return None
            s2 = self.match_term(schema.right, goal.right, param_names, s1)
            return s2

        elif schema.kind == JudgmentKind.TYPE_CHECK:
            if schema.term is not None and goal.term is not None:
                return self.match_term(schema.term, goal.term, param_names, subst)
            return subst

        # For other judgment kinds, succeed if kinds match
        return subst

    def match_term(self, schema: SynTerm, goal: SynTerm,
                   param_names: set[str],
                   subst: dict[str, SynTerm]) -> dict[str, SynTerm] | None:
        """Match a schema term against a goal term.

        Schema variables (names in ``param_names``) match anything
        and bind in the substitution. Everything else must match
        structurally.
        """
        # Schema variable — matches anything
        if isinstance(schema, Var) and schema.name in param_names:
            if schema.name in subst:
                # Already bound — check consistency
                if not self.terms_equal(subst[schema.name], goal):
                    return None
            else:
                subst = {**subst, schema.name: goal}
            return subst

        # Both are Op — must match name and module
        if isinstance(schema, Op) and isinstance(goal, Op):
            if schema.name == goal.name and schema.module == goal.module:
                return subst
            return None

        # Both are OpCall — match op then args
        if isinstance(schema, OpCall) and isinstance(goal, OpCall):
            if not (isinstance(schema.op, Op) and isinstance(goal.op, Op)):
                return None
            if schema.op.name != goal.op.name or schema.op.module != goal.op.module:
                return None
            if len(schema.args) != len(goal.args):
                return None
            for sa, ga in zip(schema.args, goal.args):
                subst_result = self.match_term(sa, ga, param_names, subst)
                if subst_result is None:
                    return None
                subst = subst_result
            return subst

        # Both are Var (not schema variables) — names must match
        if isinstance(schema, Var) and isinstance(goal, Var):
            if schema.name == goal.name:
                return subst
            return None

        # Both are Literal — values must match
        if isinstance(schema, Literal) and isinstance(goal, Literal):
            if schema.value == goal.value:
                return subst
            return None

        # Both are App — match func and arg
        if isinstance(schema, App) and isinstance(goal, App):
            s1 = self.match_term(schema.func, goal.func, param_names, subst)
            if s1 is None:
                return None
            return self.match_term(schema.arg, goal.arg, param_names, s1)

        # Both are PyCall — match func and all args
        if isinstance(schema, PyCall) and isinstance(goal, PyCall):
            s1 = self.match_term(schema.func, goal.func, param_names, subst)
            if s1 is None:
                return None
            if len(schema.args) != len(goal.args):
                return None
            for sa, ga in zip(schema.args, goal.args):
                s1 = self.match_term(sa, ga, param_names, s1)
                if s1 is None:
                    return None
            return s1

        # Both are GetAttr — match obj and attr name
        if isinstance(schema, GetAttr) and isinstance(goal, GetAttr):
            if schema.attr != goal.attr:
                return None
            return self.match_term(schema.obj, goal.obj, param_names, subst)

        # Both are GetItem — match obj and key
        if isinstance(schema, GetItem) and isinstance(goal, GetItem):
            s1 = self.match_term(schema.obj, goal.obj, param_names, subst)
            if s1 is None:
                return None
            return self.match_term(schema.key, goal.key, param_names, s1)

        # Both are Lam — match body (treating param as non-schema)
        if isinstance(schema, Lam) and isinstance(goal, Lam):
            if schema.param != goal.param:
                return None
            return self.match_term(schema.body, goal.body,
                                   param_names - {schema.param}, subst)

        # Both are Pair
        if isinstance(schema, Pair) and isinstance(goal, Pair):
            s1 = self.match_term(schema.fst, goal.fst, param_names, subst)
            if s1 is None:
                return None
            return self.match_term(schema.snd, goal.snd, param_names, s1)

        # Both are Fst
        if isinstance(schema, Fst) and isinstance(goal, Fst):
            return self.match_term(schema.pair, goal.pair, param_names, subst)

        # Both are Snd
        if isinstance(schema, Snd) and isinstance(goal, Snd):
            return self.match_term(schema.pair, goal.pair, param_names, subst)

        # Both are LetIn
        if isinstance(schema, LetIn) and isinstance(goal, LetIn):
            if schema.var_name != goal.var_name:
                return None
            s1 = self.match_term(schema.value, goal.value, param_names, subst)
            if s1 is None:
                return None
            return self.match_term(schema.body, goal.body,
                                   param_names - {schema.var_name}, s1)

        # Both are IfThenElse
        if isinstance(schema, IfThenElse) and isinstance(goal, IfThenElse):
            s1 = self.match_term(schema.cond, goal.cond, param_names, subst)
            if s1 is None:
                return None
            s2 = self.match_term(schema.then_branch, goal.then_branch, param_names, s1)
            if s2 is None:
                return None
            return self.match_term(schema.else_branch, goal.else_branch, param_names, s2)

        # Both are PathAbs
        if isinstance(schema, PathAbs) and isinstance(goal, PathAbs):
            return self.match_term(schema.body, goal.body,
                                   param_names - {schema.ivar}, subst)

        # Both are PathApp
        if isinstance(schema, PathApp) and isinstance(goal, PathApp):
            s1 = self.match_term(schema.path, goal.path, param_names, subst)
            if s1 is None:
                return None
            return self.match_term(schema.arg, goal.arg, param_names, s1)

        # Cross-form: OpCall schema vs PyCall goal (normalization bridge)
        if isinstance(schema, OpCall) and isinstance(goal, PyCall):
            if isinstance(goal.func, Var):
                if schema.op.name != goal.func.name:
                    return None
                if len(schema.args) != len(goal.args):
                    return None
                for sa, ga in zip(schema.args, goal.args):
                    subst_result = self.match_term(sa, ga, param_names, subst)
                    if subst_result is None:
                        return None
                    subst = subst_result
                return subst

        # No match
        return None

    def terms_equal(self, a: SynTerm, b: SynTerm) -> bool:
        """Structural equality check for terms (used for substitution consistency)."""
        if type(a) is type(b):
            if isinstance(a, Var) and isinstance(b, Var):
                return a.name == b.name
            if isinstance(a, Op) and isinstance(b, Op):
                return a.name == b.name and a.module == b.module
            if isinstance(a, Literal) and isinstance(b, Literal):
                return a.value == b.value
            if isinstance(a, OpCall) and isinstance(b, OpCall):
                if not self.terms_equal(a.op, b.op):
                    return False
                if len(a.args) != len(b.args):
                    return False
                return all(self.terms_equal(x, y)
                           for x, y in zip(a.args, b.args))
            if isinstance(a, App) and isinstance(b, App):
                return (self.terms_equal(a.func, b.func) and
                        self.terms_equal(a.arg, b.arg))
            if isinstance(a, PyCall) and isinstance(b, PyCall):
                if not self.terms_equal(a.func, b.func):
                    return False
                if len(a.args) != len(b.args):
                    return False
                return all(self.terms_equal(x, y)
                           for x, y in zip(a.args, b.args))
            if isinstance(a, Lam) and isinstance(b, Lam):
                return a.param == b.param and self.terms_equal(a.body, b.body)
            if isinstance(a, GetAttr) and isinstance(b, GetAttr):
                return a.attr == b.attr and self.terms_equal(a.obj, b.obj)
            if isinstance(a, GetItem) and isinstance(b, GetItem):
                return (self.terms_equal(a.obj, b.obj) and
                        self.terms_equal(a.key, b.key))
            if isinstance(a, Pair) and isinstance(b, Pair):
                return (self.terms_equal(a.fst, b.fst) and
                        self.terms_equal(a.snd, b.snd))
            if isinstance(a, Fst) and isinstance(b, Fst):
                return self.terms_equal(a.pair, b.pair)
            if isinstance(a, Snd) and isinstance(b, Snd):
                return self.terms_equal(a.pair, b.pair)
            if isinstance(a, IfThenElse) and isinstance(b, IfThenElse):
                return (self.terms_equal(a.cond, b.cond) and
                        self.terms_equal(a.then_branch, b.then_branch) and
                        self.terms_equal(a.else_branch, b.else_branch))
            if isinstance(a, LetIn) and isinstance(b, LetIn):
                return (a.var_name == b.var_name and
                        self.terms_equal(a.value, b.value) and
                        self.terms_equal(a.body, b.body))
            if isinstance(a, PathAbs) and isinstance(b, PathAbs):
                return (a.ivar == b.ivar and
                        self.terms_equal(a.body, b.body))
            if isinstance(a, PathApp) and isinstance(b, PathApp):
                return (self.terms_equal(a.path, b.path) and
                        self.terms_equal(a.arg, b.arg))
        return False


# ═══════════════════════════════════════════════════════════════════
# Canonical operation constructors
# ═══════════════════════════════════════════════════════════════════

# ── Arithmetic ────────────────────────────────────────────────────

def op_add(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__add__"), (a, b))

def op_sub(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__sub__"), (a, b))

def op_mul(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__mul__"), (a, b))

def op_truediv(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__truediv__"), (a, b))

def op_floordiv(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__floordiv__"), (a, b))

def op_mod(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__mod__"), (a, b))

def op_pow(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__pow__"), (a, b))

def op_neg(a: SynTerm) -> OpCall:
    return OpCall(Op("__neg__"), (a,))

def op_abs(a: SynTerm) -> OpCall:
    return OpCall(Op("__abs__"), (a,))

# ── Comparison ────────────────────────────────────────────────────

def op_eq(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__eq__"), (a, b))

def op_ne(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__ne__"), (a, b))

def op_lt(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__lt__"), (a, b))

def op_le(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__le__"), (a, b))

def op_gt(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__gt__"), (a, b))

def op_ge(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__ge__"), (a, b))

# ── Boolean ───────────────────────────────────────────────────────

def op_and(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__and__"), (a, b))

def op_or(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("__or__"), (a, b))

def op_not(a: SynTerm) -> OpCall:
    return OpCall(Op("__not__"), (a,))

# ── Collection operations ────────────────────────────────────────

def op_len(a: SynTerm) -> OpCall:
    return OpCall(Op("len"), (a,))

def op_contains(collection: SynTerm, item: SynTerm) -> OpCall:
    return OpCall(Op("__contains__"), (collection, item))

def op_getitem(obj: SynTerm, key: SynTerm) -> OpCall:
    return OpCall(Op("__getitem__"), (obj, key))

def op_setitem(obj: SynTerm, key: SynTerm, val: SynTerm) -> OpCall:
    return OpCall(Op("__setitem__"), (obj, key, val))

def op_delitem(obj: SynTerm, key: SynTerm) -> OpCall:
    return OpCall(Op("__delitem__"), (obj, key))

def op_iter(obj: SynTerm) -> OpCall:
    return OpCall(Op("__iter__"), (obj,))

def op_next(iterator: SynTerm) -> OpCall:
    return OpCall(Op("__next__"), (iterator,))

def op_append(lst: SynTerm, item: SynTerm) -> OpCall:
    return OpCall(Op("list.append"), (lst, item))

def op_extend(lst: SynTerm, items: SynTerm) -> OpCall:
    return OpCall(Op("list.extend"), (lst, items))

def op_pop(lst: SynTerm) -> OpCall:
    return OpCall(Op("list.pop"), (lst,))

def op_sort(lst: SynTerm) -> OpCall:
    return OpCall(Op("list.sort"), (lst,))

def op_sorted(lst: SynTerm) -> OpCall:
    return OpCall(Op("sorted"), (lst,))

def op_reversed(lst: SynTerm) -> OpCall:
    return OpCall(Op("reversed"), (lst,))

def op_dict_get(d: SynTerm, key: SynTerm, default: SynTerm | None = None) -> OpCall:
    args = (d, key, default) if default else (d, key)
    return OpCall(Op("dict.get"), args)

def op_dict_keys(d: SynTerm) -> OpCall:
    return OpCall(Op("dict.keys"), (d,))

def op_dict_values(d: SynTerm) -> OpCall:
    return OpCall(Op("dict.values"), (d,))

def op_dict_items(d: SynTerm) -> OpCall:
    return OpCall(Op("dict.items"), (d,))

def op_dict_update(d: SynTerm, other: SynTerm) -> OpCall:
    return OpCall(Op("dict.update"), (d, other))

def op_set_add(s: SynTerm, item: SynTerm) -> OpCall:
    return OpCall(Op("set.add"), (s, item))

def op_set_union(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("set.union"), (a, b))

def op_set_intersection(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("set.intersection"), (a, b))

# ── String operations ────────────────────────────────────────────

def op_str_concat(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("str.__add__"), (a, b))

def op_str_format(template: SynTerm, *args: SynTerm) -> OpCall:
    return OpCall(Op("str.format"), (template, *args))

def op_str_join(sep: SynTerm, items: SynTerm) -> OpCall:
    return OpCall(Op("str.join"), (sep, items))

def op_str_split(s: SynTerm, sep: SynTerm | None = None) -> OpCall:
    args = (s, sep) if sep else (s,)
    return OpCall(Op("str.split"), args)

def op_str_startswith(s: SynTerm, prefix: SynTerm) -> OpCall:
    return OpCall(Op("str.startswith"), (s, prefix))

def op_str_endswith(s: SynTerm, suffix: SynTerm) -> OpCall:
    return OpCall(Op("str.endswith"), (s, suffix))

# ── Type operations ──────────────────────────────────────────────

def op_isinstance(obj: SynTerm, ty: SynTerm) -> OpCall:
    return OpCall(Op("isinstance"), (obj, ty))

def op_issubclass(cls: SynTerm, parent: SynTerm) -> OpCall:
    return OpCall(Op("issubclass"), (cls, parent))

def op_type(obj: SynTerm) -> OpCall:
    return OpCall(Op("type"), (obj,))

def op_hasattr(obj: SynTerm, name: SynTerm) -> OpCall:
    return OpCall(Op("hasattr"), (obj, name))

def op_getattr_op(obj: SynTerm, name: SynTerm) -> OpCall:
    return OpCall(Op("getattr"), (obj, name))

def op_setattr(obj: SynTerm, name: SynTerm, val: SynTerm) -> OpCall:
    return OpCall(Op("setattr"), (obj, name, val))

def op_delattr(obj: SynTerm, name: SynTerm) -> OpCall:
    return OpCall(Op("delattr"), (obj, name))

# ── Callable operations ─────────────────────────────────────────

def op_call(func: SynTerm, *args: SynTerm) -> OpCall:
    return OpCall(Op("__call__"), (func, *args))

def op_apply(func: SynTerm, args: SynTerm, kwargs: SynTerm | None = None) -> OpCall:
    a = (func, args, kwargs) if kwargs else (func, args)
    return OpCall(Op("apply"), a)

# ── MRO / dispatch ───────────────────────────────────────────────

def op_mro(cls: SynTerm) -> OpCall:
    return OpCall(Op("__mro__"), (cls,))

def op_super(cls: SynTerm, obj: SynTerm) -> OpCall:
    return OpCall(Op("super"), (cls, obj))

def op_dispatch(obj: SynTerm, method: SynTerm) -> OpCall:
    return OpCall(Op("__dispatch__"), (obj, method))

# ── Context manager ──────────────────────────────────────────────

def op_enter(mgr: SynTerm) -> OpCall:
    return OpCall(Op("__enter__"), (mgr,))

def op_exit(mgr: SynTerm, exc_type: SynTerm, exc_val: SynTerm,
            exc_tb: SynTerm) -> OpCall:
    return OpCall(Op("__exit__"), (mgr, exc_type, exc_val, exc_tb))

# ── Generator / iterator ────────────────────────────────────────

def op_send(gen: SynTerm, value: SynTerm) -> OpCall:
    return OpCall(Op("generator.send"), (gen, value))

def op_throw(gen: SynTerm, exc: SynTerm) -> OpCall:
    return OpCall(Op("generator.throw"), (gen, exc))

def op_close(gen: SynTerm) -> OpCall:
    return OpCall(Op("generator.close"), (gen,))

def op_yield(value: SynTerm) -> OpCall:
    return OpCall(Op("yield"), (value,))

def op_yield_from(iterable: SynTerm) -> OpCall:
    return OpCall(Op("yield_from"), (iterable,))

# ── Exception operations ────────────────────────────────────────

def op_raise(exc: SynTerm) -> OpCall:
    return OpCall(Op("raise"), (exc,))

def op_raise_from(exc: SynTerm, cause: SynTerm) -> OpCall:
    return OpCall(Op("raise_from"), (exc, cause))

# ── Async operations ────────────────────────────────────────────

def op_await(awaitable: SynTerm) -> OpCall:
    return OpCall(Op("__await__"), (awaitable,))

def op_aiter(obj: SynTerm) -> OpCall:
    return OpCall(Op("__aiter__"), (obj,))

def op_anext(aiterator: SynTerm) -> OpCall:
    return OpCall(Op("__anext__"), (aiterator,))

def op_aenter(mgr: SynTerm) -> OpCall:
    return OpCall(Op("__aenter__"), (mgr,))

def op_aexit(mgr: SynTerm, exc_type: SynTerm, exc_val: SynTerm,
             exc_tb: SynTerm) -> OpCall:
    return OpCall(Op("__aexit__"), (mgr, exc_type, exc_val, exc_tb))

# ── Descriptor protocol ─────────────────────────────────────────

def op_desc_get(desc: SynTerm, obj: SynTerm, objtype: SynTerm) -> OpCall:
    return OpCall(Op("__get__"), (desc, obj, objtype))

def op_desc_set(desc: SynTerm, obj: SynTerm, value: SynTerm) -> OpCall:
    return OpCall(Op("__set__"), (desc, obj, value))

def op_desc_delete(desc: SynTerm, obj: SynTerm) -> OpCall:
    return OpCall(Op("__delete__"), (desc, obj))

# ── Numeric special methods ──────────────────────────────────────

def op_int(a: SynTerm) -> OpCall:
    return OpCall(Op("__int__"), (a,))

def op_float(a: SynTerm) -> OpCall:
    return OpCall(Op("__float__"), (a,))

def op_complex(a: SynTerm) -> OpCall:
    return OpCall(Op("__complex__"), (a,))

def op_round(a: SynTerm, ndigits: SynTerm | None = None) -> OpCall:
    args = (a, ndigits) if ndigits else (a,)
    return OpCall(Op("__round__"), args)

def op_hash(a: SynTerm) -> OpCall:
    return OpCall(Op("__hash__"), (a,))

def op_bool(a: SynTerm) -> OpCall:
    return OpCall(Op("__bool__"), (a,))

def op_repr(a: SynTerm) -> OpCall:
    return OpCall(Op("__repr__"), (a,))

def op_str(a: SynTerm) -> OpCall:
    return OpCall(Op("__str__"), (a,))

# ── Library-specific: SymPy ──────────────────────────────────────

def op_sympy_expand(expr: SynTerm) -> OpCall:
    return OpCall(Op("expand", "sympy"), (expr,))

def op_sympy_simplify(expr: SynTerm) -> OpCall:
    return OpCall(Op("simplify", "sympy"), (expr,))

def op_sympy_factor(expr: SynTerm) -> OpCall:
    return OpCall(Op("factor", "sympy"), (expr,))

def op_sympy_diff(expr: SynTerm, var: SynTerm) -> OpCall:
    return OpCall(Op("diff", "sympy"), (expr, var))

def op_sympy_integrate(expr: SynTerm, var: SynTerm) -> OpCall:
    return OpCall(Op("integrate", "sympy"), (expr, var))

def op_sympy_solve(eq: SynTerm, var: SynTerm) -> OpCall:
    return OpCall(Op("solve", "sympy"), (eq, var))

def op_sympy_limit(expr: SynTerm, var: SynTerm, point: SynTerm) -> OpCall:
    return OpCall(Op("limit", "sympy"), (expr, var, point))

# ── Library-specific: NumPy ──────────────────────────────────────

def op_np_dot(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("dot", "numpy"), (a, b))

def op_np_transpose(a: SynTerm) -> OpCall:
    return OpCall(Op("transpose", "numpy"), (a,))

def op_np_reshape(a: SynTerm, shape: SynTerm) -> OpCall:
    return OpCall(Op("reshape", "numpy"), (a, shape))

def op_np_sum(a: SynTerm) -> OpCall:
    return OpCall(Op("sum", "numpy"), (a,))

# ── Library-specific: PyTorch ────────────────────────────────────

def op_torch_matmul(a: SynTerm, b: SynTerm) -> OpCall:
    return OpCall(Op("matmul", "torch"), (a, b))

def op_torch_relu(a: SynTerm) -> OpCall:
    return OpCall(Op("relu", "torch"), (a,))

def op_torch_softmax(a: SynTerm, dim: SynTerm) -> OpCall:
    return OpCall(Op("softmax", "torch"), (a, dim))

def op_torch_linear(weight: SynTerm, bias: SynTerm, x: SynTerm) -> OpCall:
    return OpCall(Op("linear", "torch"), (weight, bias, x))

def op_torch_grad(output: SynTerm, input: SynTerm) -> OpCall:
    return OpCall(Op("grad", "torch"), (output, input))

def op_torch_sum(a: SynTerm, dim: SynTerm | None = None) -> OpCall:
    args = (a, dim) if dim else (a,)
    return OpCall(Op("sum", "torch"), args)

# ── Fold / reduce (for loops, comprehensions) ────────────────────

def op_fold(func: SynTerm, init: SynTerm, collection: SynTerm) -> OpCall:
    return OpCall(Op("fold"), (func, init, collection))

def op_map(func: SynTerm, collection: SynTerm) -> OpCall:
    return OpCall(Op("map"), (func, collection))

def op_filter(pred: SynTerm, collection: SynTerm) -> OpCall:
    return OpCall(Op("filter"), (pred, collection))

def op_reduce(func: SynTerm, collection: SynTerm, init: SynTerm | None = None) -> OpCall:
    args = (func, collection, init) if init else (func, collection)
    return OpCall(Op("reduce"), args)

# ── Comprehension ────────────────────────────────────────────────

def op_listcomp(body: SynTerm, var: str, iterable: SynTerm,
                cond: SynTerm | None = None) -> OpCall:
    """[body for var in iterable if cond]"""
    parts: list[SynTerm] = [body, Var(var), iterable]
    if cond:
        parts.append(cond)
    return OpCall(Op("listcomp"), tuple(parts))

def op_dictcomp(key: SynTerm, val: SynTerm, var: str,
                iterable: SynTerm) -> OpCall:
    return OpCall(Op("dictcomp"), (key, val, Var(var), iterable))

def op_setcomp(body: SynTerm, var: str, iterable: SynTerm) -> OpCall:
    return OpCall(Op("setcomp"), (body, Var(var), iterable))

def op_genexpr(body: SynTerm, var: str, iterable: SynTerm) -> OpCall:
    return OpCall(Op("genexpr"), (body, Var(var), iterable))


# ═══════════════════════════════════════════════════════════════════
# Helper: build formal equality judgment
# ═══════════════════════════════════════════════════════════════════

def formal_eq(ctx: Context, left: SynTerm, right: SynTerm,
              type_: SynType = PyObjType()) -> Judgment:
    """Build a formal equality judgment from actual terms."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=left,
        right=right,
        type_=type_,
    )


def formal_check(ctx: Context, term: SynTerm,
                 type_: SynType) -> Judgment:
    """Build a formal type-checking judgment."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=term,
        type_=type_,
    )


def formal_subtype(ctx: Context, sub: SynType,
                   sup: SynType) -> Judgment:
    """Build a formal subtype judgment (using types wrapped as Literal)."""
    return Judgment(
        kind=JudgmentKind.SUBTYPE,
        context=ctx,
        left=Literal(sub),
        right=Literal(sup),
    )


# ═══════════════════════════════════════════════════════════════════
# Operation name normalization
# ═══════════════════════════════════════════════════════════════════

# Maps frontend aliases to canonical Op names
_OP_ALIASES: dict[str, str] = {
    "+": "__add__", "-": "__sub__", "*": "__mul__",
    "/": "__truediv__", "//": "__floordiv__", "%": "__mod__",
    "**": "__pow__", "@": "__matmul__",
    "==": "__eq__", "!=": "__ne__",
    "<": "__lt__", "<=": "__le__", ">": "__gt__", ">=": "__ge__",
    "in": "__contains__", "not": "__not__",
    "and": "__and__", "or": "__or__",
    "[]": "__getitem__", "[]=": "__setitem__",
    "()": "__call__",
    "len": "len", "abs": "__abs__", "hash": "__hash__",
    "bool": "__bool__", "int": "__int__", "float": "__float__",
    "str": "__str__", "repr": "__repr__",
    "iter": "__iter__", "next": "__next__",
    "enter": "__enter__", "exit": "__exit__",
    "matmul": "__matmul__",
}


def normalize_op_name(name: str) -> str:
    """Normalize a frontend operation name to its canonical form."""
    return _OP_ALIASES.get(name, name)


def canonical_op(name: str, module: str = "") -> Op:
    """Create an Op with a normalized name."""
    return Op(name=normalize_op_name(name), module=module)
