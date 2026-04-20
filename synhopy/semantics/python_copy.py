"""
SynHoPy Formal Semantics — Copy Semantics, Object Identity, and Aliasing
=========================================================================

Formal axioms for Python's copy model, object identity (``is`` vs ``==``),
aliasing analysis, serialization roundtrips, weak references, and the
mutable-default-argument pitfall.

Monograph references
--------------------
- Ch N+1: Copy Semantics, Object Identity, and Aliasing
  - Object identity as a *fiber* over the heap — ``id`` maps to heap
    locations, ``is`` checks whether two names share a fiber.
  - The heap H : Loc → PyObj is a dependent context; every Python
    variable is a *reference* (location).
  - Alias partitions are flow-sensitive: assignment ``y = x`` merges
    the alias classes of *x* and *y*, while ``y = copy.copy(x)``
    forks them.
  - Copy levels: binding copy, shallow copy (``copy.copy``), deep copy
    (``copy.deepcopy``), each with formal isolation axioms.
  - Pickle / JSON roundtrip correctness as path equalities.
  - ``weakref.ref`` and the liveness axiom.
  - Mutable default arguments: detection as a type-level warning.

Architecture
------------
ObjectIdentitySemantics  — ``is`` vs ``==``, ``id()``
HeapSemantics            — abstract heap model (read / write / alloc)
AliasingSemantics        — flow-sensitive alias partitions
CopySemantics            — shallow / deep copy axioms
SerializationSemantics   — pickle / json roundtrip
WeakRefSemantics         — ``weakref.ref``, ``WeakValueDictionary``
MutableDefaultSemantics  — detection of mutable default argument bugs

``all_copy_axioms()`` collects every axiom for use by the proof kernel.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Any

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyStrType, PyBoolType, PyNoneType,
    PyListType, PyDictType, PyClassType,
    RefinementType, UnionType, OptionalType,
    Var, Literal,
    Spec, SpecKind,
)
from synhopy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, formal_check,
    op_eq, op_isinstance, op_type,
    op_len, op_getitem,
)


# ═══════════════════════════════════════════════════════════════════
# Local Op constructors — operations specific to this module
# ═══════════════════════════════════════════════════════════════════

def op_is(a: SynTerm, b: SynTerm) -> OpCall:
    """Python ``is`` operator (identity check)."""
    return OpCall(Op("is", "builtins"), (a, b))


def op_is_not(a: SynTerm, b: SynTerm) -> OpCall:
    """Python ``is not`` operator."""
    return OpCall(Op("is_not", "builtins"), (a, b))


def op_id(a: SynTerm) -> OpCall:
    """Python ``id()`` builtin."""
    return OpCall(Op("id", "builtins"), (a,))


def op_copy(a: SynTerm) -> OpCall:
    """``copy.copy(a)``."""
    return OpCall(Op("copy", "copy"), (a,))


def op_deepcopy(a: SynTerm) -> OpCall:
    """``copy.deepcopy(a)``."""
    return OpCall(Op("deepcopy", "copy"), (a,))


def op_pickle_dumps(a: SynTerm) -> OpCall:
    """``pickle.dumps(a)``."""
    return OpCall(Op("dumps", "pickle"), (a,))


def op_pickle_loads(a: SynTerm) -> OpCall:
    """``pickle.loads(a)``."""
    return OpCall(Op("loads", "pickle"), (a,))


def op_json_dumps(a: SynTerm) -> OpCall:
    """``json.dumps(a)``."""
    return OpCall(Op("dumps", "json"), (a,))


def op_json_loads(a: SynTerm) -> OpCall:
    """``json.loads(a)``."""
    return OpCall(Op("loads", "json"), (a,))


def op_weakref(a: SynTerm) -> OpCall:
    """``weakref.ref(a)``."""
    return OpCall(Op("ref", "weakref"), (a,))


def op_weakref_deref(a: SynTerm) -> OpCall:
    """``weakref.ref(x)()`` — dereference a weak reference."""
    return OpCall(Op("deref", "weakref"), (a,))


def op_heap_read(heap: SynTerm, loc: SynTerm) -> OpCall:
    """Read a location from the heap: ``read(H, loc)``."""
    return OpCall(Op("read", "heap"), (heap, loc))


def op_heap_write(heap: SynTerm, loc: SynTerm, val: SynTerm) -> OpCall:
    """Write to a location on the heap: ``write(H, loc, v)``."""
    return OpCall(Op("write", "heap"), (heap, loc, val))


def op_heap_alloc(heap: SynTerm, val: SynTerm) -> OpCall:
    """Allocate a fresh location on the heap: ``alloc(H, v)``."""
    return OpCall(Op("alloc", "heap"), (heap, val))


def op_heap_dom(heap: SynTerm) -> OpCall:
    """Domain of the heap: ``dom(H)``."""
    return OpCall(Op("dom", "heap"), (heap,))


def op_contains(collection: SynTerm, item: SynTerm) -> OpCall:
    """``item in collection``."""
    return OpCall(Op("__contains__"), (collection, item))


def op_not(a: SynTerm) -> OpCall:
    """``not a``."""
    return OpCall(Op("__not__"), (a,))


def op_append(lst: SynTerm, item: SynTerm) -> OpCall:
    """``lst.append(item)``."""
    return OpCall(Op("list.append"), (lst, item))


def op_ne(a: SynTerm, b: SynTerm) -> OpCall:
    """``a != b``."""
    return OpCall(Op("__ne__"), (a, b))


def op_and(a: SynTerm, b: SynTerm) -> OpCall:
    """``a and b``."""
    return OpCall(Op("__and__"), (a, b))


def op_implies(a: SynTerm, b: SynTerm) -> OpCall:
    """Logical implication: ``a → b``."""
    return OpCall(Op("implies", "logic"), (a, b))


def op_isolated(a: SynTerm, b: SynTerm) -> OpCall:
    """Heap isolation: mutating *a* cannot affect *b* and vice-versa."""
    return OpCall(Op("isolated", "heap"), (a, b))


def op_has_strong_ref(a: SynTerm) -> OpCall:
    """``has_strong_ref(a)`` — at least one strong reference exists."""
    return OpCall(Op("has_strong_ref", "gc"), (a,))


def op_mutated(a: SynTerm) -> OpCall:
    """``mutated(a)`` — object was mutated in the current step."""
    return OpCall(Op("mutated", "heap"), (a,))


def op_sees_mutation(a: SynTerm, b: SynTerm) -> OpCall:
    """``sees_mutation(a, b)`` — mutation through *b* is visible via *a*."""
    return OpCall(Op("sees_mutation", "heap"), (a, b))


def op_reduce(a: SynTerm) -> OpCall:
    """``a.__reduce__()``."""
    return OpCall(Op("__reduce__"), (a,))


def op_getstate(a: SynTerm) -> OpCall:
    """``a.__getstate__()``."""
    return OpCall(Op("__getstate__"), (a,))


def op_setstate(a: SynTerm, state: SynTerm) -> OpCall:
    """``a.__setstate__(state)``."""
    return OpCall(Op("__setstate__"), (a, state))


def op_fst(pair: SynTerm) -> OpCall:
    """First projection of a pair (used for alloc return)."""
    return OpCall(Op("fst", "pair"), (pair,))


def op_snd(pair: SynTerm) -> OpCall:
    """Second projection of a pair (used for alloc return)."""
    return OpCall(Op("snd", "pair"), (pair,))


# ── shorthand helpers ─────────────────────────────────────────────

_E = Context()  # empty context

def _v(name: str) -> Var:
    return Var(name)

def _lit(value: object) -> Literal:
    return Literal(value=value)

def _bool_lit(b: bool) -> Literal:
    return Literal(value=b)

def _int_lit(n: int) -> Literal:
    return Literal(value=n)

def _none_lit() -> Literal:
    return Literal(value=None)

_MODULE = "python.copy"


# ═══════════════════════════════════════════════════════════════════
# 1. Object Identity Semantics
# ═══════════════════════════════════════════════════════════════════

class ObjectIdentitySemantics:
    """Object identity as a distinct concept from equality.

    In Python: ``a is b`` checks identity (same object in memory),
    ``a == b`` checks equality (structural / value equality).
    Identity implies equality but not vice versa.

    Formally, ``id`` maps each Python object to a unique *heap location*.
    ``a is b`` ⟺ ``id(a) == id(b)`` — they share the same fiber
    over the heap.
    """

    def identity_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for ``is``, ``id()``, and their interaction with ``==``.

        Covers:
        - identity implies equality
        - reflexivity, symmetry, transitivity of ``is``
        - ``id`` characterises identity
        - immutable singletons (``None``, ``True``, ``False``)
        - small-int caching (CPython: -5 … 256)
        - string interning (short identifier-like strings)
        """
        a, b, c = _v("a"), _v("b"), _v("c")
        axioms: list[FormalAxiomEntry] = []

        # identity implies equality: (a is b) → (a == b)
        axioms.append(FormalAxiomEntry(
            name="identity_implies_equality",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(op_is(a, b), op_eq(a, b)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="(a is b) → (a == b)",
        ))

        # reflexivity: a is a
        axioms.append(FormalAxiomEntry(
            name="identity_reflexive",
            module=_MODULE,
            params=[("a", PyObjType())],
            conclusion=formal_eq(
                _E, op_is(a, a), _bool_lit(True), PyBoolType(),
            ),
            description="a is a  (reflexivity)",
        ))

        # symmetry: (a is b) → (b is a)
        axioms.append(FormalAxiomEntry(
            name="identity_symmetric",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(op_is(a, b), op_is(b, a)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="(a is b) → (b is a)  (symmetry)",
        ))

        # transitivity: (a is b) ∧ (b is c) → (a is c)
        axioms.append(FormalAxiomEntry(
            name="identity_transitive",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType()), ("c", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_and(op_is(a, b), op_is(b, c)),
                    op_is(a, c),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="(a is b) ∧ (b is c) → (a is c)  (transitivity)",
        ))

        # id characterises identity: id(a) == id(b) ↔ (a is b)
        axioms.append(FormalAxiomEntry(
            name="id_characterises_identity",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_id(a), op_id(b)),
                op_is(a, b),
                PyBoolType(),
            ),
            description="id(a) == id(b) ↔ (a is b)",
        ))

        # None is a singleton
        axioms.append(FormalAxiomEntry(
            name="none_singleton",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_is(_none_lit(), _none_lit()),
                _bool_lit(True), PyBoolType(),
            ),
            description="None is None  (singleton)",
        ))

        # True is a singleton
        axioms.append(FormalAxiomEntry(
            name="true_singleton",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_is(_bool_lit(True), _bool_lit(True)),
                _bool_lit(True), PyBoolType(),
            ),
            description="True is True  (singleton)",
        ))

        # False is a singleton
        axioms.append(FormalAxiomEntry(
            name="false_singleton",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_is(_bool_lit(False), _bool_lit(False)),
                _bool_lit(True), PyBoolType(),
            ),
            description="False is False  (singleton)",
        ))

        # Small-int caching: -5 <= n <= 256 ⇒ int(n) is int(n)
        axioms.append(FormalAxiomEntry(
            name="small_int_caching",
            module=_MODULE,
            params=[("a", RefinementType(
                base_type=PyIntType(), var_name="n",
                predicate="-5 <= n <= 256",
            ))],
            conclusion=formal_eq(
                _E, op_is(a, a), _bool_lit(True), PyBoolType(),
            ),
            description="For -5 <= n <= 256: int(n) is int(n)  (CPython cache)",
        ))

        # String interning: short identifier-like strings may be interned
        axioms.append(FormalAxiomEntry(
            name="string_interning",
            module=_MODULE,
            params=[("a", RefinementType(
                base_type=PyStrType(), var_name="s",
                predicate="s.isidentifier() and len(s) <= 256",
            ))],
            conclusion=formal_eq(
                _E, op_is(a, a), _bool_lit(True), PyBoolType(),
            ),
            description="Short identifier-like strings may be interned",
        ))

        # is not is the negation of is
        axioms.append(FormalAxiomEntry(
            name="is_not_negation",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_is_not(a, b),
                op_not(op_is(a, b)),
                PyBoolType(),
            ),
            description="(a is not b) ↔ not (a is b)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 2. Heap Semantics
# ═══════════════════════════════════════════════════════════════════

class HeapSemantics:
    """The Python heap as a dependent context.

    Every Python variable is a *reference* — a location ``loc`` in the
    heap ``H : Loc → PyObj``.  Mutation modifies the heap, not the
    variable.

    We model a simplified abstract heap with three primitives:
    - ``read(H, loc)`` — read a value from the heap
    - ``write(H, loc, v)`` — write a value, returning new heap H'
    - ``alloc(H, v)`` — allocate fresh location, returning (H', loc)

    These satisfy standard frame conditions from separation logic.
    """

    def heap_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for the abstract heap model.

        Frame conditions + allocation freshness.
        """
        h = _v("h")
        loc, loc1, loc2 = _v("loc"), _v("loc1"), _v("loc2")
        v = _v("v")
        axioms: list[FormalAxiomEntry] = []

        # read-after-write, same location
        axioms.append(FormalAxiomEntry(
            name="heap_read_after_write_same",
            module=_MODULE,
            params=[("h", PyObjType()), ("loc", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_heap_read(op_heap_write(h, loc, v), loc),
                v,
                PyObjType(),
            ),
            description="read(write(h, loc, v), loc) == v",
        ))

        # frame: read-after-write, different location
        axioms.append(FormalAxiomEntry(
            name="heap_frame",
            module=_MODULE,
            params=[
                ("h", PyObjType()), ("loc1", PyObjType()),
                ("loc2", PyObjType()), ("v", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_heap_read(op_heap_write(h, loc1, v), loc2),
                op_heap_read(h, loc2),
                PyObjType(),
            ),
            description="read(write(h, l1, v), l2) == read(h, l2)  (l1 ≠ l2)",
        ))

        # alloc returns value at fresh location
        axioms.append(FormalAxiomEntry(
            name="heap_alloc_read",
            module=_MODULE,
            params=[("h", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_heap_read(
                    op_fst(op_heap_alloc(h, v)),
                    op_snd(op_heap_alloc(h, v)),
                ),
                v,
                PyObjType(),
            ),
            description="let (h', loc) = alloc(h, v) in read(h', loc) == v",
        ))

        # alloc returns fresh location: loc ∉ dom(h)
        axioms.append(FormalAxiomEntry(
            name="heap_alloc_fresh",
            module=_MODULE,
            params=[("h", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_not(op_contains(
                    op_heap_dom(h),
                    op_snd(op_heap_alloc(h, v)),
                )),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="let (h', loc) = alloc(h, v) in loc ∉ dom(h)",
        ))

        # write is idempotent at same location: write(write(h, l, v1), l, v2) == write(h, l, v2)
        axioms.append(FormalAxiomEntry(
            name="heap_write_idempotent",
            module=_MODULE,
            params=[
                ("h", PyObjType()), ("loc", PyObjType()),
                ("v", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_heap_write(op_heap_write(h, loc, _v("v1")), loc, v),
                op_heap_write(h, loc, v),
                PyObjType(),
            ),
            description="write(write(h, l, v1), l, v2) == write(h, l, v2)",
        ))

        # write commutes at distinct locations
        axioms.append(FormalAxiomEntry(
            name="heap_write_commute",
            module=_MODULE,
            params=[
                ("h", PyObjType()), ("loc1", PyObjType()),
                ("loc2", PyObjType()), ("v", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_heap_write(op_heap_write(h, loc1, _v("v1")), loc2, v),
                op_heap_write(op_heap_write(h, loc2, v), loc1, _v("v1")),
                PyObjType(),
            ),
            description="write(write(h,l1,v1),l2,v2) == write(write(h,l2,v2),l1,v1)  (l1≠l2)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 3. Aliasing Semantics
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AliasPartition:
    """Flow-sensitive alias partition.

    Each partition class is a set of variable names that currently
    point to the same heap object.
    """
    classes: list[set[str]] = field(default_factory=list)

    def find_class(self, var: str) -> set[str] | None:
        """Return the alias class containing *var*, or ``None``."""
        for cls in self.classes:
            if var in cls:
                return cls
        return None

    def merge(self, a: str, b: str) -> None:
        """Merge the alias classes of *a* and *b* (assignment ``b = a``)."""
        cls_a = self.find_class(a)
        cls_b = self.find_class(b)
        if cls_a is None and cls_b is None:
            self.classes.append({a, b})
        elif cls_a is not None and cls_b is None:
            cls_a.add(b)
        elif cls_a is None and cls_b is not None:
            cls_b.add(a)
        elif cls_a is not cls_b and cls_a is not None and cls_b is not None:
            cls_a |= cls_b
            self.classes.remove(cls_b)

    def split(self, var: str) -> None:
        """Split *var* into its own alias class (copy / rebinding)."""
        cls = self.find_class(var)
        if cls is not None:
            cls.discard(var)
            if not cls:
                self.classes.remove(cls)
        self.classes.append({var})

    def are_aliases(self, a: str, b: str) -> bool:
        """Return ``True`` if *a* and *b* are in the same alias class."""
        cls = self.find_class(a)
        return cls is not None and b in cls


class AliasingSemantics:
    """Flow-sensitive alias analysis for Python.

    Maintains alias partitions: which variables point to the same heap
    object.  Assignment ``y = x`` creates an alias, while ``y = copy(x)``
    breaks it.
    """

    def alias_assignment(self, partition: AliasPartition,
                         var_from: str, var_to: str) -> AliasPartition:
        """``var_to = var_from`` — creates an alias.

        After this, ``var_to is var_from`` is ``True``.
        """
        partition.merge(var_from, var_to)
        return partition

    def alias_mutation(self, partition: AliasPartition,
                       var: str) -> list[str]:
        """Return all variables that see mutation through *var*.

        Mutation through one alias is visible through all aliases.
        """
        cls = partition.find_class(var)
        return sorted(cls) if cls else [var]

    def alias_copy(self, partition: AliasPartition,
                   var: str, depth: str = "shallow") -> AliasPartition:
        """Copy breaks the alias for *var*.

        After ``y = copy.copy(x)`` or ``y = copy.deepcopy(x)``,
        ``y is not x`` is ``True``.
        """
        partition.split(var)
        return partition

    def alias_rebind(self, partition: AliasPartition,
                     var: str) -> AliasPartition:
        """``var = <new value>`` — rebinding, not mutation.

        Old aliases of *var* are NOT affected; *var* gets its own
        alias class.
        """
        partition.split(var)
        return partition

    def aliasing_axioms(self) -> list[FormalAxiomEntry]:
        """Formal axioms for aliasing behaviour.

        Covers:
        - assignment creates alias
        - copy breaks alias
        - deepcopy breaks alias + isolation
        - mutation through one alias is visible through all
        - rebinding does not affect other aliases
        - function arguments are aliases
        """
        x, y = _v("x"), _v("y")
        v = _v("v")
        axioms: list[FormalAxiomEntry] = []

        # After y = x: y is x
        axioms.append(FormalAxiomEntry(
            name="assignment_creates_alias",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_is(y, x), _bool_lit(True), PyBoolType(),
            ),
            description="After y = x: y is x",
        ))

        # After y = copy.copy(x): y is not x
        axioms.append(FormalAxiomEntry(
            name="copy_breaks_alias",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_is_not(op_copy(x), x), _bool_lit(True), PyBoolType(),
            ),
            description="After y = copy.copy(x): y is not x  (for mutable x)",
        ))

        # After y = copy.copy(x): y == x
        axioms.append(FormalAxiomEntry(
            name="copy_preserves_equality",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_eq(op_copy(x), x), _bool_lit(True), PyBoolType(),
            ),
            description="After y = copy.copy(x): y == x",
        ))

        # After y = copy.deepcopy(x): y is not x AND isolated(y, x)
        axioms.append(FormalAxiomEntry(
            name="deepcopy_breaks_alias",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_is_not(op_deepcopy(x), x), _bool_lit(True), PyBoolType(),
            ),
            description="After y = copy.deepcopy(x): y is not x",
        ))

        # deepcopy preserves equality
        axioms.append(FormalAxiomEntry(
            name="deepcopy_preserves_equality",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_eq(op_deepcopy(x), x), _bool_lit(True), PyBoolType(),
            ),
            description="After y = copy.deepcopy(x): y == x",
        ))

        # deepcopy isolation: mutating y does not affect x
        axioms.append(FormalAxiomEntry(
            name="deepcopy_isolation",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_isolated(op_deepcopy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.deepcopy(x) is isolated from x",
        ))

        # Mutation through one alias is visible through all
        axioms.append(FormalAxiomEntry(
            name="alias_mutation_visible",
            module=_MODULE,
            params=[("x", PyObjType()), ("y", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(op_is(x, y), op_sees_mutation(x, y)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="(x is y) → mutation through y visible via x",
        ))

        # Rebinding is not mutation
        axioms.append(FormalAxiomEntry(
            name="rebinding_not_mutation",
            module=_MODULE,
            params=[("x", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_not(op_mutated(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="After x = []: old aliases unaffected (rebinding ≠ mutation)",
        ))

        # Function arguments are aliases of caller values
        axioms.append(FormalAxiomEntry(
            name="function_arg_is_alias",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_is(_v("param"), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="def f(param): ... called as f(x): param is x",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 4. Copy Semantics
# ═══════════════════════════════════════════════════════════════════

class CopySemantics:
    """Shallow copy, deep copy, and the copy protocol.

    Python distinguishes three copy levels:
    1. *Binding copy* (``y = x``): no copy at all, just alias.
    2. *Shallow copy* (``copy.copy(x)``): new top-level container,
       but sub-objects are shared.
    3. *Deep copy* (``copy.deepcopy(x)``): recursively new objects —
       complete isolation.

    Custom classes can override via ``__copy__`` and ``__deepcopy__``.
    """

    def copy_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for copy.copy and copy.deepcopy.

        Covers:
        - new identity for mutable objects
        - equality preservation
        - sub-object sharing (shallow) vs isolation (deep)
        - immutable optimisation (may return same object)
        - type preservation
        - custom __copy__ and __deepcopy__
        """
        x, i = _v("x"), _v("i")
        axioms: list[FormalAxiomEntry] = []

        # ── shallow copy ──────────────────────────────────────────

        # copy.copy(x) creates a new identity
        axioms.append(FormalAxiomEntry(
            name="copy_new_identity",
            module=_MODULE,
            params=[("x", PyListType())],
            conclusion=formal_eq(
                _E,
                op_ne(op_id(op_copy(x)), op_id(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="id(copy.copy(x)) != id(x)  (for mutable x)",
        ))

        # copy.copy(x) == x (shallow equality)
        axioms.append(FormalAxiomEntry(
            name="copy_equals_original",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E, op_eq(op_copy(x), x), _bool_lit(True), PyBoolType(),
            ),
            description="copy.copy(x) == x",
        ))

        # Shallow copy shares sub-objects: copy.copy(x)[i] is x[i]
        axioms.append(FormalAxiomEntry(
            name="copy_shares_subitems",
            module=_MODULE,
            params=[("x", PyListType()), ("i", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_is(op_getitem(op_copy(x), i), op_getitem(x, i)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.copy(x)[i] is x[i]  (sub-objects shared)",
        ))

        # copy preserves type
        axioms.append(FormalAxiomEntry(
            name="copy_preserves_type",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_type(op_copy(x)), op_type(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="type(copy.copy(x)) == type(x)",
        ))

        # copy preserves length
        axioms.append(FormalAxiomEntry(
            name="copy_preserves_len",
            module=_MODULE,
            params=[("x", PyListType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_len(op_copy(x)), op_len(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="len(copy.copy(x)) == len(x)",
        ))

        # ── deep copy ────────────────────────────────────────────

        # deepcopy creates new identity
        axioms.append(FormalAxiomEntry(
            name="deepcopy_new_identity",
            module=_MODULE,
            params=[("x", PyListType())],
            conclusion=formal_eq(
                _E,
                op_ne(op_id(op_deepcopy(x)), op_id(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="id(copy.deepcopy(x)) != id(x)  (for mutable x)",
        ))

        # deepcopy preserves equality
        axioms.append(FormalAxiomEntry(
            name="deepcopy_equals_original",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_deepcopy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.deepcopy(x) == x",
        ))

        # deepcopy isolation
        axioms.append(FormalAxiomEntry(
            name="deepcopy_full_isolation",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_isolated(op_deepcopy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="mutating copy.deepcopy(x) does NOT affect x",
        ))

        # deepcopy preserves type
        axioms.append(FormalAxiomEntry(
            name="deepcopy_preserves_type",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_type(op_deepcopy(x)), op_type(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="type(copy.deepcopy(x)) == type(x)",
        ))

        # deepcopy preserves length
        axioms.append(FormalAxiomEntry(
            name="deepcopy_preserves_len",
            module=_MODULE,
            params=[("x", PyListType())],
            conclusion=formal_eq(
                _E,
                op_eq(op_len(op_deepcopy(x)), op_len(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="len(copy.deepcopy(x)) == len(x)",
        ))

        # deepcopy sub-items are NOT shared: deepcopy(x)[i] is not x[i]
        axioms.append(FormalAxiomEntry(
            name="deepcopy_does_not_share_subitems",
            module=_MODULE,
            params=[("x", PyListType(element_type=PyListType())),
                    ("i", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_is_not(
                    op_getitem(op_deepcopy(x), i),
                    op_getitem(x, i),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.deepcopy(x)[i] is not x[i]  (nested mutable)",
        ))

        # ── immutable optimisation ────────────────────────────────

        # copy.copy of immutable may return same object
        axioms.append(FormalAxiomEntry(
            name="copy_immutable_int",
            module=_MODULE,
            params=[("x", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_is(op_copy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.copy(42) is 42  (ints are immutable)",
        ))

        axioms.append(FormalAxiomEntry(
            name="copy_immutable_str",
            module=_MODULE,
            params=[("x", PyStrType())],
            conclusion=formal_eq(
                _E,
                op_is(op_copy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.copy('hello') is 'hello'  (strings are immutable)",
        ))

        axioms.append(FormalAxiomEntry(
            name="copy_immutable_none",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E,
                op_is(op_copy(_none_lit()), _none_lit()),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.copy(None) is None  (None is immutable)",
        ))

        axioms.append(FormalAxiomEntry(
            name="copy_immutable_bool",
            module=_MODULE,
            params=[("x", PyBoolType())],
            conclusion=formal_eq(
                _E,
                op_is(op_copy(x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="copy.copy(True) is True  (bools are immutable)",
        ))

        # ── custom copy protocol ──────────────────────────────────

        # __copy__ overrides copy.copy
        axioms.append(FormalAxiomEntry(
            name="custom_copy_protocol",
            module=_MODULE,
            params=[("x", PyClassType(name="C", methods=(
                ("__copy__", PyObjType()),
            )))],
            conclusion=formal_eq(
                _E,
                op_copy(x),
                OpCall(Op("__copy__"), (x,)),
                PyObjType(),
            ),
            description="copy.copy(x) calls x.__copy__() if defined",
        ))

        # __deepcopy__ overrides copy.deepcopy
        axioms.append(FormalAxiomEntry(
            name="custom_deepcopy_protocol",
            module=_MODULE,
            params=[("x", PyClassType(name="C", methods=(
                ("__deepcopy__", PyObjType()),
            )))],
            conclusion=formal_eq(
                _E,
                op_deepcopy(x),
                OpCall(Op("__deepcopy__"), (x, _v("memo"))),
                PyObjType(),
            ),
            description="copy.deepcopy(x) calls x.__deepcopy__(memo) if defined",
        ))

        return axioms

    def copy_isolation_obligation(self, cls_type: PyClassType) -> Judgment:
        """Generate proof obligation: custom __copy__/__deepcopy__ satisfies isolation.

        For a class ``C`` with custom ``__copy__``, the obligation is:
            ∀ x : C.  copy.copy(x) == x  ∧  copy.copy(x) is not x
        """
        x = _v("x")
        return formal_eq(
            Context(bindings={"x": cls_type}),
            op_and(
                op_eq(op_copy(x), x),
                op_is_not(op_copy(x), x),
            ),
            _bool_lit(True),
            PyBoolType(),
        )


# ═══════════════════════════════════════════════════════════════════
# 5. Serialization Semantics (Pickle / JSON)
# ═══════════════════════════════════════════════════════════════════

class SerializationSemantics:
    """Pickle, JSON, and marshal roundtrip properties.

    The central property is *roundtrip correctness*: serialising and
    deserialising an object yields an equal (but not identical) object.
    """

    def serialization_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for pickle and json roundtrips.

        Covers:
        - pickle roundtrip: loads(dumps(x)) == x
        - json roundtrip: loads(dumps(x)) == x
        - roundtrip creates new identity (no aliasing)
        - type preservation
        - __reduce__ / __getstate__ / __setstate__ consistency
        """
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        # pickle roundtrip
        axioms.append(FormalAxiomEntry(
            name="pickle_roundtrip",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(
                    op_pickle_loads(op_pickle_dumps(x)),
                    x,
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="pickle.loads(pickle.dumps(x)) == x",
        ))

        # json roundtrip
        axioms.append(FormalAxiomEntry(
            name="json_roundtrip",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(
                    op_json_loads(op_json_dumps(x)),
                    x,
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="json.loads(json.dumps(x)) == x  (for JSON-serializable x)",
        ))

        # pickle creates new identity (not aliased)
        axioms.append(FormalAxiomEntry(
            name="pickle_new_identity",
            module=_MODULE,
            params=[("x", PyListType())],
            conclusion=formal_eq(
                _E,
                op_is_not(op_pickle_loads(op_pickle_dumps(x)), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="pickle roundtrip creates a new object (no aliasing)",
        ))

        # json creates new identity
        axioms.append(FormalAxiomEntry(
            name="json_new_identity",
            module=_MODULE,
            params=[("x", PyDictType())],
            conclusion=formal_eq(
                _E,
                op_is_not(op_json_loads(op_json_dumps(x)), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="json roundtrip creates a new object (no aliasing)",
        ))

        # pickle preserves type
        axioms.append(FormalAxiomEntry(
            name="pickle_preserves_type",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(
                    op_type(op_pickle_loads(op_pickle_dumps(x))),
                    op_type(x),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="type(pickle.loads(pickle.dumps(x))) == type(x)",
        ))

        # __reduce__ / __getstate__ / __setstate__ consistency
        axioms.append(FormalAxiomEntry(
            name="getstate_setstate_inverse",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_eq(
                    op_setstate(op_copy(x), op_getstate(x)),
                    x,
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="setstate(new_x, getstate(x)) == x  (state roundtrip)",
        ))

        # pickle isolation (same as deepcopy)
        axioms.append(FormalAxiomEntry(
            name="pickle_isolation",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_isolated(op_pickle_loads(op_pickle_dumps(x)), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="pickle roundtrip produces isolated copy (like deepcopy)",
        ))

        # json roundtrip may change types (e.g. tuple → list)
        axioms.append(FormalAxiomEntry(
            name="json_type_lossy",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E,
                op_eq(
                    op_type(op_json_loads(op_json_dumps(_lit((1, 2))))),
                    _lit(list),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="json roundtrip: tuples become lists",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 6. Weak Reference Semantics
# ═══════════════════════════════════════════════════════════════════

class WeakRefSemantics:
    """Weak references: references that don't prevent garbage collection.

    ``weakref.ref(x)`` creates a weak reference to *x*.  Calling the
    weak reference returns the object if it is still alive, or ``None``
    otherwise.

    The *liveness axiom* is the key property: the weak reference
    resolves to the original object only while strong references exist.
    """

    def weakref_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for weak references.

        Covers:
        - deref while alive: weakref.ref(x)() is x
        - deref after collection: weakref.ref(x)() is None
        - liveness implication
        - WeakValueDictionary / WeakSet properties
        """
        x = _v("x")
        w = _v("w")
        axioms: list[FormalAxiomEntry] = []

        # while x has strong refs: weakref.ref(x)() is x
        axioms.append(FormalAxiomEntry(
            name="weakref_deref_alive",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_has_strong_ref(x),
                    op_is(op_weakref_deref(op_weakref(x)), x),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="weakref.ref(x)() is x  (while x alive)",
        ))

        # after collection: weakref.ref(x)() may be None
        axioms.append(FormalAxiomEntry(
            name="weakref_deref_dead",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_not(op_has_strong_ref(x)),
                    op_is(op_weakref_deref(op_weakref(x)), _none_lit()),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="weakref.ref(x)() is None  (after x collected)",
        ))

        # liveness: weakref.ref(x)() is None → x has no strong refs
        axioms.append(FormalAxiomEntry(
            name="weakref_liveness_contrapositive",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_is(op_weakref_deref(op_weakref(x)), _none_lit()),
                    op_not(op_has_strong_ref(x)),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="weakref.ref(x)() is None → no strong refs to x",
        ))

        # weakref does not prevent collection
        axioms.append(FormalAxiomEntry(
            name="weakref_no_prevent_gc",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_not(op_has_strong_ref(op_weakref(x))),
                op_not(op_has_strong_ref(op_weakref(x))),
                PyBoolType(),
            ),
            description="weakref itself does not count as strong reference",
        ))

        # weakref type: weakref.ref(x) is Optional[type(x)] when deref'd
        axioms.append(FormalAxiomEntry(
            name="weakref_deref_type",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_check(
                _E,
                op_weakref_deref(op_weakref(x)),
                OptionalType(inner=PyObjType()),
            ),
            description="weakref.ref(x)() : Optional[type(x)]",
        ))

        # WeakValueDictionary: values may disappear
        axioms.append(FormalAxiomEntry(
            name="weak_value_dict_may_shrink",
            module=_MODULE,
            params=[("x", PyDictType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_not(op_has_strong_ref(_v("val"))),
                    op_not(op_contains(x, _v("key"))),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="WeakValueDictionary: entry removed when value collected",
        ))

        # WeakSet: elements may disappear
        axioms.append(FormalAxiomEntry(
            name="weak_set_may_shrink",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_not(op_has_strong_ref(_v("elem"))),
                    op_not(op_contains(x, _v("elem"))),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="WeakSet: element removed when collected",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 7. Mutable Default Arguments
# ═══════════════════════════════════════════════════════════════════

# Known mutable types whose literals appear as default arguments
_MUTABLE_DEFAULT_TYPES = {"List", "Dict", "Set", "list", "dict", "set"}

# AST node types that are mutable constructors
_MUTABLE_AST_NODES = (ast.List, ast.Dict, ast.Set)


class MutableDefaultSemantics:
    """Detection and verification of mutable default argument bugs.

    In Python, default argument values are evaluated *once* at function
    definition time.  If the default is a mutable object (list, dict,
    set), it is *shared across all calls* — this is a classic Python
    gotcha.

    Safe pattern::

        def f(x=None):
            if x is None:
                x = []

    Unsafe pattern::

        def f(x=[]):   # ← all calls share the same list!
            x.append(1)
    """

    def mutable_default_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms formalising the mutable-default semantics.

        Covers:
        - default evaluated once at definition time
        - mutable default shared across calls (aliased)
        - mutation in one call visible in next call
        - safe pattern: ``None`` sentinel
        """
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        # Default evaluated once at function definition
        axioms.append(FormalAxiomEntry(
            name="default_evaluated_once",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E,
                op_is(_v("default_call1"), _v("default_call2")),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="Default arg evaluated once: same object on every call",
        ))

        # Mutable default shared across calls
        axioms.append(FormalAxiomEntry(
            name="mutable_default_shared",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E,
                op_implies(
                    op_mutated(_v("default")),
                    op_sees_mutation(_v("next_call_default"), _v("default")),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="If mutable default is mutated, next call sees it",
        ))

        # Safe pattern: None sentinel
        axioms.append(FormalAxiomEntry(
            name="none_sentinel_safe",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E,
                op_is_not(_v("local_list_call1"), _v("local_list_call2")),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="None sentinel + local init → fresh object per call",
        ))

        # Immutable defaults are safe
        axioms.append(FormalAxiomEntry(
            name="immutable_default_safe",
            module=_MODULE,
            params=[("x", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_not(op_mutated(x)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="Immutable defaults (int, str, tuple, None) are safe",
        ))

        return axioms

    def detect_mutable_default(self, func_source: str) -> list[str]:
        """Detect mutable default arguments in a function definition.

        Parses *func_source* as Python AST and checks each function's
        default argument values.  Returns a list of warning strings.

        Parameters
        ----------
        func_source : str
            Python source code (may contain one or more function defs).

        Returns
        -------
        list[str]
            One warning string per mutable default found.
        """
        warnings: list[str] = []
        try:
            tree = ast.parse(func_source)
        except SyntaxError:
            return warnings

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_name = node.name
                defaults = node.args.defaults + node.args.kw_defaults
                param_names = (
                    [a.arg for a in node.args.args]
                    + [a.arg for a in node.args.kwonlyargs]
                )
                # Align defaults with param names (defaults are right-aligned)
                n_pos_no_default = len(node.args.args) - len(node.args.defaults)
                for idx, default in enumerate(node.args.defaults):
                    if default is None:
                        continue
                    param_idx = n_pos_no_default + idx
                    param = (param_names[param_idx]
                             if param_idx < len(param_names) else "?")
                    if self._is_mutable_default(default):
                        lineno = getattr(default, "lineno", "?")
                        warnings.append(
                            f"{func_name}(): mutable default for "
                            f"'{param}' at line {lineno}"
                        )
                for idx, default in enumerate(node.args.kw_defaults):
                    if default is None:
                        continue
                    kw_param = node.args.kwonlyargs[idx].arg
                    if self._is_mutable_default(default):
                        lineno = getattr(default, "lineno", "?")
                        warnings.append(
                            f"{func_name}(): mutable default for "
                            f"'{kw_param}' at line {lineno}"
                        )
        return warnings

    @staticmethod
    def _is_mutable_default(node: ast.expr) -> bool:
        """Check if an AST node represents a mutable default value."""
        # Direct literal constructors: [], {}, set()
        if isinstance(node, _MUTABLE_AST_NODES):
            return True
        # Call constructors: list(), dict(), set()
        if isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Name) and func.id in _MUTABLE_DEFAULT_TYPES:
                return True
            if isinstance(func, ast.Attribute) and func.attr in _MUTABLE_DEFAULT_TYPES:
                return True
        return False


# ═══════════════════════════════════════════════════════════════════
# 8. Collect All Axioms
# ═══════════════════════════════════════════════════════════════════

def all_copy_axioms() -> list[FormalAxiomEntry]:
    """Return every axiom from this module.

    Collects axioms from:
    - ObjectIdentitySemantics
    - HeapSemantics
    - AliasingSemantics
    - CopySemantics
    - SerializationSemantics
    - WeakRefSemantics
    - MutableDefaultSemantics
    """
    axioms: list[FormalAxiomEntry] = []

    axioms.extend(ObjectIdentitySemantics().identity_axioms())
    axioms.extend(HeapSemantics().heap_axioms())
    axioms.extend(AliasingSemantics().aliasing_axioms())
    axioms.extend(CopySemantics().copy_axioms())
    axioms.extend(SerializationSemantics().serialization_axioms())
    axioms.extend(WeakRefSemantics().weakref_axioms())
    axioms.extend(MutableDefaultSemantics().mutable_default_axioms())

    return axioms


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Validate all axioms and supporting infrastructure."""

    # ── 1. Collect and validate all axioms ────────────────────────
    all_ax = all_copy_axioms()
    assert len(all_ax) >= 50, f"Expected ≥50 axioms, got {len(all_ax)}"

    # ── 2. Unique names ──────────────────────────────────────────
    names = [ax.name for ax in all_ax]
    assert len(names) == len(set(names)), (
        f"Duplicate axiom names: "
        f"{[n for n in names if names.count(n) > 1]}"
    )

    # ── 3. All conclusions are Judgments ──────────────────────────
    for ax in all_ax:
        assert ax.conclusion is not None, f"Axiom {ax.name} has no conclusion"
        assert isinstance(ax.conclusion, Judgment), (
            f"Axiom {ax.name}: conclusion is {type(ax.conclusion)}, "
            f"expected Judgment"
        )

    # ── 4. Equality axioms have left and right ────────────────────
    for ax in all_ax:
        if ax.conclusion.kind == JudgmentKind.EQUAL:
            assert ax.conclusion.left is not None, f"{ax.name} missing left"
            assert ax.conclusion.right is not None, f"{ax.name} missing right"

    # ── 5. Spot-check specific axioms ────────────────────────────
    name_set = set(names)
    for expected in [
        "identity_implies_equality",
        "identity_reflexive",
        "identity_symmetric",
        "identity_transitive",
        "id_characterises_identity",
        "none_singleton",
        "heap_read_after_write_same",
        "heap_frame",
        "heap_alloc_read",
        "heap_alloc_fresh",
        "assignment_creates_alias",
        "copy_breaks_alias",
        "deepcopy_isolation",
        "copy_new_identity",
        "copy_shares_subitems",
        "deepcopy_full_isolation",
        "copy_immutable_int",
        "pickle_roundtrip",
        "json_roundtrip",
        "pickle_new_identity",
        "weakref_deref_alive",
        "weakref_deref_dead",
        "weakref_liveness_contrapositive",
        "default_evaluated_once",
        "mutable_default_shared",
        "none_sentinel_safe",
    ]:
        assert expected in name_set, f"Missing expected axiom: {expected}"

    # ── 6. Per-class axiom counts ────────────────────────────────
    ident = ObjectIdentitySemantics()
    assert len(ident.identity_axioms()) >= 8, "Need ≥8 identity axioms"

    heap = HeapSemantics()
    assert len(heap.heap_axioms()) >= 4, "Need ≥4 heap axioms"

    alias = AliasingSemantics()
    assert len(alias.aliasing_axioms()) >= 6, "Need ≥6 aliasing axioms"

    cp = CopySemantics()
    assert len(cp.copy_axioms()) >= 12, "Need ≥12 copy axioms"

    ser = SerializationSemantics()
    assert len(ser.serialization_axioms()) >= 6, "Need ≥6 serialization axioms"

    wr = WeakRefSemantics()
    assert len(wr.weakref_axioms()) >= 5, "Need ≥5 weakref axioms"

    md = MutableDefaultSemantics()
    assert len(md.mutable_default_axioms()) >= 3, "Need ≥3 mutable-default axioms"

    # ── 7. AliasPartition data structure ─────────────────────────
    p = AliasPartition()
    p.merge("x", "y")
    assert p.are_aliases("x", "y"), "x and y should be aliases after merge"
    assert not p.are_aliases("x", "z"), "x and z should not be aliases"

    p.merge("y", "z")
    assert p.are_aliases("x", "z"), "x and z should be aliases after transitive merge"

    p.split("z")
    assert not p.are_aliases("x", "z"), "z should be split from x after split"
    assert p.are_aliases("x", "y"), "x and y should still be aliases"

    # ── 8. AliasingSemantics methods ─────────────────────────────
    asem = AliasingSemantics()
    part = AliasPartition()
    asem.alias_assignment(part, "a", "b")
    assert part.are_aliases("a", "b")

    affected = asem.alias_mutation(part, "a")
    assert "a" in affected and "b" in affected

    asem.alias_copy(part, "b")
    assert not part.are_aliases("a", "b")

    # ── 9. Mutable default detection ─────────────────────────────
    md = MutableDefaultSemantics()

    unsafe_code = '''
def foo(x=[]):
    x.append(1)
    return x

def bar(y={}, *, z=set()):
    pass
'''
    warns = md.detect_mutable_default(unsafe_code)
    assert len(warns) >= 3, f"Expected ≥3 warnings, got {len(warns)}: {warns}"
    assert any("foo" in w for w in warns)
    assert any("bar" in w for w in warns)

    safe_code = '''
def baz(x=None):
    if x is None:
        x = []
    return x

def qux(n=42, s="hello", t=(1, 2)):
    pass
'''
    safe_warns = md.detect_mutable_default(safe_code)
    assert len(safe_warns) == 0, f"Expected 0 warnings, got {safe_warns}"

    # ── 10. CopySemantics.copy_isolation_obligation ───────────────
    cls_ty = PyClassType(name="Foo")
    obligation = CopySemantics().copy_isolation_obligation(cls_ty)
    assert isinstance(obligation, Judgment)
    assert obligation.kind == JudgmentKind.EQUAL

    # ── 11. Op constructors smoke test ───────────────────────────
    a, b = _v("a"), _v("b")
    assert isinstance(op_is(a, b), OpCall)
    assert op_is(a, b).op.name == "is"
    assert isinstance(op_copy(a), OpCall)
    assert op_copy(a).op.module == "copy"
    assert isinstance(op_deepcopy(a), OpCall)
    assert isinstance(op_pickle_dumps(a), OpCall)
    assert isinstance(op_weakref(a), OpCall)
    assert isinstance(op_heap_read(a, b), OpCall)
    assert isinstance(op_heap_write(a, b, _v("c")), OpCall)
    assert isinstance(op_implies(a, b), OpCall)
    assert isinstance(op_isolated(a, b), OpCall)

    print(f"✓ python_copy self-test passed — {len(all_ax)} axioms verified")


if __name__ == "__main__":
    _self_test()
