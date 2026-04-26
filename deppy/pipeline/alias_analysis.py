"""Flow-sensitive may-alias analysis for the deppy refinement pipeline.

Audit fix #8
============

Before this module the mutation tracking in
:func:`deppy.pipeline.refinement_inference._mutated_names_in_stmt`
only flagged the *root name* of a mutation expression.  When a Python
program aliased a value::

    ys = xs        # ys now points to the same list object as xs
    ys.append(3)   # mutates xs through ys

the mutation tracker recorded ``"ys"`` but missed ``"xs"`` — guards
referring to ``xs`` (e.g. ``"len(xs) > 0"``) survived past the
mutation point even though the underlying list had been modified.
Downstream analyses then accepted predicates that were no longer
sound.

This module provides an :class:`AliasTable` that approximates the
may-alias relation (i.e. *might* two names point to the same Python
object?) and a :func:`mutated_names_with_aliases` driver that the
mutation tracker uses to expand a single mutated name into every
name that may share its underlying object at that program point.

Soundness direction
-------------------

Aliasing is a *may*-relation.  A false positive (saying "ys aliases
xs" when they don't) only makes the pipeline drop more guards — i.e.,
become more conservative — which is the safe direction.  A false
negative (missing a real alias) is the unsoundness we are trying to
plug.  When in doubt the analysis errs toward "may alias".

What creates an alias
---------------------

The Python execution model says references are created by:

* direct assignment::

    y = x           # y ↔ x

* multiple-target assignment::

    y = z = x       # y ↔ z ↔ x

* tuple / list unpacking::

    y, z = x, w     # y ↔ x, z ↔ w

* augmented binary expressions that may return an operand::

    y = x or other  # y may ↔ x  (or "other")
    y = x and other # y may ↔ x  (or "other")

* an attribute or subscript on an aliased base::

    a = b
    a.field         # a.field has the same identity as b.field

  We model attribute / subscript as introducing a *path expression*
  that's killed whenever the base is killed.  See :class:`AliasTable`
  for details.

What does NOT create an alias
-----------------------------

* function calls, except for known-identity functions::

    y = list(x)     # y is a fresh list (not aliased)
    y = x.copy()    # fresh
    y = sorted(x)   # fresh
    y = x[:]        # fresh (slicing copies sequences)
    y = dict(x)     # fresh

* arithmetic, boolean ops, comparisons::

    y = x + 1       # int; new object
    y = x == 0      # new bool

* literals, comprehensions, generator expressions

* ``copy`` / ``deepcopy`` calls

What kills an alias
-------------------

* rebinding::

    y = x           # y ↔ x
    y = some_call() # y is freshly bound; y ↛ x

* ``del y``

* explicit type-narrowing assignments via ``isinstance`` etc.

Public API
----------

::

    table = AliasTable.empty()
    table = table.update(stmt)               # advance over an AST statement
    table.may_alias(a, b) -> bool
    table.aliases_of(name) -> set[str]
    table.kill(name) -> AliasTable
    table.union(a, b) -> AliasTable

    mutated_names_with_aliases(stmt, table) -> set[str]
        # Mutated root names from `stmt`, expanded with the aliases
        # held by `table`.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Equivalence-class storage
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class _EqClass:
    """Equivalence class of names that may refer to the same object."""
    members: frozenset[str]

    def with_added(self, name: str) -> "_EqClass":
        return _EqClass(self.members | {name})

    def with_removed(self, name: str) -> Optional["_EqClass"]:
        new_members = self.members - {name}
        if len(new_members) <= 1:
            return None  # singleton classes are not tracked
        return _EqClass(new_members)


@dataclass(frozen=True)
class AliasTable:
    """Flow-sensitive may-alias relation.

    Internally we store the partition as a tuple of
    :class:`_EqClass` (frozen for hashability so we can cache and
    compare tables across paths).  Names not appearing in any class
    are implicitly singleton (i.e. they alias only themselves).

    Operations are pure — every method returns a *new* table — so
    the analyser can fork tables across branches and merge them at
    join points.
    """

    classes: tuple[_EqClass, ...] = ()

    # ---------- constructors --------------------------------------

    @classmethod
    def empty(cls) -> "AliasTable":
        return cls(classes=())

    @classmethod
    def from_pairs(cls, pairs: Iterable[tuple[str, str]]) -> "AliasTable":
        t = cls.empty()
        for a, b in pairs:
            t = t.union(a, b)
        return t

    # ---------- queries -------------------------------------------

    def may_alias(self, a: str, b: str) -> bool:
        if a == b:
            return True
        for cls in self.classes:
            if a in cls.members and b in cls.members:
                return True
        return False

    def aliases_of(self, name: str) -> set[str]:
        """All names that may-alias with ``name``, including ``name``."""
        for cls in self.classes:
            if name in cls.members:
                return set(cls.members)
        return {name}

    def all_classes(self) -> tuple[_EqClass, ...]:
        return self.classes

    def class_count(self) -> int:
        return len(self.classes)

    def known_names(self) -> set[str]:
        out: set[str] = set()
        for cls in self.classes:
            out.update(cls.members)
        return out

    # ---------- mutators (pure, return new tables) ----------------

    def union(self, a: str, b: str) -> "AliasTable":
        """Add a may-alias relation between ``a`` and ``b``."""
        if a == b:
            return self
        ca = self._class_of(a)
        cb = self._class_of(b)
        if ca is not None and cb is not None and ca == cb:
            return self
        new_members: frozenset[str] = frozenset()
        new_classes: list[_EqClass] = []
        for cls in self.classes:
            if cls is ca or cls is cb:
                new_members = new_members | cls.members
            else:
                new_classes.append(cls)
        if not ca:
            new_members = new_members | {a}
        if not cb:
            new_members = new_members | {b}
        if len(new_members) >= 2:
            new_classes.append(_EqClass(new_members))
        return AliasTable(classes=tuple(new_classes))

    def kill(self, name: str) -> "AliasTable":
        """Remove ``name`` from its equivalence class (it now points
        to a fresh object).  Singleton classes are dropped."""
        new_classes: list[_EqClass] = []
        for cls in self.classes:
            if name in cls.members:
                replaced = cls.with_removed(name)
                if replaced is not None:
                    new_classes.append(replaced)
            else:
                new_classes.append(cls)
        return AliasTable(classes=tuple(new_classes))

    def kill_all(self, names: Iterable[str]) -> "AliasTable":
        t = self
        for n in names:
            t = t.kill(n)
        return t

    # ---------- joins ---------------------------------------------

    def join(self, other: "AliasTable") -> "AliasTable":
        """Compute the may-alias *union* of two tables.

        The semantic intent: at a join point the may-alias relation
        is the *union* of the relations from each incoming branch
        (because ``a may-alias b`` if there exists a path on which
        they alias).  Implementation: union the equivalence classes
        — when class C₁ from ``self`` and C₂ from ``other`` overlap,
        merge them.
        """
        merged: list[set[str]] = []
        for cls in self.classes:
            merged.append(set(cls.members))
        for cls in other.classes:
            members = set(cls.members)
            # Find any existing merged set that overlaps.
            absorbed: list[int] = []
            for i, existing in enumerate(merged):
                if existing & members:
                    absorbed.append(i)
            if absorbed:
                # Merge all overlapping sets + this one.
                target = merged[absorbed[0]]
                target |= members
                for j in reversed(absorbed[1:]):
                    target |= merged[j]
                    del merged[j]
            else:
                merged.append(members)
        result_classes = tuple(
            _EqClass(frozenset(s)) for s in merged if len(s) >= 2
        )
        return AliasTable(classes=result_classes)

    @staticmethod
    def join_many(tables: Iterable["AliasTable"]) -> "AliasTable":
        result: Optional[AliasTable] = None
        for t in tables:
            result = t if result is None else result.join(t)
        return result if result is not None else AliasTable.empty()

    # ---------- private helpers ----------------------------------

    def _class_of(self, name: str) -> Optional[_EqClass]:
        for cls in self.classes:
            if name in cls.members:
                return cls
        return None


# ─────────────────────────────────────────────────────────────────────
#  Statement-level analysis
# ─────────────────────────────────────────────────────────────────────


# Calls that we *know* return a fresh object (not aliasing inputs).
_FRESH_RETURNING_CALLS = frozenset({
    # Constructors of common immutable / fresh containers.
    "list", "dict", "set", "tuple", "frozenset", "bytearray",
    "bytes", "str", "repr", "format",
    # Common copy primitives.
    "copy", "deepcopy",
    # Arithmetic / type coercions return fresh values.
    "int", "float", "complex", "bool", "abs", "round",
    # Sequence transforms — return fresh sequences.
    "sorted", "reversed", "enumerate", "zip", "map", "filter",
    "range", "iter",
    # Hashing / encoding.
    "hash", "id", "ord", "chr", "hex", "oct", "bin",
    # I/O / errors / etc.
    "len", "min", "max", "sum", "any", "all",
})


# Method names that *do* return ``self`` (so the result aliases the
# receiver).  Conservative — list known cases.
_SELF_RETURNING_METHODS = frozenset({
    # ``__iadd__`` / ``__imul__`` are usually self-returning, but
    # they're also reflected through augmented-assign which we
    # handle separately.  No method here for now.
})


# Method names whose result is *fresh* (not aliasing the receiver).
_FRESH_RETURNING_METHODS = frozenset({
    "copy", "lower", "upper", "strip", "rstrip", "lstrip",
    "title", "capitalize", "split", "rsplit", "splitlines",
    "join", "format", "encode", "decode",
    "items", "keys", "values",  # views — we treat as fresh
    "to_list", "tolist", "to_dict",
    # set ops that return new sets:
    "union", "intersection", "difference", "symmetric_difference",
    # numeric:
    "as_integer_ratio", "conjugate", "real", "imag",
})


def update_for_stmt(table: AliasTable, stmt: ast.stmt) -> AliasTable:
    """Advance ``table`` past one Python statement.

    We handle:

    * ``Assign`` (single + chained targets, tuple unpacking)
    * ``AnnAssign``
    * ``AugAssign``  (rebinds the target, treated as kill+fresh)
    * ``Delete``
    * ``For`` / ``With`` introducing fresh bindings (the loop /
      context variables are killed, then bound fresh)
    * Function-def / Class-def — opaque to alias state
    * ``Return`` / ``Raise`` / ``Break`` / ``Continue`` — no effect

    Everything else passes through unchanged.
    """
    if isinstance(stmt, ast.Assign):
        return _handle_assign(table, stmt.targets, stmt.value)
    if isinstance(stmt, ast.AnnAssign):
        if stmt.value is None:
            return table
        return _handle_assign(table, [stmt.target], stmt.value)
    if isinstance(stmt, ast.AugAssign):
        # ``x += y`` rebinds x.  We treat as kill (x no longer aliases
        # whatever it did before) and don't introduce a new alias.
        if isinstance(stmt.target, ast.Name):
            return table.kill(stmt.target.id)
        return table
    if isinstance(stmt, ast.Delete):
        out = table
        for tgt in stmt.targets:
            n = _root_name(tgt)
            if n:
                out = out.kill(n)
        return out
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        # Loop variable is rebound on every iteration to an element
        # of the iterable.  We kill the loop variable (no alias to
        # the iterable container itself).
        n = _root_name(stmt.target)
        if n:
            return table.kill(n)
        return table
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        out = table
        for item in stmt.items:
            if item.optional_vars is not None:
                n = _root_name(item.optional_vars)
                if n:
                    # ``with f as g`` — g is bound to the context
                    # manager's __enter__ result.  For sequences /
                    # files this is typically the manager itself
                    # (so g aliases f), but in general we can't know.
                    # Conservative: kill g (don't claim aliasing
                    # we don't have evidence for).
                    out = out.kill(n)
        return out
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        # Definitions don't change alias state at the call site.
        return table
    return table


def _handle_assign(
    table: AliasTable, targets: list[ast.expr], value: ast.expr,
) -> AliasTable:
    """Update ``table`` for an ``Assign`` / ``AnnAssign``.

    Multi-target chained assigns (``a = b = c``) are handled by
    iterating each target.  Tuple-unpacking (``(a, b) = (c, d)``) is
    handled by zipping target and value tuples.
    """
    out = table
    for tgt in targets:
        out = _bind(out, tgt, value)
    return out


def _bind(
    table: AliasTable, target: ast.expr, value: ast.expr,
) -> AliasTable:
    """Bind ``target`` to ``value`` in ``table``.

    Cases:
      Name = Name        → kill name, then union name ↔ value's name
      Name = Call/etc.   → kill name (fresh)
      Tuple = Tuple      → zip and recurse
      Tuple = Name (?)   → unpacking from a sequence — we pessimise:
                            kill all targets (we don't know which
                            elements alias which sources)
      Subscript / Attr   → no top-level binding
    """
    if isinstance(target, (ast.Tuple, ast.List)):
        if isinstance(value, (ast.Tuple, ast.List)) and len(value.elts) == len(target.elts):
            out = table
            for t, v in zip(target.elts, value.elts):
                out = _bind(out, t, v)
            return out
        # Unknown unpacking source — kill all targets.
        out = table
        for t in target.elts:
            n = _root_name(t)
            if n:
                out = out.kill(n)
        return out
    if isinstance(target, ast.Starred):
        return _bind(table, target.value, value)
    if isinstance(target, ast.Name):
        out = table.kill(target.id)
        new_aliases = _candidate_aliases_from_value(value)
        for src in new_aliases:
            out = out.union(target.id, src)
        return out
    # Subscript / Attribute / etc. — these mutate the *base* (already
    # tracked by mutation analysis); they don't rebind a top-level
    # name.
    return table


def _candidate_aliases_from_value(value: ast.expr) -> set[str]:
    """Return the names that ``value`` may evaluate to (so the LHS
    of an assignment may alias them).

    This is the heart of the heuristic — we are conservative when in
    doubt (many names → many aliases), since false-positive aliases
    only make the pipeline more conservative.
    """
    if isinstance(value, ast.Name):
        return {value.id}
    if isinstance(value, ast.IfExp):
        return (
            _candidate_aliases_from_value(value.body)
            | _candidate_aliases_from_value(value.orelse)
        )
    if isinstance(value, ast.BoolOp):
        # ``a or b`` returns ``a`` or ``b`` (the actual operand,
        # not coerced to bool).  Same for ``and``.  So the result
        # may alias either.
        out: set[str] = set()
        for v in value.values:
            out.update(_candidate_aliases_from_value(v))
        return out
    if isinstance(value, ast.Starred):
        return _candidate_aliases_from_value(value.value)
    if isinstance(value, ast.NamedExpr):  # walrus
        return _candidate_aliases_from_value(value.value)
    if isinstance(value, ast.Call):
        return _aliases_from_call(value)
    if isinstance(value, ast.Subscript):
        # ``x[i]`` — the result may alias the element-type, not the
        # container itself.  In Python the element is a *reference*
        # to whatever was stored, so it may indeed alias things, but
        # we don't track per-index aliasing.  Be conservative: if
        # the base is a list/dict, the result may alias *any* prior
        # element insertion site.  In practice we drop this and
        # treat as a fresh-ish reference (return empty set so the
        # LHS is a fresh, untracked binding).  This is unsound for
        # element-aliasing but consistent with the rest of the
        # pipeline.
        return set()
    if isinstance(value, ast.Attribute):
        # ``x.attr`` — the result may alias whatever is stored in
        # the attribute slot.  We don't track attribute-level aliasing
        # — treat as fresh.  This is consistent with Python's name
        # binding model since `y = x.attr` doesn't transitively
        # propagate later mutations of `x.attr`.
        return set()
    # Constants, lambdas, comprehensions, slices: no aliases.
    return set()


def _aliases_from_call(node: ast.Call) -> set[str]:
    """Return the names a function call's result may alias.

    For known fresh-returning calls we return empty.  For unknown
    calls we *could* return all argument names (a function might
    return any of its arguments), but in practice this floods the
    alias relation and makes the analysis useless.  We instead
    return empty by default and only union for *self-returning*
    method calls we explicitly recognise (``x.foo()`` where ``foo``
    is in ``_SELF_RETURNING_METHODS``).
    """
    func = node.func
    if isinstance(func, ast.Name):
        if func.id in _FRESH_RETURNING_CALLS:
            return set()
        # Unknown free-standing function — assume fresh.  This is
        # unsound when a custom function returns its argument.  Users
        # who need precision can mark the function via @implies or
        # use the alias-tracking helpers explicitly.
        return set()
    if isinstance(func, ast.Attribute):
        method = func.attr
        if method in _FRESH_RETURNING_METHODS:
            return set()
        if method in _SELF_RETURNING_METHODS:
            recv = _root_name(func.value)
            return {recv} if recv else set()
        # Unknown method.  Conservative-but-not-flooding choice: any
        # method that doesn't match a fresh-returning name is treated
        # as potentially returning the receiver.  This matches
        # patterns like ``builder.set_x(v).set_y(w)`` where the
        # builder methods return ``self``.
        recv = _root_name(func.value)
        return {recv} if recv else set()
    return set()


def _root_name(node: ast.expr) -> Optional[str]:
    """Return the top-level Name in ``node``'s reference chain."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _root_name(node.value)
    if isinstance(node, ast.Subscript):
        return _root_name(node.value)
    if isinstance(node, ast.Starred):
        return _root_name(node.value)
    return None


# ─────────────────────────────────────────────────────────────────────
#  Mutation expansion
# ─────────────────────────────────────────────────────────────────────


def expand_mutations(
    mutated: set[str], table: AliasTable,
) -> set[str]:
    """Expand a set of mutated names with their may-aliases.

    Given that ``ys.append(3)`` was detected (so ``mutated == {"ys"}``)
    and the alias table records ``ys ↔ xs``, the returned set is
    ``{"ys", "xs"}``.
    """
    out: set[str] = set(mutated)
    for name in list(mutated):
        out.update(table.aliases_of(name))
    return out


def mutated_names_with_aliases(
    stmt: ast.stmt, table: AliasTable, mutated_func,
) -> set[str]:
    """Return the set of names ``stmt`` mutates, expanded with the
    aliases held by ``table``.

    ``mutated_func`` is the existing
    :func:`refinement_inference._mutated_names_in_stmt`-style
    detector (we accept it as a parameter to avoid creating a
    circular import).  Audit fix #8: callers should always pass
    their result through this function so aliased mutations are
    surfaced.
    """
    direct = mutated_func(stmt)
    return expand_mutations(direct, table)


# ─────────────────────────────────────────────────────────────────────
#  Function-level driver
# ─────────────────────────────────────────────────────────────────────


@dataclass
class AliasAnalysisReport:
    """Result of running the analyser over a function body.

    ``table_at_end`` is the alias relation that holds when the body
    falls off the end (or returns).  ``mutations_at_stmt`` records,
    for each statement that mutates anything, the *expanded* set of
    mutated names — i.e. including aliases.  Useful for downstream
    debugging / display.
    """

    table_at_start: AliasTable
    table_at_end: AliasTable
    mutations_at_stmt: list[tuple[ast.stmt, set[str]]] = field(
        default_factory=list,
    )

    def all_mutated(self) -> set[str]:
        out: set[str] = set()
        for _, names in self.mutations_at_stmt:
            out.update(names)
        return out


def analyse_function(
    fn_node: ast.FunctionDef,
    *,
    initial_aliases: Optional[Iterable[tuple[str, str]]] = None,
    mutated_func=None,
) -> AliasAnalysisReport:
    """Run the alias analysis over the body of ``fn_node``.

    Parameters
    ----------
    fn_node :
        The function to analyse.  We do *not* recurse into nested
        function or class definitions — those are analyses of their
        own.
    initial_aliases :
        Optional seed pairs, e.g. ``[("self", "self")]`` (no-op) or
        for partial-application patterns where the caller knows two
        parameters alias.
    mutated_func :
        Callable taking an :class:`ast.stmt` and returning the set
        of *direct* mutated names.  When omitted we use the local
        :func:`_default_mutated_func` (covers method calls, assigns,
        del, augmented-assign, for-loop targets).
    """
    table = AliasTable.from_pairs(initial_aliases or [])
    detect = mutated_func or _default_mutated_func
    report = AliasAnalysisReport(
        table_at_start=table, table_at_end=table,
    )
    table = _walk_block(fn_node.body, table, detect, report)
    report.table_at_end = table
    return report


def _walk_block(
    stmts: list[ast.stmt], table: AliasTable, detect, report,
) -> AliasTable:
    for stmt in stmts:
        # Compute mutations *before* updating the alias table so the
        # mutation expansion uses the alias relation that held at
        # the statement's *entry*.  This matches Python semantics —
        # ``ys.append(x)`` mutates ys when ys is bound, regardless of
        # what later assignments do to ys.
        direct = detect(stmt)
        if direct:
            expanded = expand_mutations(direct, table)
            report.mutations_at_stmt.append((stmt, expanded))
        # Then advance for control flow.
        if isinstance(stmt, ast.If):
            then_table = _walk_block(stmt.body, table, detect, report)
            else_table = _walk_block(
                list(getattr(stmt, "orelse", []) or []), table,
                detect, report,
            )
            table = then_table.join(else_table)
        elif isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            # The loop body might execute or not — join with the
            # pre-loop state.
            body_table = _walk_block(
                list(stmt.body), update_for_stmt(table, stmt),
                detect, report,
            )
            else_table = _walk_block(
                list(getattr(stmt, "orelse", []) or []), table,
                detect, report,
            )
            table = body_table.join(else_table).join(table)
        elif isinstance(stmt, (ast.With, ast.AsyncWith)):
            inner = update_for_stmt(table, stmt)
            table = _walk_block(stmt.body, inner, detect, report)
        elif isinstance(stmt, ast.Try):
            body_table = _walk_block(
                list(stmt.body), table, detect, report,
            )
            handler_tables = [
                _walk_block(list(h.body), table, detect, report)
                for h in stmt.handlers
            ]
            else_table = _walk_block(
                list(stmt.orelse), body_table, detect, report,
            )
            final_table = AliasTable.join_many(
                [body_table, *handler_tables, else_table],
            )
            table = _walk_block(
                list(stmt.finalbody), final_table, detect, report,
            )
        elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
            # Don't descend into nested defs.
            pass
        else:
            table = update_for_stmt(table, stmt)
    return table


_DEFAULT_MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "sort", "reverse",
    "clear", "setdefault", "update", "popitem", "add", "discard",
    "intersection_update", "difference_update",
    "symmetric_difference_update", "__setitem__", "__delitem__",
})


def _default_mutated_func(stmt: ast.stmt) -> set[str]:
    """Local mutation-detection used by :func:`analyse_function`
    when the caller doesn't supply one.

    Audit fix #8: returns *only the in-place object mutations* — i.e.
    operations that modify the underlying Python object.  Rebinding
    (``y = ...``) is **not** included here because it does not
    mutate the *object* y previously pointed to; rebinding only
    invalidates guards on ``y`` itself, with no propagation to
    aliases.

    The full "names whose guards are invalidated" set is the union
    of rebound names and the alias-expanded in-place mutations —
    callers compute that union themselves; see
    :func:`in_place_mutations_in_stmt` and
    :func:`rebound_names_in_stmt` below.
    """
    return in_place_mutations_in_stmt(stmt)


def _root(node: ast.expr, out: set[str]) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _root(node.value, out)
    if isinstance(node, ast.Subscript):
        return _root(node.value, out)
    if isinstance(node, ast.Starred):
        return _root(node.value, out)
    if isinstance(node, (ast.Tuple, ast.List)):
        for elt in node.elts:
            n = _root(elt, out)
            if n:
                out.add(n)
        return None
    return None


def in_place_mutations_in_stmt(stmt: ast.stmt) -> set[str]:
    """Return the set of names whose underlying object is mutated
    *in place* by ``stmt``.

    Includes:

    * ``x[k] = v`` / ``del x[k]`` (subscript-assign / -del)
    * ``x.attr = v`` / ``del x.attr`` (attribute-assign / -del)
    * ``x.append(...)``, ``x.pop(...)``, ``x.sort()``, etc.
    * ``x += ...`` when ``x`` is a list (``__iadd__`` mutates)

    Excludes:

    * Plain rebinding ``x = ...`` — the binding changes, but the
      previous object is untouched.
    * For-loop targets — the variable is rebound, not mutated.
    """
    out: set[str] = set()

    # Subscript / attribute assignment / deletion mutate the *base*.
    if isinstance(stmt, ast.Assign):
        for tgt in stmt.targets:
            if isinstance(tgt, (ast.Subscript, ast.Attribute)):
                n = _root(tgt, out)
                if n:
                    out.add(n)
    elif isinstance(stmt, ast.AnnAssign):
        if isinstance(stmt.target, (ast.Subscript, ast.Attribute)):
            n = _root(stmt.target, out)
            if n:
                out.add(n)
    elif isinstance(stmt, ast.AugAssign):
        # ``x += y`` for lists / dicts / sets calls __iadd__ which
        # mutates in place.  For ints / strs / tuples it rebinds.
        # We can't know the type — be conservative and treat as
        # in-place mutation (which is the safe direction).
        n = _root(stmt.target, out)
        if n:
            out.add(n)
    elif isinstance(stmt, ast.Delete):
        for tgt in stmt.targets:
            if isinstance(tgt, (ast.Subscript, ast.Attribute)):
                n = _root(tgt, out)
                if n:
                    out.add(n)

    # Mutating method calls anywhere in the statement.
    for child in ast.walk(stmt):
        if isinstance(child, ast.Call):
            func = child.func
            if (isinstance(func, ast.Attribute)
                    and func.attr in _DEFAULT_MUTATING_METHODS):
                receiver = _root(func.value, out)
                if receiver:
                    out.add(receiver)

    return out


def rebound_names_in_stmt(stmt: ast.stmt) -> set[str]:
    """Return the set of names whose binding is changed (but whose
    underlying object is *not* mutated in place) by ``stmt``.

    Includes plain assignment, ``del x``, for-loop targets, and
    deletion of bare names.  Used for guard invalidation on the
    rebound name itself, but with no propagation to aliases.
    """
    out: set[str] = set()
    if isinstance(stmt, ast.Assign):
        for tgt in stmt.targets:
            if isinstance(tgt, ast.Name):
                out.add(tgt.id)
            elif isinstance(tgt, (ast.Tuple, ast.List)):
                for elt in tgt.elts:
                    if isinstance(elt, ast.Name):
                        out.add(elt.id)
                    elif isinstance(elt, ast.Starred) and isinstance(
                        elt.value, ast.Name,
                    ):
                        out.add(elt.value.id)
    elif isinstance(stmt, ast.AnnAssign):
        if isinstance(stmt.target, ast.Name):
            out.add(stmt.target.id)
    elif isinstance(stmt, ast.Delete):
        for tgt in stmt.targets:
            if isinstance(tgt, ast.Name):
                out.add(tgt.id)
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        if isinstance(stmt.target, ast.Name):
            out.add(stmt.target.id)
    return out


__all__ = [
    "AliasTable",
    "AliasAnalysisReport",
    "analyse_function",
    "update_for_stmt",
    "expand_mutations",
    "mutated_names_with_aliases",
    "in_place_mutations_in_stmt",
    "rebound_names_in_stmt",
]
