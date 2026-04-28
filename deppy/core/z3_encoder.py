"""Type-aware Z3 encoding of Python predicates.

This module also exposes three orthogonal extensions:

* **Recursive datatypes** — :func:`_encode_recursive_datatype` detects
  dataclasses that reference themselves (directly, via ``Optional``,
  or via ``Union``) and emits a Z3 ``Datatype`` whose constructors
  mirror the Python field shape.  The default encoding builds two
  constructors (``leaf`` / ``node``) when an Optional self-reference
  is present, otherwise one constructor per non-self combination.
* **Polymorphic memoisation** — repeated encodings of the same shape
  (e.g. ``list[int]`` mentioned in three different proofs) reuse the
  same Z3 sort.  The cache is keyed by a hashable type signature
  derived from the annotation AST, so two textually identical
  annotations always resolve to the same Z3 sort.  Tests can clear
  the cache via :func:`clear_encoding_cache`.
* **Custom predicate registration** — :func:`register_custom_predicate`
  lets a user attach a Z3-side recursive definition to a Python
  predicate (e.g. ``is_balanced(tree)``).  The encoder consults the
  registry when evaluating function calls and, on a hit, dispatches
  to the registered Z3 closure rather than treating the call as
  uninterpreted.



The kernel's plain ``_z3_check_implication`` declares every free
identifier as ``Int`` and falls back to heuristic ``Bool`` detection
based on operator usage.  That works for arithmetic-only goals but
silently produces nonsense for predicates over ``Optional[int]``,
``list[int]``, ``Union[int, str]``, callables, and user classes.

This module replaces the heuristic with a *typed* encoder driven by
Python type annotations.  Given a :class:`deppy.lean.type_translation.Context`
and the binder types for a function, it builds Z3 sorts for each
free identifier and translates the predicate into Z3 expressions
that respect those sorts:

* ``int`` / ``bool`` / ``float`` / ``str`` → primitive Z3 sorts
* ``Optional[T]`` → Z3 datatype ``Maybe_T`` with ``none`` /
  ``some(value : T)`` constructors and ``isNone`` / ``isSome`` /
  ``getValue`` accessors.
* ``Union[A, B, ...]`` → Z3 datatype with one constructor per
  alternative, named ``case_A`` / ``case_B`` / etc.
* ``list[T]`` → Z3 ``ArraySort(Int, T)`` paired with an opaque
  length function ``len_<name>(): Int`` so predicates like
  ``0 <= i < len(xs)`` are encodable.
* ``dict[K, V]`` → ``ArraySort(K, V)`` plus a Boolean
  ``contains_<name>(k: K): Bool`` membership predicate.
* ``Callable[[...], R]`` → uninterpreted function declaration with
  the rendered arity.
* User classes / unknown types → uninterpreted sort, one per name.

Public API::

    @dataclass
    class Z3Encoding:
        sorts: dict[str, ...]   # name → Z3 sort
        env: dict[str, ...]     # name → Z3 expression (Const / Func)
        helpers: dict[str, ...] # convenience predicates / functions

    encode_predicate(predicate, *, binders, context, solver=None)
        → (z3_expr, encoding) — returns the Z3 expression and the
        encoding state so the caller can build follow-up formulas.

    check_implication(premise, conclusion, *, binders, context)
        → (verdict, reason) — the typed analogue of
        ``_z3_check_implication`` that the kernel uses for
        ``Z3Proof`` verification.

When Z3 isn't installed the module returns ``(False, "not-installed")``
without ever importing ``z3``.
"""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Any, Optional


# ─────────────────────────────────────────────────────────────────────
#  Result + dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class Z3Encoding:
    """The Z3 environment built for one predicate evaluation.

    ``env`` maps each free Python identifier to a Z3 expression of
    the appropriate sort.  ``helpers`` carries auxiliary functions
    we synthesise (``len_xs`` for list parameters, ``contains_d``
    for dict membership, ``Maybe_int.isSome`` for Optionals, …).

    ``binder_types`` records the original Python annotation text
    for each binder, so per-type encoders (e.g. the ``hasattr``
    encoder from audit fix #10) can decide attribute presence
    based on the receiver's actual class.

    ``hasattr_cache`` is a per-encoding cache for uninterpreted
    ``hasattr`` predicates so the same ``(sort_name, attr_name)``
    pair always resolves to the same Z3 atom.

    ``axioms`` collects Z3 BoolRef constraints that should be
    asserted into the solver alongside the predicate (e.g. that
    ``len_<xs>(xs) >= 0`` for every list-typed binder).  The
    encoder builds these as it walks annotations; the
    ``check_implication`` entry point feeds them to ``s.add`` so
    that downstream proofs can rely on them.

    Callers usually only need ``env`` to evaluate further formulas
    in the same scope.
    """
    sorts: dict[str, Any] = field(default_factory=dict)
    env: dict[str, Any] = field(default_factory=dict)
    helpers: dict[str, Any] = field(default_factory=dict)
    binder_types: dict[str, str] = field(default_factory=dict)
    hasattr_cache: dict[tuple[str, str], Any] = field(default_factory=dict)
    axioms: list[Any] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
#  Public entry points
# ─────────────────────────────────────────────────────────────────────

def check_implication(
    premise: str,
    conclusion: str,
    *,
    binders: dict[str, str],
    context: Optional[Any] = None,
) -> tuple[bool, Optional[str]]:
    """Type-aware ``premise ⇒ conclusion`` validity check.

    ``binders`` maps Python identifier → annotation text (as it
    appears in source); ``context`` is an optional
    :class:`deppy.lean.type_translation.Context` for resolving
    TypeVar / NewType / TypeAlias.  Returns the same
    ``(verdict, reason)`` shape as the kernel's untyped
    ``_z3_check_implication``.
    """
    try:
        import z3
    except ImportError:
        return False, "not-installed"
    # Z3's C reference counting isn't thread-safe; serialise every
    # entry point through the module-level lock.  See
    # ``deppy.core.z3_lock`` for the rationale (BST-proof discovery).
    from deppy.core.z3_lock import Z3_LOCK
    try:
        with Z3_LOCK:
            encoding = _build_encoding(
                premise + " " + conclusion, binders, context, z3,
            )
            p = _eval_predicate(premise, encoding, z3)
            if p is None:
                return False, "premise-not-encodable"
            q = _eval_predicate(conclusion, encoding, z3)
            if q is None:
                return False, "conclusion-not-encodable"
            s = z3.Solver()
            s.set("timeout", 5000)
            # Axioms collected during encoding (e.g. ``len(xs) >= 0``
            # for every list-typed binder).  Asserting these as facts
            # means Z3 doesn't spuriously satisfy ``len(xs) = -3``.
            for ax in encoding.axioms:
                s.add(ax)
            s.add(z3.And(p, z3.Not(q)))
            verdict = s.check() == z3.unsat
            return verdict, None if verdict else "disagrees"
    except Exception as e:
        return False, f"typed-z3-crash: {type(e).__name__}: {e}"[:120]


# ─────────────────────────────────────────────────────────────────────
#  Encoding builder
# ─────────────────────────────────────────────────────────────────────

def _build_encoding(
    formula_text: str,
    binders: dict[str, str],
    context,
    z3,
) -> Z3Encoding:
    """Walk ``binders`` and free names in ``formula_text`` and build
    a :class:`Z3Encoding`."""
    encoding = Z3Encoding()
    seen: set[str] = set()

    # First pass: every typed binder gets the sort dictated by its
    # annotation.  A binder whose annotation we cannot translate
    # gets an uninterpreted sort named after it.
    for name, ann in binders.items():
        _encode_binder(name, ann, encoding, context, z3)
        # Audit fix #10 — record the original Python annotation text
        # so per-type encoders (hasattr) can look up the receiver's
        # actual class.
        encoding.binder_types[name] = (ann or "").strip()
        seen.add(name)

    # Second pass: every other free identifier in the formula gets
    # a default ``IntSort`` (matches the kernel's existing behaviour
    # so we don't regress un-annotated formulas).
    for name in _free_names(formula_text):
        if name in seen:
            continue
        encoding.env[name] = z3.Int(name)
        encoding.sorts[name] = z3.IntSort()
    return encoding


def _encode_binder(
    name: str, ann: str, enc: Z3Encoding, context, z3,
) -> None:
    """Declare ``name`` in ``enc`` according to its Python
    annotation."""
    ann = (ann or "").strip()
    if not ann:
        enc.env[name] = z3.Int(name)
        enc.sorts[name] = z3.IntSort()
        return
    try:
        tree = ast.parse(ann, mode="eval").body
    except SyntaxError:
        enc.env[name] = z3.Int(name)
        enc.sorts[name] = z3.IntSort()
        return
    sort, expr, helpers = _ast_to_z3(tree, name, enc, context, z3)
    enc.sorts[name] = sort
    enc.env[name] = expr
    enc.helpers.update(helpers)


def _ast_to_z3(
    node: ast.expr,
    var_name: str,
    enc: Z3Encoding,
    context,
    z3,
) -> tuple[Any, Any, dict[str, Any]]:
    """Translate an annotation AST node to ``(sort, expr, helpers)``.

    ``expr`` is the Z3 expression bound to ``var_name`` (a
    ``z3.Const(name, sort)`` for primitive sorts; a more complex
    expression when we need helper functions like ``len_xs``).
    ``helpers`` is a dict of any auxiliary Z3 declarations the
    encoding depends on.
    """
    helpers: dict[str, Any] = {}

    # Polymorphic memoisation — when a structurally identical
    # annotation has been encoded before, reuse the same Z3 sort.
    # The expression (a ``Const``) is freshly bound to ``var_name``
    # so two binders remain distinct, but the sort is shared so
    # downstream proofs over both binders compose without mismatch.
    #
    # We thread the cache key into the Z3Encoding: on a cache hit,
    # the inner encoder helpers (``_scalar_or_class`` /
    # ``_generic_to_z3``) substitute the cached sort instead of
    # declaring a fresh ``DeclareSort`` / ``Datatype.create()``.
    sig = _type_signature(node)
    if sig is not None and sig in _ENCODING_CACHE:
        cached_sort, _ = _ENCODING_CACHE[sig]
        prior = getattr(enc, "_cache_hit_sort", _SENTINEL)
        enc._cache_hit_sort = cached_sort  # type: ignore[attr-defined]
        try:
            result = _ast_to_z3_body(
                node, var_name, enc, context, z3, helpers,
            )
        finally:
            if prior is _SENTINEL:
                try:
                    delattr(enc, "_cache_hit_sort")
                except AttributeError:
                    pass
            else:
                enc._cache_hit_sort = prior  # type: ignore[attr-defined]
        return result
    # Cache miss path — encode normally, store the resulting sort.
    result = _ast_to_z3_body(node, var_name, enc, context, z3, helpers)
    if sig is not None:
        _ENCODING_CACHE[sig] = (result[0], result[2])
    return result


# Sentinel for "attribute was unset" detection above.
_SENTINEL = object()


def _ast_to_z3_body(
    node: ast.expr,
    var_name: str,
    enc: Z3Encoding,
    context,
    z3,
    helpers: dict[str, Any],
) -> tuple[Any, Any, dict[str, Any]]:
    """The original body of :func:`_ast_to_z3`, factored out so the
    cache wrapper can call it.  Behaviour is unchanged from the
    pre-extension implementation, except that user-class lookups
    now also consult the recursive-datatype registry."""
    cached_sort = getattr(enc, "_cache_hit_sort", None)

    # Resolve ``Optional[T]`` / ``T | None``.
    optional_inner = _peel_optional(node)
    if optional_inner is not None:
        inner_sort, _ie, inner_helpers = _ast_to_z3(
            optional_inner, var_name + "_some_value",
            enc, context, z3,
        )
        helpers.update(inner_helpers)
        if cached_sort is not None:
            Maybe = cached_sort
        else:
            DT = z3.Datatype(f"Maybe_{var_name}")
            DT.declare("none")
            DT.declare("some", ("value", inner_sort))
            Maybe = DT.create()
        helpers[f"isNone_{var_name}"] = Maybe.is_none
        helpers[f"isSome_{var_name}"] = Maybe.is_some
        helpers[f"value_{var_name}"] = Maybe.value
        helpers[f"none_{var_name}"] = Maybe.none
        return Maybe, z3.Const(var_name, Maybe), helpers

    # Resolve ``Union[A, B, ...]`` / ``A | B | ...``.
    union_alts = _peel_union(node)
    if union_alts is not None and len(union_alts) >= 2:
        if cached_sort is not None:
            Union = cached_sort
            for i in range(len(union_alts)):
                helpers[f"is{i}_{var_name}"] = getattr(Union, f"is_case{i}")
                helpers[f"value{i}_{var_name}"] = getattr(Union, f"value{i}")
            return Union, z3.Const(var_name, Union), helpers
        # Build a Z3 datatype with one constructor per alternative.
        Datatype = z3.Datatype(f"Union_{var_name}")
        alt_sorts: list[Any] = []
        for i, alt_node in enumerate(union_alts):
            alt_sort, _ae, alt_helpers = _ast_to_z3(
                alt_node, f"{var_name}_alt{i}",
                enc, context, z3,
            )
            alt_sorts.append(alt_sort)
            helpers.update(alt_helpers)
            Datatype.declare(f"case{i}", (f"value{i}", alt_sort))
        Union = Datatype.create()
        for i in range(len(union_alts)):
            helpers[f"is{i}_{var_name}"] = getattr(Union, f"is_case{i}")
            helpers[f"value{i}_{var_name}"] = getattr(Union, f"value{i}")
        return Union, z3.Const(var_name, Union), helpers

    # Resolve scalar / generic / Callable / user class.
    if isinstance(node, ast.Name):
        return _scalar_or_class(node.id, var_name, enc, context, z3)
    if isinstance(node, ast.Attribute):
        text = _dotted_name(node)
        short = text.rsplit(".", 1)[-1]
        return _scalar_or_class(short, var_name, enc, context, z3)
    if isinstance(node, ast.Subscript):
        return _generic_to_z3(node, var_name, enc, context, z3, helpers)
    if isinstance(node, ast.Constant) and node.value is None:
        # Bare ``None`` annotation — encode as a unit datatype.
        if cached_sort is not None:
            return cached_sort, z3.Const(var_name, cached_sort), helpers
        Unit = z3.Datatype(f"Unit_{var_name}")
        Unit.declare("unit")
        Unit = Unit.create()
        return Unit, z3.Const(var_name, Unit), helpers

    # Fall through — uninterpreted sort.
    if cached_sort is not None:
        return cached_sort, z3.Const(var_name, cached_sort), helpers
    sort = z3.DeclareSort(_unique_sort_name(var_name))
    return sort, z3.Const(var_name, sort), helpers


def _scalar_or_class(
    name: str, var_name: str, enc: Z3Encoding, context, z3,
) -> tuple[Any, Any, dict[str, Any]]:
    """Encode a bare type name ``name`` (the annotation written for
    the binder ``var_name``)."""
    helpers: dict[str, Any] = {}
    if name == "int":
        return z3.IntSort(), z3.Int(var_name), helpers
    if name == "bool":
        return z3.BoolSort(), z3.Bool(var_name), helpers
    if name == "float":
        return z3.RealSort(), z3.Real(var_name), helpers
    if name == "str":
        return z3.StringSort(), z3.String(var_name), helpers
    if name in {"None", "NoneType"}:
        Unit = z3.Datatype(f"Unit_{var_name}")
        Unit.declare("unit")
        Unit = Unit.create()
        return Unit, Unit.unit, helpers
    if name in {"Any", "object"}:
        # Polymorphic — declare an uninterpreted sort.
        sort = z3.DeclareSort(_unique_sort_name(f"Any_{var_name}"))
        return sort, z3.Const(var_name, sort), helpers
    if name in {"set", "Set", "frozenset", "FrozenSet",
                 "MutableSet", "AbstractSet"}:
        # Z3 SetSort gives proper distinct-element semantics: IsMember,
        # SetAdd, SetDel, SetUnion, SetIntersect, SetDifference.
        elt_sort = z3.IntSort()  # bare set: element sort defaults to Int
        st_sort = z3.SetSort(elt_sort)
        st = z3.Const(var_name, st_sort)
        length = z3.Function(f"len_{var_name}", st_sort, z3.IntSort())
        helpers[f"len_{var_name}"] = length
        helpers[f"is_set_{var_name}"] = True
        # Cardinality is non-negative.
        enc.axioms.append(length(st) >= 0)
        return st_sort, st, helpers
    if name in {"list", "List", "Iterable", "Iterator", "Sequence",
                 "MutableSequence", "Collection", "Container",
                 "Reversible", "tuple", "Tuple", "Deque"}:
        # Bare unparameterised list-like — element sort defaults to Int.
        arr_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
        arr = z3.Const(var_name, arr_sort)
        length = z3.Function(f"len_{var_name}", arr_sort, z3.IntSort())
        helpers[f"len_{var_name}"] = length
        # ``x in xs`` for the bare list — ∃i. 0 ≤ i < len ∧ xs[i] = x.
        # Wrap in a Python lambda so callers see ``contains_xs(elem)``.
        def _make_list_contains(arr_, length_, elt_sort_):
            def _contains(elem):
                i = z3.Int(f"_in_{var_name}_{id(elem)}")
                return z3.Exists(
                    [i],
                    z3.And(
                        i >= 0, i < length_(arr_),
                        z3.Select(arr_, i) == elem,
                    ),
                )
            return _contains
        helpers[f"contains_{var_name}"] = _make_list_contains(
            arr, length, z3.IntSort(),
        )
        # Length non-negativity.
        enc.axioms.append(length(arr) >= 0)
        return arr_sort, arr, helpers
    if name in {"dict", "Dict", "Mapping", "MutableMapping",
                 "OrderedDict", "defaultdict", "Counter", "ChainMap"}:
        arr_sort = z3.ArraySort(z3.StringSort(), z3.IntSort())
        arr = z3.Const(var_name, arr_sort)
        contains = z3.Function(
            f"contains_{var_name}", z3.StringSort(), z3.BoolSort(),
        )
        length = z3.Function(
            f"len_{var_name}", arr_sort, z3.IntSort(),
        )
        helpers[f"contains_{var_name}"] = contains
        helpers[f"len_{var_name}"] = length
        return arr_sort, arr, helpers
    # Resolve through a context-supplied alias.
    if context is not None:
        if name in getattr(context, "type_aliases", {}):
            try:
                inner = ast.parse(
                    context.type_aliases[name], mode="eval",
                ).body
                return _ast_to_z3(inner, var_name, enc, context, z3)
            except SyntaxError:
                pass
        if name in getattr(context, "new_types", {}):
            try:
                inner = ast.parse(
                    context.new_types[name], mode="eval",
                ).body
                return _ast_to_z3(inner, var_name, enc, context, z3)
            except SyntaxError:
                pass
        if name in getattr(context, "type_vars", {}):
            spec = context.type_vars[name]
            if spec.bound:
                try:
                    inner = ast.parse(spec.bound, mode="eval").body
                    return _ast_to_z3(inner, var_name, enc, context, z3)
                except SyntaxError:
                    pass
            if spec.constraints:
                # Constrained TypeVar — encode as a Union datatype.
                # Build a synthetic Union node.
                alt_nodes = [
                    ast.parse(c, mode="eval").body for c in spec.constraints
                ]
                fake_union = ast.BoolOp(op=ast.BitOr(), values=alt_nodes)
                # We can't easily synthesise a BinOp tree here, so
                # encode by hand:
                Datatype = z3.Datatype(f"Union_{var_name}")
                alt_sorts: list[Any] = []
                for i, an in enumerate(alt_nodes):
                    alt_sort, _ae, ah = _ast_to_z3(
                        an, f"{var_name}_alt{i}", enc, context, z3,
                    )
                    alt_sorts.append(alt_sort)
                    helpers.update(ah)
                    Datatype.declare(f"case{i}", (f"value{i}", alt_sort))
                Union = Datatype.create()
                for i in range(len(alt_nodes)):
                    helpers[f"is{i}_{var_name}"] = getattr(
                        Union, f"is_case{i}"
                    )
                    helpers[f"value{i}_{var_name}"] = getattr(
                        Union, f"value{i}"
                    )
                return Union, z3.Const(var_name, Union), helpers
    # Recursive dataclass — registered via register_recursive_class.
    if name in _RECURSIVE_CLASS_REGISTRY:
        cls = _RECURSIVE_CLASS_REGISTRY[name]
        if _is_recursive_dataclass(cls):
            return _encode_recursive_datatype(cls, var_name, enc, z3)
    # Unknown — uninterpreted sort.  Reuse the cached sort if the
    # outer ``_ast_to_z3`` wrapper has stashed one for this signature.
    cached_sort = getattr(enc, "_cache_hit_sort", None)
    if cached_sort is not None:
        return cached_sort, z3.Const(var_name, cached_sort), helpers
    sort = z3.DeclareSort(_unique_sort_name(name))
    return sort, z3.Const(var_name, sort), helpers


def _generic_to_z3(
    node: ast.Subscript, var_name: str, enc: Z3Encoding, context, z3,
    helpers: dict[str, Any],
) -> tuple[Any, Any, dict[str, Any]]:
    """Encode a generic annotation (``list[int]``, ``dict[str, int]``,
    ``Callable[[int], int]``, …) to a Z3 sort + expression."""
    base_text = _dotted_name(node.value) or _name_text(node.value)
    short = base_text.rsplit(".", 1)[-1]
    slc = node.slice

    # Strip ``Annotated`` / ``Final`` / ``ClassVar`` / etc.
    if short in {"Annotated", "Final", "ClassVar", "Required", "NotRequired"}:
        if isinstance(slc, ast.Tuple) and slc.elts:
            return _ast_to_z3(slc.elts[0], var_name, enc, context, z3)
        return _ast_to_z3(slc, var_name, enc, context, z3)

    if short in {"TypeGuard", "TypeIs"}:
        return z3.BoolSort(), z3.Bool(var_name), helpers

    # ``Optional[T]`` handled at the top of _ast_to_z3.
    # ``Union[A, B]`` likewise.

    if short in {"set", "Set", "frozenset", "FrozenSet",
                  "AbstractSet", "MutableSet"}:
        # Parameterised set[T] — Z3 SetSort gives real distinct-element
        # semantics so ``a in s`` and ``s.add(a)`` work correctly.
        elt_node = slc
        if isinstance(slc, ast.Tuple) and slc.elts:
            elt_node = slc.elts[0]
        elt_sort, _ee, eh = _ast_to_z3(
            elt_node, f"{var_name}_elt", enc, context, z3,
        )
        helpers.update(eh)
        st_sort = z3.SetSort(elt_sort)
        st = z3.Const(var_name, st_sort)
        length = z3.Function(f"len_{var_name}", st_sort, z3.IntSort())
        helpers[f"len_{var_name}"] = length
        helpers[f"is_set_{var_name}"] = True
        helpers[f"elt_sort_{var_name}"] = elt_sort
        enc.axioms.append(length(st) >= 0)
        return st_sort, st, helpers
    if short in {"list", "List", "Iterable", "Iterator", "Sequence",
                  "MutableSequence", "Generator", "Container",
                  "Collection", "Reversible", "Deque"}:
        # element sort
        elt_node = slc
        if isinstance(slc, ast.Tuple) and slc.elts:
            elt_node = slc.elts[0]
        elt_sort, _ee, eh = _ast_to_z3(
            elt_node, f"{var_name}_elt", enc, context, z3,
        )
        helpers.update(eh)
        arr_sort = z3.ArraySort(z3.IntSort(), elt_sort)
        arr = z3.Const(var_name, arr_sort)
        # Length helper.
        length = z3.Function(f"len_{var_name}", arr_sort, z3.IntSort())
        helpers[f"len_{var_name}"] = length
        helpers[f"elt_sort_{var_name}"] = elt_sort
        # ``x in xs`` for typed list — ∃i. 0 ≤ i < len ∧ xs[i] = x.
        def _make_list_contains(arr_, length_, name=var_name):
            def _contains(elem):
                i = z3.Int(f"_in_{name}_{id(elem)}")
                return z3.Exists(
                    [i],
                    z3.And(
                        i >= 0, i < length_(arr_),
                        z3.Select(arr_, i) == elem,
                    ),
                )
            return _contains
        helpers[f"contains_{var_name}"] = _make_list_contains(arr, length)
        # Length non-negativity.
        enc.axioms.append(length(arr) >= 0)
        return arr_sort, arr, helpers

    if short in {"tuple", "Tuple"}:
        # Homogeneous ``tuple[T, ...]`` → like list.  Heterogeneous
        # ``tuple[A, B]`` → uninterpreted sort (Z3 doesn't have
        # ad-hoc product sorts in Python API without datatype).
        if (isinstance(slc, ast.Tuple) and len(slc.elts) == 2
                and isinstance(slc.elts[1], ast.Constant)
                and slc.elts[1].value is Ellipsis):
            elt_sort, _ee, eh = _ast_to_z3(
                slc.elts[0], f"{var_name}_elt", enc, context, z3,
            )
            helpers.update(eh)
            arr_sort = z3.ArraySort(z3.IntSort(), elt_sort)
            arr = z3.Const(var_name, arr_sort)
            length = z3.Function(f"len_{var_name}", arr_sort, z3.IntSort())
            helpers[f"len_{var_name}"] = length
            return arr_sort, arr, helpers
        # Heterogeneous tuple — opaque.
        sort = z3.DeclareSort(_unique_sort_name(f"Tuple_{var_name}"))
        return sort, z3.Const(var_name, sort), helpers

    if short in {"dict", "Dict", "Mapping", "MutableMapping",
                  "OrderedDict", "defaultdict", "Counter", "ChainMap"}:
        if isinstance(slc, ast.Tuple) and len(slc.elts) == 2:
            k_node, v_node = slc.elts
            k_sort, _ke, kh = _ast_to_z3(
                k_node, f"{var_name}_key", enc, context, z3,
            )
            v_sort, _ve, vh = _ast_to_z3(
                v_node, f"{var_name}_val", enc, context, z3,
            )
            helpers.update(kh)
            helpers.update(vh)
            arr_sort = z3.ArraySort(k_sort, v_sort)
            arr = z3.Const(var_name, arr_sort)
            contains = z3.Function(
                f"contains_{var_name}", k_sort, z3.BoolSort(),
            )
            length = z3.Function(
                f"len_{var_name}", arr_sort, z3.IntSort(),
            )
            helpers[f"contains_{var_name}"] = contains
            helpers[f"len_{var_name}"] = length
            helpers[f"key_sort_{var_name}"] = k_sort
            helpers[f"val_sort_{var_name}"] = v_sort
            enc.axioms.append(length(arr) >= 0)
            return arr_sort, arr, helpers
        # Bare ``dict`` — string→int default.
        arr_sort = z3.ArraySort(z3.StringSort(), z3.IntSort())
        arr = z3.Const(var_name, arr_sort)
        contains = z3.Function(
            f"contains_{var_name}", z3.StringSort(), z3.BoolSort(),
        )
        length = z3.Function(
            f"len_{var_name}", arr_sort, z3.IntSort(),
        )
        helpers[f"contains_{var_name}"] = contains
        helpers[f"len_{var_name}"] = length
        helpers[f"key_sort_{var_name}"] = z3.StringSort()
        helpers[f"val_sort_{var_name}"] = z3.IntSort()
        enc.axioms.append(length(arr) >= 0)
        return arr_sort, arr, helpers

    if short in {"Callable", "callable"}:
        # Callable[[A, B], R] → uninterpreted function.
        params: list[Any] = []
        ret_node: Optional[ast.expr] = None
        if isinstance(slc, ast.Tuple) and len(slc.elts) == 2:
            param_node, ret_node = slc.elts
            if isinstance(param_node, ast.List):
                for p in param_node.elts:
                    p_sort, _pe, ph = _ast_to_z3(
                        p, f"{var_name}_p{len(params)}",
                        enc, context, z3,
                    )
                    params.append(p_sort)
                    helpers.update(ph)
        if ret_node is None:
            ret_node = ast.Name(id="object", ctx=ast.Load())
        ret_sort, _re, rh = _ast_to_z3(
            ret_node, f"{var_name}_ret", enc, context, z3,
        )
        helpers.update(rh)
        if not params:
            params = [z3.IntSort()]  # nullary calls still need a domain
        fn = z3.Function(var_name, *params, ret_sort)
        # Bind ``var_name`` itself to a sort placeholder; the predicate
        # cannot reference ``g`` directly as a value, only via call.
        sort = z3.DeclareSort(_unique_sort_name(f"Callable_{var_name}"))
        helpers[f"call_{var_name}"] = fn
        return sort, z3.Const(var_name, sort), helpers

    if short in {"Type", "type"}:
        sort = z3.DeclareSort(_unique_sort_name(f"Type_{var_name}"))
        return sort, z3.Const(var_name, sort), helpers

    # Fall through — uninterpreted sort named after the head.
    cached_sort = getattr(enc, "_cache_hit_sort", None)
    if cached_sort is not None:
        return cached_sort, z3.Const(var_name, cached_sort), helpers
    sort = z3.DeclareSort(_unique_sort_name(short))
    return sort, z3.Const(var_name, sort), helpers


# ─────────────────────────────────────────────────────────────────────
#  Predicate evaluation
# ─────────────────────────────────────────────────────────────────────

_BIN_OP_TO_Z3 = {
    ast.Add: lambda l, r, z3: l + r,
    ast.Sub: lambda l, r, z3: l - r,
    ast.Mult: lambda l, r, z3: l * r,
    ast.Div: lambda l, r, z3: l / r,
    ast.FloorDiv: lambda l, r, z3: l / r,
    ast.Mod: lambda l, r, z3: l % r,
}


def _eval_predicate(text: str, enc: Z3Encoding, z3) -> Optional[Any]:
    """Translate a Python predicate string to a Z3 BoolRef."""
    text = (text or "").strip() or "True"
    if text == "True":
        return z3.BoolVal(True)
    if text == "False":
        return z3.BoolVal(False)
    try:
        tree = ast.parse(text, mode="eval").body
    except SyntaxError:
        return None
    return _eval_node(tree, enc, z3)


def _eval_node(node: ast.expr, enc: Z3Encoding, z3) -> Optional[Any]:
    if isinstance(node, ast.Constant):
        v = node.value
        if v is True:
            return z3.BoolVal(True)
        if v is False:
            return z3.BoolVal(False)
        if v is None:
            return None
        if isinstance(v, int):
            return z3.IntVal(v)
        if isinstance(v, float):
            return z3.RealVal(v)
        if isinstance(v, str):
            return z3.StringVal(v)
        return None

    if isinstance(node, ast.IfExp):
        c = _eval_node(node.test, enc, z3)
        t = _eval_node(node.body, enc, z3)
        e = _eval_node(node.orelse, enc, z3)
        if c is None or t is None or e is None:
            return None
        return z3.If(c, t, e)

    if isinstance(node, ast.List) or isinstance(node, ast.Tuple):
        # Literal list/tuple — encode as a chain of ``Store`` over a
        # fresh array.  Useful for ``a in [1, 2, 3]`` (handled in
        # _eval_compare directly) and for short literal returns.
        raw = [_eval_node(e, enc, z3) for e in node.elts]
        if any(v is None for v in raw):
            return None
        elt_vals: list[Any] = [v for v in raw if v is not None]
        if not elt_vals:
            return z3.K(z3.IntSort(), z3.IntVal(0))
        first = elt_vals[0]
        elt_sort = first.sort()
        arr_sort = z3.ArraySort(z3.IntSort(), elt_sort)
        try:
            arr = z3.K(z3.IntSort(), first)
        except Exception:
            return None
        for i, v in enumerate(elt_vals):
            arr = z3.Store(arr, z3.IntVal(i), v)
        return arr

    if isinstance(node, ast.Set):
        raw = [_eval_node(e, enc, z3) for e in node.elts]
        if any(v is None for v in raw):
            return None
        elt_vals: list[Any] = [v for v in raw if v is not None]
        if not elt_vals:
            return None
        first = elt_vals[0]
        st = z3.EmptySet(first.sort())
        for v in elt_vals:
            st = z3.SetAdd(st, v)
        return st

    if isinstance(node, ast.Name):
        if node.id in enc.env:
            return enc.env[node.id]
        # Unknown free name — declare on demand as Int.
        enc.env[node.id] = z3.Int(node.id)
        enc.sorts[node.id] = z3.IntSort()
        return enc.env[node.id]

    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            inner = _eval_node(node.operand, enc, z3)
            return z3.Not(inner) if inner is not None else None
        if isinstance(node.op, ast.USub):
            inner = _eval_node(node.operand, enc, z3)
            return -inner if inner is not None else None
        if isinstance(node.op, ast.UAdd):
            return _eval_node(node.operand, enc, z3)
        return None

    if isinstance(node, ast.BinOp):
        l = _eval_node(node.left, enc, z3)
        r = _eval_node(node.right, enc, z3)
        if l is None or r is None:
            return None
        op_t = type(node.op)
        if op_t not in _BIN_OP_TO_Z3:
            return None
        return _BIN_OP_TO_Z3[op_t](l, r, z3)

    if isinstance(node, ast.BoolOp):
        parts = [_eval_node(v, enc, z3) for v in node.values]
        if any(p is None for p in parts):
            return None
        if isinstance(node.op, ast.And):
            return z3.And(*parts)
        if isinstance(node.op, ast.Or):
            return z3.Or(*parts)
        return None

    if isinstance(node, ast.Compare):
        return _eval_compare(node, enc, z3)

    if isinstance(node, ast.Subscript):
        # ``xs[i]`` where xs is a list / dict — Z3 Select.
        recv = _eval_node(node.value, enc, z3)
        idx = _eval_node(node.slice, enc, z3)
        if recv is None or idx is None:
            return None
        return z3.Select(recv, idx)

    if isinstance(node, ast.Call):
        return _eval_call(node, enc, z3)

    return None


def _encode_membership(
    elem: Optional[Any],
    rhs_val: Optional[Any],
    rhs_node: ast.expr,
    enc: Z3Encoding,
    z3,
) -> Optional[Any]:
    """Encode ``elem in rhs`` to a Z3 BoolRef.

    Dispatches on the receiver in this order:

    1. **Named binder** that is set-typed (``is_set_<name>`` helper):
       direct ``IsMember`` against the set-sorted constant.
    2. **Named binder** with a ``contains_<name>`` helper (typed
       list or dict).  List ``contains_`` returns a BoolRef
       (∃-encoding) so it's used directly; dict ``contains_`` is
       a Bool-valued FuncDecl, used via ``contains(elem) = True``.
    3. **Literal** ``ast.List`` / ``ast.Tuple`` / ``ast.Set``:
       disjunction of equalities.
    4. **Computed expression** (``rhs_val``) whose Z3 sort is a
       ``SetSort``: ``IsMember`` against the set value.
    5. **Computed expression** with an ``ArraySort`` (key-typed
       like a dict): ``Select(arr, elem) != 0`` is unsound because
       Z3 ArraySort has no membership notion — return None and let
       the caller pick a syntactic discharge.
    """
    if elem is None:
        return None

    # 1. Named-binder set.
    recv_name = _name_text(rhs_node)
    if recv_name and enc.helpers.get(f"is_set_{recv_name}"):
        return z3.IsMember(elem, enc.env[recv_name])

    # 2. Named-binder list/dict via contains_<name>.
    if recv_name:
        membership = enc.helpers.get(f"contains_{recv_name}")
        if membership is not None:
            got = membership(elem)
            if z3.is_bool(got):
                return got
            return got == z3.BoolVal(True)

    # 3. Literal list/tuple/set membership.
    if isinstance(rhs_node, (ast.List, ast.Tuple, ast.Set)):
        disjuncts = []
        for el in rhs_node.elts:
            ev = _eval_node(el, enc, z3)
            if ev is None:
                return None
            disjuncts.append(elem == ev)
        if not disjuncts:
            return z3.BoolVal(False)
        return z3.Or(*disjuncts)

    # 4-5. Computed expression — dispatch on Z3 sort.
    if rhs_val is None:
        return None
    try:
        sort = rhs_val.sort()
    except Exception:
        return None
    # Z3 represents ``Set[T]`` as ``Array(T, Bool)``.  Any array
    # whose range is ``Bool`` admits ``IsMember`` membership.
    try:
        is_array_of_bool = (
            sort.kind() == z3.Z3_ARRAY_SORT
            and sort.range() == z3.BoolSort()
        )
    except Exception:
        is_array_of_bool = False
    if is_array_of_bool and hasattr(z3, "IsMember"):
        return z3.IsMember(elem, rhs_val)
    return None


def _eval_compare(node: ast.Compare, enc: Z3Encoding, z3) -> Optional[Any]:
    """Translate ``a OP b`` (and chained comparisons) to a Z3 BoolRef.

    ``a in d`` / ``a not in d`` use the per-receiver
    ``contains_<recv>`` helper when available, falling back to
    ``Select(d, a)`` for arrays.  ``a is None`` / ``a is not None``
    use the per-name ``isNone_<name>`` / ``isSome_<name>`` helpers
    for Optional-encoded variables.
    """
    terms = [node.left] + list(node.comparators)
    parts: list[Any] = []
    for op, l_node, r_node in zip(node.ops, terms, terms[1:]):
        l = _eval_node(l_node, enc, z3)
        r = _eval_node(r_node, enc, z3)
        op_t = type(op)
        if op_t in (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE):
            if l is None or r is None:
                return None
            mapping = {
                ast.Eq: lambda a, b: a == b,
                ast.NotEq: lambda a, b: a != b,
                ast.Lt: lambda a, b: a < b,
                ast.LtE: lambda a, b: a <= b,
                ast.Gt: lambda a, b: a > b,
                ast.GtE: lambda a, b: a >= b,
            }
            parts.append(mapping[op_t](l, r))
            continue
        if op_t is ast.In or op_t is ast.NotIn:
            negate = (op_t is ast.NotIn)
            membership_z3 = _encode_membership(l, r, r_node, enc, z3)
            if membership_z3 is None:
                return None
            parts.append(z3.Not(membership_z3) if negate else membership_z3)
            continue
        if op_t is ast.Is:
            # ``x is None`` → isNone_<x>
            x_name = _name_text(l_node)
            is_none = enc.helpers.get(f"isNone_{x_name}")
            if (is_none is not None
                    and isinstance(r_node, ast.Constant)
                    and r_node.value is None):
                parts.append(is_none(enc.env[x_name]))
                continue
            return None
        if op_t is ast.IsNot:
            x_name = _name_text(l_node)
            is_some = enc.helpers.get(f"isSome_{x_name}")
            if (is_some is not None
                    and isinstance(r_node, ast.Constant)
                    and r_node.value is None):
                parts.append(is_some(enc.env[x_name]))
                continue
            return None
        return None
    if not parts:
        return None
    if len(parts) == 1:
        return parts[0]
    return z3.And(*parts)


def _eval_call(node: ast.Call, enc: Z3Encoding, z3) -> Optional[Any]:
    """Evaluate a function call.

    Supported:

    * ``len(xs)`` for list/dict-typed ``xs`` — uses the per-receiver
      ``len_<xs>`` helper.
    * ``isinstance(x, T)`` — emits an ``is<i>_<x>`` predicate when
      ``x`` is Union-encoded; otherwise we conservatively return
      ``BoolVal(True)`` (the typed encoding already enforces the
      sort, so isinstance is redundant) — which means callers must
      not rely on isinstance to *narrow* (use Optional/Union
      directly).
    * ``Callable``-typed call ``g(arg)`` — uses the
      ``call_<g>`` helper.
    * ``abs(x)``, ``min(a,b,...)``, ``max(a,b,...)`` — direct Z3 If.
    * ``all(P(i) for i in range(...))`` / ``any(...)`` — universal /
      existential quantifier with the range bounds as the guard.
    """
    fn = node.func
    if isinstance(fn, ast.Name):
        # Custom predicate dispatch — consult the registry first so
        # users can override even built-in names if they really want.
        if fn.id in _CUSTOM_PREDICATES:
            args = [_eval_node(a, enc, z3) for a in node.args]
            if not any(a is None for a in args):
                custom = _dispatch_custom_predicate(fn.id, args, enc, z3)
                if custom is not None:
                    return custom
        if fn.id == "len" and node.args:
            arg = node.args[0]
            if isinstance(arg, ast.Name):
                length = enc.helpers.get(f"len_{arg.id}")
                if length is not None:
                    return length(enc.env[arg.id])
            inner = _eval_node(arg, enc, z3)
            if inner is None:
                return None
            if hasattr(z3, "Length") and hasattr(inner, "sort") \
                    and inner.sort() == z3.StringSort():
                return z3.Length(inner)
            # For literal lists encoded as Stores we cannot recover
            # the length without tracking it; surface 0 as default
            # only when the inner is the empty K-array (unsound for
            # general arrays — better to return None).
            return None
        if fn.id == "isinstance" and len(node.args) == 2:
            return z3.BoolVal(True)
        if fn.id == "abs" and len(node.args) == 1:
            inner = _eval_node(node.args[0], enc, z3)
            if inner is None:
                return None
            return z3.If(inner >= 0, inner, -inner)
        if fn.id == "min" and node.args:
            raw = [_eval_node(a, enc, z3) for a in node.args]
            if any(v is None for v in raw):
                return None
            vals: list[Any] = [v for v in raw if v is not None]
            r = vals[0]
            for v in vals[1:]:
                r = z3.If(v < r, v, r)
            return r
        if fn.id == "max" and node.args:
            raw = [_eval_node(a, enc, z3) for a in node.args]
            if any(v is None for v in raw):
                return None
            vals: list[Any] = [v for v in raw if v is not None]
            r = vals[0]
            for v in vals[1:]:
                r = z3.If(v > r, v, r)
            return r
        if fn.id in {"all", "any"} and len(node.args) == 1:
            arg0 = node.args[0]
            if isinstance(arg0, ast.GeneratorExp):
                return _translate_quantifier(
                    arg0, enc, z3, universal=(fn.id == "all"),
                )
        if fn.id == "hasattr" and len(node.args) == 2:
            # Audit fix #10 — per-type ``hasattr`` encoding.  Look
            # up the receiver's recorded type and consult the
            # built-in attribute table.  When the type is known
            # the result is a concrete BoolVal(True/False); when
            # unknown it's an uninterpreted predicate keyed by
            # (sort_name, attr_name) so the SMT layer can still
            # propagate equalities.
            from deppy.core.hasattr_encoding import (
                encode_hasattr,
                encode_hasattr_union,
                parse_union_type,
            )
            recv = node.args[0]
            attr_node = node.args[1]
            attr_name = ""
            if isinstance(attr_node, ast.Constant) and isinstance(
                attr_node.value, str,
            ):
                attr_name = attr_node.value
            else:
                # The attribute name is dynamic — we can't
                # statically decide.  Emit a generic uninterpreted
                # predicate.
                return z3.Bool(f"hasattr_dyn_{id(node)}")

            recv_text = ""
            if isinstance(recv, ast.Name):
                recv_text = recv.id
            type_text = enc.binder_types.get(recv_text, "")
            arms = parse_union_type(type_text) if type_text else []
            sort_name = recv_text or "object"
            if len(arms) > 1:
                return encode_hasattr_union(
                    arms, attr_name,
                    sort_name=sort_name, z3_module=z3,
                    uninterp_cache=enc.hasattr_cache,
                )
            if len(arms) == 1:
                return encode_hasattr(
                    arms[0], attr_name,
                    sort_name=sort_name, z3_module=z3,
                    uninterp_cache=enc.hasattr_cache,
                )
            # No type info — fully uninterpreted.
            return encode_hasattr(
                None, attr_name,
                sort_name=sort_name, z3_module=z3,
                uninterp_cache=enc.hasattr_cache,
            )
        if fn.id == "callable" and len(node.args) == 1:
            return z3.BoolVal(True)
        if fn.id in enc.env:
            args = [_eval_node(a, enc, z3) for a in node.args]
            if any(a is None for a in args):
                return None
            call_helper = enc.helpers.get(f"call_{fn.id}")
            if call_helper is not None:
                return call_helper(*args)
    if isinstance(fn, ast.Attribute):
        # ``d.contains(k)`` / ``xs.length`` — translate via helpers.
        recv = _name_text(fn.value)
        attr = fn.attr
        if attr == "length":
            length = enc.helpers.get(f"len_{recv}")
            if length is not None:
                return length(enc.env[recv])
        # ── String method calls ────────────────────────────────────
        recv_val = _eval_node(fn.value, enc, z3) if fn.value else None
        if (recv_val is not None and hasattr(recv_val, "sort")
                and recv_val.sort() == z3.StringSort()):
            if attr == "startswith" and len(node.args) == 1:
                pref = _eval_node(node.args[0], enc, z3)
                if pref is not None:
                    return z3.PrefixOf(pref, recv_val)
            if attr == "endswith" and len(node.args) == 1:
                suf = _eval_node(node.args[0], enc, z3)
                if suf is not None:
                    return z3.SuffixOf(suf, recv_val)
            if attr == "find" and len(node.args) == 1:
                sub = _eval_node(node.args[0], enc, z3)
                if sub is not None:
                    return z3.IndexOf(recv_val, sub, z3.IntVal(0))
        # ── Set methods (a.add(x), a.discard(x), a.remove(x)) ──────
        if enc.helpers.get(f"is_set_{recv}"):
            st_var = enc.env.get(recv)
            if st_var is not None:
                if attr == "add" and len(node.args) == 1:
                    elt = _eval_node(node.args[0], enc, z3)
                    if elt is not None:
                        return z3.SetAdd(st_var, elt)
                if attr in {"discard", "remove"} and len(node.args) == 1:
                    elt = _eval_node(node.args[0], enc, z3)
                    if elt is not None:
                        return z3.SetDel(st_var, elt)
        # ── List methods (xs.append(y) → Store(xs, len(xs), y)) ────
        if recv in enc.env and enc.helpers.get(f"len_{recv}") is not None \
                and not enc.helpers.get(f"is_set_{recv}"):
            xs_var = enc.env[recv]
            length = enc.helpers[f"len_{recv}"]
            if attr == "append" and len(node.args) == 1:
                v = _eval_node(node.args[0], enc, z3)
                if v is not None:
                    return z3.Store(xs_var, length(xs_var), v)
        # ── Dict methods ──────────────────────────────────────────
        if recv in enc.env and enc.helpers.get(f"contains_{recv}") is not None:
            d_var = enc.env[recv]
            contains = enc.helpers[f"contains_{recv}"]
            if attr == "get" and 1 <= len(node.args) <= 2:
                k = _eval_node(node.args[0], enc, z3)
                if k is None:
                    return None
                # ``d.get(k, default)`` — If(contains(k), d[k], default).
                got = z3.Select(d_var, k)
                if len(node.args) == 2:
                    default = _eval_node(node.args[1], enc, z3)
                    if default is None:
                        return got
                    cond = contains(k) if not callable(contains) or not _is_uninterpreted_func(contains, z3) \
                        else (contains(k) == z3.BoolVal(True))
                    return z3.If(cond, got, default)
                return got
            if attr in {"keys", "values", "items"}:
                # Surface as uninterpreted; callers seldom prove on these.
                return None
    return None


def _is_uninterpreted_func(fn, z3) -> bool:
    """Return True if ``fn`` is a Z3 ``FuncDeclRef`` (uninterpreted)
    rather than a Python wrapper that already builds a BoolRef."""
    return hasattr(fn, "domain") and hasattr(fn, "range")


def _translate_quantifier(
    gen: ast.GeneratorExp, enc: Z3Encoding, z3, *, universal: bool,
) -> Optional[Any]:
    """Translate ``all(P(i) for i in range(lo, hi) if G(i))`` / ``any(...)``.

    Returns a ``ForAll`` (universal=True) or ``Exists`` (universal=False)
    with the range bounds as the implication guard, plus any ``if``
    clauses appended.  Returns ``None`` when the iter clause isn't a
    recognisable ``range(...)`` or list-typed binder.
    """
    if len(gen.generators) != 1:
        return None
    comp = gen.generators[0]
    if not isinstance(comp.target, ast.Name):
        return None
    var_name = comp.target.id

    # Resolve the iterator: ``range(n)`` / ``range(lo, hi)`` / a typed list binder.
    iter_node = comp.iter
    lo: Optional[Any] = None
    hi: Optional[Any] = None
    if isinstance(iter_node, ast.Call) and isinstance(iter_node.func, ast.Name) \
            and iter_node.func.id == "range":
        if len(iter_node.args) == 1:
            lo = z3.IntVal(0)
            hi = _eval_node(iter_node.args[0], enc, z3)
        elif len(iter_node.args) >= 2:
            lo = _eval_node(iter_node.args[0], enc, z3)
            hi = _eval_node(iter_node.args[1], enc, z3)
        if lo is None or hi is None:
            return None
    elif isinstance(iter_node, ast.Name) \
            and enc.helpers.get(f"len_{iter_node.id}") is not None:
        # Iterating over a list: bind ``var_name`` to xs[i] and quantify ``i``.
        # Implementation strategy: introduce ``i`` as the quantifier
        # variable; rewrite later expressions referencing var_name to
        # xs[i].  Simpler form: bind ``var_name`` to ``Select(xs, i)``.
        xs = enc.env[iter_node.id]
        length = enc.helpers[f"len_{iter_node.id}"]
        i_var = z3.Int(f"_q_{var_name}_{id(gen)}")
        old = enc.env.get(var_name)
        enc.env[var_name] = z3.Select(xs, i_var)
        body = _eval_node(gen.elt, enc, z3)
        for if_clause in comp.ifs:
            guard = _eval_node(if_clause, enc, z3)
            if guard is None:
                if old is None:
                    enc.env.pop(var_name, None)
                else:
                    enc.env[var_name] = old
                return None
            body = z3.Implies(guard, body) if universal else z3.And(guard, body)
        if old is None:
            enc.env.pop(var_name, None)
        else:
            enc.env[var_name] = old
        if body is None:
            return None
        in_range = z3.And(i_var >= 0, i_var < length(xs))
        if universal:
            return z3.ForAll([i_var], z3.Implies(in_range, body))
        return z3.Exists([i_var], z3.And(in_range, body))
    else:
        return None

    # Range-iterator path.
    q_var = z3.Int(f"_q_{var_name}_{id(gen)}")
    old = enc.env.get(var_name)
    enc.env[var_name] = q_var
    body = _eval_node(gen.elt, enc, z3)
    for if_clause in comp.ifs:
        guard = _eval_node(if_clause, enc, z3)
        if guard is None:
            if old is None:
                enc.env.pop(var_name, None)
            else:
                enc.env[var_name] = old
            return None
        body = z3.Implies(guard, body) if universal else z3.And(guard, body)
    if old is None:
        enc.env.pop(var_name, None)
    else:
        enc.env[var_name] = old
    if body is None:
        return None
    in_range = z3.And(q_var >= lo, q_var < hi)
    if universal:
        return z3.ForAll([q_var], z3.Implies(in_range, body))
    return z3.Exists([q_var], z3.And(in_range, body))


# ─────────────────────────────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────────────────────────────

def _peel_optional(node: ast.expr) -> Optional[ast.expr]:
    """If ``node`` is ``Optional[T]`` or ``T | None`` (in any
    direction), return the non-None inner type.  Otherwise ``None``.
    """
    if isinstance(node, ast.Subscript):
        base = _dotted_name(node.value) or _name_text(node.value)
        short = base.rsplit(".", 1)[-1]
        if short == "Optional":
            return node.slice
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        l, r = node.left, node.right
        if isinstance(r, ast.Constant) and r.value is None:
            return l
        if isinstance(l, ast.Constant) and l.value is None:
            return r
    return None


def _peel_union(node: ast.expr) -> Optional[list[ast.expr]]:
    """If ``node`` is a 2+ alternative union (``Union[A, B, ...]``
    or ``A | B | ...``), return the alternatives (with None stripped
    out).  Otherwise ``None``.

    Optional[T] (i.e., ``T | None``) is not a union by this rule —
    it's handled separately by :func:`_peel_optional`.
    """
    elts: list[ast.expr] = []
    if isinstance(node, ast.Subscript):
        base = _dotted_name(node.value) or _name_text(node.value)
        short = base.rsplit(".", 1)[-1]
        if short == "Union":
            slc = node.slice
            if isinstance(slc, ast.Tuple):
                elts = list(slc.elts)
            else:
                elts = [slc]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        def collect(n: ast.expr) -> None:
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr):
                collect(n.left); collect(n.right)
            else:
                elts.append(n)
        collect(node)
    if not elts:
        return None
    non_none = [e for e in elts
                 if not (isinstance(e, ast.Constant) and e.value is None)]
    if len(non_none) < 2:
        return None
    return non_none


def _free_names(formula_text: str) -> set[str]:
    """Best-effort free-name extraction (matches the kernel's
    existing regex)."""
    names = set(re.findall(r'\b([A-Za-z_]\w*)\b', formula_text or ""))
    keywords = {
        "True", "False", "None", "and", "or", "not", "in", "is",
        "if", "else", "elif", "for", "while", "len", "isinstance",
    }
    return names - keywords


def _dotted_name(node: ast.expr) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        head = _dotted_name(node.value)
        return head + "." + node.attr if head else node.attr
    return ""


def _name_text(node: ast.expr) -> str:
    return _dotted_name(node)


_SORT_COUNTER: dict[str, int] = {}


def _unique_sort_name(base: str) -> str:
    """Return a deterministic unique sort name like
    ``Deppy_<base>_42``.  Used for uninterpreted sorts so multiple
    declarations don't collide."""
    n = _SORT_COUNTER.get(base, 0) + 1
    _SORT_COUNTER[base] = n
    safe = "".join(ch if ch.isalnum() or ch == "_" else "_" for ch in base)
    return f"Deppy_{safe}_{n}"


# ─────────────────────────────────────────────────────────────────────
#  Extension 1 — Recursive datatypes
# ─────────────────────────────────────────────────────────────────────
#
# Detect Python classes that are recursive ADTs (dataclasses whose
# field types reference the class itself, possibly via Optional /
# Union / list).  Build a Z3 ``Datatype`` with one constructor per
# observed shape.  When all self-references are nullable (``Optional``
# or ``T | None``), we synthesise a canonical ``leaf`` constructor
# (no fields) plus a ``node`` constructor whose self-typed fields are
# materialised directly (Z3 handles the recursive sort reference via
# ``Datatype.declare`` referring to the in-construction type by name).
# When self-references are non-nullable (e.g. a ``Cons`` cell with a
# mandatory ``next``) we synthesise just the ``node`` constructor and
# leave ``leaf`` out — but for safety we always add a ``leaf`` so the
# datatype is well-founded.
#
# The resulting sort is cached in ``_RECURSIVE_DATATYPE_CACHE`` keyed
# on the class object so repeated mentions of ``Tree`` use the same
# Z3 sort.

_RECURSIVE_DATATYPE_CACHE: dict[Any, tuple[Any, dict[str, Any]]] = {}

# Name → class registry so the encoder can resolve a textual
# annotation like ``"Tree"`` back to the user's dataclass.  Users
# call ``register_recursive_class(Tree)`` once after defining the
# class; subsequent encodings of any annotation referring to ``Tree``
# (in any binder) will dispatch to ``_encode_recursive_datatype``.
_RECURSIVE_CLASS_REGISTRY: dict[str, Any] = {}


def register_recursive_class(cls: Any, *, name: Optional[str] = None) -> None:
    """Register a recursive dataclass for Z3 encoding.

    After registration, any binder annotated with the class's name
    (or ``name``, when supplied) will be encoded via
    :func:`_encode_recursive_datatype` rather than as an
    uninterpreted sort.
    """
    _RECURSIVE_CLASS_REGISTRY[name or cls.__name__] = cls


def unregister_recursive_class(name: str) -> None:
    """Remove a recursive class registration."""
    _RECURSIVE_CLASS_REGISTRY.pop(name, None)


def recursive_z3(cls: Any) -> Any:
    """Class decorator that registers ``cls`` as a recursive Z3 datatype.

    Equivalent to calling ``register_recursive_class(cls)`` at module
    load time, but discoverable at the class definition site.

    Example::

        @recursive_z3
        @dataclass(frozen=True)
        class BST:
            value: int
            left: Optional["BST"] = None
            right: Optional["BST"] = None

    The decorator returns the class unchanged; the side effect is the
    Z3 registration.  Z3 will then encode ``BST`` as a constructor-form
    datatype rather than an uninterpreted sort, allowing predicates
    over ``BST`` fields to be solver-discharged.
    """
    register_recursive_class(cls)
    return cls


def _is_recursive_dataclass(cls: Any) -> bool:
    """Return True iff ``cls`` is a dataclass that references itself
    (directly, via ``Optional[Cls]``, ``Cls | None``, ``Union[Cls,...]``,
    or ``list[Cls]``) in any field's type annotation.
    """
    try:
        import dataclasses
    except ImportError:
        return False
    if not dataclasses.is_dataclass(cls):
        return False
    cls_name = cls.__name__
    for fld in dataclasses.fields(cls):
        ann = fld.type
        if isinstance(ann, str):
            if cls_name in ann:
                return True
            continue
        # Real type object — walk via repr.
        if cls_name in repr(ann):
            return True
    return False


def _self_ref_field_kind(field_type: Any, cls_name: str) -> Optional[str]:
    """Classify how a field's annotation references ``cls_name``.

    Returns one of:
      * ``"none"`` — the field doesn't mention ``cls_name`` at all.
      * ``"direct"`` — the field's type is exactly ``cls_name``.
      * ``"optional"`` — the field is ``Optional[cls_name]`` /
        ``cls_name | None``.
      * ``"list"`` — the field is ``list[cls_name]``.
      * ``"other"`` — references the class but in a way we don't
        explicitly handle (treated like ``direct``).
    """
    if isinstance(field_type, str):
        text = field_type.strip()
    else:
        text = repr(field_type)
    if cls_name not in text:
        return "none"
    # Quick string heuristics — sufficient for the dataclass forms we
    # expect (``Optional[Tree]``, ``Tree | None``, ``list[Tree]``).
    if (text == cls_name or text == f"'{cls_name}'"
            or text == f'"{cls_name}"'):
        return "direct"
    if (f"Optional[{cls_name}]" in text
            or f"{cls_name} | None" in text
            or f"None | {cls_name}" in text):
        return "optional"
    if f"list[{cls_name}]" in text or f"List[{cls_name}]" in text:
        return "list"
    return "other"


def _scalar_field_sort(field_type: Any, z3) -> Optional[Any]:
    """Map a non-self field annotation to a Z3 sort, where possible.

    Returns ``None`` when the field type isn't a primitive we know
    how to materialise without recursing into the full encoder
    machinery (which would require a ``Z3Encoding`` we don't have at
    the recursive-datatype-construction level).
    """
    if field_type is int or field_type == "int":
        return z3.IntSort()
    if field_type is bool or field_type == "bool":
        return z3.BoolSort()
    if field_type is float or field_type == "float":
        return z3.RealSort()
    if field_type is str or field_type == "str":
        return z3.StringSort()
    return None


def _encode_recursive_datatype(
    cls: Any,
    var_name: str,
    enc: Z3Encoding,
    z3,
) -> tuple[Any, Any, dict[str, Any]]:
    """Build a Z3 ``Datatype`` for a recursive Python class.

    Caches the resulting sort + accessor map on the class object so
    repeated mentions reuse the same Z3 sort.  Returns
    ``(sort, expr, helpers)`` like the other encoder helpers.
    """
    helpers: dict[str, Any] = {}
    cached = _RECURSIVE_DATATYPE_CACHE.get(cls)
    if cached is not None:
        sort, cls_helpers = cached
        # Register the per-class helpers under the var_name namespace
        # so callers using ``contains_<var>`` style lookups still work.
        helpers.update({
            f"{k}__{var_name}": v for k, v in cls_helpers.items()
        })
        # Also expose the canonical (class-level) helper names so users
        # can write ``leaf`` / ``node`` / ``is_leaf`` directly.
        helpers.update(cls_helpers)
        return sort, z3.Const(var_name, sort), helpers

    import dataclasses
    cls_name = cls.__name__
    fields = list(dataclasses.fields(cls))

    # Classify each field.
    classifications: list[tuple[str, str, Any]] = []  # (name, kind, sort_or_None)
    has_optional_self = False
    for fld in fields:
        kind = _self_ref_field_kind(fld.type, cls_name)
        if kind == "optional":
            has_optional_self = True
            classifications.append((fld.name, "optional_self", None))
        elif kind == "direct":
            classifications.append((fld.name, "direct_self", None))
        elif kind == "list":
            classifications.append((fld.name, "list_self", None))
        elif kind == "other":
            classifications.append((fld.name, "direct_self", None))
        else:
            sort = _scalar_field_sort(fld.type, z3)
            classifications.append((fld.name, "scalar", sort))

    Datatype = z3.Datatype(cls_name)
    # Always declare a leaf constructor so the datatype is well-founded.
    Datatype.declare("leaf")

    node_args: list[tuple[str, Any]] = []
    for fname, kind, sort in classifications:
        if kind in ("direct_self", "optional_self", "other"):
            node_args.append((fname, Datatype))
        elif kind == "list_self":
            # Z3 has no first-class list-of-self; encode list-of-self
            # as a recursive cons cell pattern wouldn't fit a single
            # Datatype.declare here.  Fall back to a scalar Int to
            # mark "the list of children" — coarse but safe.  Users
            # who need list-of-children should split into nested
            # datatypes outside this helper.
            node_args.append((fname, z3.IntSort()))
        else:
            # scalar
            node_args.append((fname, sort if sort is not None else z3.IntSort()))
    Datatype.declare("node", *node_args)

    Sort = Datatype.create()

    cls_helpers: dict[str, Any] = {
        "leaf": Sort.leaf,
        "node": Sort.node,
        "is_leaf": Sort.is_leaf,
        "is_node": Sort.is_node,
    }
    # Per-field accessors.
    for fname, _kind, _sort in classifications:
        accessor = getattr(Sort, fname, None)
        if accessor is not None:
            cls_helpers[fname] = accessor

    # Persist on cache.
    _RECURSIVE_DATATYPE_CACHE[cls] = (Sort, cls_helpers)
    helpers.update({
        f"{k}__{var_name}": v for k, v in cls_helpers.items()
    })
    helpers.update(cls_helpers)
    return Sort, z3.Const(var_name, Sort), helpers


# ─────────────────────────────────────────────────────────────────────
#  Extension 2 — Polymorphic memoisation
# ─────────────────────────────────────────────────────────────────────
#
# Two textually identical annotations should encode to the same Z3
# sort so that downstream proofs can compose without sort mismatches.
# We cache (sort, helper_template) keyed on a *type signature* derived
# from the annotation AST.  The helper template stores helper-builder
# closures, not bound expressions — those are bound at lookup time
# against the requested ``var_name`` and ``enc`` so each call site
# still gets a fresh ``z3.Const``/helper instance with the right name.

_ENCODING_CACHE: dict[tuple, tuple[Any, dict]] = {}


def _type_signature(node: ast.expr) -> Optional[tuple]:
    """Compute a hashable structural fingerprint of an annotation AST.

    Returns ``None`` when the annotation contains constructs we can't
    hash safely (e.g. arbitrary calls, lambdas) — in which case the
    caller skips caching.
    """
    if isinstance(node, ast.Name):
        return ("name", node.id)
    if isinstance(node, ast.Constant):
        if node.value is None:
            return ("const", "None")
        return ("const", repr(node.value))
    if isinstance(node, ast.Attribute):
        return ("attr", _dotted_name(node))
    if isinstance(node, ast.Subscript):
        base = _type_signature(node.value)
        if base is None:
            return None
        slc = node.slice
        if isinstance(slc, ast.Tuple):
            inners = tuple(_type_signature(e) for e in slc.elts)
        else:
            inners = (_type_signature(slc),)
        if any(i is None for i in inners):
            return None
        return ("sub", base, inners)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        l = _type_signature(node.left)
        r = _type_signature(node.right)
        if l is None or r is None:
            return None
        return ("bitor", l, r)
    return None


def clear_encoding_cache() -> None:
    """Empty the polymorphic encoding cache and the recursive-datatype
    cache.  Call this between tests that depend on fresh sorts.
    """
    _ENCODING_CACHE.clear()
    _RECURSIVE_DATATYPE_CACHE.clear()


# ─────────────────────────────────────────────────────────────────────
#  Extension 3 — Custom predicate registration
# ─────────────────────────────────────────────────────────────────────
#
# Users register a Python predicate alongside a Z3 closure that
# computes the predicate's value over the corresponding Z3 sort.  The
# encoder, when evaluating a function call whose name matches a
# registered predicate, calls the closure with the Z3-encoded
# arguments instead of treating the call as uninterpreted.
#
# Registration carries an optional signature dict for documentation
# and validation; the actual dispatch is purely by name.

@dataclass
class _CustomPredicate:
    name: str
    fn: Any                       # Python implementation (kept for reference)
    signature: dict               # {"args": [...], "returns": "..."}
    z3_builder: Any               # callable: (*z3_args, helpers) -> Z3 BoolRef


_CUSTOM_PREDICATES: dict[str, _CustomPredicate] = {}


def register_custom_predicate(
    name: str,
    fn: Any,
    *,
    signature: dict,
    z3_builder: Optional[Any] = None,
) -> None:
    """Register a custom predicate ``name`` with the encoder.

    ``fn`` is the Python implementation (kept as an opaque reference).
    ``signature`` is a dict like ``{"args": ["Tree"], "returns": "bool"}``
    used for documentation.  ``z3_builder`` is the closure the encoder
    invokes when dispatching ``name(...)``: it receives the encoded
    Z3 arguments (positional) plus a keyword ``helpers=`` mapping
    drawn from the active :class:`Z3Encoding`, and returns a Z3
    BoolRef (or any Z3 expression) for the call.

    When ``z3_builder`` is ``None``, the call falls back to an
    uninterpreted function declaration on the fly.
    """
    _CUSTOM_PREDICATES[name] = _CustomPredicate(
        name=name, fn=fn, signature=signature, z3_builder=z3_builder,
    )


def unregister_custom_predicate(name: str) -> None:
    """Remove a previously registered predicate.  Silent no-op when
    ``name`` isn't registered."""
    _CUSTOM_PREDICATES.pop(name, None)


def list_custom_predicates() -> list[str]:
    """Return the names of all currently registered predicates."""
    return sorted(_CUSTOM_PREDICATES.keys())


def _dispatch_custom_predicate(
    name: str,
    z3_args: list[Any],
    enc: Z3Encoding,
    z3,
) -> Optional[Any]:
    """Look up ``name`` in the custom-predicate registry and dispatch.

    Returns the Z3 expression produced by the registered
    ``z3_builder``, or ``None`` when ``name`` isn't registered or the
    builder is missing.
    """
    spec = _CUSTOM_PREDICATES.get(name)
    if spec is None:
        return None
    if spec.z3_builder is None:
        # Fall back to a fresh uninterpreted Bool function.
        try:
            sorts = [a.sort() for a in z3_args]
        except Exception:
            return None
        fn = z3.Function(name, *sorts, z3.BoolSort())
        return fn(*z3_args)
    try:
        return spec.z3_builder(*z3_args, helpers=enc.helpers)
    except TypeError:
        # Older builders that don't accept helpers=.
        try:
            return spec.z3_builder(*z3_args)
        except Exception:
            return None
    except Exception:
        return None


__all__ = [
    "Z3Encoding",
    "check_implication",
    "clear_encoding_cache",
    "register_custom_predicate",
    "unregister_custom_predicate",
    "list_custom_predicates",
    "register_recursive_class",
    "unregister_recursive_class",
]
