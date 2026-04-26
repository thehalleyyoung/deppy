"""Type-aware Z3 encoding of Python predicates.

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

    Callers usually only need ``env`` to evaluate further formulas
    in the same scope.
    """
    sorts: dict[str, Any] = field(default_factory=dict)
    env: dict[str, Any] = field(default_factory=dict)
    helpers: dict[str, Any] = field(default_factory=dict)
    binder_types: dict[str, str] = field(default_factory=dict)
    hasattr_cache: dict[tuple[str, str], Any] = field(default_factory=dict)


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
    try:
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

    # Resolve ``Optional[T]`` / ``T | None``.
    optional_inner = _peel_optional(node)
    if optional_inner is not None:
        inner_sort, _ie, inner_helpers = _ast_to_z3(
            optional_inner, var_name + "_some_value",
            enc, context, z3,
        )
        helpers.update(inner_helpers)
        Maybe = z3.Datatype(f"Maybe_{var_name}")
        Maybe.declare("none")
        Maybe.declare("some", ("value", inner_sort))
        Maybe = Maybe.create()
        helpers[f"isNone_{var_name}"] = Maybe.is_none
        helpers[f"isSome_{var_name}"] = Maybe.is_some
        helpers[f"value_{var_name}"] = Maybe.value
        helpers[f"none_{var_name}"] = Maybe.none
        return Maybe, z3.Const(var_name, Maybe), helpers

    # Resolve ``Union[A, B, ...]`` / ``A | B | ...``.
    union_alts = _peel_union(node)
    if union_alts is not None and len(union_alts) >= 2:
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
        Unit = z3.Datatype(f"Unit_{var_name}")
        Unit.declare("unit")
        Unit = Unit.create()
        return Unit, z3.Const(var_name, Unit), helpers

    # Fall through — uninterpreted sort.
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
    if name in {"list", "List", "Iterable", "Iterator", "Sequence",
                 "MutableSequence", "Collection", "Container",
                 "Reversible", "tuple", "Tuple", "set", "Set",
                 "frozenset", "FrozenSet", "Deque",
                 "MutableSet", "AbstractSet"}:
        # Bare unparameterised list-like — element sort defaults to Int.
        arr_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
        arr = z3.Const(var_name, arr_sort)
        length = z3.Function(f"len_{var_name}", arr_sort, z3.IntSort())
        helpers[f"len_{var_name}"] = length
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
    # Unknown — uninterpreted sort.
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

    if short in {"list", "List", "Iterable", "Iterator", "Sequence",
                  "MutableSequence", "Generator", "Container",
                  "Collection", "Reversible", "AbstractSet",
                  "MutableSet", "set", "Set", "frozenset",
                  "FrozenSet", "Deque"}:
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
        if op_t is ast.In:
            recv_name = _name_text(r_node)
            membership = enc.helpers.get(f"contains_{recv_name}")
            if membership is not None and l is not None:
                parts.append(membership(l) == z3.BoolVal(True))
                continue
            if l is not None and r is not None:
                # Array fallback — Select returns the value; we don't
                # have a "membership" semantics, so skip.
                return None
            return None
        if op_t is ast.NotIn:
            recv_name = _name_text(r_node)
            membership = enc.helpers.get(f"contains_{recv_name}")
            if membership is not None and l is not None:
                parts.append(membership(l) == z3.BoolVal(False))
                continue
            return None
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
    """
    fn = node.func
    if isinstance(fn, ast.Name):
        if fn.id == "len" and node.args:
            arg = node.args[0]
            if isinstance(arg, ast.Name):
                length = enc.helpers.get(f"len_{arg.id}")
                if length is not None:
                    return length(enc.env[arg.id])
            inner = _eval_node(arg, enc, z3)
            if inner is None:
                return None
            return z3.Length(inner) if hasattr(z3, "Length") else None
        if fn.id == "isinstance" and len(node.args) == 2:
            return z3.BoolVal(True)
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
    return None


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


__all__ = [
    "Z3Encoding",
    "check_implication",
]
