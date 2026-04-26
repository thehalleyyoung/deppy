"""Python function-body → Lean 4 definition translator.

The deppy pipeline already translates *types* and *predicates* to
Lean.  For "Lean as the gold standard" the certificate also needs a
Lean *definition* of each Python function so theorems about the
function are well-typed.  This module translates a function body
best-effort:

* arithmetic (Int / Float / Bool) — direct
* if/elif/else → ``if-then-else``
* return — bound through to the result
* recursive self-calls — preserved
* list ops: ``xs[:n]`` → ``xs.take n``; ``xs[n:]`` → ``xs.drop n``;
  ``xs[i]`` → ``xs.get!``
* ``len(xs)`` → ``xs.length``
* function calls — preserved (the callee must also have a Lean
  definition or be in scope)

When a body uses constructs we can't translate, the function emits
``sorry`` for the body — the user fills it in (or accepts the
weaker ``Lean has not validated the body`` note).

Audit fix #6 — type-aware translation
-------------------------------------

The translator now runs in two passes:

1. **Type-inference pass.**  An :class:`_InferTypes` walker
   propagates types from parameter annotations through assignments
   and operations, accumulating a ``locals_types`` map.  Operations
   like ``xs.length`` / ``xs.take`` / ``len(xs)`` constrain ``xs``'s
   type to ``List``; ``xs[k]`` constrains ``xs`` to ``List`` /
   ``Std.HashMap``; ``a.append(b)`` constrains ``a`` to ``List``;
   etc.  Param types are inferred from operations on them when the
   annotation is missing.
2. **Translation pass.**  Uses the inferred ``locals_types`` to:

   * pick the right Lean return type for the function (e.g.,
     ``List Int`` instead of ``Int`` for ``mergesort(xs)``);
   * turn ``len(xs)`` into ``xs.length`` only when ``xs : List``,
     ``xs.size`` for HashMap;
   * select the right comparison operator (``=`` vs ``==``) based on
     types;
   * route list-indexing through ``List.get?`` / ``Option.get!``
     correctly.

Public API::

    translate_body(fn_node, *, type_context, predicate_registry=None,
                   param_types=None) → BodyTranslation
    infer_function_signature(fn_node, type_context, param_types) →
        (binders_str, return_type)

The :func:`infer_function_signature` helper exposes the type-
inference pass to callers (e.g., the certificate generator) so the
function's *signature* uses the inferred types.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class BodyTranslation:
    """Result of translating a single function body to Lean."""
    lean_text: str
    exact: bool = True
    sorry_count: int = 0
    notes: list[str] = field(default_factory=list)


def translate_body(
    fn_node,
    *,
    type_context=None,
    predicate_registry: Optional[dict[str, str]] = None,
    param_types: Optional[dict[str, str]] = None,
) -> BodyTranslation:
    """Translate ``fn_node``'s body into a Lean expression.

    The expression returned matches the Lean definition's body — i.e.
    it should be wrapped in ``def fn_name : ... := <body>`` by the
    caller.  Recursive self-calls in the body refer to the Lean
    function name unchanged.

    Audit fix #6: the translator now uses inferred ``locals_types``
    (from the type-inference pass) to pick the right Lean operations.
    Pass ``param_types`` to seed the inference with caller-supplied
    annotation text (e.g. ``{"xs": "list[int]"}``); when omitted,
    the translator infers from the function's own annotations.
    """
    if fn_node is None or not getattr(fn_node, "body", None):
        return BodyTranslation(lean_text="sorry", exact=False, sorry_count=1)

    # Pass 1 — type inference.
    inferred = infer_locals_types(fn_node, param_types=param_types)

    translator = _BodyT(
        fn_name=fn_node.name,
        type_context=type_context,
        predicate_registry=predicate_registry or {},
        locals_types=inferred,
    )
    try:
        text = translator.visit_block(fn_node.body)
    except _Untranslatable as e:
        return BodyTranslation(
            lean_text="sorry",
            exact=False,
            sorry_count=1,
            notes=[f"untranslatable body: {e}"],
        )
    return BodyTranslation(
        lean_text=text,
        exact=translator.exact,
        sorry_count=translator.sorry_count,
        notes=translator.notes,
    )


# ─────────────────────────────────────────────────────────────────────
#  Type inference (Audit fix #6)
# ─────────────────────────────────────────────────────────────────────

def infer_locals_types(
    fn_node, *, param_types: Optional[dict[str, str]] = None,
) -> dict[str, str]:
    """Infer the Python type of every local variable in ``fn_node``.

    Returns ``{name: annotation_text}`` where ``annotation_text`` is
    a Python-syntax type string (``"int"`` / ``"list[int]"`` /
    ``"dict[str, int]"`` / ``"None"`` / etc.) suitable for feeding
    to :mod:`deppy.lean.type_translation`.

    Inference rules (best-effort, error on the side of conservative):

    1. Annotated parameters establish the seed (or use ``param_types``
       when supplied).
    2. Operations constrain the type:

       * ``len(x)`` / ``x.length`` / ``x.append(...)`` / ``x.pop()`` /
         ``x[k] = v`` (indexed assign) / ``x[i:j]`` (slice) → ``x : list``
       * ``x in d`` / ``x.contains(k)`` / ``x.keys()`` / ``x.values()`` /
         ``x.get(k)`` → ``x : dict``
       * Arithmetic ``a + b`` / ``a * b`` / etc. when one operand has
         a numeric type → propagate to the other.
       * Boolean operators / comparisons → ``bool``.
       * ``str.format`` / ``str.upper`` / etc. → ``str``.

    3. Variable assignments propagate types through ``Assign`` /
       ``AnnAssign`` / ``AugAssign`` and through ``return`` (the
       function's return type joins).
    4. When evidence conflicts (e.g. ``x.append(1)`` after ``x : int``)
       the *later* evidence wins (a tracked python idiom is
       reassignment); the inferrer logs a note.

    Parametric types are tracked when possible: ``[1, 2, 3]`` →
    ``list[int]``; ``{}`` → ``dict``; ``(1, 'a')`` → ``tuple[int, str]``.
    """
    seed = dict(param_types or {})
    # Add annotated parameter types when ``param_types`` didn't.
    if fn_node is not None:
        for arg in getattr(getattr(fn_node, "args", None), "args", []) or []:
            if arg.arg not in seed and arg.annotation is not None:
                try:
                    seed[arg.arg] = ast.unparse(arg.annotation).strip()
                except Exception:
                    pass
    if fn_node is None:
        return seed

    inferrer = _InferTypes(seed=seed)
    try:
        inferrer.visit(fn_node)
    except Exception:
        pass
    return inferrer.types


class _InferTypes(ast.NodeVisitor):
    """Walk a function and accumulate ``{name: type_text}``.

    The walker uses :data:`_INFER_OPS` and :data:`_INFER_METHODS`
    tables to decide what operation constrains what type.  When a
    name has multiple constraints we keep the most-specific one
    (parametric > bare; later evidence > earlier).
    """

    def __init__(self, seed: dict[str, str]) -> None:
        self.types: dict[str, str] = dict(seed)
        # Methods that mutate / read a known shape.
        self._list_methods = {
            "append", "extend", "insert", "pop", "remove",
            "reverse", "sort", "clear", "index", "count",
        }
        self._dict_methods = {
            "keys", "values", "items", "get", "setdefault",
            "update", "popitem", "contains", "fromkeys",
        }
        self._set_methods = {
            "add", "discard", "intersection", "union", "difference",
        }
        self._str_methods = {
            "upper", "lower", "strip", "format", "split", "rsplit",
            "join", "replace", "startswith", "endswith", "isdigit",
            "isalpha", "encode",
        }

    # -- annotations / assignments ------------------------------------

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if isinstance(node.target, ast.Name) and node.annotation is not None:
            try:
                self.types[node.target.id] = ast.unparse(node.annotation).strip()
            except Exception:
                pass
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        rhs_type = self._expr_type(node.value)
        if rhs_type is not None:
            for tgt in node.targets:
                if isinstance(tgt, ast.Name):
                    # Last-write-wins; preserves Python's reassignment
                    # semantics.
                    self.types[tgt.id] = rhs_type
        self.generic_visit(node)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        if isinstance(node.target, ast.Name):
            existing = self.types.get(node.target.id)
            rhs_type = self._expr_type(node.value)
            if existing is None and rhs_type is not None:
                self.types[node.target.id] = rhs_type
        self.generic_visit(node)

    # -- operations that constrain types -----------------------------

    def visit_Call(self, node: ast.Call) -> None:
        # Method call constrains receiver.
        if isinstance(node.func, ast.Attribute):
            recv = node.func.value
            method = node.func.attr
            if isinstance(recv, ast.Name):
                self._constrain(recv.id, method)
        elif isinstance(node.func, ast.Name):
            # ``len(x)`` / ``next(it)`` etc.
            fn = node.func.id
            if fn == "len" and node.args:
                a = node.args[0]
                if isinstance(a, ast.Name):
                    self._constrain_list_or_dict(a.id)
            elif fn in {"sum", "min", "max", "any", "all", "sorted",
                        "reversed", "iter", "list", "tuple", "set"}:
                if node.args and isinstance(node.args[0], ast.Name):
                    self._constrain_list_or_dict(node.args[0].id)
            elif fn == "next":
                pass  # iterator state is opaque
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        recv = node.value
        if isinstance(recv, ast.Name):
            existing = self.types.get(recv.id, "")
            slc = node.slice
            # Slice → list-only (dicts don't slice).
            if isinstance(slc, ast.Slice):
                if not self._is_list_like(existing):
                    self.types[recv.id] = "list"
            elif isinstance(slc, ast.Constant) and isinstance(slc.value, int):
                # Integer index → list/tuple/sequence.
                if not (self._is_list_like(existing)
                        or self._is_dict_like(existing)):
                    self.types[recv.id] = "list"
            elif isinstance(slc, ast.Constant) and isinstance(slc.value, str):
                # String key → dict.
                if not self._is_dict_like(existing):
                    self.types[recv.id] = "dict"
        self.generic_visit(node)

    def visit_Compare(self, node: ast.Compare) -> None:
        # ``x in y`` constrains y to a container.
        for op, right in zip(node.ops, node.comparators):
            if isinstance(op, (ast.In, ast.NotIn)) and isinstance(right, ast.Name):
                existing = self.types.get(right.id, "")
                if not (self._is_list_like(existing)
                        or self._is_dict_like(existing)
                        or self._is_set_like(existing)):
                    # Default ``in`` constrains to dict (most common
                    # in Python idioms — explicit list-membership is
                    # rarer than dict-key lookups).
                    self.types[right.id] = "dict"
        self.generic_visit(node)

    # -- helpers -----------------------------------------------------

    def _constrain(self, name: str, method: str) -> None:
        if method in self._list_methods:
            self._set_if_unset_or_compatible(name, "list")
        elif method in self._dict_methods:
            self._set_if_unset_or_compatible(name, "dict")
        elif method in self._set_methods:
            self._set_if_unset_or_compatible(name, "set")
        elif method in self._str_methods:
            self._set_if_unset_or_compatible(name, "str")
        elif method == "length":
            self._constrain_list_or_dict(name)

    def _constrain_list_or_dict(self, name: str) -> None:
        """``len(x)`` constrains x to a sized container.  Don't
        clobber an existing list/dict/set/str inference — they are
        all sized."""
        existing = self.types.get(name, "")
        if (self._is_list_like(existing) or self._is_dict_like(existing)
                or self._is_set_like(existing)
                or existing in {"str", "bytes"}):
            return
        self.types[name] = "list"

    def _set_if_unset_or_compatible(self, name: str, ty: str) -> None:
        existing = self.types.get(name, "")
        # Only overwrite when the existing type is not parametric or is
        # compatible with the inferred one.
        if not existing or existing == "int" or existing == "Any":
            self.types[name] = ty
        # ``list`` ↔ ``list[T]`` are compatible.
        elif existing.startswith(ty + "[") or existing == ty:
            return
        # else: leave the more-specific existing type alone.

    def _is_list_like(self, t: str) -> bool:
        if not t:
            return False
        for prefix in ("list", "List", "Sequence", "tuple", "Tuple",
                       "Iterable", "Iterator", "MutableSequence"):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    def _is_dict_like(self, t: str) -> bool:
        if not t:
            return False
        for prefix in ("dict", "Dict", "Mapping", "MutableMapping",
                       "OrderedDict", "defaultdict", "Counter"):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    def _is_set_like(self, t: str) -> bool:
        if not t:
            return False
        for prefix in ("set", "Set", "frozenset", "FrozenSet",
                       "MutableSet"):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    # -- expression-type inference ----------------------------------

    def _expr_type(self, expr: ast.expr) -> Optional[str]:
        if isinstance(expr, ast.Constant):
            v = expr.value
            if isinstance(v, bool):
                return "bool"
            if isinstance(v, int):
                return "int"
            if isinstance(v, float):
                return "float"
            if isinstance(v, str):
                return "str"
            if isinstance(v, bytes):
                return "bytes"
            if v is None:
                return "None"
        if isinstance(expr, ast.List):
            inner = (
                self._expr_type(expr.elts[0]) if expr.elts else "Any"
            )
            return f"list[{inner or 'Any'}]"
        if isinstance(expr, ast.Tuple):
            parts = [self._expr_type(e) or "Any" for e in expr.elts]
            return "tuple[" + ", ".join(parts) + "]"
        if isinstance(expr, ast.Dict):
            kt = (
                self._expr_type(expr.keys[0])
                if expr.keys and expr.keys[0] is not None else "Any"
            )
            vt = (
                self._expr_type(expr.values[0])
                if expr.values else "Any"
            )
            return f"dict[{kt or 'Any'}, {vt or 'Any'}]"
        if isinstance(expr, ast.Set):
            inner = (
                self._expr_type(next(iter(expr.elts)))
                if expr.elts else "Any"
            )
            return f"set[{inner or 'Any'}]"
        if isinstance(expr, ast.Name):
            return self.types.get(expr.id)
        if isinstance(expr, ast.BinOp):
            l = self._expr_type(expr.left)
            r = self._expr_type(expr.right)
            if l == "str" or r == "str":
                return "str"
            if l == "float" or r == "float":
                return "float"
            if l == "int" and r == "int":
                return "int"
            return l or r
        if isinstance(expr, ast.BoolOp) or isinstance(expr, ast.Compare):
            return "bool"
        if isinstance(expr, ast.Call):
            if isinstance(expr.func, ast.Name):
                fn = expr.func.id
                if fn in {"int"}:
                    return "int"
                if fn in {"float"}:
                    return "float"
                if fn in {"str"}:
                    return "str"
                if fn in {"bool"}:
                    return "bool"
                if fn in {"len"}:
                    return "int"
                if fn in {"list"}:
                    return "list"
                if fn in {"dict"}:
                    return "dict"
                if fn in {"tuple"}:
                    return "tuple"
                if fn in {"set"}:
                    return "set"
                if fn in {"sorted", "reversed"}:
                    if expr.args and isinstance(expr.args[0], ast.Name):
                        return self.types.get(expr.args[0].id, "list")
                    return "list"
            if isinstance(expr.func, ast.Attribute):
                method = expr.func.attr
                if method in self._str_methods:
                    return "str"
                if method == "length":
                    return "int"
                if method in {"keys", "values", "items"}:
                    return "list"
        return None


def infer_function_signature(
    fn_node, type_context, *,
    param_types: Optional[dict[str, str]] = None,
) -> tuple[str, str, list[str]]:
    """Infer a function's Lean binders + return type from its
    annotations + body.  Returns ``(binders_str, return_type,
    aux_decls)``.

    The return type is determined by:

    1. The explicit ``-> T`` annotation if present.
    2. Otherwise, the *most specific* type the inferrer assigns to
       any ``return`` statement's value in the function body.
    3. Falls back to ``α`` (polymorphic placeholder) when no return
       evidence is found.
    """
    import ast as _ast
    from deppy.lean.type_translation import translate_annotation_str
    aux_decls: list[str] = []
    binders: list[str] = []
    seed: dict[str, str] = dict(param_types or {})
    inferred = infer_locals_types(fn_node, param_types=seed)

    for arg in fn_node.args.args:
        ann_text = inferred.get(arg.arg, "")
        if not ann_text and arg.annotation is not None:
            try:
                ann_text = _ast.unparse(arg.annotation).strip()
            except Exception:
                ann_text = ""
        result = translate_annotation_str(
            ann_text, context=type_context,
        )
        for d in result.aux_decls:
            if d not in aux_decls:
                aux_decls.append(d)
        binders.append(f"({arg.arg} : {result.lean})")

    # Return type: explicit annotation wins, else infer from returns.
    return_text = ""
    if getattr(fn_node, "returns", None) is not None:
        try:
            return_text = _ast.unparse(fn_node.returns).strip()
        except Exception:
            return_text = ""
    if not return_text:
        return_text = _infer_return_type(fn_node, inferred)
    ret_result = translate_annotation_str(
        return_text or "Any", context=type_context,
    )
    for d in ret_result.aux_decls:
        if d not in aux_decls:
            aux_decls.append(d)
    return " ".join(binders), ret_result.lean, aux_decls


def _infer_return_type(
    fn_node, locals_types: dict[str, str],
) -> str:
    """Walk return statements and return the most-specific shared
    type.  When returns disagree, choose the most general (Optional
    of common parent) — currently we conservatively pick
    ``list``/``dict``/``int``/etc. by majority."""
    counts: dict[str, int] = {}
    for sub in ast.walk(fn_node):
        if isinstance(sub, ast.Return) and sub.value is not None:
            t = _const_or_local_type(sub.value, locals_types)
            if t:
                counts[t] = counts.get(t, 0) + 1
    if not counts:
        return ""
    return max(counts, key=lambda k: counts[k])


def _const_or_local_type(
    expr: ast.expr, locals_types: dict[str, str],
) -> str:
    if isinstance(expr, ast.Name):
        return locals_types.get(expr.id, "")
    if isinstance(expr, ast.Constant):
        v = expr.value
        if isinstance(v, bool):
            return "bool"
        if isinstance(v, int):
            return "int"
        if isinstance(v, float):
            return "float"
        if isinstance(v, str):
            return "str"
        if v is None:
            return "None"
    if isinstance(expr, ast.List):
        return "list"
    if isinstance(expr, ast.Dict):
        return "dict"
    if isinstance(expr, ast.Tuple):
        return "tuple"
    if isinstance(expr, ast.Call):
        if isinstance(expr.func, ast.Name):
            fn = expr.func.id
            if fn in {"list", "sorted", "reversed"}:
                return "list"
            if fn in {"dict"}:
                return "dict"
            if fn in {"set"}:
                return "set"
            if fn in {"int"}:
                return "int"
            if fn in {"str"}:
                return "str"
    return ""


class _Untranslatable(Exception):
    pass


_BIN_OPS_LEAN = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
    ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "%",
    ast.BitAnd: "&&&", ast.BitOr: "|||", ast.BitXor: "^^^",
}

_CMP_LEAN = {
    ast.Eq: "==", ast.NotEq: "!=",
    ast.Lt: "<", ast.LtE: "≤",
    ast.Gt: ">", ast.GtE: "≥",
}


class _BodyT:
    """Stateful walker.  Tracks ``sorry`` insertions and notes.

    Audit fix #6: ``locals_types`` is the type-inference output —
    a ``{name: type_text}`` dict keyed by Python identifier with
    Python-syntax type strings (``"list[int]"``, ``"dict[str, int]"``,
    etc.).  The walker uses it to choose the right Lean operations:

    * ``len(xs)`` → ``xs.length`` if ``xs`` is list-like, ``xs.size``
      if ``xs`` is dict-like, ``xs.length`` if ``str``;
    * ``x in d`` → ``Std.HashMap.contains d x`` for dicts vs
      ``List.contains xs x`` for lists;
    * ``xs[i]`` → ``xs.get! i.toNat`` for lists, ``d.get! k`` for
      dicts;
    * ``xs[i:j]`` → ``xs.take`` / ``xs.drop`` (only when list-like;
      sliced strings/dicts get a ``sorry`` since Python slicing on
      those translates poorly).

    When the inferrer doesn't have a type for a name (e.g. globals,
    function parameters with no annotation that couldn't be inferred
    from operations) the walker falls back to its previous,
    untyped behaviour so existing certificates don't regress.
    """

    def __init__(
        self, fn_name: str,
        type_context, predicate_registry: dict[str, str],
        locals_types: Optional[dict[str, str]] = None,
    ) -> None:
        self.fn_name = fn_name
        self.ctx = type_context
        self.preds = predicate_registry
        self.locals_types: dict[str, str] = dict(locals_types or {})
        self.exact = True
        self.sorry_count = 0
        self.notes: list[str] = []

    # -- type queries -------------------------------------------------

    def _type_of(self, expr: ast.expr) -> str:
        """Best-effort type-of-expression query.  Returns the empty
        string when the type is unknown (callers fall back to
        type-agnostic emission)."""
        if isinstance(expr, ast.Name):
            return self.locals_types.get(expr.id, "")
        if isinstance(expr, ast.Constant):
            v = expr.value
            if isinstance(v, bool):
                return "bool"
            if isinstance(v, int):
                return "int"
            if isinstance(v, float):
                return "float"
            if isinstance(v, str):
                return "str"
            if v is None:
                return "None"
        if isinstance(expr, ast.List):
            return "list"
        if isinstance(expr, ast.Tuple):
            return "tuple"
        if isinstance(expr, ast.Dict):
            return "dict"
        if isinstance(expr, ast.Set):
            return "set"
        if isinstance(expr, ast.Call):
            if isinstance(expr.func, ast.Name):
                fn = expr.func.id
                if fn in ("list", "sorted", "reversed"):
                    return "list"
                if fn == "dict":
                    return "dict"
                if fn == "set":
                    return "set"
                if fn == "tuple":
                    return "tuple"
                if fn in ("str", "repr"):
                    return "str"
                if fn in ("int", "len", "abs"):
                    return "int"
                if fn == "float":
                    return "float"
                if fn == "bool":
                    return "bool"
            if isinstance(expr.func, ast.Attribute):
                method = expr.func.attr
                if method in (
                    "upper", "lower", "strip", "format", "join",
                    "replace", "encode",
                ):
                    return "str"
                if method == "length":
                    return "int"
                if method in ("keys", "values", "items"):
                    return "list"
        if isinstance(expr, (ast.Compare, ast.BoolOp)):
            return "bool"
        if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
            return "bool"
        return ""

    @staticmethod
    def _is_list_like(t: str) -> bool:
        if not t:
            return False
        for prefix in (
            "list", "List", "Sequence", "tuple", "Tuple",
            "Iterable", "Iterator", "MutableSequence",
        ):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    @staticmethod
    def _is_dict_like(t: str) -> bool:
        if not t:
            return False
        for prefix in (
            "dict", "Dict", "Mapping", "MutableMapping",
            "OrderedDict", "defaultdict", "Counter",
        ):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    @staticmethod
    def _is_set_like(t: str) -> bool:
        if not t:
            return False
        for prefix in ("set", "Set", "frozenset", "FrozenSet", "MutableSet"):
            if t == prefix or t.startswith(prefix + "["):
                return True
        return False

    @staticmethod
    def _is_str_like(t: str) -> bool:
        return t in {"str", "bytes"}

    @staticmethod
    def _is_int_like(t: str) -> bool:
        return t == "int" or t == "Int" or t == "bool"

    @staticmethod
    def _is_bool(t: str) -> bool:
        return t == "bool" or t == "Bool"

    def _sorry(self, why: str) -> str:
        self.exact = False
        self.sorry_count += 1
        self.notes.append(why)
        return "sorry"

    # -- block / statement entry ---------------------------------------

    def visit_block(self, stmts: list[ast.stmt]) -> str:
        """Translate a function/method body — a list of statements
        ending in (ideally) a ``return``.

        We recognise these shapes:

        * ``return e`` alone → translate ``e``.
        * ``if cond: ... else: ...`` whose branches both return →
          emit ``if cond then T else F``.
        * Sequenced ``a = e ; ...`` (assignments) → emit
          ``let a := e ; ...`` chained.
        * Anything else falls back to ``sorry``.
        """
        return self._fold_stmts(stmts)

    def _fold_stmts(self, stmts: list[ast.stmt]) -> str:
        if not stmts:
            return self._sorry("empty body")

        # Strip leading docstring.
        if (isinstance(stmts[0], ast.Expr)
                and isinstance(stmts[0].value, ast.Constant)
                and isinstance(stmts[0].value.value, str)):
            stmts = stmts[1:]
            if not stmts:
                return self._sorry("docstring-only body")

        head = stmts[0]
        rest = stmts[1:]

        if isinstance(head, ast.Return):
            if rest:
                self.notes.append(
                    "code after return ignored in Lean translation"
                )
            return self._visit_expr(head.value) if head.value else "()"

        if isinstance(head, ast.If):
            then_terminal = self._stmts_terminal(head.body)
            else_terminal = (
                self._stmts_terminal(head.orelse) if head.orelse else False
            )
            # Three workable shapes:
            #   1. ``if ... return ; else ... return``   (both terminal)
            #   2. ``if ... return ; rest ...``          (then terminal,
            #       rest treated as else)
            #   3. ``if ... rest ; else ... return``     (else terminal,
            #       symmetric — translate as ``if not cond then else
            #       else then`` essentially).
            if then_terminal:
                cond = self._visit_expr(head.test)
                t = self._fold_stmts(head.body)
                if head.orelse:
                    e = self._fold_stmts(head.orelse)
                    if rest and not else_terminal:
                        # Both else and rest exist — append rest after else.
                        e = self._fold_stmts(list(head.orelse) + rest)
                else:
                    # No else — rest IS the else.
                    e = (
                        self._fold_stmts(rest) if rest
                        else self._sorry("if-then with no else and no fall-through")
                    )
                return f"if {cond} then {t} else {e}"
            if else_terminal and head.orelse:
                # Mirror case: pull the else as the terminal arm.
                cond = self._visit_expr(head.test)
                t_body = self._fold_stmts(list(head.body) + rest)
                e = self._fold_stmts(head.orelse)
                return f"if {cond} then {t_body} else {e}"
            # Neither branch is terminal — bail.
            return self._sorry("if without terminal branches")

        if isinstance(head, ast.Assign) and len(head.targets) == 1:
            tgt = head.targets[0]
            if isinstance(tgt, ast.Name):
                value = self._visit_expr(head.value)
                # Record the inferred type of the RHS so subsequent
                # statements that reference ``tgt.id`` get typed
                # operations (e.g. ``len(x)`` after ``x = sorted(xs)``
                # uses ``x.length`` because ``x : list``).
                rhs_type = self._type_of(head.value)
                if rhs_type:
                    self.locals_types[tgt.id] = rhs_type
                tail = self._fold_stmts(rest)
                return f"let {tgt.id} := {value};\n  {tail}"
            return self._sorry("non-Name assignment target")

        if isinstance(head, ast.AnnAssign) and isinstance(head.target, ast.Name):
            # Record the explicit annotation, if present, so subsequent
            # operations are routed through the right Lean idiom.
            if head.annotation is not None:
                try:
                    self.locals_types[head.target.id] = ast.unparse(
                        head.annotation,
                    ).strip()
                except Exception:
                    pass
            if head.value is None:
                # type-only declaration — skip.
                return self._fold_stmts(rest)
            value = self._visit_expr(head.value)
            tail = self._fold_stmts(rest)
            return f"let {head.target.id} := {value};\n  {tail}"

        if isinstance(head, ast.AugAssign) and isinstance(head.target, ast.Name):
            op = _BIN_OPS_LEAN.get(type(head.op))
            if op is None:
                return self._sorry("unsupported augmented assign")
            value = self._visit_expr(head.value)
            tail = self._fold_stmts(rest)
            return (
                f"let {head.target.id} := {head.target.id} {op} {value};\n"
                f"  {tail}"
            )

        if isinstance(head, ast.Pass):
            return self._fold_stmts(rest)

        return self._sorry(
            f"unsupported statement {type(head).__name__}",
        )

    @staticmethod
    def _stmts_terminal(stmts: list[ast.stmt]) -> bool:
        if not stmts:
            return False
        last = stmts[-1]
        return isinstance(last, (ast.Return, ast.Raise))

    # -- expressions ---------------------------------------------------

    def _visit_expr(self, node: Optional[ast.expr]) -> str:
        if node is None:
            return "()"

        if isinstance(node, ast.Constant):
            v = node.value
            if v is None:
                return "()"
            if v is True:
                return "true"
            if v is False:
                return "false"
            if isinstance(v, int):
                return str(v)
            if isinstance(v, float):
                return repr(v)
            if isinstance(v, str):
                return f"\"{v}\""
            return self._sorry(f"unsupported constant {v!r}")

        if isinstance(node, ast.Name):
            return node.id

        if isinstance(node, ast.UnaryOp):
            inner = self._visit_expr(node.operand)
            if isinstance(node.op, ast.Not):
                return f"¬ ({inner})"
            if isinstance(node.op, ast.USub):
                return f"-({inner})"
            if isinstance(node.op, ast.UAdd):
                return inner
            return self._sorry(
                f"unsupported unary op {type(node.op).__name__}"
            )

        if isinstance(node, ast.BinOp):
            op = _BIN_OPS_LEAN.get(type(node.op))
            if op is None:
                return self._sorry(
                    f"unsupported binary op {type(node.op).__name__}"
                )
            l = self._visit_expr(node.left)
            r = self._visit_expr(node.right)
            return f"({l} {op} {r})"

        if isinstance(node, ast.BoolOp):
            sep = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
            parts = [self._visit_expr(v) for v in node.values]
            return "(" + sep.join(parts) + ")"

        if isinstance(node, ast.Compare):
            return self._visit_compare(node)

        if isinstance(node, ast.Call):
            return self._visit_call(node)

        if isinstance(node, ast.Subscript):
            return self._visit_subscript(node)

        if isinstance(node, ast.IfExp):
            cond = self._visit_expr(node.test)
            t = self._visit_expr(node.body)
            e = self._visit_expr(node.orelse)
            return f"if {cond} then {t} else {e}"

        if isinstance(node, ast.List):
            elts = [self._visit_expr(e) for e in node.elts]
            return "[" + ", ".join(elts) + "]"

        if isinstance(node, ast.Tuple):
            parts = [self._visit_expr(e) for e in node.elts]
            return "(" + ", ".join(parts) + ")"

        return self._sorry(f"unsupported expression {type(node).__name__}")

    def _visit_compare(self, node: ast.Compare) -> str:
        # First, try the typed lowering for ``in`` / ``not in``.
        typed = self._visit_compare_typed(node)
        if typed is not None:
            return typed
        if len(node.ops) == 1:
            op_t = type(node.ops[0])
            if op_t in _CMP_LEAN:
                l = self._visit_expr(node.left)
                r_node = node.comparators[0]
                r = self._visit_expr(r_node)
                # When comparing a non-Int type we must use Lean's
                # ``=``/``≠`` rather than ``==``/``!=`` — for List, it's
                # decidable equality.
                lhs_type = self._type_of(node.left)
                rhs_type = self._type_of(r_node)
                op = _CMP_LEAN[op_t]
                # Equality on non-numerics: switch to propositional ``=``.
                if op == "==" and (
                    self._is_list_like(lhs_type) or self._is_list_like(rhs_type)
                    or self._is_dict_like(lhs_type) or self._is_dict_like(rhs_type)
                    or self._is_str_like(lhs_type) or self._is_str_like(rhs_type)
                ):
                    op = "="
                elif op == "!=" and (
                    self._is_list_like(lhs_type) or self._is_list_like(rhs_type)
                    or self._is_dict_like(lhs_type) or self._is_dict_like(rhs_type)
                    or self._is_str_like(lhs_type) or self._is_str_like(rhs_type)
                ):
                    op = "≠"
                return f"({l} {op} {r})"
            if isinstance(node.ops[0], (ast.In, ast.NotIn)):
                # Already handled by _visit_compare_typed above.
                return self._sorry("untyped 'in' comparison")
            if isinstance(node.ops[0], ast.Is):
                l = self._visit_expr(node.left)
                r = self._visit_expr(node.comparators[0])
                return f"({l} = {r})"
            if isinstance(node.ops[0], ast.IsNot):
                l = self._visit_expr(node.left)
                r = self._visit_expr(node.comparators[0])
                return f"({l} ≠ {r})"
        # Chained: a < b < c → (a < b) ∧ (b < c)
        terms = [node.left] + list(node.comparators)
        parts: list[str] = []
        for op, l_node, r_node in zip(node.ops, terms, terms[1:]):
            op_t = type(op)
            if op_t not in _CMP_LEAN:
                return self._sorry(f"unsupported comparator {op_t.__name__}")
            l = self._visit_expr(l_node)
            r = self._visit_expr(r_node)
            parts.append(f"({l} {_CMP_LEAN[op_t]} {r})")
        return "(" + " ∧ ".join(parts) + ")"

    def _visit_call(self, node: ast.Call) -> str:
        if isinstance(node.func, ast.Name):
            fn = node.func.id
            if fn == "len" and len(node.args) == 1:
                arg_text = self._visit_expr(node.args[0])
                arg_type = self._type_of(node.args[0])
                if self._is_dict_like(arg_type):
                    return f"({arg_text}.size)"
                if self._is_set_like(arg_type):
                    return f"({arg_text}.toList.length)"
                if self._is_str_like(arg_type):
                    return f"({arg_text}.length)"
                # Default: list-like (covers known list, tuple, and
                # the unknown-type case where the previous behaviour
                # was to emit ``.length``).
                return f"({arg_text}.length)"
            if fn == "abs" and len(node.args) == 1:
                inner_type = self._type_of(node.args[0])
                inner = self._visit_expr(node.args[0])
                if inner_type == "float":
                    return f"(Float.abs {inner})"
                return f"(Int.natAbs {inner})"
            if fn == "min" and len(node.args) == 2:
                return f"(min {self._visit_expr(node.args[0])} {self._visit_expr(node.args[1])})"
            if fn == "max" and len(node.args) == 2:
                return f"(max {self._visit_expr(node.args[0])} {self._visit_expr(node.args[1])})"
            if fn in ("int", "float", "str", "bool") and len(node.args) == 1:
                # Coercion — Lean handles most of these via ``.toX``.
                inner = self._visit_expr(node.args[0])
                inner_type = self._type_of(node.args[0])
                if fn == "int":
                    if inner_type == "float":
                        return f"({inner}.toInt)"
                    if self._is_str_like(inner_type):
                        return f"({inner}.toInt!)"
                    return inner  # already int-like
                if fn == "str":
                    return f"(toString {inner})"
                if fn == "float":
                    if self._is_int_like(inner_type):
                        return f"((Int.toFloat) {inner})"
                    return inner
                if fn == "bool":
                    return f"({inner} ≠ 0)"
            if fn == "sum" and len(node.args) == 1:
                return f"(({self._visit_expr(node.args[0])}).foldl (· + ·) 0)"
            if fn == "any" and len(node.args) == 1:
                return f"(({self._visit_expr(node.args[0])}).any id)"
            if fn == "all" and len(node.args) == 1:
                return f"(({self._visit_expr(node.args[0])}).all id)"
            if fn == "sorted" and len(node.args) == 1:
                return f"(({self._visit_expr(node.args[0])}).mergeSort)"
            if fn == "reversed" and len(node.args) == 1:
                return f"(({self._visit_expr(node.args[0])}).reverse)"
            if fn == "list" and len(node.args) == 1:
                return f"({self._visit_expr(node.args[0])}).toList"
            if fn == "set" and len(node.args) == 1:
                return f"({self._visit_expr(node.args[0])}).toFinset"
            # Self-recursive call.
            if fn == self.fn_name:
                args = [self._visit_expr(a) for a in node.args]
                return f"({fn} " + " ".join(args) + ")"
            # Generic function call.
            args = [self._visit_expr(a) for a in node.args]
            return f"({fn} " + " ".join(args) + ")"
        if isinstance(node.func, ast.Attribute):
            recv_node = node.func.value
            recv = self._visit_expr(recv_node)
            method = node.func.attr
            recv_type = self._type_of(recv_node)
            args = [self._visit_expr(a) for a in node.args]
            return self._render_method_call(recv, recv_type, method, args)
        return self._sorry("call to non-name/attribute")

    def _render_method_call(
        self, recv: str, recv_type: str, method: str,
        args: list[str],
    ) -> str:
        """Pick the right Lean idiom for ``recv.method(args)`` based
        on the inferred receiver type.  For untyped receivers we keep
        the previous untyped emission for compatibility."""

        # ----- list-like methods --------------------------------------
        if self._is_list_like(recv_type):
            if method == "length":
                return f"({recv}.length)"
            if method == "append" and len(args) == 1:
                return f"({recv}.concat {args[0]})"
            if method == "extend" and len(args) == 1:
                return f"({recv} ++ {args[0]})"
            if method == "pop" and len(args) <= 1:
                if not args:
                    return f"(({recv}.dropLast))"
                return f"({recv}.eraseIdx ({args[0]}.toNat))"
            if method == "insert" and len(args) == 2:
                return f"({recv}.insertAt ({args[0]}.toNat) {args[1]})"
            if method == "reverse" and not args:
                return f"({recv}.reverse)"
            if method == "sort" and not args:
                return f"({recv}.mergeSort)"
            if method == "count" and len(args) == 1:
                return f"({recv}.count {args[0]})"
            if method == "index" and len(args) == 1:
                return f"(({recv}.indexOf? {args[0]}).getD 0)"
            if method == "contains" and len(args) == 1:
                return f"({recv}.contains {args[0]})"
            if method == "map" and len(args) == 1:
                return f"({recv}.map {args[0]})"
            if method == "filter" and len(args) == 1:
                return f"({recv}.filter {args[0]})"
            if method in ("get", "head"):
                if args:
                    return f"({recv}.get? ({args[0]}.toNat) |>.getD default)"
                return f"({recv}.head?.getD default)"
        # ----- dict-like methods --------------------------------------
        if self._is_dict_like(recv_type):
            if method == "size":
                return f"({recv}.size)"
            if method == "get" and len(args) >= 1:
                if len(args) == 2:
                    return f"({recv}.findD {args[0]} {args[1]})"
                return f"({recv}.find? {args[0]} |>.getD default)"
            if method == "keys" and not args:
                return f"({recv}.keys)"
            if method == "values" and not args:
                return f"({recv}.values)"
            if method == "items" and not args:
                return f"({recv}.toList)"
            if method == "contains" and len(args) == 1:
                return f"({recv}.contains {args[0]})"
            if method == "setdefault" and len(args) == 2:
                return f"((if {recv}.contains {args[0]} then {recv} else {recv}.insert {args[0]} {args[1]}).find! {args[0]})"
            if method == "update" and len(args) == 1:
                return f"({recv} ∪ {args[0]})"
            if method == "popitem" and not args:
                return f"({recv}.toList.head?.getD default)"
        # ----- set-like methods ---------------------------------------
        if self._is_set_like(recv_type):
            if method == "add" and len(args) == 1:
                return f"({recv}.insert {args[0]})"
            if method == "discard" and len(args) == 1:
                return f"({recv}.erase {args[0]})"
            if method == "intersection" and len(args) == 1:
                return f"({recv} ∩ {args[0]})"
            if method == "union" and len(args) == 1:
                return f"({recv} ∪ {args[0]})"
            if method == "difference" and len(args) == 1:
                return f"({recv} \\\\ {args[0]})"
            if method == "contains" and len(args) == 1:
                return f"({args[0]} ∈ {recv})"
        # ----- str-like methods ---------------------------------------
        if self._is_str_like(recv_type):
            if method == "upper" and not args:
                return f"({recv}.toUpper)"
            if method == "lower" and not args:
                return f"({recv}.toLower)"
            if method == "strip" and not args:
                return f"({recv}.trim)"
            if method == "split" and len(args) <= 1:
                if args:
                    return f"({recv}.split (· == {args[0]}.front))"
                return f"({recv}.split (· == ' '))"
            if method == "join" and len(args) == 1:
                return f"({args[0]}.foldl (· ++ ·) \"\")"
            if method == "replace" and len(args) == 2:
                return f"({recv}.replace {args[0]} {args[1]})"
            if method == "startswith" and len(args) == 1:
                return f"({recv}.startsWith {args[0]})"
            if method == "endswith" and len(args) == 1:
                return f"({recv}.endsWith {args[0]})"
            if method == "format":
                # Format strings are tricky; fall back gracefully.
                return f"({recv}  /- format args dropped -/)"
            if method == "encode":
                return f"({recv}.toUTF8)"
            if method == "isdigit" and not args:
                return f"({recv}.all Char.isDigit)"
            if method == "isalpha" and not args:
                return f"({recv}.all Char.isAlpha)"
        # ----- generic fallback --------------------------------------
        if not args:
            return f"({recv}.{method})"
        return f"({recv}.{method} " + " ".join(args) + ")"

    def _visit_subscript(self, node: ast.Subscript) -> str:
        recv = self._visit_expr(node.value)
        recv_type = self._type_of(node.value)
        slc = node.slice
        if isinstance(slc, ast.Slice):
            lower = (
                self._visit_expr(slc.lower) if slc.lower is not None else "0"
            )
            upper = self._visit_expr(slc.upper) if slc.upper is not None else None
            if slc.step is not None:
                return self._sorry("slice step not supported")
            if self._is_str_like(recv_type):
                # Strings use ``substring`` / ``extract``.
                if upper is None:
                    return f"({recv}.drop {lower})"
                if lower == "0":
                    return f"({recv}.take {upper})"
                return f"(({recv}.drop {lower}).take ({upper} - {lower}))"
            if self._is_dict_like(recv_type):
                # Dicts can't be sliced — emit a sorry with note.
                return self._sorry("slice on dict-like value")
            # Default: list-like (covers known list, tuple, and unknown).
            if upper is None:
                return f"({recv}.drop {lower})"
            if lower == "0":
                return f"({recv}.take {upper})"
            return f"(({recv}.drop {lower}).take ({upper} - {lower}))"
        idx = self._visit_expr(slc)
        idx_type = self._type_of(slc)
        if self._is_dict_like(recv_type):
            return f"({recv}.find! {idx})"
        if self._is_str_like(recv_type):
            return f"({recv}.get ({idx}.toNat))"
        # Default: list-like indexing — convert int → Nat.
        if idx_type == "int" or idx_type == "" or self._is_int_like(idx_type):
            return f"({recv}.get! ({idx}.toNat))"
        return f"({recv}.get! {idx})"

    def _visit_compare_typed(self, node: ast.Compare) -> Optional[str]:
        """Override for ``in`` / ``not in`` operators when we know
        the rhs is dict-like or set-like.  Returns ``None`` if no
        type-specific lowering applies and the caller should use
        the default chain-comparison handling."""
        if len(node.ops) != 1:
            return None
        op = node.ops[0]
        right = node.comparators[0]
        if not isinstance(op, (ast.In, ast.NotIn)):
            return None
        rty = self._type_of(right)
        l = self._visit_expr(node.left)
        r = self._visit_expr(right)
        if self._is_dict_like(rty):
            base = f"({r}.contains {l})"
            return base if isinstance(op, ast.In) else f"(¬ {base})"
        if self._is_set_like(rty):
            base = f"({l} ∈ {r})"
            return base if isinstance(op, ast.In) else f"({l} ∉ {r})"
        if self._is_list_like(rty):
            base = f"({r}.contains {l})"
            return base if isinstance(op, ast.In) else f"(¬ {base})"
        if self._is_str_like(rty):
            base = f"({r}.contains {l})"
            return base if isinstance(op, ast.In) else f"(¬ {base})"
        # Unknown — use a generic membership.
        base = f"({l} ∈ {r})"
        return base if isinstance(op, ast.In) else f"({l} ∉ {r})"


__all__ = [
    "BodyTranslation",
    "translate_body",
    "infer_function_signature",
    "infer_locals_types",
]
