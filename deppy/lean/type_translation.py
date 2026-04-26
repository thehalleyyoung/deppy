"""Comprehensive Python type annotation → Lean 4 type translation.

Used by both the obligation emitter and the pipeline's Lean-proof
discharge to turn the formal-parameter annotations of a Python
function into Lean binder types.

Coverage is intentionally broad — the translator attempts to render
*every* importable Python typing-system construct rather than
defaulting to opaque axioms for anything non-trivial.

Built-ins
---------
* Scalar types — ``int``, ``float``, ``str``, ``bool``, ``bytes``,
  ``bytearray``, ``complex``, ``None``, ``object``.
* Generic containers — ``list[T]``, ``dict[K, V]``, ``tuple[T, ...]``,
  ``set[T]``, ``frozenset[T]``.

``typing`` module
-----------------
* Aliases — ``typing.List`` / ``Dict`` / ``Set`` / ``FrozenSet`` /
  ``Tuple`` (alias to the built-in counterparts).
* ``Optional[T]`` / ``T | None`` → ``Option T``.
* ``Union[A, B, …]`` / PEP 604 ``A | B | …`` → ``Sum`` (recursive
  for 3+).
* ``Any``, ``object`` → polymorphic placeholder.
* ``Callable[[A, B], R]`` → ``A → B → R``; supports higher-order
  callables, ``Callable[..., R]``, and ``Callable[Concatenate[A, P], R]``.
* ``Literal[v1, v2, …]`` → underlying scalar type with a note.
* ``Annotated[T, *meta]`` → ``T`` (metadata stripped).
* ``Final[T]`` / ``ClassVar[T]`` → ``T`` (qualifier stripped).
* ``NewType('Name', T)`` → opaque alias preserving the underlying.
* ``Self`` → enclosing class type when supplied via context.
* ``TypeGuard[T]`` / ``TypeIs[T]`` → ``Bool``.
* ``Generic[T]`` / ``Protocol`` base markers — recognised and
  rendered as their underlying body (or opaque when used directly
  as a type).
* ``TypeVar`` / ``ParamSpec`` / ``TypeVarTuple`` references — opaque,
  but reuse the same axiom name across occurrences for cleaner
  output.
* ``Concatenate[A, P]`` / ``Unpack[Ts]`` for variadics.

``collections.abc``
-------------------
``Iterable``, ``Iterator``, ``Generator``, ``Sequence``,
``MutableSequence``, ``Mapping``, ``MutableMapping``, ``Set``,
``MutableSet``, ``Container``, ``Reversible``, ``Hashable``,
``Sized``, ``Awaitable``, ``Coroutine``, ``AsyncIterable``,
``AsyncIterator``, ``AsyncGenerator`` — translated where Lean has a
parallel, otherwise opaque.

Public API::

    translate_annotation(node, *, known_classes=(), context=None)
    translate_annotation_str(text, *, known_classes=(), context=None)
    Context — extra knowledge from the surrounding source

The ``Context`` object lets the caller pass module-level information
the translator can't infer from a single annotation: the enclosing
class (for ``Self``), declared ``TypeVar`` / ``NewType`` /
``TypeAlias`` bindings, and the import map (for resolving
``typing.X`` style names).
"""
from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, field
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Result + Context dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class TypeTranslation:
    """Result of translating a single annotation."""
    lean: str
    aux_decls: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


@dataclass
class Context:
    """Module-level information the translator can use.

    All fields are optional — if not supplied, the translator falls
    back to conservative defaults (opaque axioms for unknowns).
    """
    enclosing_class: Optional[str] = None
    type_vars: dict[str, "TypeVarSpec"] = field(default_factory=dict)
    new_types: dict[str, str] = field(default_factory=dict)  # name → underlying
    type_aliases: dict[str, str] = field(default_factory=dict)
    known_classes: set[str] = field(default_factory=set)
    # PEP 695 ``type X[T] = ...`` aliases would go in ``type_aliases``.

    @classmethod
    def from_module_source(cls, source: str) -> "Context":
        """Walk ``source`` for ``TypeVar(...)`` / ``NewType(...)`` /
        ``TypeAlias`` declarations and build a Context.  Defensive —
        any single declaration that fails to parse is silently
        skipped."""
        ctx = cls()
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return ctx
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                ctx.known_classes.add(node.name)
            elif isinstance(node, ast.Assign) and len(node.targets) == 1:
                tgt = node.targets[0]
                if not isinstance(tgt, ast.Name):
                    continue
                spec = _try_parse_type_var(node.value)
                if spec is not None:
                    ctx.type_vars[tgt.id] = spec
                    continue
                nt = _try_parse_new_type(node.value)
                if nt is not None:
                    ctx.new_types[tgt.id] = nt
                    continue
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                # ``MyAlias: TypeAlias = ...``
                ann = node.annotation
                if isinstance(ann, ast.Name) and ann.id == "TypeAlias":
                    if node.value is not None:
                        try:
                            ctx.type_aliases[node.target.id] = (
                                ast.unparse(node.value)
                            )
                        except Exception:
                            pass
        return ctx


@dataclass
class TypeVarSpec:
    """Constraints / bound recovered from a ``TypeVar(...)`` call."""
    name: str
    bound: Optional[str] = None
    constraints: list[str] = field(default_factory=list)
    is_param_spec: bool = False
    is_type_var_tuple: bool = False


def _try_parse_type_var(value: ast.expr) -> Optional[TypeVarSpec]:
    """Recognise ``TypeVar('T', ...)``, ``ParamSpec('P')``,
    ``TypeVarTuple('Ts')`` calls."""
    if not isinstance(value, ast.Call):
        return None
    if not isinstance(value.func, (ast.Name, ast.Attribute)):
        return None
    fn_name = (
        value.func.id if isinstance(value.func, ast.Name)
        else value.func.attr
    )
    if fn_name not in {"TypeVar", "ParamSpec", "TypeVarTuple"}:
        return None
    if not value.args or not isinstance(value.args[0], ast.Constant):
        return None
    name = value.args[0].value
    if not isinstance(name, str):
        return None
    spec = TypeVarSpec(
        name=name,
        is_param_spec=(fn_name == "ParamSpec"),
        is_type_var_tuple=(fn_name == "TypeVarTuple"),
    )
    # constraints: TypeVar('T', int, str)
    for arg in value.args[1:]:
        try:
            spec.constraints.append(ast.unparse(arg))
        except Exception:
            pass
    # bound=
    for kw in value.keywords:
        if kw.arg == "bound":
            try:
                spec.bound = ast.unparse(kw.value)
            except Exception:
                pass
    return spec


def _try_parse_new_type(value: ast.expr) -> Optional[str]:
    """Recognise ``NewType('Name', Underlying)``."""
    if not isinstance(value, ast.Call):
        return None
    if not isinstance(value.func, (ast.Name, ast.Attribute)):
        return None
    fn_name = (
        value.func.id if isinstance(value.func, ast.Name)
        else value.func.attr
    )
    if fn_name != "NewType":
        return None
    if len(value.args) != 2:
        return None
    try:
        return ast.unparse(value.args[1])
    except Exception:
        return None


# ─────────────────────────────────────────────────────────────────────
#  Constants — fixed lookup tables
# ─────────────────────────────────────────────────────────────────────

_SCALAR: dict[str, str] = {
    "int": "Int", "float": "Float", "str": "String",
    "bool": "Bool", "bytes": "ByteArray", "bytearray": "ByteArray",
    "complex": "Complex", "None": "Unit", "NoneType": "Unit",
    "object": "α", "Any": "α",
}

# All names that should resolve to ``int`` / ``str`` / etc. when
# referenced via ``typing.<X>`` or as plain identifiers.
_BUILTIN_GENERIC: dict[str, tuple[str, int]] = {
    # name → (Lean head, expected number of params)
    "list": ("List", 1), "List": ("List", 1),
    "set": ("List", 1), "Set": ("List", 1),  # Set as List (no parametric Set in Lean stdlib)
    "frozenset": ("List", 1), "FrozenSet": ("List", 1),
    "tuple": ("Tuple", -1), "Tuple": ("Tuple", -1),  # variadic
    "dict": ("Std.HashMap", 2), "Dict": ("Std.HashMap", 2),
    "Iterable": ("List", 1),  "MutableSequence": ("List", 1),
    "Sequence": ("List", 1),
    "Iterator": ("List", 1),  "Generator": ("List", 1),
    "Mapping": ("Std.HashMap", 2),
    "MutableMapping": ("Std.HashMap", 2),
    "OrderedDict": ("Std.HashMap", 2),
    "defaultdict": ("Std.HashMap", 2),
    "Counter": ("Std.HashMap", 2),
    "Container": ("List", 1),
    "Reversible": ("List", 1),
    "Collection": ("List", 1),
    "AbstractSet": ("List", 1), "MutableSet": ("List", 1),
    "Awaitable": ("Task", 1),
    "Coroutine": ("Task", 1),
    "AsyncIterable": ("Task", 1),
    "AsyncIterator": ("Task", 1),
    "AsyncGenerator": ("Task", 1),
    "Deque": ("List", 1),
    "ChainMap": ("Std.HashMap", 2),
}

# Single Names that resolve to a specific Lean type (no parameters).
_BUILTIN_SINGLETON: dict[str, str] = {
    "Hashable": "α",
    "Sized": "α",
    "ByteString": "ByteArray",
}


# ─────────────────────────────────────────────────────────────────────
#  Public API
# ─────────────────────────────────────────────────────────────────────

def translate_annotation(
    node: Optional[ast.expr],
    *,
    known_classes: Iterable[str] = (),
    context: Optional[Context] = None,
) -> TypeTranslation:
    """Translate an AST annotation node to a Lean 4 type."""
    aux_decls: list[str] = []
    notes: list[str] = []
    ctx = context or Context()
    ctx_known = set(ctx.known_classes) | set(known_classes)
    text = _T(aux_decls, notes, ctx, ctx_known).visit(node)
    return TypeTranslation(lean=text, aux_decls=aux_decls, notes=notes)


def translate_annotation_str(
    text: str,
    *,
    known_classes: Iterable[str] = (),
    context: Optional[Context] = None,
) -> TypeTranslation:
    text = (text or "").strip()
    if not text:
        return TypeTranslation(lean="Int")
    try:
        node = ast.parse(text, mode="eval").body
    except SyntaxError:
        aux: list[str] = []
        nm = _opaque_class(text, aux)
        return TypeTranslation(
            lean=nm, aux_decls=aux,
            notes=[f"unparseable annotation {text!r}"],
        )
    return translate_annotation(
        node, known_classes=known_classes, context=context,
    )


# ─────────────────────────────────────────────────────────────────────
#  Internal recursive translator
# ─────────────────────────────────────────────────────────────────────

class _T:
    """Stateful AST → Lean type walker.  Keeps a single ``aux``
    declaration list across recursive descent so opaque types are
    declared once even when they appear multiple times."""

    def __init__(self, aux: list[str], notes: list[str],
                 ctx: Context, known: set[str]) -> None:
        self.aux = aux
        self.notes = notes
        self.ctx = ctx
        self.known = known

    # -- entry --------------------------------------------------------

    def visit(self, node: Optional[ast.expr]) -> str:
        if node is None:
            return "Int"

        if isinstance(node, ast.Constant):
            return self._visit_constant(node)

        if isinstance(node, ast.Name):
            return self._visit_name(node)

        if isinstance(node, ast.Attribute):
            return self._visit_attribute(node)

        if isinstance(node, ast.Subscript):
            return self._visit_subscript(node)

        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            return self._visit_pep604_union(node)

        # ``Generic[T, U]`` / ``Protocol`` used as a base class — fall
        # through to opaque, with a note.
        if isinstance(node, ast.Tuple):
            # Bare tuple in an annotation is rare, but render as a
            # product type.
            return "(" + " × ".join(self.visit(e) for e in node.elts) + ")"

        if isinstance(node, ast.List):
            # ``[A, B]`` form — used inside ``Callable[[A, B], R]``
            # which is handled by the Subscript path.  Translate as
            # a product as a fallback.
            return "(" + " × ".join(self.visit(e) for e in node.elts) + ")"

        self.notes.append(
            f"unsupported annotation form {type(node).__name__}"
        )
        return _opaque_class(_safe_text(node), self.aux)

    # -- per-node visitors -------------------------------------------

    def _visit_constant(self, node: ast.Constant) -> str:
        v = node.value
        if v is None:
            return "Unit"
        if v is Ellipsis:
            return "α"
        if isinstance(v, str):
            # Forward-reference annotation as a string literal.
            try:
                inner = ast.parse(v, mode="eval").body
                return self.visit(inner)
            except SyntaxError:
                self.notes.append(f"unparseable forward ref: {v!r}")
                return _opaque_class(v, self.aux)
        if isinstance(v, bool):
            return "Bool"
        if isinstance(v, int):
            return "Int"
        if isinstance(v, float):
            return "Float"
        self.notes.append(f"unsupported annotation literal {v!r}")
        return "Int"

    def _visit_name(self, node: ast.Name) -> str:
        nm = node.id

        # Scalars and ``Any`` / ``object``.
        if nm in _SCALAR:
            return _SCALAR[nm]

        # ``Self`` — when in a method of a known class, render as the
        # enclosing class type.
        if nm == "Self" and self.ctx.enclosing_class:
            return _opaque_class(self.ctx.enclosing_class, self.aux)
        if nm == "Self":
            return _opaque_class("Self", self.aux)

        # User-declared TypeAlias takes precedence.
        if nm in self.ctx.type_aliases:
            try:
                inner = ast.parse(self.ctx.type_aliases[nm], mode="eval").body
                return self.visit(inner)
            except SyntaxError:
                pass

        # User-declared NewType.
        if nm in self.ctx.new_types:
            try:
                inner = ast.parse(self.ctx.new_types[nm], mode="eval").body
                # NewType wraps an underlying — emit it as that type
                # for arithmetic purposes, but record an opaque axiom
                # tag so theorems can still distinguish them when
                # needed.
                inner_text = self.visit(inner)
                self.notes.append(
                    f"NewType({nm!r}, {self.ctx.new_types[nm]}) — "
                    f"rendered as the underlying type"
                )
                return inner_text
            except SyntaxError:
                pass

        # User-declared TypeVar / ParamSpec / TypeVarTuple.
        if nm in self.ctx.type_vars:
            spec = self.ctx.type_vars[nm]
            return self._render_type_var(spec)

        # Bare generic without subscript — fall to default param.
        if nm in _BUILTIN_GENERIC:
            head, _arity = _BUILTIN_GENERIC[nm]
            # Default parameters: Int for unary, String→Int for binary.
            if head == "Std.HashMap":
                return "(Std.HashMap String Int)"
            if head == "Tuple":
                return "(List Int)"
            return f"({head} Int)"

        if nm in _BUILTIN_SINGLETON:
            return _BUILTIN_SINGLETON[nm]

        # User-defined class — opaque.
        if nm in self.known or (nm and nm[0].isupper()):
            return _opaque_class(nm, self.aux)

        self.notes.append(f"unknown bare type {nm!r}")
        return _opaque_class(nm, self.aux)

    def _visit_attribute(self, node: ast.Attribute) -> str:
        # Dotted access — typing.X, collections.abc.X, etc.
        text = _dotted_name(node)
        if text:
            short = text.rsplit(".", 1)[-1]
            # If the short form is a known scalar / generic, dispatch.
            if short in _SCALAR:
                return _SCALAR[short]
            if short in _BUILTIN_GENERIC:
                head, _arity = _BUILTIN_GENERIC[short]
                if head == "Std.HashMap":
                    return "(Std.HashMap String Int)"
                if head == "Tuple":
                    return "(List Int)"
                return f"({head} Int)"
            if short in _BUILTIN_SINGLETON:
                return _BUILTIN_SINGLETON[short]
        try:
            text = ast.unparse(node)
        except Exception:
            text = node.attr
        return _opaque_class(text, self.aux)

    def _visit_subscript(self, node: ast.Subscript) -> str:
        base_node = node.value
        base = _dotted_name(base_node) or _name_text(base_node)
        slc = node.slice

        # Strip ``Annotated[T, *meta]`` / ``Final[T]`` / ``ClassVar[T]``.
        short = base.rsplit(".", 1)[-1]
        if short in {"Annotated", "Final", "ClassVar"}:
            if isinstance(slc, ast.Tuple) and slc.elts:
                return self.visit(slc.elts[0])
            return self.visit(slc)

        # ``TypeGuard[T]`` / ``TypeIs[T]`` are bool-valued.
        if short in {"TypeGuard", "TypeIs"}:
            return "Bool"

        # ``Required[T]`` / ``NotRequired[T]`` (TypedDict) — emit T.
        if short in {"Required", "NotRequired"}:
            return self.visit(slc)

        # ``Optional[T]``.
        if short == "Optional":
            inner = self.visit(slc)
            return f"(Option {inner})"

        # ``Union[A, B, ...]``.
        if short == "Union":
            return self._build_union(self._slice_elts(slc))

        # ``Literal[v1, v2, ...]``.
        if short == "Literal":
            return self._visit_literal(slc)

        # ``Callable[[A, B], R]`` / ``Callable[..., R]`` /
        # ``Callable[Concatenate[A, P], R]``.
        if short == "Callable":
            return self._visit_callable(slc)

        # ``Concatenate[A, P]`` — translate as a sequence of arrow
        # binders.  Used inside Callable; if we see it standalone,
        # render as the first arg.
        if short == "Concatenate":
            elts = self._slice_elts(slc)
            return self.visit(elts[0]) if elts else "α"

        # ``Unpack[Ts]`` for variadics — opaque.
        if short == "Unpack":
            return _opaque_class("Unpack", self.aux)

        # ``Generic[T, U]`` / ``Protocol[T]`` used as base class
        # markers — emit ``α`` so Lean treats them polymorphically.
        if short in {"Generic", "Protocol"}:
            return "α"

        # ``type[T]`` / ``Type[T]`` — Lean has no exact analogue;
        # emit opaque.
        if short in {"Type", "type"}:
            inner = self.visit(slc)
            return f"(Type_of {inner})"

        # Built-in / typing generics with known arity.
        if short in _BUILTIN_GENERIC:
            head, arity = _BUILTIN_GENERIC[short]
            params = self._slice_elts(slc)
            if head == "Std.HashMap":
                # dict[K, V]
                if len(params) == 2:
                    k = self.visit(params[0])
                    v = self.visit(params[1])
                    return f"(Std.HashMap {k} {v})"
                return "(Std.HashMap String Int)"
            if head == "Tuple":
                # ``tuple[T, ...]`` (homogeneous) vs ``tuple[A, B, C]``.
                if (len(params) == 2
                        and isinstance(params[1], ast.Constant)
                        and params[1].value is Ellipsis):
                    return f"(List {self.visit(params[0])})"
                if not params:
                    return "Unit"
                if len(params) == 1:
                    return f"(List {self.visit(params[0])})"
                rendered = [self.visit(p) for p in params]
                return "(" + " × ".join(rendered) + ")"
            if head == "Task":
                inner = self.visit(params[0]) if params else "Unit"
                return f"(Task {inner})"
            # Default: head with each arg.
            if not params:
                return f"({head} α)"
            rendered = [self.visit(p) for p in params]
            return "(" + head + " " + " ".join(rendered) + ")"

        # Subscript on a TypeVar / NewType / user class — render as
        # the underlying with type parameters.
        if base in self.ctx.type_aliases:
            try:
                inner = ast.parse(
                    self.ctx.type_aliases[base], mode="eval"
                ).body
                return self.visit(inner)
            except SyntaxError:
                pass
        if base in self.ctx.new_types:
            try:
                inner = ast.parse(
                    self.ctx.new_types[base], mode="eval"
                ).body
                return self.visit(inner)
            except SyntaxError:
                pass

        # Generic user class — emit opaque base with rendered args.
        params = self._slice_elts(slc)
        if not params:
            return _opaque_class(base, self.aux)
        head_text = _opaque_class(base, self.aux)
        rendered = [self.visit(p) for p in params]
        return "(" + head_text + " " + " ".join(rendered) + ")"

    def _visit_pep604_union(self, node: ast.BinOp) -> str:
        # Flatten chained ``A | B | C``.
        elts: list[ast.expr] = []
        def collect(n: ast.expr) -> None:
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr):
                collect(n.left); collect(n.right)
            else:
                elts.append(n)
        collect(node)
        return self._build_union(elts)

    def _visit_literal(self, slc: ast.expr) -> str:
        # Literal[v] → underlying scalar of v.
        elts = self._slice_elts(slc)
        if not elts:
            return "Unit"
        # Detect a uniform underlying type (all ints → Int, etc.).
        sample = elts[0]
        scalar = self._literal_scalar(sample)
        if all(self._literal_scalar(e) == scalar for e in elts):
            return scalar
        # Heterogeneous Literal — fall back to opaque.
        self.notes.append("Literal[...] with heterogeneous values")
        return _opaque_class("Literal", self.aux)

    @staticmethod
    def _literal_scalar(node: ast.expr) -> str:
        if isinstance(node, ast.Constant):
            v = node.value
            if isinstance(v, bool):
                return "Bool"
            if isinstance(v, int):
                return "Int"
            if isinstance(v, float):
                return "Float"
            if isinstance(v, str):
                return "String"
            if isinstance(v, bytes):
                return "ByteArray"
        return "α"

    def _visit_callable(self, slc: ast.expr) -> str:
        # ``Callable[<params>, <return>]``  — slc is a Tuple.
        elts = self._slice_elts(slc)
        if len(elts) != 2:
            self.notes.append("Callable with unrecognised parameter form")
            return "(α → β)"
        params_node, ret_node = elts
        # Params is one of:
        #   ast.List([A, B])              → A → B → R
        #   ast.Constant(Ellipsis)        → α → R   (any args)
        #   Concatenate[A, P]             → A → P_args → R
        #   ast.Name 'P'  (ParamSpec)     → P_args → R
        ret = self.visit(ret_node)
        if isinstance(params_node, ast.List):
            if not params_node.elts:
                return f"(Unit → {ret})"
            ps = [self.visit(p) for p in params_node.elts]
            return "(" + " → ".join(ps + [ret]) + ")"
        if (isinstance(params_node, ast.Constant)
                and params_node.value is Ellipsis):
            return f"(α → {ret})"
        if isinstance(params_node, ast.Subscript):
            base = _dotted_name(params_node.value) or _name_text(
                params_node.value)
            short = base.rsplit(".", 1)[-1]
            if short == "Concatenate":
                inner_elts = self._slice_elts(params_node.slice)
                # Concatenate[A, B, P] — render as A → B → α → R
                # (the trailing ParamSpec is replaced by α).
                front = inner_elts[:-1] if inner_elts else []
                fronts = [self.visit(p) for p in front]
                return "(" + " → ".join(fronts + ["α", ret]) + ")"
        if isinstance(params_node, ast.Name):
            # ParamSpec usage — opaque arg list.
            return f"(α → {ret})"
        self.notes.append("Callable with unrecognised parameter form")
        return f"(α → {ret})"

    # -- helpers -----------------------------------------------------

    @staticmethod
    def _slice_elts(slc: ast.expr) -> list[ast.expr]:
        if isinstance(slc, ast.Tuple):
            return list(slc.elts)
        return [slc]

    def _build_union(self, elts: list[ast.expr]) -> str:
        # Detect None alternatives → Optional / Option.
        nones = [e for e in elts
                 if isinstance(e, ast.Constant) and e.value is None]
        non_none = [e for e in elts if e not in nones]
        if not non_none:
            return "Unit"
        if len(non_none) == 1:
            translated = self.visit(non_none[0])
            return f"(Option {translated})" if nones else translated
        # 2+ non-None alternatives — recursive Sum.
        translated = [self.visit(e) for e in non_none]
        sum_text = self._fold_sum(translated)
        return f"(Option {sum_text})" if nones else sum_text

    @staticmethod
    def _fold_sum(types: list[str]) -> str:
        """Fold a list of Lean types into nested ``Sum`` — left-
        associative.  ``[A, B, C]`` → ``(Sum (Sum A B) C)``."""
        if not types:
            return "Unit"
        if len(types) == 1:
            return types[0]
        out = f"(Sum {types[0]} {types[1]})"
        for t in types[2:]:
            out = f"(Sum {out} {t})"
        return out

    def _render_type_var(self, spec: TypeVarSpec) -> str:
        """Render a TypeVar / ParamSpec / TypeVarTuple as Lean.

        With a single ``bound``, the underlying scalar wins (the
        TypeVar can be substituted with any subtype).  With
        ``constraints``, we union them.  Otherwise opaque.
        """
        if spec.is_param_spec:
            return "(α → β)"
        if spec.is_type_var_tuple:
            return _opaque_class(f"Variadic_{spec.name}", self.aux)
        if spec.bound:
            try:
                inner = ast.parse(spec.bound, mode="eval").body
                # Translate the bound — TypeVar('T', bound=Foo) means
                # any subtype of Foo, so emit Foo.
                return self.visit(inner)
            except SyntaxError:
                pass
        if spec.constraints:
            try:
                parsed = [ast.parse(c, mode="eval").body
                          for c in spec.constraints]
                return self._build_union(parsed)
            except SyntaxError:
                pass
        # Opaque polymorphic placeholder, deterministic per name.
        return _opaque_class(f"TypeVar_{spec.name}", self.aux)


# ─────────────────────────────────────────────────────────────────────
#  Helpers (public)
# ─────────────────────────────────────────────────────────────────────

def _opaque_class(name: str, aux: list[str]) -> str:
    safe = _sanitize_ident(name)
    decl = f"axiom {safe} : Type"
    if decl not in aux:
        aux.append(decl)
    return safe


def _sanitize_ident(text: str) -> str:
    raw = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in text)
    raw = raw.strip("_")
    if not raw:
        raw = "T"
    if not raw[0].isalpha() and raw[0] != "_":
        raw = "T_" + raw
    if len(raw) > 32:
        digest = hashlib.sha1(text.encode("utf-8")).hexdigest()[:8]
        raw = raw[:24] + "_" + digest
    return f"Deppy_{raw}" if not raw.startswith("Deppy_") else raw


def _dotted_name(node: ast.expr) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        head = _dotted_name(node.value)
        return head + "." + node.attr if head else node.attr
    return ""


def _name_text(node: ast.expr) -> str:
    return _dotted_name(node)


def _safe_text(node) -> str:
    try:
        return ast.unparse(node)
    except Exception:
        return ast.dump(node) if hasattr(node, "_fields") else str(node)


__all__ = [
    "TypeTranslation",
    "Context",
    "TypeVarSpec",
    "translate_annotation",
    "translate_annotation_str",
]
