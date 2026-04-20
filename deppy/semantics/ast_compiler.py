"""
Deppy AST Compiler — Python AST → SynTerm translation.

Translates Python source code (via the ``ast`` module) into Deppy's internal
representation (``SynTerm`` / ``SynType``).  This is the bridge between
concrete Python syntax and the formal verification layer.

Every Python expression maps to a ``SynTerm``, every type annotation maps to a
``SynType``, and every function definition maps to a ``CompiledFunction`` that
bundles the translated body together with extracted specifications.
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from typing import Any, Sequence

from deppy.core.types import (
    SynType, SynTerm, Context, Spec, SpecKind, FunctionSpec,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PyTupleType, PySetType, PyClassType,
    PiType, SigmaType, RefinementType, UnionType, OptionalType,
    Var, Literal, Lam, App, Pair, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)

# ═══════════════════════════════════════════════════════════════════
# Compiled output
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CompiledFunction:
    """Result of compiling a single Python function definition."""
    name: str
    params: list[tuple[str, SynType]]
    return_type: SynType
    body: SynTerm
    specs: list[Spec] = field(default_factory=list)
    source: str = ""
    ast_node: ast.FunctionDef | None = None

    def to_function_spec(self) -> FunctionSpec:
        """Convert to a ``FunctionSpec`` for the proof engine."""
        return FunctionSpec(
            name=self.name,
            params=list(self.params),
            return_type=self.return_type,
            guarantees=[s for s in self.specs if s.kind == SpecKind.GUARANTEE],
            assumptions=[s for s in self.specs if s.kind == SpecKind.ASSUME],
            checks=[s for s in self.specs if s.kind == SpecKind.CHECK],
        )


# ═══════════════════════════════════════════════════════════════════
# Operator mappings
# ═══════════════════════════════════════════════════════════════════

_BINOP_MAP: dict[type[ast.operator], str] = {
    ast.Add:      "__add__",
    ast.Sub:      "__sub__",
    ast.Mult:     "__mul__",
    ast.Div:      "__truediv__",
    ast.FloorDiv: "__floordiv__",
    ast.Mod:      "__mod__",
    ast.Pow:      "__pow__",
    ast.LShift:   "__lshift__",
    ast.RShift:   "__rshift__",
    ast.BitOr:    "__or__",
    ast.BitXor:   "__xor__",
    ast.BitAnd:   "__and__",
    ast.MatMult:  "__matmul__",
}

_UNARYOP_MAP: dict[type[ast.unaryop], str] = {
    ast.UAdd:   "__pos__",
    ast.USub:   "__neg__",
    ast.Invert: "__invert__",
    ast.Not:    "__not__",
}

_CMPOP_MAP: dict[type[ast.cmpop], str] = {
    ast.Eq:    "__eq__",
    ast.NotEq: "__ne__",
    ast.Lt:    "__lt__",
    ast.LtE:   "__le__",
    ast.Gt:    "__gt__",
    ast.GtE:   "__ge__",
    ast.Is:    "__is__",
    ast.IsNot: "__isnot__",
    ast.In:    "__contains__",
    ast.NotIn: "__not_contains__",
}

_AUGASSIGN_MAP: dict[type[ast.operator], str] = _BINOP_MAP  # reuses same ops


# ═══════════════════════════════════════════════════════════════════
# Annotation → SynType
# ═══════════════════════════════════════════════════════════════════

_SIMPLE_TYPE_MAP: dict[str, SynType] = {
    "int":    PyIntType(),
    "float":  PyFloatType(),
    "str":    PyStrType(),
    "bool":   PyBoolType(),
    "None":   PyNoneType(),
    "object": PyObjType(),
    "Any":    PyObjType(),
}


def _annotation_to_type(node: ast.expr | None) -> SynType:
    """Convert a Python type-annotation AST node to a ``SynType``."""
    if node is None:
        return PyObjType()

    # Simple name  ─  int, str, float, …
    if isinstance(node, ast.Name):
        return _SIMPLE_TYPE_MAP.get(node.id, PyObjType())

    if isinstance(node, ast.Constant) and node.value is None:
        return PyNoneType()

    # Subscript  ─  list[int], dict[str, int], Optional[X], …
    if isinstance(node, ast.Subscript):
        base = node.value
        if isinstance(base, ast.Name):
            name = base.id
            if name == "list":
                return PyListType(element_type=_annotation_to_type(node.slice))
            if name == "set":
                return PySetType(element_type=_annotation_to_type(node.slice))
            if name == "dict":
                if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                    return PyDictType(
                        key_type=_annotation_to_type(node.slice.elts[0]),
                        value_type=_annotation_to_type(node.slice.elts[1]),
                    )
                return PyDictType()
            if name == "tuple":
                if isinstance(node.slice, ast.Tuple):
                    return PyTupleType(
                        element_types=tuple(
                            _annotation_to_type(e) for e in node.slice.elts
                        )
                    )
                return PyTupleType(
                    element_types=(_annotation_to_type(node.slice),)
                )
            if name == "Optional":
                return OptionalType(inner=_annotation_to_type(node.slice))
            if name == "Callable":
                if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                    params_node, ret_node = node.slice.elts
                    param_types: tuple[SynType, ...] = ()
                    if isinstance(params_node, ast.List):
                        param_types = tuple(
                            _annotation_to_type(p) for p in params_node.elts
                        )
                    return PyCallableType(
                        param_types=param_types,
                        return_type=_annotation_to_type(ret_node),
                    )
                return PyCallableType()
        # Attribute subscript — e.g. typing.List[int]
        if isinstance(base, ast.Attribute):
            return _annotation_to_type(
                ast.Subscript(
                    value=ast.Name(id=base.attr, ctx=ast.Load()),
                    slice=node.slice,
                    ctx=ast.Load(),
                )
            )

    # Union  ─  X | Y  (Python 3.10+)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left = _annotation_to_type(node.left)
        right = _annotation_to_type(node.right)
        lefts = left.alternatives if isinstance(left, UnionType) else (left,)
        rights = right.alternatives if isinstance(right, UnionType) else (right,)
        return UnionType(alternatives=(*lefts, *rights))

    # Attribute  ─  module.Type
    if isinstance(node, ast.Attribute):
        return _SIMPLE_TYPE_MAP.get(node.attr, PyObjType())

    return PyObjType()


# ═══════════════════════════════════════════════════════════════════
# The compiler
# ═══════════════════════════════════════════════════════════════════

class ASTCompiler:
    """Compile Python AST to Deppy terms.

    Usage::

        compiler = ASTCompiler()
        funcs = compiler.compile_module(source_code)
        for f in funcs:
            print(f.name, f.body)
    """

    def __init__(self) -> None:
        self._source: str = ""

    # ── public API ────────────────────────────────────────────────

    def compile_module(self, source: str) -> list[CompiledFunction]:
        """Parse *source* and compile every top-level function."""
        self._source = textwrap.dedent(source)
        tree = ast.parse(self._source)
        results: list[CompiledFunction] = []
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                results.append(self.compile_function(node))
        return results

    def compile_function(self, node: ast.FunctionDef) -> CompiledFunction:
        """Compile a single ``ast.FunctionDef`` (or ``AsyncFunctionDef``)."""
        params = self._compile_params(node.args)
        return_type = _annotation_to_type(node.returns)
        body = self._compile_body(node.body)
        specs = self.extract_specs(node)
        source = ast.get_source_segment(self._source, node) or ""
        return CompiledFunction(
            name=node.name,
            params=params,
            return_type=return_type,
            body=body,
            specs=specs,
            source=source,
            ast_node=node,
        )

    # ── expression compilation ────────────────────────────────────

    def compile_expr(self, node: ast.expr) -> SynTerm:
        """Translate an ``ast.expr`` into a ``SynTerm``."""
        # --- literals ---
        if isinstance(node, ast.Constant):
            return Literal(value=node.value, type_=self._literal_type(node.value))

        # --- names ---
        if isinstance(node, ast.Name):
            return Var(name=node.id)

        # --- calls ---
        if isinstance(node, ast.Call):
            return self._compile_call(node)

        # --- attribute access ---
        if isinstance(node, ast.Attribute):
            return GetAttr(obj=self.compile_expr(node.value), attr=node.attr)

        # --- subscript ---
        if isinstance(node, ast.Subscript):
            return GetItem(
                obj=self.compile_expr(node.value),
                key=self.compile_expr(node.slice),
            )

        # --- binary ops ---
        if isinstance(node, ast.BinOp):
            dunder = _BINOP_MAP.get(type(node.op), "__add__")
            left = self.compile_expr(node.left)
            right = self.compile_expr(node.right)
            return PyCall(func=Var(dunder), args=(left, right))

        # --- unary ops ---
        if isinstance(node, ast.UnaryOp):
            dunder = _UNARYOP_MAP.get(type(node.op), "__pos__")
            operand = self.compile_expr(node.operand)
            if isinstance(node.op, ast.Not):
                return PyCall(func=Var("__not__"), args=(operand,))
            return PyCall(func=Var(dunder), args=(operand,))

        # --- comparisons (chained) ---
        if isinstance(node, ast.Compare):
            return self._compile_compare(node)

        # --- boolean ops (short-circuit) ---
        if isinstance(node, ast.BoolOp):
            return self._compile_boolop(node)

        # --- ternary if ---
        if isinstance(node, ast.IfExp):
            return IfThenElse(
                cond=self.compile_expr(node.test),
                then_branch=self.compile_expr(node.body),
                else_branch=self.compile_expr(node.orelse),
            )

        # --- lambda ---
        if isinstance(node, ast.Lambda):
            return self._compile_lambda(node)

        # --- list / tuple / set / dict constructors ---
        if isinstance(node, ast.List):
            elts = tuple(self.compile_expr(e) for e in node.elts)
            return PyCall(func=Var("list"), args=elts)

        if isinstance(node, ast.Tuple):
            elts = tuple(self.compile_expr(e) for e in node.elts)
            return PyCall(func=Var("tuple"), args=elts)

        if isinstance(node, ast.Set):
            elts = tuple(self.compile_expr(e) for e in node.elts)
            return PyCall(func=Var("set"), args=elts)

        if isinstance(node, ast.Dict):
            return self._compile_dict(node)

        # --- comprehensions ---
        if isinstance(node, ast.ListComp):
            return self._compile_comprehension(node, "list")

        if isinstance(node, ast.SetComp):
            return self._compile_comprehension(node, "set")

        if isinstance(node, ast.DictComp):
            return self._compile_dict_comprehension(node)

        if isinstance(node, ast.GeneratorExp):
            return self._compile_comprehension(node, "iter")

        # --- f-strings ---
        if isinstance(node, ast.JoinedStr):
            parts = tuple(self.compile_expr(v) for v in node.values)
            return PyCall(func=Var("format"), args=parts)

        if isinstance(node, ast.FormattedValue):
            return self.compile_expr(node.value)

        # --- starred ---
        if isinstance(node, ast.Starred):
            return PyCall(func=Var("__star__"), args=(self.compile_expr(node.value),))

        # --- named expression (walrus) ---
        if isinstance(node, ast.NamedExpr):
            return LetIn(
                var_name=node.target.id if isinstance(node.target, ast.Name) else "_",
                value=self.compile_expr(node.value),
                body=Var(node.target.id if isinstance(node.target, ast.Name) else "_"),
            )

        # --- slice ---
        if isinstance(node, ast.Slice):
            lower = self.compile_expr(node.lower) if node.lower else Literal(None)
            upper = self.compile_expr(node.upper) if node.upper else Literal(None)
            step = self.compile_expr(node.step) if node.step else Literal(None)
            return PyCall(func=Var("slice"), args=(lower, upper, step))

        # --- await ---
        if isinstance(node, ast.Await):
            return PyCall(func=Var("__await__"), args=(self.compile_expr(node.value),))

        # --- yield / yield from ---
        if isinstance(node, ast.Yield):
            val = self.compile_expr(node.value) if node.value else Literal(None)
            return PyCall(func=Var("__yield__"), args=(val,))

        if isinstance(node, ast.YieldFrom):
            return PyCall(
                func=Var("__yield_from__"),
                args=(self.compile_expr(node.value),),
            )

        # fallback
        return Var(f"<unsupported:{type(node).__name__}>")

    # ── statement compilation ─────────────────────────────────────

    def compile_stmt(self, node: ast.stmt) -> SynTerm:
        """Translate an ``ast.stmt`` into a ``SynTerm``."""
        # --- return ---
        if isinstance(node, ast.Return):
            if node.value is None:
                return Literal(None, type_=PyNoneType())
            return self.compile_expr(node.value)

        # --- expression statement ---
        if isinstance(node, ast.Expr):
            return self.compile_expr(node.value)

        # --- assignment ---
        if isinstance(node, ast.Assign):
            return self._compile_assign(node)

        # --- annotated assignment ---
        if isinstance(node, ast.AnnAssign):
            return self._compile_ann_assign(node)

        # --- augmented assignment ---
        if isinstance(node, ast.AugAssign):
            return self._compile_aug_assign(node)

        # --- if/elif/else ---
        if isinstance(node, ast.If):
            return self._compile_if(node)

        # --- while ---
        if isinstance(node, ast.While):
            return self._compile_while(node)

        # --- for ---
        if isinstance(node, ast.For):
            return self._compile_for(node)

        # --- with ---
        if isinstance(node, ast.With):
            return self._compile_with(node)

        # --- try ---
        if isinstance(node, ast.Try):
            return self._compile_try(node)

        # --- raise ---
        if isinstance(node, ast.Raise):
            exc = self.compile_expr(node.exc) if node.exc else Literal(None)
            return PyCall(func=Var("__raise__"), args=(exc,))

        # --- assert ---
        if isinstance(node, ast.Assert):
            test = self.compile_expr(node.test)
            msg = self.compile_expr(node.msg) if node.msg else Literal("assertion failed")
            return PyCall(func=Var("__assert__"), args=(test, msg))

        # --- nested function ---
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return self._compile_nested_function(node)

        # --- class ---
        if isinstance(node, ast.ClassDef):
            return self._compile_class(node)

        # --- import (kept as marker) ---
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            return Literal(value=None, type_=PyNoneType())

        # --- pass / break / continue ---
        if isinstance(node, ast.Pass):
            return Literal(value=None, type_=PyNoneType())

        if isinstance(node, ast.Break):
            return PyCall(func=Var("__break__"), args=())

        if isinstance(node, ast.Continue):
            return PyCall(func=Var("__continue__"), args=())

        # --- delete ---
        if isinstance(node, ast.Delete):
            targets = tuple(self.compile_expr(t) for t in node.targets)
            return PyCall(func=Var("__del__"), args=targets)

        # --- global / nonlocal (markers) ---
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            return Literal(value=None, type_=PyNoneType())

        return Var(f"<unsupported_stmt:{type(node).__name__}>")

    # ── type inference (basic) ────────────────────────────────────

    def infer_type(self, node: ast.expr) -> SynType:
        """Infer a ``SynType`` for an expression from available information.

        Uses type annotations when present, otherwise falls back to literal
        analysis and constructor recognition.
        """
        if isinstance(node, ast.Constant):
            return self._literal_type(node.value)

        if isinstance(node, ast.Name):
            return _SIMPLE_TYPE_MAP.get(node.id, PyObjType())

        if isinstance(node, ast.List):
            if node.elts:
                return PyListType(element_type=self.infer_type(node.elts[0]))
            return PyListType()

        if isinstance(node, ast.Dict):
            kt = self.infer_type(node.keys[0]) if node.keys and node.keys[0] else PyObjType()
            vt = self.infer_type(node.values[0]) if node.values else PyObjType()
            return PyDictType(key_type=kt, value_type=vt)

        if isinstance(node, ast.Tuple):
            return PyTupleType(
                element_types=tuple(self.infer_type(e) for e in node.elts)
            )

        if isinstance(node, ast.Set):
            if node.elts:
                return PySetType(element_type=self.infer_type(node.elts[0]))
            return PySetType()

        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                name = node.func.id
                if name in _SIMPLE_TYPE_MAP:
                    return _SIMPLE_TYPE_MAP[name]
                if name == "list":
                    return PyListType()
                if name == "dict":
                    return PyDictType()
                if name == "tuple":
                    return PyTupleType()
                if name == "set":
                    return PySetType()

        if isinstance(node, ast.BinOp):
            return self.infer_type(node.left)

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                return PyBoolType()
            return self.infer_type(node.operand)

        if isinstance(node, ast.Compare):
            return PyBoolType()

        if isinstance(node, ast.BoolOp):
            return PyBoolType()

        if isinstance(node, ast.IfExp):
            return self.infer_type(node.body)

        if isinstance(node, ast.JoinedStr):
            return PyStrType()

        if isinstance(node, ast.Lambda):
            ret = self.infer_type(node.body)
            ptypes = tuple(PyObjType() for _ in node.args.args)
            return PyCallableType(param_types=ptypes, return_type=ret)

        return PyObjType()

    # ── spec extraction ───────────────────────────────────────────

    def extract_specs(self, node: ast.FunctionDef) -> list[Spec]:
        """Extract ``@guarantee``, ``@assume``, ``@check`` specs from decorators
        and docstrings of *node*.
        """
        specs: list[Spec] = []

        # Decorators
        for deco in node.decorator_list:
            spec = self._spec_from_decorator(deco, node.name)
            if spec is not None:
                specs.append(spec)

        # Docstring — treat first triple-quoted string as a guarantee
        if (
            node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
            and isinstance(node.body[0].value.value, str)
        ):
            docstring = node.body[0].value.value.strip()
            if docstring:
                specs.append(Spec(
                    kind=SpecKind.GUARANTEE,
                    description=docstring,
                    source_func=node.name,
                    source_line=node.lineno,
                ))

        return specs

    # ══════════════════════════════════════════════════════════════
    # Private helpers
    # ══════════════════════════════════════════════════════════════

    # ── parameters ────────────────────────────────────────────────

    def _compile_params(
        self, args: ast.arguments
    ) -> list[tuple[str, SynType]]:
        """Extract ``(name, SynType)`` pairs from function arguments."""
        params: list[tuple[str, SynType]] = []
        for arg in args.args:
            ty = _annotation_to_type(arg.annotation)
            params.append((arg.arg, ty))
        if args.vararg:
            ty = _annotation_to_type(args.vararg.annotation)
            params.append((f"*{args.vararg.arg}", PyListType(element_type=ty)))
        for arg in args.kwonlyargs:
            ty = _annotation_to_type(arg.annotation)
            params.append((arg.arg, ty))
        if args.kwarg:
            ty = _annotation_to_type(args.kwarg.annotation)
            params.append((f"**{args.kwarg.arg}", PyDictType(key_type=PyStrType(), value_type=ty)))
        return params

    # ── body ──────────────────────────────────────────────────────

    def _compile_body(self, stmts: list[ast.stmt]) -> SynTerm:
        """Compile a list of statements into a single ``SynTerm``.

        The key idea: a sequence ``s1; s2; … ; sN`` is translated into
        nested ``LetIn`` nodes so that each statement feeds into the next.
        The last statement is the "return value" of the block.
        """
        if not stmts:
            return Literal(None, type_=PyNoneType())

        # Skip docstrings at the top
        start = 0
        if (
            isinstance(stmts[0], ast.Expr)
            and isinstance(stmts[0].value, ast.Constant)
            and isinstance(stmts[0].value.value, str)
        ):
            start = 1

        compiled = [self.compile_stmt(s) for s in stmts[start:]]
        if not compiled:
            return Literal(None, type_=PyNoneType())

        return self._sequence(compiled, stmts[start:])

    def _sequence(
        self, terms: list[SynTerm], stmts: list[ast.stmt]
    ) -> SynTerm:
        """Chain *terms* produced from *stmts* into nested ``LetIn`` bindings.

        If a statement already produced a ``LetIn`` (e.g. from an assignment),
        the next term is spliced into its body.  Otherwise a fresh ``LetIn``
        with a throwaway name is created.
        """
        if len(terms) == 1:
            return terms[0]

        result = terms[-1]
        for i in range(len(terms) - 2, -1, -1):
            cur = terms[i]
            if isinstance(cur, LetIn) and self._is_placeholder_body(cur):
                result = LetIn(
                    var_name=cur.var_name,
                    var_type=cur.var_type,
                    value=cur.value,
                    body=result,
                )
            else:
                result = LetIn(
                    var_name=f"_s{i}",
                    value=cur,
                    body=result,
                )
        return result

    @staticmethod
    def _is_placeholder_body(letin: LetIn) -> bool:
        """Check if a ``LetIn``'s body is just the bound variable (placeholder)."""
        return isinstance(letin.body, Var) and letin.body.name == letin.var_name

    # ── calls ─────────────────────────────────────────────────────

    def _compile_call(self, node: ast.Call) -> SynTerm:
        func = self.compile_expr(node.func)
        args = tuple(self.compile_expr(a) for a in node.args)
        kwargs = tuple(
            (kw.arg or "_", self.compile_expr(kw.value)) for kw in node.keywords
        )
        return PyCall(func=func, args=args, kwargs=kwargs)

    # ── comparisons ───────────────────────────────────────────────

    def _compile_compare(self, node: ast.Compare) -> SynTerm:
        """Compile chained comparisons ``a < b < c`` into ANDed pairs."""
        left = self.compile_expr(node.left)
        parts: list[SynTerm] = []
        for op, comp in zip(node.ops, node.comparators):
            right = self.compile_expr(comp)
            dunder = _CMPOP_MAP.get(type(op), "__eq__")
            parts.append(PyCall(func=Var(dunder), args=(left, right)))
            left = right
        if len(parts) == 1:
            return parts[0]
        # chain with AND
        result = parts[0]
        for p in parts[1:]:
            result = IfThenElse(cond=result, then_branch=p, else_branch=Literal(False))
        return result

    # ── boolean ops ───────────────────────────────────────────────

    def _compile_boolop(self, node: ast.BoolOp) -> SynTerm:
        """Compile ``and`` / ``or`` as short-circuit ``IfThenElse``."""
        values = [self.compile_expr(v) for v in node.values]
        if isinstance(node.op, ast.And):
            result = values[-1]
            for v in reversed(values[:-1]):
                result = IfThenElse(
                    cond=v, then_branch=result, else_branch=Literal(False)
                )
            return result
        else:  # Or
            result = values[-1]
            for v in reversed(values[:-1]):
                result = IfThenElse(
                    cond=v, then_branch=v, else_branch=result
                )
            return result

    # ── lambda ────────────────────────────────────────────────────

    def _compile_lambda(self, node: ast.Lambda) -> SynTerm:
        """Compile a lambda expression to nested ``Lam`` terms."""
        body = self.compile_expr(node.body)
        params = node.args.args
        if not params:
            return Lam(param="_", param_type=PyNoneType(), body=body)
        result = body
        for arg in reversed(params):
            ty = _annotation_to_type(arg.annotation)
            result = Lam(param=arg.arg, param_type=ty, body=result)
        return result

    # ── dict ──────────────────────────────────────────────────────

    def _compile_dict(self, node: ast.Dict) -> SynTerm:
        pairs: list[SynTerm] = []
        for k, v in zip(node.keys, node.values):
            if k is None:
                # ** unpacking
                pairs.append(PyCall(func=Var("__star__"), args=(self.compile_expr(v),)))
            else:
                pairs.append(Pair(fst=self.compile_expr(k), snd=self.compile_expr(v)))
        return PyCall(func=Var("dict"), args=tuple(pairs))

    # ── comprehensions ────────────────────────────────────────────

    def _compile_comprehension(
        self,
        node: ast.ListComp | ast.SetComp | ast.GeneratorExp,
        kind: str,
    ) -> SynTerm:
        """Compile a list/set/generator comprehension as a fold.

        ``[f(x) for x in xs if p(x)]`` becomes:
        ``fold(xs, [], λ(acc, x). if p(x) then append(acc, f(x)) else acc)``
        """
        elt = self.compile_expr(node.elt)
        result: SynTerm = elt

        for gen in reversed(node.generators):
            iter_expr = self.compile_expr(gen.iter)
            target_name = self._target_name(gen.target)

            # Apply filters (innermost first)
            for cond in reversed(gen.ifs):
                cond_term = self.compile_expr(cond)
                result = IfThenElse(
                    cond=cond_term,
                    then_branch=PyCall(
                        func=Var(f"__{kind}_append__"),
                        args=(Var("__acc__"), result),
                    ),
                    else_branch=Var("__acc__"),
                )

            if not gen.ifs:
                result = PyCall(
                    func=Var(f"__{kind}_append__"),
                    args=(Var("__acc__"), result),
                )

            step_fn = Lam(
                param="__acc__",
                param_type=PyObjType(),
                body=Lam(param=target_name, param_type=PyObjType(), body=result),
            )
            result = PyCall(
                func=Var("__fold__"),
                args=(iter_expr, PyCall(func=Var(kind), args=()), step_fn),
            )

        return result

    def _compile_dict_comprehension(self, node: ast.DictComp) -> SynTerm:
        """Compile ``{k: v for ...}`` as a fold producing a dict."""
        key_expr = self.compile_expr(node.key)
        val_expr = self.compile_expr(node.value)
        entry = Pair(fst=key_expr, snd=val_expr)
        result: SynTerm = entry

        for gen in reversed(node.generators):
            iter_expr = self.compile_expr(gen.iter)
            target_name = self._target_name(gen.target)

            for cond in reversed(gen.ifs):
                cond_term = self.compile_expr(cond)
                result = IfThenElse(
                    cond=cond_term,
                    then_branch=PyCall(
                        func=Var("__dict_set__"),
                        args=(Var("__acc__"), result),
                    ),
                    else_branch=Var("__acc__"),
                )

            if not gen.ifs:
                result = PyCall(
                    func=Var("__dict_set__"),
                    args=(Var("__acc__"), result),
                )

            step_fn = Lam(
                param="__acc__",
                param_type=PyDictType(),
                body=Lam(param=target_name, param_type=PyObjType(), body=result),
            )
            result = PyCall(
                func=Var("__fold__"),
                args=(iter_expr, PyCall(func=Var("dict"), args=()), step_fn),
            )

        return result

    # ── assignments ───────────────────────────────────────────────

    def _compile_assign(self, node: ast.Assign) -> SynTerm:
        """``x = expr`` → ``LetIn(x, expr, x)``  (placeholder body)."""
        value = self.compile_expr(node.value)
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            return LetIn(var_name=name, value=value, body=Var(name))
        # Tuple unpacking or complex targets — emit as generic assign call
        targets = tuple(self.compile_expr(t) for t in node.targets)
        return PyCall(func=Var("__assign__"), args=(*targets, value))

    def _compile_ann_assign(self, node: ast.AnnAssign) -> SynTerm:
        """``x: int = expr`` → ``LetIn(x, expr, x)`` with type."""
        ty = _annotation_to_type(node.annotation)
        if node.value is None:
            val: SynTerm = Literal(None, type_=PyNoneType())
        else:
            val = self.compile_expr(node.value)
        if isinstance(node.target, ast.Name):
            return LetIn(var_name=node.target.id, var_type=ty, value=val, body=Var(node.target.id))
        return PyCall(func=Var("__assign__"), args=(self.compile_expr(node.target), val))

    def _compile_aug_assign(self, node: ast.AugAssign) -> SynTerm:
        """``x += expr`` → ``LetIn(x, __iadd__(x, expr), x)``."""
        dunder = _AUGASSIGN_MAP.get(type(node.op), "__add__")
        i_dunder = dunder.replace("__", "__i", 1)  # e.g. __iadd__
        target = self.compile_expr(node.target)
        value = self.compile_expr(node.value)
        combined = PyCall(func=Var(i_dunder), args=(target, value))
        if isinstance(node.target, ast.Name):
            return LetIn(var_name=node.target.id, value=combined, body=Var(node.target.id))
        return PyCall(func=Var("__assign__"), args=(target, combined))

    # ── control flow ──────────────────────────────────────────────

    def _compile_if(self, node: ast.If) -> SynTerm:
        cond = self.compile_expr(node.test)
        then_body = self._compile_body(node.body)
        else_body = (
            self._compile_body(node.orelse)
            if node.orelse
            else Literal(None, type_=PyNoneType())
        )
        return IfThenElse(cond=cond, then_branch=then_body, else_branch=else_body)

    def _compile_while(self, node: ast.While) -> SynTerm:
        """``while cond: body`` → recursive fold with termination marker.

        We model it as:
        ``__while__(λ(). cond, λ(). body)``
        """
        cond = self.compile_expr(node.test)
        body = self._compile_body(node.body)
        cond_fn = Lam(param="_", param_type=PyNoneType(), body=cond)
        body_fn = Lam(param="_", param_type=PyNoneType(), body=body)
        term: SynTerm = PyCall(func=Var("__while__"), args=(cond_fn, body_fn))
        if node.orelse:
            else_body = self._compile_body(node.orelse)
            term = LetIn(var_name="_while_res", value=term, body=else_body)
        return term

    def _compile_for(self, node: ast.For) -> SynTerm:
        """``for x in iter: body`` → ``__fold__(iter, None, λ(acc, x). body)``."""
        target_name = self._target_name(node.target)
        iter_expr = self.compile_expr(node.iter)
        body = self._compile_body(node.body)
        step_fn = Lam(
            param="__acc__",
            param_type=PyObjType(),
            body=Lam(param=target_name, param_type=PyObjType(), body=body),
        )
        init = Literal(None, type_=PyNoneType())
        term: SynTerm = PyCall(func=Var("__fold__"), args=(iter_expr, init, step_fn))
        if node.orelse:
            else_body = self._compile_body(node.orelse)
            term = LetIn(var_name="_for_res", value=term, body=else_body)
        return term

    def _compile_with(self, node: ast.With) -> SynTerm:
        """``with expr as x: body`` → LetIn with __enter__/__exit__."""
        body = self._compile_body(node.body)
        for item in reversed(node.items):
            ctx_expr = self.compile_expr(item.context_expr)
            enter = PyCall(func=GetAttr(obj=ctx_expr, attr="__enter__"), args=())
            exit_call = PyCall(func=GetAttr(obj=ctx_expr, attr="__exit__"), args=())
            var_name = (
                item.optional_vars.id
                if item.optional_vars and isinstance(item.optional_vars, ast.Name)
                else "_ctx"
            )
            body = LetIn(
                var_name=var_name,
                value=enter,
                body=LetIn(var_name="_exit", value=body, body=LetIn(
                    var_name="_", value=exit_call, body=Var("_exit"),
                )),
            )
        return body

    def _compile_try(self, node: ast.Try) -> SynTerm:
        """``try: … except …: … else: … finally: …`` → structured term."""
        try_body = self._compile_body(node.body)
        handlers: list[SynTerm] = []
        for handler in node.handlers:
            exc_name = handler.name or "_exc"
            exc_type_str = ""
            if handler.type:
                if isinstance(handler.type, ast.Name):
                    exc_type_str = handler.type.id
                else:
                    exc_type_str = ast.dump(handler.type)
            handler_body = self._compile_body(handler.body)
            handlers.append(
                Lam(param=exc_name, param_type=PyObjType(), body=handler_body)
            )
        else_body = self._compile_body(node.orelse) if node.orelse else Literal(None)
        finally_body = self._compile_body(node.finalbody) if node.finalbody else Literal(None)
        return PyCall(
            func=Var("__try__"),
            args=(try_body, *handlers),
            kwargs=(
                ("else_", else_body),
                ("finally_", finally_body),
            ),
        )

    # ── nested definitions ────────────────────────────────────────

    def _compile_nested_function(self, node: ast.FunctionDef) -> SynTerm:
        """Nested function → ``LetIn(name, lambda, name)`` (placeholder body)."""
        params = self._compile_params(node.args)
        body = self._compile_body(node.body)
        fn_term = body
        for pname, ptype in reversed(params):
            fn_term = Lam(param=pname, param_type=ptype, body=fn_term)
        return LetIn(var_name=node.name, value=fn_term, body=Var(node.name))

    def _compile_class(self, node: ast.ClassDef) -> SynTerm:
        """Class → ``LetIn(name, dict-of-methods, name)`` (duck-type view)."""
        methods: list[SynTerm] = []
        for stmt in node.body:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                nested = self._compile_nested_function(stmt)
                methods.append(Pair(fst=Literal(stmt.name), snd=nested))
            elif isinstance(stmt, ast.Assign):
                compiled = self._compile_assign(stmt)
                methods.append(compiled)
        class_dict = PyCall(func=Var("__class__"), args=tuple(methods),
                            kwargs=(("name", Literal(node.name)),))
        return LetIn(var_name=node.name, value=class_dict, body=Var(node.name))

    # ── spec extraction helpers ───────────────────────────────────

    def _spec_from_decorator(
        self, deco: ast.expr, func_name: str
    ) -> Spec | None:
        """Try to parse a decorator as ``@guarantee("…")``, ``@assume("…")``,
        or ``@check("…")``."""
        # @guarantee("desc") / @assume("desc") / @check("desc")
        if isinstance(deco, ast.Call) and isinstance(deco.func, ast.Name):
            kind_name = deco.func.id.upper()
            try:
                kind = SpecKind[kind_name]
            except KeyError:
                return None
            if deco.args and isinstance(deco.args[0], ast.Constant):
                desc = str(deco.args[0].value)
            else:
                desc = kind_name.lower()
            return Spec(
                kind=kind,
                description=desc,
                source_func=func_name,
            )
        # @guarantee  (bare decorator — no args)
        if isinstance(deco, ast.Name):
            kind_name = deco.id.upper()
            try:
                kind = SpecKind[kind_name]
            except KeyError:
                return None
            return Spec(kind=kind, description="", source_func=func_name)
        return None

    # ── utilities ─────────────────────────────────────────────────

    @staticmethod
    def _target_name(target: ast.expr) -> str:
        """Extract a variable name from an assignment target."""
        if isinstance(target, ast.Name):
            return target.id
        if isinstance(target, ast.Tuple):
            names = []
            for elt in target.elts:
                if isinstance(elt, ast.Name):
                    names.append(elt.id)
                else:
                    names.append("_")
            return "_".join(names)
        return "_"

    @staticmethod
    def _literal_type(value: object) -> SynType:
        """Map a Python literal value to its ``SynType``."""
        if isinstance(value, bool):
            return PyBoolType()
        if isinstance(value, int):
            return PyIntType()
        if isinstance(value, float):
            return PyFloatType()
        if isinstance(value, str):
            return PyStrType()
        if value is None:
            return PyNoneType()
        if isinstance(value, bytes):
            return PyObjType()
        if isinstance(value, complex):
            return PyObjType()
        return PyObjType()


# ═══════════════════════════════════════════════════════════════════
# Self-test
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    sample = textwrap.dedent("""\
        def add(x: int, y: int) -> int:
            return x + y

        def greet(name: str) -> str:
            greeting = "Hello, " + name
            return greeting

        def maximum(a: int, b: int) -> int:
            if a > b:
                return a
            else:
                return b

        def total(xs: list[int]) -> int:
            s = 0
            for x in xs:
                s += x
            return s
    """)

    compiler = ASTCompiler()
    funcs = compiler.compile_module(sample)

    for fn in funcs:
        print(f"╔══ {fn.name} ══")
        print(f"║  params:  {fn.params}")
        print(f"║  returns: {fn.return_type}")
        print(f"║  body:    {fn.body}")
        if fn.specs:
            print(f"║  specs:   {fn.specs}")
        print("╚" + "═" * 40)
        print()
